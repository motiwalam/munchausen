// The exact search on a GPU, through Vulkan. shaders/search.comp holds the
// search itself; this file builds its tables, feeds it work items in
// dispatches of bounded length, and collects the results.
use super::{DV, Local, Search, Unit};
use crate::vk::{Buffer, Gpu, Kernel};
use std::time::Instant;

const HEADER: usize = 16;
const FOUND: usize = 80;
// at most one cursor per level below the root, plus the current one
const MAXLEV: usize = 63;
const MAXFOUND: usize = 4096;
// a dispatch should take about this long; the xe driver kills jobs after 5 s
const TARGET_SECS: f64 = 0.25;

static SPIRV1: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/search1.spv"));
static SPIRV2: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/search2.spv"));

pub struct GpuOptions {
    /// number of subgroups that search in parallel
    pub subgroups: u32,
    pub verbose: bool,
}

struct Ctx {
    gpu: Gpu,
    kernel: Kernel,
    items: Buffer,
    out: Buffer,
    stats: Buffer,
    found: Buffer,
    ctl: Buffer,
    bufs: Vec<Buffer>,
}

impl<const N: usize> Search<N> {
    fn gpu_tables(&self) -> (Vec<u32>, Vec<u8>) {
        let vb = 32 * N;
        let mut par = vec![];
        let mut tab: Vec<u8> = vec![];
        let put = |tab: &mut Vec<u8>, v: &DV<N>| -> u32 {
            let i = tab.len() / vb;
            let mut x = [0u8; 64];
            v.to_bytes(&mut x);
            tab.extend_from_slice(&x[..vb]);
            i as u32
        };
        for p in &self.params {
            let (kmax, d) = (p.kmax, p.d as usize);
            let mut row = [0u32; 16];
            row[0] = p.d;
            row[1] = kmax as u32;
            row[2] = tab.len() as u32 / vb as u32;
            p.w.iter().for_each(|v| _ = put(&mut tab, v));
            row[3] = tab.len() as u32 / vb as u32;
            p.dhi.iter().for_each(|v| _ = put(&mut tab, v));
            row[4] = tab.len() as u32 / vb as u32;
            p.shift.iter().for_each(|v| _ = put(&mut tab, v));
            row[5] = tab.len() as u32 / vb as u32;
            p.drop.iter().for_each(|v| _ = put(&mut tab, v));
            row[6] = tab.len() as u32 / vb as u32;
            (0..=d).for_each(|m| _ = put(&mut tab, p.mul_w(0, m as u32)));
            row[7] = put(&mut tab, &p.pow_lo);
            row[8] = put(&mut tab, &p.max_v);
            debug_assert_eq!(p.w.len(), kmax + 1);
            par.extend_from_slice(&row);
        }
        (par, tab)
    }

    fn gpu_item(&self, u: &Unit<N>, out: &mut Vec<u8>) {
        let vb = 32 * N;
        let mut h = [0u8; HEADER];
        h[0] = u.pi as u8;
        h[1] = u.k as u8;
        h[4] = u.n.pp as u8;
        h[5] = u.n.rf as u8;
        h[6] = 1; // count the node itself
        out.extend_from_slice(&h);
        let mut x = [0u8; 64];
        u.n.t.to_bytes(&mut x);
        out.extend_from_slice(&x[..vb]);
        u.n.hi.to_bytes(&mut x);
        out.extend_from_slice(&x[..vb]);
        out.extend(std::iter::repeat_n(0u8, 2 * vb));
        out.extend_from_slice(&u.cnt[..vb]);
    }

    fn gpu_setup(&self, b: u32, o: &GpuOptions) -> Result<Ctx, String> {
        let vb = 32 * N;
        let item = HEADER + 5 * vb;
        let gpu = Gpu::new()?;
        if o.verbose {
            eprintln!("  gpu: {}", gpu.name);
        }
        let (par, tab) = self.gpu_tables();
        let mut parb = gpu.buffer(par.len() * 4)?;
        parb.u32s_mut()[..par.len()].copy_from_slice(&par);
        let mut tabb = gpu.buffer(tab.len())?;
        tabb.bytes_mut()[..tab.len()].copy_from_slice(&tab);
        let sg = o.subgroups as usize;
        let items = gpu.buffer(64 * sg * item)?;
        let out = gpu.buffer(MAXLEV * sg * item)?;
        let stats = gpu.buffer(2 * sg * 8)?;
        let found = gpu.buffer(MAXFOUND * FOUND)?;
        let ctl = gpu.buffer(16)?;
        let kernel = gpu.kernel(if N == 1 { SPIRV1 } else { SPIRV2 }, 7, 20, 32)?;
        gpu.bind(&kernel, &[&parb, &tabb, &items, &out, &stats, &found, &ctl]);
        let _ = b;
        Ok(Ctx { gpu, kernel, items, out, stats, found, ctl, bufs: vec![parb, tabb] })
    }

    /// Search the given units on the GPU. Adds to the node counts and the
    /// solutions of self, like run_units.
    pub fn run_gpu(&self, b: u32, units: &[Unit<N>], o: &GpuOptions) -> Result<(), String> {
        if b as usize > 32 * N {
            return Err(format!("--gpu handles bases up to {} for numbers of this width", 32 * N));
        }
        if self.inexact {
            return Err("--gpu runs only the exact search".into());
        }
        let vb = 32 * N;
        let item = HEADER + 5 * vb;
        let mut c = self.gpu_setup(b, o)?;
        let sg = o.subgroups as usize;
        let cap = 64 * sg;
        // a stack of work items; the first unit is on top
        let mut pending: Vec<u8> = Vec::with_capacity(units.len() * item);
        for u in units.iter().rev() {
            self.gpu_item(u, &mut pending);
        }
        let mut budget: u32 = 4096;
        let (mut rounds, mut busy) = (0u64, 0.0f64);
        let start = Instant::now();
        while !pending.is_empty() {
            let have = pending.len() / item;
            let n = have.min(cap);
            let chunk = pending.split_off((have - n) * item);
            c.items.bytes_mut()[..chunk.len()].copy_from_slice(&chunk);
            c.ctl.u32s_mut()[..4].fill(0);
            // with few items, split them sooner so that every subgroup gets work
            let eff = if n < sg { ((budget as usize * n / sg) as u32).max(256) } else { budget };
            let push: Vec<u8> = [n as u32, eff, (MAXLEV * sg) as u32, MAXFOUND as u32, b].iter().flat_map(|v| v.to_le_bytes()).collect();
            let t = Instant::now();
            c.gpu.run(&c.kernel, &push, (sg / 2) as u32)?;
            let dt = t.elapsed().as_secs_f64();
            busy += dt;
            rounds += 1;
            let ctl = c.ctl.u32s();
            let (taken, nout, nfound) = ((ctl[0] as usize).min(n), ctl[1] as usize, ctl[2] as usize);
            if nfound > MAXFOUND {
                return Err("too many solutions for the GPU buffer".into());
            }
            // the subgroups stopped early, so the time measures the budget
            if taken < n && eff == budget {
                budget = ((budget as f64 * (TARGET_SECS / dt).clamp(0.5, 2.0)) as u32).clamp(256, 1 << 24);
            }
            pending.extend_from_slice(&chunk[taken * item..]);
            pending.extend_from_slice(&c.out.bytes()[..nout * item]);
            for r in c.found.bytes()[..nfound * FOUND].chunks_exact(FOUND) {
                let (mode, d) = (r[0] as u32, r[1] as u32);
                let mut x = [0u8; 64];
                x.copy_from_slice(&r[16..80]);
                if let Some(f) = &self.on_found {
                    f(mode, d, &x);
                }
                self.found.lock().unwrap().push((mode, d, x));
            }
            if o.verbose {
                eprintln!("  gpu round {rounds}: {n} items, {taken} taken, {nout} split off, budget {eff}, {:.1} ms", dt * 1e3);
            }
        }
        let st = c.stats.bytes();
        let word = |i: usize| u64::from_le_bytes(st[8 * i..8 * i + 8].try_into().unwrap());
        let l = Local { nodes: (0..sg).map(|i| word(2 * i)).sum(), evals: (0..sg).map(|i| word(2 * i + 1)).sum(), skipped: 0.0 };
        {
            eprintln!(
                "  gpu: {rounds} dispatches, {:.3} s on the GPU, {:.3} s in all, {:.1} M nodes/s",
                busy,
                start.elapsed().as_secs_f64(),
                l.nodes as f64 / busy / 1e6
            );
        }
        self.flush(&l);
        let Ctx { gpu, kernel, items, out, stats, found, ctl, bufs } = c;
        gpu.free_kernel(kernel);
        for x in [items, out, stats, found, ctl].into_iter().chain(bufs) {
            gpu.free(x);
        }
        Ok(())
    }
}
