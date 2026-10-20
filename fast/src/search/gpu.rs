// The exact search on a GPU, through Vulkan. shaders/search.comp holds the
// search itself; this file builds its tables, feeds it work items in
// dispatches of bounded length, and collects the results.
use super::{DV, Local, Search, Unit};
use crate::vk::{Buffer, Gpu, Kernel};
use super::{Cursor, Head, Node};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Instant;

const HEADER: usize = 16;
const FOUND: usize = 80;
// at most one cursor per level below the root, plus the current one
const MAXLEV: usize = 63;
const MAXFOUND: usize = 4096;
// a dispatch should take about this long; the xe driver kills jobs after 5 s
const TARGET_SECS: f64 = 0.25;
// threads per workgroup
const GROUP: usize = 64;

// Digit vectors in GPU buffers are stored lane by lane: byte l * C + c
// holds digit l + L c, with L lanes and C digits per lane.
fn gpu_order(x: &[u8], c: usize, out: &mut Vec<u8>) {
    let l = x.len() / c;
    for i in 0..l {
        for j in 0..c {
            out.push(x[l * j + i]);
        }
    }
}

static SPIRV1: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/search1.spv"));
static SPIRV2: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/search2.spv"));
// lanes per subgroup; numbers of N words have N digits per lane. Subgroups
// of 16 lanes with 2 N digits each measured slower for N = 1 and the same
// for N = 2.
const LANES: usize = 32;

pub struct GpuOptions {
    /// number of subgroups that search in parallel
    pub subgroups: u32,
    /// whether the CPU threads search units too
    pub cpu: bool,
    pub verbose: bool,
}

struct Shared {
    /// the next unit to claim
    next: AtomicUsize,
    /// a stack of GPU work items: claimed units and split-off cursors
    pending: Mutex<Vec<u8>>,
    gpu_done: AtomicBool,
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
            gpu_order(&x[..vb], N, tab);
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
            // the residue rule: r_m(x) by digit value for m = 0, 1, then the
            // sets rok[2 k + m] as four words each
            let mut x = [0u8; 64];
            for m in 0..2 {
                x[..=kmax].copy_from_slice(&p.rres[m * (kmax + 1)..(m + 1) * (kmax + 1)]);
                let i = put(&mut tab, &DV::from_bytes(&x));
                if m == 0 {
                    row[12] = i;
                }
            }
            row[13] = (tab.len() / 4) as u32;
            for v in &p.rok {
                (0..4).for_each(|j| tab.extend_from_slice(&((v >> (32 * j)) as u32).to_le_bytes()));
            }
            tab.resize(tab.len().next_multiple_of(vb), 0);
            if self.inexact {
                // The typical-set test in fixed point (2^-20): a child fails
                // if lneed + G[k][rf] > A[k][pp], where lneed is the sum of
                // LF[need_x] = ln(need_x!) over the decided digits, and
                // ln E < thr is the same inequality. A cell that is not
                // tested holds i32::MAX.
                let fix = |x: f64| (x * (1u64 << 20) as f64).round() as i32;
                let words = |tab: &mut Vec<u8>, v: &[i32]| -> u32 {
                    let i = tab.len() / 4;
                    v.iter().for_each(|x| tab.extend_from_slice(&x.to_le_bytes()));
                    i as u32
                };
                let lf: Vec<i32> = (0..=64).map(|n| fix((1..=n).map(|j| (j as f64).ln()).sum())).collect();
                let mut g = vec![0i32; (kmax + 1) * (d + 1)];
                let mut a = vec![i32::MAX; (kmax + 1) * (d + 1)];
                for k in 1..=kmax {
                    for m in 0..=d {
                        g[k * (d + 1) + m] = fix(p.ln_fact[m] - m as f64 * p.ln_k[k]);
                        if p.zscore.is_finite() && k <= p.zk {
                            a[k * (d + 1) + m] = fix(p.ln_fact[m] - m as f64 * p.ln_b - p.lik_thr[k * (d + 1) + m]);
                        }
                    }
                }
                row[9] = words(&mut tab, &lf);
                row[10] = words(&mut tab, &g);
                row[11] = words(&mut tab, &a);
                // keep the next digit vectors aligned
                tab.resize(tab.len().next_multiple_of(vb), 0);
            }
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
        gpu_order(&x[..vb], N, out);
        u.n.hi.to_bytes(&mut x);
        gpu_order(&x[..vb], N, out);
        out.extend(std::iter::repeat_n(0u8, 2 * vb));
        gpu_order(&u.cnt[..vb], N, out);
    }

    fn gpu_setup(&self, b: u32, o: &GpuOptions) -> Result<Ctx, String> {
        let vb = 32 * N;
        let item = HEADER + 5 * vb;
        let t0 = Instant::now();
        let gpu = Gpu::new()?;
        let t1 = Instant::now();
        if o.verbose {
            eprintln!("  gpu: {}", gpu.name);
        }
        let (par, tab) = self.gpu_tables();
        let mut parb = gpu.buffer(par.len() * 4)?;
        parb.u32s_mut()[..par.len()].copy_from_slice(&par);
        let mut tabb = gpu.buffer(tab.len())?;
        tabb.bytes_mut()[..tab.len()].copy_from_slice(&tab);
        let sg = (o.subgroups as usize).next_multiple_of(GROUP / LANES);
        let items = gpu.buffer(64 * sg * item)?;
        let out = gpu.buffer(MAXLEV * sg * item)?;
        let stats = gpu.buffer(2 * sg * 8)?;
        let found = gpu.buffer(MAXFOUND * FOUND)?;
        let ctl = gpu.buffer(16)?;
        let kernel = gpu.kernel(if N == 1 { SPIRV1 } else { SPIRV2 }, 7, 24, LANES as u32)?;
        gpu.bind(&kernel, &[&parb, &tabb, &items, &out, &stats, &found, &ctl]);
        let _ = b;
        if o.verbose {
            eprintln!("  gpu: {:.3} s to open the device, {:.3} s for buffers and pipeline", (t1 - t0).as_secs_f64(), t1.elapsed().as_secs_f64());
        }
        Ok(Ctx { gpu, kernel, items, out, stats, found, ctl, bufs: vec![parb, tabb] })
    }

    /// Search the given units on the GPU, and with o.cpu also on the
    /// threads of the rayon pool. Both sides take units from one shared
    /// index, and the CPU threads also take the cursors that the GPU split
    /// off. Adds to the node counts and the solutions of self, like
    /// run_units.
    pub fn run_gpu(&self, b: u32, units: &[Unit<N>], o: &GpuOptions) -> Result<(), String> {
        if b as usize > 32 * N {
            return Err(format!("--gpu handles bases up to {} for numbers of this width", 32 * N));
        }
        if self.inexact && !self.zscore_only {
            return Err("--gpu runs only the exact search and --zscore (with --zlaw, --zfrom, --zslope, --ztable)".into());
        }
        let item = HEADER + 5 * 32 * N;
        let sh = Shared { next: AtomicUsize::new(0), pending: Mutex::new(vec![]), gpu_done: AtomicBool::new(false) };
        let (on_cpu, cursors) = (AtomicUsize::new(0), AtomicUsize::new(0));
        let start = Instant::now();
        let mut cpu_secs = 0.0;
        let r = std::thread::scope(|s| {
            let g = s.spawn(|| {
                let r = self.gpu_loop(b, units, &sh, o);
                sh.gpu_done.store(true, Ordering::Release);
                r
            });
            if o.cpu {
                rayon::scope(|s| {
                    for _ in 0..rayon::current_num_threads() {
                        s.spawn(|_| {
                            loop {
                                let i = sh.next.fetch_add(1, Ordering::Relaxed);
                                if i < units.len() {
                                    let u = &units[i];
                                    let p = &self.params[u.pi];
                                    if self.inexact {
                                        rayon::scope(|s| self.rec::<true, 0>(s, p, u.k, u.n, u.cnt, 0));
                                    } else {
                                        rayon::scope(|s| self.rec::<false, 0>(s, p, u.k, u.n, u.cnt, 0));
                                    }
                                    on_cpu.fetch_add(1, Ordering::Relaxed);
                                    continue;
                                }
                                // read the flag first: once it is set, the GPU adds no more items
                                let done = sh.gpu_done.load(Ordering::Acquire);
                                let it = {
                                    let mut pd = sh.pending.lock().unwrap();
                                    let have = pd.len() / item;
                                    if have > 0 { Some(pd.split_off((have - 1) * item)) } else { None }
                                };
                                match it {
                                    Some(it) => {
                                        self.cpu_item(&it);
                                        cursors.fetch_add(1, Ordering::Relaxed);
                                    }
                                    None if done => break,
                                    None => std::thread::sleep(std::time::Duration::from_micros(200)),
                                }
                            }
                        });
                    }
                });
                cpu_secs = start.elapsed().as_secs_f64();
            }
            g.join().unwrap()
        });
        if o.cpu {
            eprintln!(
                "  cpu: {} of {} units and {} GPU items, done after {cpu_secs:.3} s",
                on_cpu.load(Ordering::Relaxed),
                units.len(),
                cursors.load(Ordering::Relaxed)
            );
        }
        r
    }

    // Run one GPU work item on this thread: a unit, or a cursor that a
    // subgroup handed back.
    fn cpu_item(&self, it: &[u8]) {
        let vb = 32 * N;
        let dv = |off: usize| {
            let mut x = [0u8; 64];
            for l in 0..LANES {
                for c in 0..N {
                    x[LANES * c + l] = it[off + l * N + c];
                }
            }
            x
        };
        let (pi, k, e, occk, pp, rf, root) = (it[0] as usize, it[1] as usize, it[2] as u32, it[3] as u32, it[4] as u32, it[5] as u32, it[6] != 0);
        let mut cnt = [0u8; 128];
        cnt[..64].copy_from_slice(&dv(HEADER + 4 * vb));
        let p = &self.params[pi];
        let mut n = Node { t: DV::from_bytes(&dv(HEADER)), hi: DV::from_bytes(&dv(HEADER + vb)), pp, rf, m: 0, lneed: 0.0, ln_e: 0.0, zmin: f32::INFINITY, res: [0; 2], avail: 0 };
        n.res = p.node_res(&n, k, &cnt);
        if self.inexact {
            // The item does not carry the model's bookkeeping. The node has
            // decided the digits above k; rebuild m and lneed from the counts
            // and the known leading digits.
            let lo = p.clip_lo(&n.t);
            let known = p.known(pp);
            for x in k + 1..=p.kmax {
                n.m += cnt[x] as u32;
                n.lneed += p.ln_fact[(cnt[x] as u32 - lo.count(x as u8, known)) as usize];
            }
        }
        if root {
            if self.inexact {
                rayon::scope(|s| self.rec::<true, 0>(s, p, k, n, cnt, 0));
            } else {
                rayon::scope(|s| self.rec::<false, 0>(s, p, k, n, cnt, 0));
            }
            return;
        }
        // A GPU cursor holds the sums of the last e it tried, e - 1; a CPU
        // cursor holds those of the next one.
        let (mut te, mut hi) = (DV::from_bytes(&dv(HEADER + 2 * vb)), DV::from_bytes(&dv(HEADER + 3 * vb)));
        if e > 0 {
            te = te.add(&p.w[k], &p.base);
            hi = hi.add(&p.dhi[k], &p.base);
        }
        let res = (0..e).fold(n.res, |r, _| p.res_add(r, k));
        let mut cur = Cursor { te, hi, h: Head { pp, rf, m: n.m, lneed: n.lneed, ln_e: 0.0, zmin: f32::INFINITY, avail: 0 }, k, e, occk, res, z: 0 };
        let mut l = Local::for_params(p);
        rayon::scope(|s| {
            if self.inexact {
                while let Some(c) = self.next_child::<true, 0>(p, &mut cur, &mut cnt, &mut l) {
                    self.rec_seq::<true, 0>(s, p, k - 1, &c, &mut cnt, &mut l, 0);
                }
            } else {
                while let Some(c) = self.next_child::<false, 0>(p, &mut cur, &mut cnt, &mut l) {
                    self.rec_seq::<false, 0>(s, p, k - 1, &c, &mut cnt, &mut l, 0);
                }
            }
        });
        self.flush(&l);
    }

    fn gpu_loop(&self, b: u32, units: &[Unit<N>], sh: &Shared, o: &GpuOptions) -> Result<(), String> {
        let vb = 32 * N;
        let item = HEADER + 5 * vb;
        let mut c = self.gpu_setup(b, o)?;
        let sg = (o.subgroups as usize).next_multiple_of(GROUP / LANES);
        let cap = 64 * sg;
        // The GPU takes only about as many items as it finished in the last
        // dispatch, and claims units only as fast as that, so that the CPU
        // threads find work in the shared stack.
        let mut want = 4 * sg;
        let mut budget: u32 = 4096;
        let (mut rounds, mut busy) = (0u64, 0.0f64);
        let start = Instant::now();
        loop {
            let chunk = {
                let mut pending = sh.pending.lock().unwrap();
                let have = pending.len() / item;
                if have < want {
                    let i = sh.next.fetch_add(want - have, Ordering::Relaxed).min(units.len());
                    let j = (i + want - have).min(units.len());
                    for u in units[i..j].iter().rev() {
                        self.gpu_item(u, &mut pending);
                    }
                }
                let have = pending.len() / item;
                let n = have.min(want);
                pending.split_off((have - n) * item)
            };
            if chunk.is_empty() {
                break;
            }
            let n = chunk.len() / item;
            c.items.bytes_mut()[..chunk.len()].copy_from_slice(&chunk);
            c.ctl.u32s_mut()[..4].fill(0);
            // with few items, split them sooner so that every subgroup gets work
            let eff = if n < sg { ((budget as usize * n / sg) as u32).max(256) } else { budget };
            let push: Vec<u8> = [n as u32, eff, (MAXLEV * sg) as u32, MAXFOUND as u32, b, self.inexact as u32].iter().flat_map(|v| v.to_le_bytes()).collect();
            let t = Instant::now();
            let per_group = GROUP / LANES;
            c.gpu.run(&c.kernel, &push, sg.div_ceil(per_group) as u32)?;
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
            // grow while the GPU finishes every item, else follow what it finished
            want = if taken == n || !o.cpu { 2 * taken } else { taken + taken / 4 }.clamp(2 * sg, cap);
            {
                let mut pending = sh.pending.lock().unwrap();
                pending.extend_from_slice(&chunk[taken * item..]);
                pending.extend_from_slice(&c.out.bytes()[..nout * item]);
            }
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
        let l = Local { nodes: (0..sg).map(|i| word(2 * i)).sum(), evals: (0..sg).map(|i| word(2 * i + 1)).sum(), ..Local::default() };
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
