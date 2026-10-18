//! Cycle census of n -> F(n) in base b, on digit multisets.
//!
//! F(n) depends only on the multiset of digits of n, so the map lives on
//! multisets: c -> multiset of S(c), where S(c) = sum of w(x) over the
//! digits. Every n with at most b digits has F(n) < b^b, so the multisets
//! of size 1 to b (with a nonzero digit) are closed under the map. Cycles of
//! multisets and cycles of integers correspond one to one.
//!
//! A multiset of size at most b over the digits 0..b-1 is a multiset of size
//! exactly b over 0..b (the value b fills the slack). Its sorted sequence
//! x_1 <= ... <= x_b gives the b-subset y_i = x_i + i - 1 of [0, 2b), ranked
//! by the combinatorial number system. So the nodes are 0..C(2b, b).
//!
//! The walk keeps 2 bits per node: unvisited, on the current path, done.
//! Each node is entered once, so the work is linear in C(2b, b).
//!
//! The same pass builds the length-and-residue transition matrix of the
//! random model: a d-digit string with digit sum r mod (b-1) is a class;
//! the weight of a multiset in its class is the number of d-digit strings
//! (nonzero leading digit) with that multiset; its image has D digits and
//! residue S mod (b-1). The matrix goes to the file given by --matrix.
//!
//! It also writes, for each class, the sum of the squared weights, which
//! gives the collision probability of the class: the chance that two draws
//! from it give the same multiset. --model-only skips the walk.
//!
//! usage: dyn_cycles <b> <m> [--matrix FILE] [--show L] [--model-only]
//! prints one "cycle" line per cycle and a "summary" line. Cycles of length
//! at most L (default 8) list their elements as base-b digit strings.

use std::io::Write;

const MAXB: usize = 26;

struct Ctx<const B: usize> {
    w: [u128; MAXB],
    wres: [u64; MAXB],
    binom: Vec<Vec<u64>>,
    pow: Vec<u128>,
    state: Vec<u64>,
    lnfact: [f64; MAXB + 1],
    mat: Vec<f64>,
    coll: Vec<f64>,
    model_only: bool,
    show: usize,
    cycles: Vec<(usize, u128)>,
    out: std::io::BufWriter<std::io::Stdout>,
}

impl<const B: usize> Ctx<B> {
    fn new(m: u32, show: usize) -> Self {
        let mut w = [0u128; MAXB];
        let mut wres = [0u64; MAXB];
        let q = (B - 1) as u128;
        for x in 0..B {
            w[x] = if x == 0 { m as u128 } else { (x as u128).pow(x as u32) };
            wres[x] = (w[x] % q) as u64;
        }
        let n2 = 2 * B + 1;
        let mut binom = vec![vec![0u64; n2]; n2];
        for n in 0..n2 {
            binom[n][0] = 1;
            for k in 1..=n {
                binom[n][k] = binom[n - 1][k - 1] + if k < n { binom[n - 1][k] } else { 0 };
            }
        }
        let mut pow = vec![1u128];
        for _ in 0..=B {
            let p = *pow.last().unwrap();
            pow.push(p.saturating_mul(B as u128));
        }
        let nodes = binom[2 * B][B] as usize;
        let mut lnfact = [0f64; MAXB + 1];
        for i in 1..=MAXB {
            lnfact[i] = lnfact[i - 1] + (i as f64).ln();
        }
        let s = B * (B - 1);
        Ctx {
            w,
            wres,
            binom,
            pow,
            state: Vec::with_capacity(nodes / 32 + 1),
            lnfact,
            mat: vec![0f64; s * s],
            coll: vec![0f64; s],
            model_only: false,
            show,
            cycles: Vec::new(),
            out: std::io::BufWriter::new(std::io::stdout()),
        }
    }

    #[inline]
    fn get(&self, x: usize) -> u64 {
        (self.state[x >> 5] >> ((x & 31) * 2)) & 3
    }

    #[inline]
    fn set(&mut self, x: usize, v: u64) {
        let s = (x & 31) * 2;
        let word = &mut self.state[x >> 5];
        *word = (*word & !(3 << s)) | (v << s);
    }

    /// Digit counts, number of digits and F of n.
    #[inline]
    fn digits(&self, n: u128) -> ([u8; MAXB], usize, u128) {
        let mut cnt = [0u8; MAXB];
        let mut d = 0;
        let mut f = 0u128;
        let b = B as u64;
        let mut lo;
        if n >> 64 == 0 {
            lo = n as u64;
        } else {
            // split off 12 low digits so that the rest fits in a u64
            let p = self.pow[12];
            let hi = n / p;
            let mut low = (n % p) as u64;
            for _ in 0..12 {
                let x = (low % b) as usize;
                low /= b;
                cnt[x] += 1;
                f += self.w[x];
                d += 1;
            }
            debug_assert!(hi >> 64 == 0);
            lo = hi as u64;
        }
        while lo > 0 {
            let x = (lo % b) as usize;
            lo /= b;
            cnt[x] += 1;
            f += self.w[x];
            d += 1;
        }
        (cnt, d, f)
    }

    #[inline]
    fn rank(&self, cnt: &[u8; MAXB], d: usize) -> usize {
        let mut r = 0u64;
        let mut i = 1usize;
        for v in 0..B {
            let c = cnt[v] as usize;
            if c > 0 {
                if v > 0 {
                    r += self.binom[v + i + c - 1][i + c - 1] - self.binom[v + i - 1][i - 1];
                }
                i += c;
            }
        }
        let c = B - d;
        if c > 0 {
            r += self.binom[B + i + c - 1][i + c - 1] - self.binom[B + i - 1][i - 1];
        }
        r as usize
    }

    fn len_of(&self, s: u128) -> usize {
        let mut d = 1;
        while d <= B && self.pow[d] <= s {
            d += 1;
        }
        d
    }

    fn fmt(&self, mut n: u128) -> String {
        let mut v = Vec::new();
        while n > 0 {
            v.push((n % B as u128) as u64);
            n /= B as u128;
        }
        v.reverse();
        let s: Vec<String> = v.iter().map(|x| x.to_string()).collect();
        format!("({})", s.join(","))
    }

    fn record_cycle(&mut self, n0: u128) {
        let mut elems = vec![n0];
        let mut n = self.digits(n0).2;
        while n != n0 {
            elems.push(n);
            n = self.digits(n).2;
        }
        let l = elems.len();
        let mn = *elems.iter().min().unwrap();
        let q = (B - 1) as u128;
        let par: Vec<String> = elems.iter().map(|e| (e % 2).to_string()).collect();
        let res: Vec<String> = elems.iter().map(|e| (e % q).to_string()).collect();
        let mut line = format!("cycle {} L={} min={} parity={} res={}", B, l, mn, par.join(""), res.join(","));
        if l <= self.show {
            let s: Vec<String> = elems.iter().map(|&e| self.fmt(e)).collect();
            line.push_str(&format!(" elems={}", s.join(">")));
        }
        writeln!(self.out, "{}", line).unwrap();
        self.cycles.push((l, mn));
    }

    fn visit(&mut self, cnt: &[u8; MAXB], d: usize, s: u128, path: &mut Vec<usize>) {
        // model matrix: class of the multiset and of its image
        let q = (B - 1) as u64;
        let mut ds = 0u64;
        let mut sr = 0u64;
        let mut lw = self.lnfact[d];
        for v in 0..B {
            let c = cnt[v] as u64;
            ds += c * v as u64;
            sr += c * self.wres[v];
            lw -= self.lnfact[c as usize];
        }
        let nz = (d - cnt[0] as usize) as f64 / d as f64;
        let weight = lw.exp() * nz;
        let from = (d - 1) * (B - 1) + (ds % q) as usize;
        let to = (self.len_of(s) - 1) * (B - 1) + (sr % q) as usize;
        self.mat[from * B * (B - 1) + to] += weight;
        self.coll[from] += weight * weight;
        if self.model_only {
            return;
        }

        let r = self.rank(cnt, d);
        if self.get(r) != 0 {
            return;
        }
        path.clear();
        self.set(r, 1);
        path.push(r);
        let mut n = s;
        loop {
            let (c2, d2, f2) = self.digits(n);
            let y = self.rank(&c2, d2);
            match self.get(y) {
                0 => {
                    self.set(y, 1);
                    path.push(y);
                    n = f2;
                }
                1 => {
                    self.record_cycle(n);
                    break;
                }
                _ => break,
            }
        }
        for &y in path.iter() {
            self.set(y, 2);
        }
    }

    fn enumerate(&mut self, v: usize, budget: usize, cnt: &mut [u8; MAXB], s: u128, path: &mut Vec<usize>) {
        // assign counts for digit values v, v-1, ..., 0
        if v == 0 {
            for c0 in 0..=budget {
                cnt[0] = c0 as u8;
                let d = B - budget + c0;
                let nonzero = d - c0;
                if nonzero == 0 {
                    continue;
                }
                let s2 = s + self.w[0] * c0 as u128;
                self.visit(cnt, d, s2, path);
            }
            cnt[0] = 0;
            return;
        }
        for c in 0..=budget {
            cnt[v] = c as u8;
            self.enumerate(v - 1, budget - c, cnt, s + self.w[v] * c as u128, path);
        }
        cnt[v] = 0;
    }
}

fn run<const B: usize>(m: u32, matrix: Option<String>, show: usize, model_only: bool) {
    let t0 = std::time::Instant::now();
    let mut ctx: Ctx<B> = Ctx::new(m, show);
    let nodes = ctx.binom[2 * B][B];
    ctx.model_only = model_only;
    if !model_only {
        ctx.state.resize(nodes as usize / 32 + 1, 0);
    }
    let mut cnt = [0u8; MAXB];
    let mut path = Vec::new();
    ctx.enumerate(B - 1, B, &mut cnt, 0, &mut path);
    let mut by_len = std::collections::BTreeMap::new();
    for &(l, _) in &ctx.cycles {
        *by_len.entry(l).or_insert(0usize) += 1;
    }
    let s: Vec<String> = by_len.iter().map(|(l, c)| format!("{}:{}", l, c)).collect();
    writeln!(
        ctx.out,
        "summary b={} m={} nodes={} cycles={} lengths={} seconds={:.1}",
        B,
        m,
        nodes,
        ctx.cycles.len(),
        s.join(","),
        t0.elapsed().as_secs_f64()
    )
    .unwrap();
    if let Some(path) = matrix {
        let st = B * (B - 1);
        let mut f = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
        writeln!(f, "# b={} m={} states=(digits-1)*(b-1)+residue; from to weight; coll state sum-of-squared-weights", B, m).unwrap();
        for i in 0..st {
            if ctx.coll[i] > 0.0 {
                writeln!(f, "coll {} {:e}", i, ctx.coll[i]).unwrap();
            }
        }
        for i in 0..st {
            for j in 0..st {
                let x = ctx.mat[i * st + j];
                if x > 0.0 {
                    writeln!(f, "{} {} {:e}", i, j, x).unwrap();
                }
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: dyn_cycles <b> <m> [--matrix FILE] [--show L] [--model-only]");
        std::process::exit(1);
    }
    let b: usize = args[1].parse().unwrap();
    let m: u32 = args[2].parse().unwrap();
    let mut matrix = None;
    let mut show = 8;
    let mut model_only = false;
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--matrix" => {
                matrix = Some(args[i + 1].clone());
                i += 2;
            }
            "--model-only" => {
                model_only = true;
                i += 1;
            }
            "--show" => {
                show = args[i + 1].parse().unwrap();
                i += 2;
            }
            _ => panic!("unknown option {}", args[i]),
        }
    }
    macro_rules! go {
        ($($n:literal),*) => {
            match b {
                $($n => run::<$n>(m, matrix, show, model_only),)*
                _ => panic!("base must be 3 to 24"),
            }
        };
    }
    go!(3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24);
}
