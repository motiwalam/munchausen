//! Two-cycles and near-two-cycles of n -> F(n) in base b, on digit multisets
//! (question 35 of docs/library/questions.md).
//!
//! For every multiset c of 1 to b digits with a nonzero digit, let S(c) be
//! its sum of weights, c' the multiset of S(c), and G(c) = S(c'). For the
//! offsets D = j (b-1), j = 0..J, the program counts
//!   A_j = #{ c : the digits of G(c) + D form c, and c' != c },
//!   B_j = #{ c with at least 2 digits : the digits of S(c) + D form c }.
//! A_0 is twice the number of 2-cycles and B_0 the number of nontrivial
//! fixed points. An offset that is a multiple of b-1 keeps the residue
//! condition mod b-1 (and mod 2 in odd bases), so each j > 0 is a fresh draw
//! of the same coincidence, as in section 11.1.
//!
//! The same pass writes the class transition matrix of dyn_cycles.rs
//! (--matrix), so analysis/dyn_cycle_model.py can compute the model.
//!
//! The work is cut into items (the counts of the top three digit values) and
//! batches of items. After each batch the program appends its results to
//! the journal, and a rerun skips the batches that are already there.
//!
//! usage: r2c_cycles2 <b> <m> <J> <journal> [--matrix FILE] [--batches N]

use rayon::prelude::*;
use std::collections::HashSet;
use std::io::{BufRead, Write};

const MAXB: usize = 26;

struct Tables {
    b: usize,
    q: u64,
    w: [u128; MAXB],
    pow: Vec<u128>,
    lnfact: [f64; MAXB + 1],
    jmax: usize,
}

#[derive(Default, Clone)]
struct Stats {
    a: Vec<u64>,
    bfix: Vec<u64>,
    two: Vec<String>,
    near: Vec<String>,
    mat: Vec<f64>,
    coll: Vec<f64>,
    sdim: usize,
    nodes: u64,
}

impl Stats {
    fn new(j: usize, sdim: usize) -> Stats {
        Stats { a: vec![0; j + 1], bfix: vec![0; j + 1], mat: vec![0.0; sdim * sdim], coll: vec![0.0; sdim], sdim, ..Default::default() }
    }
    fn add(mut self, o: Stats) -> Stats {
        for (x, y) in self.a.iter_mut().zip(&o.a) {
            *x += y;
        }
        for (x, y) in self.bfix.iter_mut().zip(&o.bfix) {
            *x += y;
        }
        self.two.extend(o.two);
        self.near.extend(o.near);
        for (x, y) in self.mat.iter_mut().zip(&o.mat) {
            *x += y;
        }
        for (x, y) in self.coll.iter_mut().zip(&o.coll) {
            *x += y;
        }
        self.nodes += o.nodes;
        self
    }
}

impl Tables {
    fn new(b: usize, m: u32, jmax: usize) -> Tables {
        let mut w = [0u128; MAXB];
        for x in 0..b {
            w[x] = if x == 0 { m as u128 } else { (x as u128).pow(x as u32) };
        }
        let mut pow = vec![1u128];
        for _ in 0..=b + 1 {
            let p = *pow.last().unwrap();
            pow.push(p.saturating_mul(b as u128));
        }
        let mut lnfact = [0f64; MAXB + 1];
        for i in 1..=MAXB {
            lnfact[i] = lnfact[i - 1] + (i as f64).ln();
        }
        Tables { b, q: (b - 1) as u64, w, pow, lnfact, jmax }
    }

    /// Digit counts, number of digits and weight sum of n.
    #[inline]
    fn digits(&self, mut n: u128) -> ([u8; MAXB], usize, u128) {
        let mut cnt = [0u8; MAXB];
        let mut d = 0;
        let mut f = 0u128;
        let b = self.b as u128;
        while n >> 64 != 0 {
            let x = (n % b) as usize;
            n /= b;
            cnt[x] += 1;
            f += self.w[x];
            d += 1;
        }
        let mut lo = n as u64;
        let bb = self.b as u64;
        while lo > 0 {
            let x = (lo % bb) as usize;
            lo /= bb;
            cnt[x] += 1;
            f += self.w[x];
            d += 1;
        }
        (cnt, d, f)
    }

    fn len_of(&self, s: u128) -> usize {
        let mut d = 1;
        while d <= self.b && self.pow[d] <= s {
            d += 1;
        }
        d
    }

    fn fmt(&self, mut n: u128) -> String {
        let mut v = Vec::new();
        while n > 0 {
            v.push((n % self.b as u128) as u64);
            n /= self.b as u128;
        }
        v.reverse();
        let s: Vec<String> = v.iter().map(|x| x.to_string()).collect();
        s.join(",")
    }

    fn visit(&self, cnt: &[u8; MAXB], d: usize, s: u128, st: &mut Stats) {
        let b = self.b;
        let q = self.q;
        st.nodes += 1;
        let mut ds = 0u64;
        let mut lw = self.lnfact[d];
        for v in 0..b {
            let c = cnt[v] as u64;
            ds += c * v as u64;
            lw -= self.lnfact[c as usize];
        }
        let dsr = ds % q;
        // model matrix, as in dyn_cycles.rs
        let nz = (d - cnt[0] as usize) as f64 / d as f64;
        let weight = lw.exp() * nz;
        let from = (d - 1) * (b - 1) + dsr as usize;
        let to = (self.len_of(s) - 1) * (b - 1) + (s % q as u128) as usize;
        st.mat[from * st.sdim + to] += weight;
        st.coll[from] += weight * weight;

        let lo_d = self.pow[d - 1];
        let hi_d = self.pow[d];
        let qq = q as u128;
        // near fixed points: digits of S(c) + j (b-1) form c
        if d >= 2 && (s % qq) as u64 == dsr {
            for j in 0..=self.jmax {
                let n = s + j as u128 * qq;
                if n >= hi_d {
                    break;
                }
                if n < lo_d {
                    continue;
                }
                let (c2, d2, _) = self.digits(n);
                if d2 == d && c2[..b] == cnt[..b] {
                    st.bfix[j] += 1;
                    if j > 0 {
                        st.near.push(format!("fix {} {}", j, self.fmt(n)));
                    }
                }
            }
        }
        // near two-cycles: digits of G(c) + j (b-1) form c, with c' != c
        let (c1, _d1, g) = self.digits(s);
        if (g % qq) as u64 != dsr {
            return;
        }
        if c1[..b] == cnt[..b] {
            return;
        }
        for j in 0..=self.jmax {
            let n = g + j as u128 * qq;
            if n >= hi_d {
                break;
            }
            if n < lo_d {
                continue;
            }
            let (c2, d2, _) = self.digits(n);
            if d2 == d && c2[..b] == cnt[..b] {
                st.a[j] += 1;
                st.two.push(format!("two {} {} > {}", j, self.fmt(n), self.fmt(s)));
            }
        }
    }

    /// Counts for the digit values v, v-1, ..., 0, with `budget` slots left.
    fn enumerate(&self, v: usize, budget: usize, cnt: &mut [u8; MAXB], s: u128, st: &mut Stats) {
        if v == 0 {
            for c0 in 0..=budget {
                cnt[0] = c0 as u8;
                let d = self.b - budget + c0;
                if d - c0 == 0 {
                    continue;
                }
                self.visit(cnt, d, s + self.w[0] * c0 as u128, st);
            }
            cnt[0] = 0;
            return;
        }
        for c in 0..=budget {
            cnt[v] = c as u8;
            self.enumerate(v - 1, budget - c, cnt, s + self.w[v] * c as u128, st);
        }
        cnt[v] = 0;
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 5 {
        eprintln!("usage: r2c_cycles2 <b> <m> <J> <journal> [--matrix FILE] [--batches N]");
        std::process::exit(2);
    }
    let b: usize = args[1].parse().unwrap();
    let m: u32 = args[2].parse().unwrap();
    let jmax: usize = args[3].parse().unwrap();
    let jpath = args[4].clone();
    let mut matrix = None;
    let mut nbatch = 40usize;
    let mut i = 5;
    while i < args.len() {
        match args[i].as_str() {
            "--matrix" => matrix = Some(args[i + 1].clone()),
            "--batches" => nbatch = args[i + 1].parse().unwrap(),
            a => panic!("unknown option {a}"),
        }
        i += 2;
    }
    assert!((4..=24).contains(&b));
    let t = Tables::new(b, m, jmax);
    let sdim = b * (b - 1);

    // items: counts of the digit values b-1, b-2, b-3
    let mut items = vec![];
    for x in 0..=b {
        for y in 0..=b - x {
            for z in 0..=b - x - y {
                items.push((x, y, z));
            }
        }
    }
    let per = items.len().div_ceil(nbatch);
    let header = format!("# r2c_cycles2 b={b} m={m} J={jmax} items={} per={per}", items.len());

    // the journal: batches with an "end" line are done
    let mut done = HashSet::new();
    let mut total = Stats::new(jmax, sdim);
    if std::path::Path::new(&jpath).exists() {
        let f = std::fs::File::open(&jpath).unwrap();
        let mut lines = std::io::BufReader::new(f).lines();
        let h = lines.next().unwrap().unwrap();
        assert_eq!(h, header, "journal of another run");
        let mut cur = Stats::new(jmax, sdim);
        for line in lines {
            let line = line.unwrap();
            let p: Vec<&str> = line.split_whitespace().collect();
            match p.first().copied() {
                Some("batch") => cur = Stats::new(jmax, sdim),
                Some("A") => cur.a[p[1].parse::<usize>().unwrap()] = p[2].parse().unwrap(),
                Some("B") => cur.bfix[p[1].parse::<usize>().unwrap()] = p[2].parse().unwrap(),
                Some("two") => cur.two.push(line.clone()),
                Some("fix") => cur.near.push(line.clone()),
                Some("mat") => {
                    let (i, j): (usize, usize) = (p[1].parse().unwrap(), p[2].parse().unwrap());
                    cur.mat[i * sdim + j] = p[3].parse().unwrap();
                }
                Some("coll") => cur.coll[p[1].parse::<usize>().unwrap()] = p[2].parse().unwrap(),
                Some("nodes") => cur.nodes = p[1].parse().unwrap(),
                Some("end") => {
                    done.insert(p[1].parse::<usize>().unwrap());
                    total = total.add(std::mem::replace(&mut cur, Stats::new(jmax, sdim)));
                }
                _ => {}
            }
        }
    } else {
        let mut f = std::fs::File::create(&jpath).unwrap();
        writeln!(f, "{header}").unwrap();
    }

    let t0 = std::time::Instant::now();
    for k in 0..nbatch {
        if done.contains(&k) || k * per >= items.len() {
            continue;
        }
        let chunk = &items[k * per..((k + 1) * per).min(items.len())];
        let st = chunk
            .par_iter()
            .fold(
                || Stats::new(jmax, sdim),
                |mut st, &(x, y, z)| {
                    let mut cnt = [0u8; MAXB];
                    cnt[b - 1] = x as u8;
                    cnt[b - 2] = y as u8;
                    cnt[b - 3] = z as u8;
                    let s = t.w[b - 1] * x as u128 + t.w[b - 2] * y as u128 + t.w[b - 3] * z as u128;
                    t.enumerate(b - 4, b - x - y - z, &mut cnt, s, &mut st);
                    st
                },
            )
            .reduce(|| Stats::new(jmax, sdim), |a, o| a.add(o));
        let mut out = String::new();
        out.push_str(&format!("batch {k}\n"));
        for (j, v) in st.a.iter().enumerate() {
            out.push_str(&format!("A {j} {v}\n"));
        }
        for (j, v) in st.bfix.iter().enumerate() {
            out.push_str(&format!("B {j} {v}\n"));
        }
        for s in &st.two {
            out.push_str(&format!("{s}\n"));
        }
        for s in &st.near {
            out.push_str(&format!("{s}\n"));
        }
        for (k, v) in st.mat.iter().enumerate().filter(|x| *x.1 != 0.0) {
            out.push_str(&format!("mat {} {} {v:e}\n", k / sdim, k % sdim));
        }
        for (i, v) in st.coll.iter().enumerate().filter(|x| *x.1 != 0.0) {
            out.push_str(&format!("coll {i} {v:e}\n"));
        }
        out.push_str(&format!("nodes {}\n", st.nodes));
        out.push_str(&format!("end {k}\n"));
        let mut f = std::fs::OpenOptions::new().append(true).open(&jpath).unwrap();
        f.write_all(out.as_bytes()).unwrap();
        f.flush().unwrap();
        eprintln!("b={b} m={m} batch {k}/{nbatch} done, {:.1} s", t0.elapsed().as_secs_f64());
        total = total.add(st);
    }

    let a: Vec<String> = total.a.iter().map(|v| v.to_string()).collect();
    let bf: Vec<String> = total.bfix.iter().map(|v| v.to_string()).collect();
    println!("summary b={b} m={m} J={jmax} nodes={} two_cycles={} A={} B={}", total.nodes, total.a[0] / 2, a.join(","), bf.join(","));
    let mut two: Vec<&String> = total.two.iter().filter(|s| s.starts_with("two 0 ")).collect();
    two.sort();
    for s in two {
        println!("b={b} m={m} {s}");
    }
    if let Some(path) = matrix {
        let mut f = std::io::BufWriter::new(std::fs::File::create(path).unwrap());
        writeln!(f, "# b={b} m={m} states=(digits-1)*(b-1)+residue; from to weight; coll state sum-of-squared-weights").unwrap();
        for (i, v) in total.coll.iter().enumerate().filter(|x| *x.1 != 0.0) {
            writeln!(f, "coll {i} {v:e}").unwrap();
        }
        for (k, v) in total.mat.iter().enumerate().filter(|x| *x.1 != 0.0) {
            writeln!(f, "{} {} {v:e}", k / sdim, k % sdim).unwrap();
        }
    }
}
