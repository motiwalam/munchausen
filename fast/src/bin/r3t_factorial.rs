//! Munchausen numbers in the factorial number system (question 62).
//!
//! Every n >= 1 has exactly one expansion n = sum_{i=1..L} d_i i! with
//! 0 <= d_i <= i and d_L >= 1, so L! <= n < (L+1)!. n is a solution when
//! n = F(n) + D, F(n) = sum w(d_i), w(d) = d^d, w(0) = m; D = 0 gives the
//! Munchausen numbers, D > 0 the near-solutions of section 11.1.
//!
//! The search fixes L and decides the digit counts from the largest value
//! down, as in fast/src/search.rs. The numbers whose digits at positions >= j
//! are fixed form an interval [a j!, (a+1) j!), so the top digits shared by
//! both ends of the range [lo, hi] of F + D are digits of every candidate.
//! A shared digit u must fit the count of u if u is decided, and adds one
//! forced copy of u otherwise. A digit u can only sit at a position >= u, so
//! the counts must satisfy #(digits >= u) <= L - u + 1.
//!
//! usage: r3t_factorial <m> <Lmin> <Lmax> [--offsets J] [--step S]   (offsets j S)
//! Arithmetic is u128, enough for L <= 33.

use rayon::prelude::*;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

const MAXV: usize = 40;

struct Cfg {
    l: usize,
    m: u128,
    off: u128,
    fact: Vec<u128>, // i!
    w: Vec<u128>,
    wmin: Vec<u128>, // min of w[0..k]
    wmax: Vec<u128>,
    wl: u128, // window [L!, (L+1)!) for F + D, clipped to reachable sums
    wu: u128,
    kmax: usize,
}

#[derive(Clone, Copy)]
struct Node {
    k: usize,         // counts of values >= k are decided
    r: usize,         // free slots for values < k
    t: u128,          // offset + decided and forced weights
    j: usize,         // positions >= j are known
    c: [u8; MAXV],    // decided and forced counts
    h: [u8; MAXV],    // histogram of known top digits
}

fn digits(n: u128, fact: &[u128]) -> Vec<u8> {
    // most significant first
    let mut l = 1;
    while fact[l + 1] <= n {
        l += 1;
    }
    let mut out = vec![];
    let mut x = n;
    for i in (1..=l).rev() {
        out.push((x / fact[i]) as u8);
        x %= fact[i];
    }
    out
}

impl Cfg {
    #[inline]
    fn digit_at(&self, n: u128, j: usize) -> usize {
        ((n / self.fact[j]) % (j as u128 + 1)) as usize
    }
    fn hall(&self, c: &[u8], k: usize) -> bool {
        // #digits >= u <= L - u + 1 for the decided values u >= k (u >= 1)
        let mut s = 0usize;
        for u in (k.max(1)..=self.kmax).rev() {
            s += c[u] as usize;
            if s > self.l + 1 - u {
                return false;
            }
        }
        true
    }
}

fn settle(cfg: &Cfg, n: &mut Node) -> bool {
    loop {
        let rr = n.r as u128;
        let lo = if n.k == 0 { n.t } else { n.t + rr * cfg.wmin[n.k] }.max(cfg.wl);
        let hi = if n.k == 0 { n.t } else { n.t + rr * cfg.wmax[n.k] }.min(cfg.wu);
        if lo > hi {
            return false;
        }
        let mut forced = false;
        while n.j > 1 {
            let j = n.j - 1;
            if lo / cfg.fact[j] != hi / cfg.fact[j] {
                break;
            }
            let x = cfg.digit_at(lo, j);
            n.j = j;
            n.h[x] += 1;
            if n.h[x] > n.c[x] {
                if x >= n.k || n.r == 0 {
                    return false;
                }
                n.c[x] += 1;
                n.t += cfg.w[x];
                n.r -= 1;
                forced = true;
                break;
            }
        }
        if !forced {
            return cfg.hall(&n.c, n.k);
        }
    }
}

fn children(cfg: &Cfg, n: &Node, mut f: impl FnMut(Node)) {
    let x = n.k - 1;
    let (e0, e1) = if x == 0 { (n.r, n.r) } else { (0, n.r) };
    for e in e0..=e1 {
        let t2 = n.t + e as u128 * cfg.w[x];
        let rr = (n.r - e) as u128;
        if x > 0 {
            if t2 + rr * cfg.wmin[x] > cfg.wu {
                break;
            }
            if t2 + rr * cfg.wmax[x] < cfg.wl {
                continue;
            }
        }
        let mut ch = *n;
        ch.k = x;
        ch.r = n.r - e;
        ch.t = t2;
        ch.c[x] += e as u8;
        if settle(cfg, &mut ch) {
            f(ch);
        }
    }
}

fn check(cfg: &Cfg, n: &Node) -> Option<Vec<u8>> {
    let v = n.t; // = F + off
    if v < cfg.fact[cfg.l] || v >= cfg.fact[cfg.l + 1] {
        return None;
    }
    let ds = digits(v, &cfg.fact);
    let mut h = [0u8; MAXV];
    for &d in &ds {
        h[d as usize] += 1;
    }
    if h[..] == n.c[..] { Some(ds) } else { None }
}

fn dfs(cfg: &Cfg, n: &Node, sols: &Mutex<Vec<Vec<u8>>>, cnt: &mut u64) {
    *cnt += 1;
    if n.k == 0 {
        if let Some(s) = check(cfg, n) {
            sols.lock().unwrap().push(s);
        }
        return;
    }
    children(cfg, n, |ch| dfs(cfg, &ch, sols, cnt));
}

fn run(m: u128, l: usize, off: u128) -> (Vec<Vec<u8>>, u64) {
    let mut fact = vec![1u128];
    for i in 1..=l + 1 {
        fact.push(fact[i - 1].checked_mul(i as u128).expect("factorial does not fit in u128"));
    }
    let top = fact[l + 1] - 1;
    // largest digit value: v <= L and v^v + off <= top
    let mut w = vec![m];
    let mut kmax = 0;
    for v in 1..=l.min(MAXV - 1) {
        let mut p: u128 = 1;
        let mut ok = true;
        for _ in 0..v {
            match p.checked_mul(v as u128) {
                Some(x) => p = x,
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok || p + off > top {
            break;
        }
        w.push(p);
        kmax = v;
    }
    let nv = kmax + 1;
    let mut wmin = vec![u128::MAX; nv + 1];
    let mut wmax = vec![0u128; nv + 1];
    for k in 1..=nv {
        wmin[k] = wmin[k - 1].min(w[k - 1]);
        wmax[k] = wmax[k - 1].max(w[k - 1]);
    }
    let maxsum = w.iter().copied().max().unwrap() * l as u128;
    let wl = fact[l];
    let wu = top.min(maxsum + off);
    if wl > wu {
        return (vec![], 0);
    }
    let cfg = Cfg { l, m, off, fact, w, wmin, wmax, wl, wu, kmax };
    let _ = (cfg.m, cfg.off);
    let mut root = Node { k: nv, r: l, t: off, j: l + 1, c: [0; MAXV], h: [0; MAXV] };
    let sols = Mutex::new(vec![]);
    if !settle(&cfg, &mut root) {
        return (vec![], 1);
    }
    let mut front = vec![root];
    let mut extra = 0u64;
    while front.len() < 2000 && front.iter().all(|n| n.k > 2) {
        let mut next = vec![];
        for n in &front {
            children(&cfg, n, |ch| next.push(ch));
        }
        extra += front.len() as u64;
        if next.is_empty() {
            return (vec![], extra);
        }
        front = next;
    }
    let nodes = AtomicU64::new(0);
    front.par_iter().for_each(|n| {
        let mut cnt = 0;
        dfs(&cfg, n, &sols, &mut cnt);
        nodes.fetch_add(cnt, Ordering::Relaxed);
    });
    let mut s = sols.into_inner().unwrap();
    s.sort();
    (s, nodes.load(Ordering::Relaxed) + extra)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let m: u128 = a[1].parse().unwrap();
    let lmin: usize = a[2].parse().unwrap();
    let lmax: usize = a[3].parse().unwrap();
    let mut jmax: u128 = 0;
    let mut step: u128 = 1;
    let mut i = 4;
    while i + 1 < a.len() {
        match a[i].as_str() {
            "--offsets" => jmax = a[i + 1].parse().unwrap(),
            "--step" => step = a[i + 1].parse().unwrap(),
            o => panic!("unknown option {o}"),
        }
        i += 2;
    }
    println!("# factorial number system, 0^0 = {m}, lengths {lmin}..{lmax}, offsets j * {step}, j = 1..{jmax}");
    for l in lmin..=lmax {
        let t0 = Instant::now();
        let (s, nodes) = run(m, l, 0);
        for d in &s {
            let n: u128 = d.iter().rev().enumerate().map(|(i, &x)| x as u128 * (1..=(i as u128 + 1)).product::<u128>()).sum();
            println!("sol m {m} L {l} n {n} digits {}", d.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","));
        }
        let mut near = vec![];
        let mut nn = 0;
        for j in 1..=jmax {
            let (sj, nd) = run(m, l, j * step);
            near.push(sj.len().to_string());
            nn += nd;
        }
        println!(
            "len m {m} L {l} sols {} nodes {nodes} near {} near_nodes {nn} secs {:.2}",
            s.len(),
            near.join(","),
            t0.elapsed().as_secs_f64()
        );
    }
}
