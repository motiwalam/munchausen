//! Munchausen numbers in the Pisot base eps = (x + sqrt(x^2 + 4)) / 2
//! (question 59).
//!
//! eps is the dominant root of t^2 - x t - 1, a Pisot unit with conjugate
//! -1/eps. Every positive integer N has a finite greedy expansion
//! N = sum_{i=-m..k} d_i eps^i with digits 0..x, in which every digit x is
//! followed by a 0 (the Parry condition for d*(1) = (x 0)^infinity); this is
//! property (F) of Frougny and Solomyak. The digit string runs from position k
//! down to position min(0, -m), where d_k != 0 and d_(-m) != 0 if m > 0. N is
//! a solution when N = sum w(d_i), w(d) = d^d, w(0) = 0 or 1.
//!
//! Arithmetic is exact in Z[eps] with pairs (a, b) = a + b eps. The sign of
//! a + b eps follows from the sign of its conjugate a - b/eps and its norm
//! a^2 + x a b - b^2.
//!
//! Length bound (proven in the draft): an integer N with total length T has
//! T <= 2 log_eps N + 2, and N < eps^T.
//!
//! Identity: N(eps - 1) = -x and eps == 1 (mod eps - 1), so N == digit sum
//! (mod x), and a solution has sum (w(d) - d) == 0 (mod x).
//!
//! usage: r3t_pisot direct <x> <Nmax>        every N <= Nmax, both conventions
//!        r3t_pisot search <x> [J]           every digit multiset in the
//!                                           proven window; J offsets j x
//!        r3t_pisot model <x> <samples>      the model per integer-part length
//!        r3t_pisot lengths <x> <Nmax>       total lengths of N <= Nmax

use rayon::prelude::*;
use std::sync::Mutex;
use std::time::Instant;

#[derive(Clone)]
struct Ctx {
    x: i128,
    pw: Vec<(i128, i128)>, // eps^i for i = -off..
    off: usize,
    eps: f64,
}

impl Ctx {
    fn new(x: i128, kmax: usize) -> Ctx {
        let off = kmax + 4;
        let mut pw = vec![(0i128, 0i128); off + kmax + 4];
        pw[off] = (1, 0);
        for i in off + 1..pw.len() {
            let (a, b) = pw[i - 1];
            pw[i] = (b, a + x * b);
        }
        for i in (0..off).rev() {
            let (a, b) = pw[i + 1];
            pw[i] = (b - a * x, a);
        }
        let xf = x as f64;
        Ctx { x, pw, off, eps: (xf + (xf * xf + 4.0).sqrt()) / 2.0 }
    }
    #[inline]
    fn p(&self, i: isize) -> (i128, i128) {
        self.pw[(i + self.off as isize) as usize]
    }
    /// sign of a + b eps
    #[inline]
    fn sign(&self, a: i128, b: i128) -> i32 {
        if b == 0 {
            return a.signum() as i32;
        }
        if a == 0 {
            return b.signum() as i32;
        }
        if (a > 0) == (b > 0) {
            return a.signum() as i32;
        }
        let norm = a * a + self.x * a * b - b * b;
        if b > 0 { -(norm.signum() as i32) } else { norm.signum() as i32 }
    }
    /// greedy digits of the integer n, from position k down; returns (k, digits)
    fn expand(&self, n: i128) -> (isize, Vec<u8>) {
        let mut k: isize = 0;
        loop {
            let (a, b) = self.p(k + 1);
            if self.sign(n - a, -b) >= 0 { k += 1 } else { break }
        }
        let (mut ra, mut rb) = (n, 0i128);
        let mut out = vec![];
        let mut i = k;
        loop {
            let (a, b) = self.p(i);
            let mut d = 0;
            // largest d with d eps^i <= r
            let (mut lo, mut hi) = (0i128, self.x);
            while lo < hi {
                let mid = (lo + hi + 1) / 2;
                if self.sign(ra - mid * a, rb - mid * b) >= 0 { lo = mid } else { hi = mid - 1 }
            }
            d += lo;
            ra -= d * a;
            rb -= d * b;
            out.push(d as u8);
            i -= 1;
            if i < 0 && ra == 0 && rb == 0 {
                break;
            }
            assert!(out.len() < 400, "no termination");
        }
        (k, out)
    }
    /// the greedy digits of n if they have total length t and histogram c
    fn expand_if(&self, n: i128, c: &[usize], t: usize) -> Option<(isize, Vec<u8>)> {
        let k = self.ipow(n);
        if (k + 1) as usize > t {
            return None;
        }
        let mut h = [0usize; 64];
        let (mut ra, mut rb) = (n, 0i128);
        let mut out = Vec::with_capacity(t);
        let mut i = k;
        loop {
            let (a, b) = self.p(i);
            let (mut lo, mut hi) = (0i128, self.x);
            while lo < hi {
                let mid = (lo + hi + 1) / 2;
                if self.sign(ra - mid * a, rb - mid * b) >= 0 { lo = mid } else { hi = mid - 1 }
            }
            ra -= lo * a;
            rb -= lo * b;
            h[lo as usize] += 1;
            out.push(lo as u8);
            if h[lo as usize] > c[lo as usize] || out.len() > t {
                return None;
            }
            i -= 1;
            if i < 0 && ra == 0 && rb == 0 {
                break;
            }
        }
        if out.len() == t { Some((k, out)) } else { None }
    }
    /// integer-part length of n is floor(log_eps n) + 1; returns floor(log_eps n)
    fn ipow(&self, n: i128) -> isize {
        let mut k: isize = 0;
        loop {
            let (a, b) = self.p(k + 1);
            if self.sign(n - a, -b) >= 0 { k += 1 } else { break }
        }
        k
    }
}

fn weight(d: u32, m: u32) -> i128 {
    if d == 0 { m as i128 } else { (d as i128).pow(d) }
}

fn fmt(k: isize, ds: &[u8]) -> String {
    let mut s = String::new();
    for (j, d) in ds.iter().enumerate() {
        let pos = k - j as isize;
        if pos == -1 {
            s.push('.');
        } else if j > 0 {
            s.push(',');
        }
        s.push_str(&d.to_string());
    }
    s
}

fn direct(x: i128, nmax: i128) {
    let ctx = Ctx::new(x, 80);
    let sols = Mutex::new(vec![]);
    let chunk = 1 << 16;
    let nchunks = (nmax + chunk - 1) / chunk;
    (0..nchunks).into_par_iter().for_each(|c| {
        let mut loc = vec![];
        for n in (c * chunk).max(1)..((c + 1) * chunk).min(nmax + 1) {
            let (k, ds) = ctx.expand(n);
            let f0: i128 = ds.iter().map(|&d| weight(d as u32, 0)).sum();
            let z = ds.iter().filter(|&&d| d == 0).count() as i128;
            for m in 0..2 {
                if f0 + m * z == n {
                    loc.push((m, n, fmt(k, &ds)));
                }
            }
        }
        sols.lock().unwrap().extend(loc);
    });
    let mut s = sols.into_inner().unwrap();
    s.sort();
    for (m, n, d) in &s {
        println!("sol x {x} m {m} N {n} digits {d}");
    }
    println!("done direct x {x} Nmax {nmax} sols {}", s.len());
}

struct Search<'a> {
    ctx: &'a Ctx,
    w: Vec<i128>, // w[d] for d >= 1, w[0] = 0
    t: usize,
    lo: i128,
    hi: i128,
    offs: Vec<i128>,
    wres: Vec<i128>,
}

struct SOut {
    sols: Vec<(i128, i128, String)>,
    near: [Vec<u64>; 2],
    leaves: u64,
}

impl Search<'_> {
    /// does n have total length t and digit multiset c?
    fn matches(&self, n: i128, c: &[usize]) -> Option<String> {
        if n < self.lo || n >= self.hi {
            return None;
        }
        self.ctx.expand_if(n, c, self.t).map(|(k, ds)| fmt(k, &ds))
    }

    fn rec(&self, c: &mut Vec<usize>, d: usize, r: usize, f: i128, res: i128, o: &mut SOut) {
        let x = self.ctx.x as usize;
        if d == 0 {
            c[0] = r;
            o.leaves += 1;
            // every digit x except a last one is followed by a 0
            if c[x] <= c[0] + 1 {
                for m in 0..2i128 {
                    let fm = f + m * r as i128;
                    let rm = (res + m * r as i128).rem_euclid(self.ctx.x);
                    if rm != 0 {
                        continue;
                    }
                    if let Some(s) = self.matches(fm, c) {
                        o.sols.push((m, fm, s));
                    }
                    for (j, &dd) in self.offs.iter().enumerate() {
                        if self.matches(fm + dd, c).is_some() {
                            o.near[m as usize][j] += 1;
                        }
                    }
                }
            }
            c[0] = 0;
            return;
        }
        let dmax = *self.offs.last().unwrap_or(&0);
        for e in 0..=r {
            let f2 = f + e as i128 * self.w[d];
            let rr = (r - e) as i128;
            // remaining digits weigh between 0 and w[d-1] (plus 1 for zeros under m = 1)
            if f2 >= self.hi {
                break;
            }
            if f2 + rr * self.w[d - 1].max(1) + dmax < self.lo {
                continue;
            }
            c[d] = e;
            self.rec(c, d - 1, r - e, f2, res + e as i128 * self.wres[d], o);
        }
        c[d] = 0;
    }
}

fn search(x: i128, jmax: usize) {
    let ctx = Ctx::new(x, 120);
    let w: Vec<i128> = (0..=x as u32).map(|d| weight(d, 0)).collect();
    let wres: Vec<i128> = (0..=x).map(|d| (w[d as usize] - d).rem_euclid(x.max(1))).collect();
    let wtop = w[x as usize];
    // T <= 2 log_eps N + 2 and N <= T wtop (+ offsets)
    let offs: Vec<i128> = (1..=jmax as i128).map(|j| j * x).collect();
    let dmax = *offs.last().unwrap_or(&0);
    let mut tmax = 1;
    for t in 1..200usize {
        let nmax = (t as f64) * wtop as f64 + t as f64 + dmax as f64;
        if (t as f64) <= 2.0 * nmax.ln() / ctx.eps.ln() + 2.0 {
            tmax = t;
        }
    }
    println!("# search x {x}: eps = {:.6}, total length at most {tmax}, offsets {jmax}", ctx.eps);
    let t0 = Instant::now();
    let mut nsol = [0usize; 2];
    let mut near_tot = [vec![0u64; jmax], vec![0u64; jmax]];
    for t in 2..=tmax {
        // window: eps^((T-2)/2) <= N < eps^T, computed exactly as integers
        let lo_f = ctx.eps.powf((t as f64 - 2.0) / 2.0);
        let mut lo = (lo_f.floor() as i128 - 2).max(1);
        // exact: the smallest integer >= eps^((T-2)/2) up to slack; any N below
        // this has T > 2 log_eps N + 2, so lo may be lowered safely
        lo = lo.max(1);
        let hi = {
            let (a, b) = ctx.p(t as isize);
            // smallest integer > eps^t is a + ceil(b eps)
            let v = a as f64 + b as f64 * ctx.eps;
            if v > 1e30 { i128::MAX / 4 } else { v.ceil() as i128 + 1 }
        };
        let s = Search { ctx: &ctx, w: w.clone(), t, lo, hi, offs: offs.clone(), wres: wres.clone() };
        let xs = x as usize;
        let tasks: Vec<(usize, usize)> = (0..=t).flat_map(|a| (0..=t - a).map(move |b| (a, b))).collect();
        let out = Mutex::new(SOut { sols: vec![], near: [vec![0; jmax], vec![0; jmax]], leaves: 0 });
        tasks.par_iter().for_each(|&(a, b)| {
            let mut o = SOut { sols: vec![], near: [vec![0; jmax], vec![0; jmax]], leaves: 0 };
            let mut c = vec![0usize; xs + 1];
            if xs >= 2 {
                c[xs] = a;
                c[xs - 1] = b;
                let f = a as i128 * w[xs] + b as i128 * w[xs - 1];
                if f < hi {
                    let res = a as i128 * wres[xs] + b as i128 * wres[xs - 1];
                    s.rec(&mut c, xs - 2, t - a - b, f, res, &mut o);
                }
            } else if b == 0 {
                c[xs] = a;
                s.rec(&mut c, xs - 1, t - a, a as i128 * w[xs], a as i128 * wres[xs], &mut o);
            }
            let mut g = out.lock().unwrap();
            g.sols.extend(o.sols);
            g.leaves += o.leaves;
            for m in 0..2 {
                for j in 0..jmax {
                    g.near[m][j] += o.near[m][j];
                }
            }
        });
        let mut o = out.into_inner().unwrap();
        o.sols.sort();
        o.sols.dedup();
        for (m, n, d) in &o.sols {
            println!("sol x {x} m {m} T {t} N {n} digits {d}");
            nsol[*m as usize] += 1;
        }
        for m in 0..2 {
            for j in 0..jmax {
                near_tot[m][j] += o.near[m][j];
            }
        }
        println!("len x {x} T {t} window {lo}..{hi} leaves {} sols {} secs {:.1}", o.leaves, o.sols.len(), t0.elapsed().as_secs_f64());
    }
    for m in 0..2 {
        let v: Vec<String> = near_tot[m].iter().map(|v| v.to_string()).collect();
        println!("near x {x} m {m} step {x} counts {}", v.join(","));
    }
    println!("done search x {x} sols0 {} sols1 {} secs {:.1}", nsol[0], nsol[1], t0.elapsed().as_secs_f64());
}

fn model(x: i128, samples: usize) {
    let ctx = Ctx::new(x, 120);
    let wtop = weight(x as u32, 0);
    let md = x.max(1);
    let mut tot = [0f64; 6];
    println!("# model x {x}: windows eps^k <= N < eps^(k+1), refined factor {md}");
    for k in 1..60isize {
        let (a, b) = ctx.p(k);
        let lo_f = a as f64 + b as f64 * ctx.eps;
        if lo_f > (2.0 * k as f64 + 8.0) * (wtop as f64 + 1.0) {
            break;
        }
        let lo = lo_f.ceil() as i128;
        let (a1, b1) = ctx.p(k + 1);
        let hi = (a1 as f64 + b1 as f64 * ctx.eps).ceil() as i128;
        let acc = Mutex::new([0u64; 6]);
        let chunks = 32usize;
        (0..chunks).into_par_iter().for_each(|ci| {
            let mut s = 0x9e37_79b9_7f4a_7c15u64 ^ (ci as u64).wrapping_mul(0x1234_5678_9abc_def1) ^ ((k as u64) << 40) ^ ((x as u64) << 50);
            let mut next = || {
                s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = s;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            };
            let mut a6 = [0u64; 6];
            for _ in 0..samples / chunks {
                let n = lo + (next() as i128).rem_euclid(hi - lo);
                if ctx.ipow(n) != k {
                    continue; // float rounding at the window ends
                }
                let (_, ds) = ctx.expand(n);
                let f0: i128 = ds.iter().map(|&d| weight(d as u32, 0)).sum();
                let z = ds.iter().filter(|&&d| d == 0).count() as i128;
                let res: i128 = ds.iter().map(|&d| weight(d as u32, 0) - d as i128).sum();
                for m in 0..2i128 {
                    let f = f0 + m * z;
                    if f >= 1 && ctx.ipow(f) == k {
                        a6[3 * m as usize] += 1;
                        if (res + m * z).rem_euclid(md) == 0 {
                            a6[3 * m as usize + 1] += 1;
                            if z == 0 {
                                a6[3 * m as usize + 2] += 1;
                            }
                        }
                    }
                }
            }
            let mut g = acc.lock().unwrap();
            for i in 0..6 {
                g[i] += a6[i];
            }
        });
        let a = acc.into_inner().unwrap();
        let ns = (samples / chunks * chunks) as f64;
        let v: Vec<f64> = (0..6).map(|i| a[i] as f64 / ns * if i % 3 == 0 { 1.0 } else { md as f64 }).collect();
        if v.iter().any(|&t| t > 0.0) {
            println!(
                "len x {x} k {k} basic0 {:.4e} refined0 {:.4e} zerofree0 {:.4e} basic1 {:.4e} refined1 {:.4e} zerofree1 {:.4e}",
                v[0], v[1], v[2], v[3], v[4], v[5]
            );
        }
        for i in 0..6 {
            tot[i] += v[i];
        }
    }
    println!(
        "model x {x} basic0 {:.4} refined0 {:.4} zerofree0 {:.4} basic1 {:.4} refined1 {:.4} zerofree1 {:.4}",
        tot[0], tot[1], tot[2], tot[3], tot[4], tot[5]
    );
}

fn lengths(x: i128, nmax: i128) {
    let ctx = Ctx::new(x, 80);
    // max of T - 2 log_eps N, and the share of integers with no fractional part
    let mut worst = f64::MIN;
    let mut nint = 0u64;
    let mut fr = std::collections::BTreeMap::new();
    for n in 1..=nmax {
        let (k, ds) = ctx.expand(n);
        let t = ds.len();
        let m = t as isize - k - 1;
        if m == 0 {
            nint += 1;
        }
        *fr.entry(m - k).or_insert(0u64) += 1;
        let v = t as f64 - 2.0 * (n as f64).ln() / ctx.eps.ln();
        if v > worst {
            worst = v;
        }
    }
    println!("lengths x {x} N <= {nmax}: max T - 2 log_eps N = {worst:.4}, integers without fractional part {nint}");
    for (dm, c) in fr {
        println!("  fractional length minus k = {dm}: {c}");
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let x: i128 = a[2].parse().unwrap();
    match a[1].as_str() {
        "direct" => direct(x, a[3].parse().unwrap()),
        "search" => search(x, a.get(3).map(|s| s.parse().unwrap()).unwrap_or(0)),
        "model" => model(x, a[3].parse().unwrap()),
        "lengths" => lengths(x, a[3].parse().unwrap()),
        _ => panic!("unknown mode"),
    }
}
