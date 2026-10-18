//! Munchausen numbers in the Eisenstein base beta = -n + omega (question 63),
//! with the Gaussian base -n + i of `gauss.rs` as a control.
//!
//! Eisenstein: omega^2 + omega + 1 = 0, beta has norm Q = n^2 + n + 1 and the
//! digits are 0..Q-1. beta is a root of t^2 + (2n+1) t + (n^2+n+1), and a
//! quadratic t^2 + B t + C is a canonical number system base exactly when
//! -1 <= B <= C and C >= 2 (Katai and Kovacs; Gilbert). So every element of
//! Z[omega] has exactly one finite representation for n >= 1.
//!
//! Digit extraction: omega == n (mod beta), so the last digit of a + b omega
//! is (a + n b) mod Q. With x = a - r, (x + b omega) / beta =
//! ((b - (n+1) x) + (-x - n b) omega) / Q.
//!
//! Identity: beta == 1 (mod beta - 1), and beta - 1 = -(n+1) + omega is
//! primitive of norm M = n^2 + 3n + 3, which is odd. So a rational integer
//! solution has sum (w(x) - x) == 0 (mod M).
//!
//! Length bound: as in gauss.rs (Proposition 14.10), with |z|^2 = a^2 - ab + b^2.
//!
//! Offsets: with --offsets J the program also counts, for j = 1..J, the
//! integers z with z = F(z) + j M (near-solutions in the class of 0), as in
//! section 11.1.
//!
//! The basic model is summed only with --basic (it needs every leaf's digits).
//! --mc S samples the model per length instead of searching.
//!
//! usage: r3t_eisen <eisen|gauss> <n> <m> [--dmax D] [--dmin D] [--offsets J] [--basic] [--mc S]

use rayon::prelude::*;
use std::sync::Mutex;
use std::time::Instant;

#[derive(Clone, Copy, PartialEq)]
enum Ring {
    Eisen,
    Gauss,
}

struct G {
    ring: Ring,
    n: i64,
    q: i64,
    nd: usize,
    w: Vec<i64>,
    modulus: i64,
    wres: Vec<i64>,
    offs: Vec<i64>,
    wminp: Vec<i64>, // min of w[..x]
    wmaxp: Vec<i64>,
}

impl G {
    fn digits(&self, mut a: i64, mut b: i64, out: &mut Vec<u8>) {
        out.clear();
        let n = self.n;
        while a != 0 || b != 0 {
            let r = (a + n * b).rem_euclid(self.q);
            let x = a - r;
            let (a2, b2) = match self.ring {
                Ring::Eisen => (b - (n + 1) * x, -x - n * b),
                Ring::Gauss => (-n * x + b, -x - n * b),
            };
            debug_assert!(a2 % self.q == 0 && b2 % self.q == 0);
            a = a2 / self.q;
            b = b2 / self.q;
            out.push(r as u8);
            assert!(out.len() < 400, "no termination");
        }
    }
    /// true when the digits of the rational integer a are exactly the multiset c
    /// with d digits; stops at the first digit that does not fit
    fn matches(&self, mut a: i64, c: &[u8], d: usize) -> bool {
        let mut b = 0i64;
        let n = self.n;
        let mut h = [0u8; 64];
        let mut k = 0;
        while a != 0 || b != 0 {
            let r = (a + n * b).rem_euclid(self.q);
            h[r as usize] += 1;
            k += 1;
            if k > d || h[r as usize] > c[r as usize] {
                return false;
            }
            let x = a - r;
            let (a2, b2) = match self.ring {
                Ring::Eisen => (b - (n + 1) * x, -x - n * b),
                Ring::Gauss => (-n * x + b, -x - n * b),
            };
            a = a2 / self.q;
            b = b2 / self.q;
        }
        k == d
    }
    fn abs2(&self, a: i64, b: i64) -> i64 {
        match self.ring {
            Ring::Eisen => a * a - a * b + b * b,
            Ring::Gauss => a * a + b * b,
        }
    }
    fn name(&self) -> String {
        match self.ring {
            Ring::Eisen => format!("-{}+w", self.n),
            Ring::Gauss => format!("-{}+i", self.n),
        }
    }
}

struct Out {
    sols: Vec<Vec<u8>>,
    near: Vec<u64>,
    basic: f64,
    refined: f64,
    zerofree: f64,
    leaves: u64,
}

impl Out {
    fn new(j: usize) -> Out {
        Out { sols: vec![], near: vec![0; j], basic: 0.0, refined: 0.0, zerofree: 0.0, leaves: 0 }
    }
    fn add(&mut self, o: Out) {
        self.sols.extend(o.sols);
        for (a, b) in self.near.iter_mut().zip(o.near) {
            *a += b;
        }
        self.basic += o.basic;
        self.refined += o.refined;
        self.zerofree += o.zerofree;
        self.leaves += o.leaves;
    }
}

struct Ctx<'a> {
    g: &'a G,
    d: usize,
    lo: i64,
    hi: i64,
    dmaxoff: i64,
    inv_fact: &'a [f64],
    basic: bool,
}

fn same_hist(buf: &[u8], c: &[u8], nd: usize) -> bool {
    let mut h = [0u8; 64];
    for &y in buf {
        h[y as usize] += 1;
    }
    h[..nd] == c[..nd]
}

#[allow(clippy::too_many_arguments)]
fn rec(cx: &Ctx, c: &mut [u8], x: usize, t: i64, r: usize, res: i64, p: f64, buf: &mut Vec<u8>, o: &mut Out) {
    let g = cx.g;
    let d = cx.d;
    if x == 0 {
        c[0] = r as u8;
        let t = t + r as i64 * g.w[0];
        let res = (res + r as i64 * g.wres[0]) % g.modulus;
        let p = p * cx.inv_fact[r] * (d - r) as f64 / d as f64;
        o.leaves += 1;
        if res == 0 {
            for (k, &off) in g.offs.iter().enumerate() {
                let v = t + off;
                if v >= cx.lo && v <= cx.hi && g.matches(v, c, d) {
                    o.near[k] += 1;
                }
            }
        }
        if t >= cx.lo && t <= cx.hi && (res == 0 || cx.basic) {
            g.digits(t, 0, buf);
            if buf.len() == d {
                o.basic += p;
                if res == 0 {
                    o.refined += p * g.modulus as f64;
                    if r == 0 {
                        o.zerofree += p * g.modulus as f64;
                    }
                    if same_hist(buf, c, g.nd) {
                        o.sols.push(buf.iter().rev().copied().collect());
                    }
                }
            }
        }
        c[0] = 0;
        return;
    }
    let wmin = g.wminp[x];
    let wmax = g.wmaxp[x];
    for e in 0..=r {
        let t2 = t + e as i64 * g.w[x];
        let rr = (r - e) as i64;
        if t2 + rr * wmin > cx.hi {
            break;
        }
        if t2 + rr * wmax + cx.dmaxoff < cx.lo {
            continue;
        }
        c[x] = e as u8;
        rec(cx, c, x - 1, t2, r - e, (res + e as i64 * g.wres[x]) % g.modulus, p * cx.inv_fact[e], buf, o);
    }
    c[x] = 0;
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let ring = match args[1].as_str() {
        "eisen" => Ring::Eisen,
        "gauss" => Ring::Gauss,
        a => panic!("unknown ring {a}"),
    };
    let n: i64 = args[2].parse().unwrap();
    let m: i64 = args[3].parse().unwrap();
    let q = match ring {
        Ring::Eisen => n * n + n + 1,
        Ring::Gauss => n * n + 1,
    };
    let nd = q as usize;
    assert!(nd <= 64);
    let w: Vec<i64> = (0..nd as u32).map(|x| if x == 0 { m } else { (x as i64).pow(x) }).collect();
    let modulus = match ring {
        Ring::Eisen => n * n + 3 * n + 3,
        Ring::Gauss => (n + 1) * (n + 1) + 1,
    };
    let wres = (0..nd).map(|x| (w[x] - x as i64).rem_euclid(modulus)).collect();
    let mut dmax = 0usize;
    let mut dmin = 2usize;
    let mut nj = 0usize;
    let mut basic = false;
    let mut mc = 0usize;
    let mut i = 4;
    while i < args.len() {
        match args[i].as_str() {
            "--dmax" => dmax = args[i + 1].parse().unwrap(),
            "--dmin" => dmin = args[i + 1].parse().unwrap(),
            "--offsets" => nj = args[i + 1].parse().unwrap(),
            "--mc" => mc = args[i + 1].parse().unwrap(),
            "--basic" => {
                basic = true;
                i -= 1;
            }
            a => panic!("unknown option {a}"),
        }
        i += 2;
    }
    let offs: Vec<i64> = (1..=nj as i64).map(|j| j * modulus).collect();
    let wminp: Vec<i64> = (0..=nd).map(|x| w[..x].iter().copied().min().unwrap_or(0)).collect();
    let wmaxp: Vec<i64> = (0..=nd).map(|x| w[..x].iter().copied().max().unwrap_or(0)).collect();
    let g = G { ring, n, q, nd, w: w.clone(), modulus, wres, offs: offs.clone(), wminp, wmaxp };
    let absb = (q as f64).sqrt();
    let r0 = (q - 1) as f64 / (absb - 1.0);
    let rad = (2.0 * (1.0 + r0)).ceil() as i64 + 1;
    let mut l0 = 0;
    let mut buf = vec![];
    let lim = (1.0 + r0) * (1.0 + r0);
    for a in -rad..=rad {
        for b in -rad..=rad {
            if (g.abs2(a, b) as f64) < lim {
                g.digits(a, b, &mut buf);
                l0 = l0.max(buf.len());
            }
        }
    }
    let wtop = *w.iter().max().unwrap();
    assert!((wtop as f64) * 400.0 < 4e18, "weights too large for i64");
    let mut dbound = 1;
    for d in 1..400usize {
        let f = (d as f64) * wtop as f64 + offs.last().copied().unwrap_or(0) as f64;
        if (d as f64) <= (f.ln() / absb.ln()).ceil() + l0 as f64 {
            dbound = d;
        }
    }
    if dmax == 0 {
        dmax = dbound;
    }
    let name = g.name();
    println!("# base {name}, 0^0 = {m}: R0 = {r0:.3}, L0 = {l0}, length bound {dbound}, modulus {modulus}, offsets {nj}");
    if mc > 0 {
        // the model per length by sampling random d-digit strings
        for d in dmin..=dmax {
            let chunks = 64usize;
            let per = mc / chunks;
            let acc = Mutex::new((0u64, 0u64, 0u64));
            (0..chunks).into_par_iter().for_each(|ci| {
                let mut s = 0x9e37_79b9_7f4a_7c15u64 ^ (ci as u64 * 0x1234_5678_9abc_def1) ^ ((d as u64) << 40);
                let mut next = || {
                    s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
                    let mut z = s;
                    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                    z ^ (z >> 31)
                };
                let (mut hit, mut rhit, mut zf) = (0u64, 0u64, 0u64);
                let mut buf = vec![];
                for _ in 0..per {
                    let mut f = 0i64;
                    let mut res = 0i64;
                    let mut zero = false;
                    for k in 0..d {
                        let x = if k == 0 { 1 + (next() % (nd as u64 - 1)) } else { next() % nd as u64 } as usize;
                        f += g.w[x];
                        res += g.wres[x];
                        zero |= x == 0;
                    }
                    g.digits(f, 0, &mut buf);
                    if buf.len() == d {
                        hit += 1;
                        if res % modulus == 0 {
                            rhit += 1;
                            if !zero {
                                zf += 1;
                            }
                        }
                    }
                }
                let mut a = acc.lock().unwrap();
                a.0 += hit;
                a.1 += rhit;
                a.2 += zf;
            });
            let a = acc.into_inner().unwrap();
            let tot = (per * chunks) as f64;
            println!(
                "mc base {name} m {m} d {d} samples {} basic {:.4e} refined {:.4e} refined_zerofree {:.4e}",
                per * chunks,
                a.0 as f64 / tot,
                a.1 as f64 * modulus as f64 / tot,
                a.2 as f64 * modulus as f64 / tot
            );
        }
        return;
    }
    let total = Instant::now();
    let mut nsol = 0;
    let mut near_tot = vec![0u64; nj];
    for d in dmin..=dmax {
        let t0 = Instant::now();
        let lo = absb.powi((d as i32) - l0 as i32 - 1).floor().max(1.0) as i64;
        let hi_f = (q - 1) as f64 * (absb.powi(d as i32) - 1.0) / (absb - 1.0);
        let hi = if hi_f > 1e18 { i64::MAX / 4 } else { hi_f.ceil() as i64 };
        let mut lf = vec![0f64; d + 2];
        for k in 1..d + 2 {
            lf[k] = lf[k - 1] + (k as f64).ln();
        }
        let inv_fact: Vec<f64> = (0..=d).map(|k| (-lf[k]).exp()).collect();
        let p0 = (lf[d] - ((nd - 1) as f64).ln() - (d as f64 - 1.0) * (nd as f64).ln()).exp();
        let top = nd - 1;
        let tasks: Vec<(usize, usize)> = (0..=d).flat_map(|a| (0..=d - a).map(move |b| (a, b))).collect();
        let out = Mutex::new(Out::new(nj));
        let cx = Ctx { g: &g, d, lo, hi, dmaxoff: offs.last().copied().unwrap_or(0), inv_fact: &inv_fact, basic };
        tasks.par_iter().for_each(|&(a, b)| {
            let mut o = Out::new(nj);
            let mut c = vec![0u8; nd];
            let mut buf = vec![];
            c[top] = a as u8;
            c[top - 1] = b as u8;
            let t = a as i64 * w[top] + b as i64 * w[top - 1];
            let res = (a as i64 * g.wres[top] + b as i64 * g.wres[top - 1]) % modulus;
            let p = p0 * inv_fact[a] * inv_fact[b];
            rec(&cx, &mut c, top - 2, t, d - a - b, res, p, &mut buf, &mut o);
            out.lock().unwrap().add(o);
        });
        let mut o = out.into_inner().unwrap();
        o.sols.sort();
        for s in &o.sols {
            println!("sol base {name} m {m} d {d} digits {}", s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","));
        }
        nsol += o.sols.len();
        for (a, b) in near_tot.iter_mut().zip(&o.near) {
            *a += b;
        }
        let near: Vec<String> = o.near.iter().map(|x| x.to_string()).collect();
        println!(
            "len base {name} m {m} d {d} sols {} leaves {} basic {:.6e} refined {:.6e} refined_zerofree {:.6e} near {} secs {:.2}",
            o.sols.len(),
            o.leaves,
            o.basic,
            o.refined,
            o.zerofree,
            near.join(","),
            t0.elapsed().as_secs_f64()
        );
    }
    let near: Vec<String> = near_tot.iter().map(|x| x.to_string()).collect();
    println!("total base {name} m {m} d {dmin}..{dmax} sols {nsol} near {} secs {:.2}", near.join(","), total.elapsed().as_secs_f64());
}
