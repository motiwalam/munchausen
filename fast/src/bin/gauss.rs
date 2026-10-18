//! Munchausen numbers in the Gaussian base beta = -n + i, digits 0..n^2.
//!
//! Every Gaussian integer has exactly one finite representation in this base
//! (Katai and Szabo). A digit string s is a Munchausen number when its value
//! equals F(s), the sum of x^x over its digits (0^0 = m). F(s) is a positive
//! rational integer, so we enumerate digit multisets, write F in base beta and
//! compare the multisets.
//!
//! Digit extraction: Z[i]/(beta) is Z/(n^2+1) through i -> n, so the last
//! digit of a + bi is (a + n b) mod (n^2+1).
//!
//! Length bound. If z has digits a_0, a_1, ..., then z_{k+1} = (z_k - a_k)/beta
//! gives |z_k| < |z| / |beta|^k + R0 with R0 = n^2 / (|beta| - 1). So for
//! k = ceil(log|z| / log|beta|), z_k lies in the disk |z| < 1 + R0, whose
//! Gaussian integers have at most L0 digits (computed below). Hence
//! len(z) <= ceil(log_|beta| |z|) + L0, and a d-digit number has
//! |z| > |beta|^(d - L0 - 1). A d-digit number also has
//! |z| <= n^2 (|beta|^d - 1) / (|beta| - 1).
//!
//! Identity: beta == 1 (mod beta - 1), so z == digit sum (mod beta - 1). For a
//! rational integer this is a congruence mod M = (n+1)^2 + 1, the norm of the
//! primitive Gaussian integer beta - 1. A solution has sum (w(x) - x) == 0 mod M.
//!
//! usage: gauss <n> <m> [--dmax D]       census, with the exact model sums
//!        gauss <n> <m> --mc D SAMPLES  the model at one length, by sampling

use rayon::prelude::*;
use std::sync::Mutex;
use std::time::Instant;

struct G {
    n: i128,
    q: i128, // n^2 + 1
    nd: usize,
    w: Vec<i128>,
    modulus: i128,
    wres: Vec<i128>,
}

impl G {
    fn digits(&self, mut a: i128, mut b: i128, out: &mut Vec<u8>) {
        out.clear();
        while a != 0 || b != 0 {
            let r = (a + self.n * b).rem_euclid(self.q);
            let x = a - r;
            let a2 = -self.n * x + b;
            let b2 = -x - self.n * b;
            debug_assert!(a2 % self.q == 0 && b2 % self.q == 0);
            a = a2 / self.q;
            b = b2 / self.q;
            out.push(r as u8);
            assert!(out.len() < 200, "no termination");
        }
    }
}

struct Out {
    sols: Vec<Vec<u8>>,
    basic: f64,
    refined: f64,
    zerofree: f64,
    leaves: u64,
}

#[allow(clippy::too_many_arguments)]
fn rec(g: &G, d: usize, c: &mut [u8], x: usize, t: i128, r: usize, res: i128, p: f64, lo: i128, hi: i128, inv_fact: &[f64], buf: &mut Vec<u8>, o: &mut Out) {
    if x == 0 {
        c[0] = r as u8;
        let t = t + r as i128 * g.w[0];
        let res = (res + r as i128 * g.wres[0]) % g.modulus;
        let p = p * inv_fact[r] * (d - r) as f64 / d as f64;
        o.leaves += 1;
        if t >= lo && t <= hi {
            g.digits(t, 0, buf);
            if buf.len() == d {
                o.basic += p;
                if res == 0 {
                    o.refined += p * g.modulus as f64;
                    if r == 0 {
                        o.zerofree += p * g.modulus as f64;
                    }
                    let mut h = vec![0u8; g.nd];
                    for &y in buf.iter() {
                        h[y as usize] += 1;
                    }
                    if h[..] == c[..g.nd] {
                        o.sols.push(buf.iter().rev().copied().collect());
                    }
                }
            }
        }
        c[0] = 0;
        return;
    }
    let wmin = g.w[..x].iter().copied().min().unwrap();
    let wmax = g.w[..x].iter().copied().max().unwrap();
    for e in 0..=r {
        let t2 = t + e as i128 * g.w[x];
        let rr = (r - e) as i128;
        if t2 + rr * wmin > hi {
            break;
        }
        if t2 + rr * wmax < lo {
            continue;
        }
        c[x] = e as u8;
        rec(g, d, c, x - 1, t2, r - e, (res + e as i128 * g.wres[x]) % g.modulus, p * inv_fact[e], lo, hi, inv_fact, buf, o);
    }
    c[x] = 0;
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: i128 = args[1].parse().unwrap();
    let m: i128 = args[2].parse().unwrap();
    let q = n * n + 1;
    let nd = q as usize;
    let w: Vec<i128> = (0..nd as u32).map(|x| if x == 0 { m } else { (x as i128).pow(x) }).collect();
    let modulus = (n + 1) * (n + 1) + 1;
    let wres = (0..nd).map(|x| (w[x] - x as i128).rem_euclid(modulus)).collect();
    let g = G { n, q, nd, w: w.clone(), modulus, wres };
    let absb = (q as f64).sqrt();
    // L0: the longest representation in the disk |z| < 1 + R0
    let r0 = (n * n) as f64 / (absb - 1.0);
    let rad = (1.0 + r0).ceil() as i128;
    let mut l0 = 0;
    let mut buf = vec![];
    for a in -rad..=rad {
        for b in -rad..=rad {
            if ((a * a + b * b) as f64).sqrt() < 1.0 + r0 {
                g.digits(a, b, &mut buf);
                l0 = l0.max(buf.len());
            }
        }
    }
    let wtop = *w.iter().max().unwrap();
    let mut dbound = 1;
    for d in 1..400usize {
        let f = (d as f64) * wtop as f64;
        if (d as f64) <= (f.ln() / absb.ln()).ceil() + l0 as f64 {
            dbound = d;
        }
    }
    let mut dmax = dbound;
    let mut mc: Option<(usize, usize)> = None;
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--dmax" => dmax = args[i + 1].parse().unwrap(),
            "--mc" => {
                mc = Some((args[i + 1].parse().unwrap(), args[i + 2].parse().unwrap()));
                i += 1;
            }
            a => panic!("unknown option {a}"),
        }
        i += 2;
    }
    println!("# base -{n}+i, 0^0 = {m}: R0 = {r0:.3}, L0 = {l0}, length bound {dbound}, modulus {modulus}");
    if let Some((d, samples)) = mc {
        // splitmix64 per thread chunk
        let chunks = 64;
        let per = samples / chunks;
        let acc = Mutex::new((0u64, 0f64, 0u64));
        (0..chunks).into_par_iter().for_each(|ci| {
            let mut s = 0x9e37_79b9_7f4a_7c15u64 ^ (ci as u64 * 0x1234_5678_9abc_def1) ^ (d as u64) << 40;
            let mut next = || {
                s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = s;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            };
            let (mut hit, mut refd, mut tot) = (0u64, 0f64, 0u64);
            let mut buf = vec![];
            for _ in 0..per {
                let mut f = 0i128;
                let mut res = 0i128;
                for k in 0..d {
                    let x = if k == 0 { 1 + (next() % (nd as u64 - 1)) } else { next() % nd as u64 } as usize;
                    f += g.w[x];
                    res += g.wres[x];
                }
                tot += 1;
                g.digits(f, 0, &mut buf);
                if buf.len() == d {
                    hit += 1;
                    if res % modulus == 0 {
                        refd += modulus as f64;
                    }
                }
            }
            let mut a = acc.lock().unwrap();
            a.0 += hit;
            a.1 += refd;
            a.2 += tot;
        });
        let a = acc.into_inner().unwrap();
        println!("mc base -{n}+i m {m} d {d} samples {} basic {:.6e} refined {:.6e}", a.2, a.0 as f64 / a.2 as f64, a.1 / a.2 as f64);
        return;
    }
    let total = Instant::now();
    let mut nsol = 0;
    for d in 2..=dmax {
        let t0 = Instant::now();
        let lo = absb.powi((d - l0 - 1) as i32).floor().max(1.0) as i128;
        let hi_f = (n * n) as f64 * (absb.powi(d as i32) - 1.0) / (absb - 1.0);
        let hi = if hi_f > 1e36 { i128::MAX / 4 } else { hi_f.ceil() as i128 };
        let mut lf = vec![0f64; d + 2];
        for k in 1..d + 2 {
            lf[k] = lf[k - 1] + (k as f64).ln();
        }
        let inv_fact: Vec<f64> = (0..=d).map(|k| (-lf[k]).exp()).collect();
        let p0 = (lf[d] - ((nd - 1) as f64).ln() - (d as f64 - 1.0) * (nd as f64).ln()).exp();
        let top = nd - 1;
        let two = top >= 2;
        let tasks: Vec<(usize, usize)> = (0..=d).flat_map(|a| (0..=if two { d - a } else { 0 }).map(move |b| (a, b))).collect();
        let out = Mutex::new(Out { sols: vec![], basic: 0.0, refined: 0.0, zerofree: 0.0, leaves: 0 });
        tasks.par_iter().for_each(|&(a, b)| {
            let mut o = Out { sols: vec![], basic: 0.0, refined: 0.0, zerofree: 0.0, leaves: 0 };
            let mut c = vec![0u8; nd];
            let mut buf = vec![];
            c[top] = a as u8;
            let mut t = a as i128 * w[top];
            let mut res = a as i128 * g.wres[top] % modulus;
            let mut p = p0 * inv_fact[a];
            if two {
                c[top - 1] = b as u8;
                t += b as i128 * w[top - 1];
                res = (res + b as i128 * g.wres[top - 1]) % modulus;
                p *= inv_fact[b];
                rec(&g, d, &mut c, top - 2, t, d - a - b, res, p, lo, hi, &inv_fact, &mut buf, &mut o);
            } else {
                rec(&g, d, &mut c, top - 1, t, d - a, res, p, lo, hi, &inv_fact, &mut buf, &mut o);
            }
            let mut g2 = out.lock().unwrap();
            g2.sols.extend(o.sols);
            g2.basic += o.basic;
            g2.refined += o.refined;
            g2.zerofree += o.zerofree;
            g2.leaves += o.leaves;
        });
        let mut o = out.into_inner().unwrap();
        o.sols.sort();
        for s in &o.sols {
            println!("sol base -{n}+i m {m} d {d} digits {}", s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","));
        }
        nsol += o.sols.len();
        println!(
            "len base -{n}+i m {m} d {d} sols {} leaves {} basic {:.6e} refined {:.6e} refined_zerofree {:.6e} secs {:.2}",
            o.sols.len(),
            o.leaves,
            o.basic,
            o.refined,
            o.zerofree,
            t0.elapsed().as_secs_f64()
        );
    }
    println!("total base -{n}+i m {m} up to d {dmax} sols {nsol} secs {:.2}", total.elapsed().as_secs_f64());
}
