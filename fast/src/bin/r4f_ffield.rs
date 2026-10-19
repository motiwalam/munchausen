//! Munchausen numbers in F_q[T] with weight d^(q^deg d): a fast census by the
//! Horner form (round 4). q prime.
//!
//! Write Phi(n) = n(T^q) = n^q. For a digit d (deg d < e), d(T^q) has at most
//! R + 1 digits, R = floor((e-1) q / e); call them beta_0(d), ..., beta_R(d).
//! Since B(T)^q = B(T^q), Phi(sum d_i B^i) = sum Phi(d_i) B^(q i): Phi maps
//! each digit to its own block of q positions, without carries. Then
//!     n = F(x) = D_0 + m z + Phi(D_1 + Phi(D_2 + ... Phi(D_(e-1)))),
//! and the digit at position 0 of each level is p_j = sigma(p_(j+1)) + D_j,
//! sigma = beta_0 = Frobenius mod B. All other digits are frozen: the digits
//! of Phi^j(p_j) above its bottom block of q^(j-1) positions. So the class
//! sums of n are class(p_0) + sum_{j>=1} K_j(p_j), with K_j a table over
//! digits. The program enumerates x level by level with table lookups only.
//!
//! The bases are reduced to orbits under T -> aT + b, which maps solutions
//! to solutions (the weight commutes with every F_q-algebra automorphism).
//!
//! Output per orbit: representative, orbit size, solutions by length, the
//! chapter 5 model (basic and refined, exact sums) and the free residue
//! dimension k(B).
//!
//! usage: r4f_ffield <q> <e> <m> [--list] [--base CODE]
//! B is written in base q: coefficient of T^t is the t-th base-q digit.

use rayon::prelude::*;
use std::time::Instant;

type P = Vec<u32>;

fn trim(mut v: P) -> P {
    while let Some(&0) = v.last() {
        v.pop();
    }
    v
}

fn deg(v: &P) -> isize {
    v.len() as isize - 1
}

fn inv(x: u32, q: u32) -> u32 {
    (1..q).find(|&y| x * y % q == 1).unwrap()
}

fn padd(a: &P, b: &P, q: u32) -> P {
    let n = a.len().max(b.len());
    trim((0..n).map(|i| (a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0)) % q).collect())
}

fn pmul(a: &P, b: &P, q: u32) -> P {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut r = vec![0u32; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            r[i + j] = (r[i + j] + x * y) % q;
        }
    }
    trim(r)
}

fn pdivmod(a: &P, b: &P, q: u32) -> (P, P) {
    let mut r = a.clone();
    let db = deg(b);
    let li = inv(*b.last().unwrap(), q);
    let mut quo = vec![0u32; (deg(a) - db + 1).max(0) as usize];
    while deg(&r) >= db {
        let dr = deg(&r);
        let c = r.last().unwrap() * li % q;
        let sh = (dr - db) as usize;
        quo[sh] = c;
        for (i, &y) in b.iter().enumerate() {
            r[i + sh] = (r[i + sh] + q - c * y % q) % q;
        }
        r = trim(r);
    }
    (trim(quo), r)
}

fn digits(n: &P, b: &P, q: u32) -> Vec<P> {
    let mut out = vec![];
    let mut x = n.clone();
    while !x.is_empty() {
        let (qq, r) = pdivmod(&x, b, q);
        out.push(r);
        x = qq;
    }
    out
}

fn code(d: &P, q: u32) -> usize {
    d.iter().rev().fold(0usize, |acc, &c| acc * q as usize + c as usize)
}

fn decode(c: usize, q: u32, k: usize) -> P {
    let mut v = vec![0u32; k];
    let mut x = c;
    for t in 0..k {
        v[t] = (x % q as usize) as u32;
        x /= q as usize;
    }
    trim(v)
}

/// B(aT + b)
fn compose(bp: &P, a: u32, b: u32, q: u32) -> P {
    let lin: P = trim(vec![b, a]);
    let mut r: P = vec![];
    for &c in bp.iter().rev() {
        r = padd(&pmul(&r, &lin, q), &trim(vec![c]), q);
    }
    r
}

/// orbits of the bases of degree e under T -> aT + b: (representative, size)
fn orbits(q: u32, e: usize) -> Vec<(P, usize)> {
    let lo = (q as usize).pow(e as u32);
    let mut seen = vec![false; lo * q as usize];
    let mut out = vec![];
    for c in lo..lo * q as usize {
        if seen[c] {
            continue;
        }
        let b = decode(c, q, e + 1);
        let mut orb = vec![];
        for a in 1..q {
            for s in 0..q {
                let k = code(&compose(&b, a, s, q), q);
                if !seen[k] {
                    seen[k] = true;
                    orb.push(k);
                }
            }
        }
        out.push((b, orb.len()));
    }
    out
}

/// the free residue dimension: e - rank of D -> sum_j (Frob^j - 1) D_j mod B - 1
fn corank(b: &P, q: u32, e: usize) -> usize {
    let bm1 = padd(b, &vec![q - 1], q);
    let mut rows: Vec<Vec<u32>> = vec![];
    for j in 0..e {
        for t in 0..=j {
            let mut v = vec![0u32; t * (q as usize).pow(j as u32) + 1];
            *v.last_mut().unwrap() = 1;
            v[t] = (v[t] + q - 1) % q;
            let r = pdivmod(&trim(v), &bm1, q).1;
            let mut row = r.clone();
            row.resize(e, 0);
            rows.push(row);
        }
    }
    let mut rank = 0;
    for col in 0..e {
        let Some(piv) = (rank..rows.len()).find(|&i| rows[i][col] != 0) else { continue };
        rows.swap(rank, piv);
        let iv = inv(rows[rank][col], q);
        for i in 0..rows.len() {
            if i != rank && rows[i][col] != 0 {
                let c = rows[i][col] * iv % q;
                for k in 0..e {
                    rows[i][k] = (rows[i][k] + q - c * rows[rank][k] % q) % q;
                }
            }
        }
        rank += 1;
    }
    e - rank
}

// ------------------------------------------------------------------ model

/// model[l][type]: probability that l random digits (top nonzero) have class
/// sums of the given type. The type of x records per class j whether D_j = 0,
/// D_j != 0 with zero T^j coefficient, or a nonzero T^j coefficient (3 values,
/// digit j of the type in base 3), and z mod q when m = 1. The probability of
/// one particular x of that type is model / (number of x of the type).
/// Here we return directly the probability of one x.
fn model(q: usize, e: usize, m: usize, lmax: usize) -> Vec<Vec<f64>> {
    let qf = q as f64;
    let qe = qf.powi(e as i32);
    // class probabilities for a lower digit: index 0 = zero digit, 1 + j = degree j
    let mut pc = vec![1.0 / qe];
    for j in 0..e {
        pc.push((qf - 1.0) * qf.powi(j as i32) / qe);
    }
    let nz = qe - 1.0;
    let mut ptop = vec![0.0];
    for j in 0..e {
        ptop.push((qf - 1.0) * qf.powi(j as i32) / nz);
    }
    // P(sum of k uniform nonzero = 0), and = c for one c != 0
    let r = -1.0 / (qf - 1.0);
    let s0 = |k: usize| (1.0 + (qf - 1.0) * r.powi(k as i32)) / qf;
    let s1 = |k: usize| (1.0 - r.powi(k as i32)) / qf;
    // f(class, tau, k): probability that k digits of class j have a given sum of type tau
    let f = |j: usize, tau: usize, k: usize| -> f64 {
        if k == 0 {
            return if tau == 0 { 1.0 } else { 0.0 };
        }
        let low = qf.powi(-(j as i32));
        match tau {
            0 | 1 => low * s0(k),
            _ => low * s1(k),
        }
    };
    let ntype = 3usize.pow(e as u32) * if m == 1 { q } else { 1 };
    let mut lf = vec![0.0f64; lmax + 2];
    for k in 1..lmax + 2 {
        lf[k] = lf[k - 1] + (k as f64).ln();
    }
    let mut out = vec![vec![0.0; ntype]; lmax + 1];
    for l in 1..=lmax {
        for ty in 0..ntype {
            let zt = ty / 3usize.pow(e as u32);
            let mut taus = vec![0usize; e];
            let mut x = ty % 3usize.pow(e as u32);
            for t in taus.iter_mut() {
                *t = x % 3;
                x /= 3;
            }
            // tau = 1 (nonzero, zero top coefficient) is impossible for j = 0
            if taus[0] == 1 {
                continue;
            }
            let mut total = 0.0;
            // ln binomial(n, k)
            let lb = |n: usize, k: usize| lf[n] - lf[k] - lf[n - k];
            for top in 1..=e {
                // sequential binomial split of the l - 1 lower digits over the classes:
                // dp[n] = probability that n digits remain, times the class factors so far
                let mut dp = vec![0.0f64; l];
                let mut rest = 1.0f64;
                // zero class first
                let pz = pc[0] / rest;
                for k in 0..l {
                    if m == 1 && k % q != zt {
                        continue;
                    }
                    let n = l - 1 - k;
                    dp[n] += (lb(l - 1, k) + (k as f64) * pz.ln() + (n as f64) * (1.0 - pz).ln()).exp();
                }
                rest -= pc[0];
                for j in 0..e {
                    let extra = if top == j + 1 { 1 } else { 0 };
                    let pj = if j == e - 1 { 1.0 } else { pc[j + 1] / rest };
                    let mut nd = vec![0.0f64; l];
                    for n in 0..l {
                        if dp[n] == 0.0 {
                            continue;
                        }
                        let krange: Vec<usize> = if j == e - 1 { vec![n] } else { (0..=n).collect() };
                        for k in krange {
                            let fk = f(j, taus[j], k + extra);
                            if fk == 0.0 {
                                continue;
                            }
                            let lp = if j == e - 1 {
                                0.0
                            } else {
                                lb(n, k) + (k as f64) * pj.ln() + ((n - k) as f64) * (1.0 - pj).ln()
                            };
                            nd[n - k] += dp[n] * lp.exp() * fk;
                        }
                    }
                    dp = nd;
                    rest -= pc[j + 1];
                }
                total += ptop[top] * dp[0];
            }
            out[l][ty] = total;
        }
    }
    out
}

// ------------------------------------------------------------------ census

struct Tables {
    q: usize,
    e: usize,
    nd: usize,
    add: Vec<u16>,       // nd * nd
    sigma: Vec<u16>,     // Frobenius mod B
    // per level j >= 1 and digit p: frozen class sums, nonzero count, top position + 1
    kcls: Vec<Vec<Vec<u8>>>, // [j][p] -> class vector, length nc0 = e(e+1)/2
    knz: Vec<Vec<u32>>,
    ktop: Vec<Vec<u32>>,
    dcls: Vec<(usize, Vec<u8>)>, // class index and coefficients of a single digit
    iota: Vec<Vec<u16>>,         // [j][D_j code] -> (Frob'^j - 1) D_j mod B - 1, as a digit code
    iz: u16,                     // residue of the constant 1 (for m z)
    coord: Vec<(usize, usize)>,  // (j, t) of each class-sum coordinate
}

fn ci(j: usize, t: usize) -> usize {
    j * (j + 1) / 2 + t
}

fn tables(q: usize, e: usize, b: &P) -> Tables {
    let qq = q as u32;
    let nd = q.pow(e as u32);
    let nc0 = e * (e + 1) / 2;
    let mut add = vec![0u16; nd * nd];
    for a in 0..nd {
        let pa = decode(a, qq, e);
        for c in 0..nd {
            add[a * nd + c] = code(&padd(&pa, &decode(c, qq, e), qq), qq) as u16;
        }
    }
    let rr = (e - 1) * q / e;
    // beta[d] = digits of d(T^q), padded to q
    let mut beta = vec![vec![0usize; q]; nd];
    for d in 0..nd {
        let pd = decode(d, qq, e);
        let mut f = vec![0u32; pd.len().max(1) * q];
        for (t, &c) in pd.iter().enumerate() {
            f[t * q] = c;
        }
        let ds = digits(&trim(f), b, qq);
        assert!(ds.len() <= rr + 1);
        for (i, dd) in ds.iter().enumerate() {
            beta[d][i] = code(dd, qq);
        }
    }
    let sigma: Vec<u16> = (0..nd).map(|d| beta[d][0] as u16).collect();
    let dcls: Vec<(usize, Vec<u8>)> = (0..nd)
        .map(|d| {
            let pd = decode(d, qq, e);
            if pd.is_empty() {
                (usize::MAX, vec![])
            } else {
                (pd.len() - 1, pd.iter().map(|&c| c as u8).collect())
            }
        })
        .collect();
    // strings S_j(d) = digit string of Phi^j(d), length q^j
    let mut kcls = vec![vec![]; e];
    let mut knz = vec![vec![]; e];
    let mut ktop = vec![vec![]; e];
    let mut strings: Vec<Vec<usize>> = (0..nd).map(|d| vec![d]).collect();
    for j in 1..e {
        strings = strings
            .iter()
            .map(|s| {
                let mut t = vec![0usize; s.len() * q];
                for (i, &d) in s.iter().enumerate() {
                    for r in 0..q {
                        t[i * q + r] = beta[d][r];
                    }
                }
                t
            })
            .collect();
        let lo = q.pow(j as u32 - 1);
        for s in &strings {
            let mut cv = vec![0u8; nc0];
            let mut nz = 0u32;
            let mut top = 0u32;
            for (i, &d) in s.iter().enumerate().skip(lo) {
                if d == 0 {
                    continue;
                }
                nz += 1;
                top = i as u32 + 1;
                let (cj, ref co) = dcls[d];
                for (t, &c) in co.iter().enumerate() {
                    let k = ci(cj, t);
                    cv[k] = ((cv[k] as u32 + c as u32) % qq) as u8;
                }
            }
            kcls[j].push(cv);
            knz[j].push(nz);
            ktop[j].push(top);
        }
    }
    // identity residues mod B - 1
    let bm1 = padd(b, &vec![qq - 1], qq);
    let mut iota = vec![vec![]; e];
    for j in 0..e {
        for dc in 0..q.pow(j as u32 + 1) {
            let pd = decode(dc, qq, j + 1);
            let mut f = vec![0u32; (j * q.pow(j as u32) + 1).max(1)];
            for (t, &c) in pd.iter().enumerate() {
                let k = t * q.pow(j as u32);
                f[k] = (f[k] + c) % qq;
            }
            let v = padd(&trim(f), &pd.iter().map(|&c| (qq - c) % qq).collect(), qq);
            iota[j].push(code(&pdivmod(&v, &bm1, qq).1, qq) as u16);
        }
    }
    let iz = code(&pdivmod(&vec![1], &bm1, qq).1, qq) as u16;
    let coord = (0..e).flat_map(|j| (0..=j).map(move |t| (j, t))).collect();
    Tables { q, e, nd, add, sigma, kcls, knz, ktop, dcls, iota, iz, coord }
}

struct Res {
    by_len: Vec<u64>,
    basic: f64,
    refined: f64,
}

#[allow(clippy::too_many_arguments)]
fn walk(tb: &Tables, m: usize, lmax: usize, mdl: &[Vec<f64>], j: usize, p_up: usize, acc: &mut Vec<u8>, nz: u32, top: u32, iot: u16, x: &mut Vec<u8>, taus: usize, res: &mut Res) {
    let q = tb.q;
    let e = tb.e;
    let nd = tb.nd;
    let nc0 = e * (e + 1) / 2;
    let base_p = if j == e - 1 { 0 } else { tb.sigma[p_up] as usize };
    let ndj = q.pow(j as u32 + 1);
    for dj in 0..ndj {
        // D_j coefficients
        let mut tau = 0;
        let mut c = dj;
        for t in 0..=j {
            x[ci(j, t)] = (c % q) as u8;
            c /= q;
        }
        if dj != 0 {
            tau = if x[ci(j, j)] != 0 { 2 } else { 1 };
        }
        let taus2 = taus + tau * 3usize.pow(j as u32);
        let iot2 = tb.add[iot as usize * nd + tb.iota[j][dj] as usize];
        if j >= 1 {
            let p = tb.add[base_p * nd + dj] as usize;
            let kc = &tb.kcls[j][p];
            let mut acc2 = acc.clone();
            for k in 0..nc0 {
                acc2[k] = ((acc2[k] as usize + kc[k] as usize) % q) as u8;
            }
            let top2 = top.max(tb.ktop[j][p]);
            walk(tb, m, lmax, mdl, j - 1, p, &mut acc2, nz + tb.knz[j][p], top2, iot2, x, taus2, res);
        } else {
            for z in 0..(if m == 1 { q } else { 1 }) {
                // p_0 = sigma(p_1) + D_0 + m z, a constant added
                let cst = (dj + m * z) % q;
                let p0 = tb.add[base_p * nd + cst] as usize;
                let len = top.max(if p0 != 0 { 1 } else { 0 }) as usize;
                if len < 2 {
                    continue;
                }
                let iot3 = if m == 1 && z > 0 {
                    let mut v = iot2 as usize;
                    for _ in 0..z {
                        v = tb.add[v * nd + tb.iz as usize] as usize;
                    }
                    v
                } else {
                    iot2 as usize
                };
                let ty = taus2 + if m == 1 { z * 3usize.pow(e as u32) } else { 0 };
                let pm = if len <= lmax { mdl[len][ty] } else { 0.0 };
                res.basic += pm;
                if iot3 == 0 {
                    res.refined += pm;
                }
                // class sums
                let (cj, ref co) = tb.dcls[p0];
                let mut ok = true;
                for k in 0..nc0 {
                    let mut v = acc[k] as usize;
                    let (jk, t) = tb.coord[k];
                    if jk == cj {
                        v += co[t] as usize;
                    }
                    if v % q != x[k] as usize {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }
                if m == 1 {
                    let nzt = nz + if p0 != 0 { 1 } else { 0 };
                    let zz = (len as u32 - nzt) as usize;
                    if zz % q != z {
                        continue;
                    }
                }
                res.by_len[len] += 1;
            }
        }
    }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let q: usize = a[1].parse().unwrap();
    let e: usize = a[2].parse().unwrap();
    let m: usize = a[3].parse().unwrap();
    let mut only: Option<usize> = None;
    let mut i = 4;
    while i < a.len() {
        match a[i].as_str() {
            "--base" => {
                only = Some(a[i + 1].parse().unwrap());
                i += 2;
            }
            o => panic!("unknown option {o}"),
        }
    }
    let qq = q as u32;
    let lmax = (e - 1) * q.pow(e as u32 - 1) / e + 1;
    let t0 = Instant::now();
    let mdl = model(q, e, m, lmax);
    let qe = q.pow(e as u32) as f64;
    println!("# r4f_ffield q {q} e {e} m {m} max length {lmax}, model in {:.1} s", t0.elapsed().as_secs_f64());
    let orbs: Vec<(P, usize)> = match only {
        Some(c) => vec![(decode(c, qq, e + 4), 1)],
        None => orbits(qq, e),
    };
    let res: Vec<(usize, usize, usize, Res)> = orbs
        .par_iter()
        .map(|(b, w)| {
            let tb = tables(q, e, b);
            let mut res = Res { by_len: vec![0; lmax + 1], basic: 0.0, refined: 0.0 };
            let mut acc = vec![0u8; e * (e + 1) / 2];
            let mut x = vec![0u8; e * (e + 1) / 2];
            walk(&tb, m, lmax, &mdl, e - 1, 0, &mut acc, 0, 0, 0, &mut x, 0, &mut res);
            res.refined *= qe;
            (code(b, qq), *w, corank(b, qq, e), res)
        })
        .collect();
    let mut tot_s = 0u64;
    let mut tot_w = 0usize;
    let (mut tb_, mut tr_) = (0.0, 0.0);
    for (c, w, k, r) in &res {
        let s: u64 = r.by_len.iter().sum();
        let lens: Vec<String> = r.by_len.iter().enumerate().filter(|(_, v)| **v > 0).map(|(l, v)| format!("{l}:{v}")).collect();
        println!("orbit {c} size {w} k {k} sols {s} basic {:.4} refined {:.4} lengths {}", r.basic, r.refined, lens.join(","));
        tot_s += s * *w as u64;
        tot_w += w;
        tb_ += r.basic * *w as f64;
        tr_ += r.refined * *w as f64;
    }
    println!(
        "# total q {q} e {e} m {m}: bases {tot_w} solutions {tot_s} per base {:.4} basic {:.4} refined {:.4} time {:.1} s",
        tot_s as f64 / tot_w as f64,
        tb_ / tot_w as f64,
        tr_ / tot_w as f64,
        t0.elapsed().as_secs_f64()
    );
}
