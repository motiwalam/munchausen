//! Munchausen numbers in F_q[T] (question 61), q prime.
//!
//! A base B of degree e >= 2 (any nonzero leading coefficient) gives every
//! polynomial n a unique expansion n = sum d_i B^i with deg d_i < e. The weight
//! of a digit d is d^|d| with |d| = q^(deg d) (mode frob), or d^(deg d)
//! (mode deg). The digit 0 weighs m (the convention 0^0 = m, m in {0, 1}).
//! A solution is n = F(n) = sum w(d_i), with at least 2 digits (nontrivial).
//!
//! Mode frob uses linearity. Over F_q, d^(q^j) = d(T^(q^j)), so
//!     F(n) = sum_j D_j(T^(q^j)) + m * z,
//! where D_j is the sum of the digits of degree exactly j and z is the number
//! of zero digits (mod p = q). So F depends only on the class sums
//! (D_0, ..., D_(e-1), z), a point of a group G of size q^(e(e+1)/2) (times q
//! if m = 1). n is a solution exactly when the class sums of F(D, z) are
//! (D, z). The program enumerates G, with the base-B digits of F(D, z)
//! updated linearly.
//!
//! Model (chapter 5 adapted): for a random digit string with L digits (top
//! digit nonzero), let P_L be the law of its class sums. Then
//!     basic   = sum over (D,z) of P_L(D,z), L = length of F(D,z), L >= 2,
//!     refined = the same sum restricted to the identity
//!               F == sum_j D_j (mod B - 1), times q^e.
//! In mode brute the same numbers come from all digit multisets with the
//! weights computed by real powering, which checks mode frob.
//!
//! With --offdeg K, mode frob also counts the near-solutions n = F(n) + (B-1) g
//! for every nonzero g of degree < K (section 11.1); the digits of F + (B-1) g
//! are the sums of the digits, since base-B expansion is linear.
//!
//! --minlen L counts only solutions (and model mass) with at least L digits.
//!
//! usage: r3t_ffield frob  <q> <e> <m> <B|all> [--offdeg K] [--minlen L]
//!        r3t_ffield brute <q> <e> <m> <frob|deg> <B|all> [--lmax L]
//! B is written in base q: coefficient of T^t is the t-th base-q digit.

use rayon::prelude::*;
use std::time::Instant;

type P = Vec<u8>;

fn trim(mut v: P) -> P {
    while let Some(&0) = v.last() {
        v.pop();
    }
    v
}

fn deg(v: &P) -> isize {
    v.len() as isize - 1
}

fn add(a: &P, b: &P, q: u8) -> P {
    let n = a.len().max(b.len());
    let mut r = vec![0u8; n];
    for i in 0..n {
        let x = a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0);
        r[i] = x % q;
    }
    trim(r)
}

fn scale(a: &P, c: u8, q: u8) -> P {
    trim(a.iter().map(|&x| ((x as u32 * c as u32) % q as u32) as u8).collect())
}

fn mul(a: &P, b: &P, q: u8) -> P {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut r = vec![0u32; a.len() + b.len() - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            r[i + j] += x as u32 * y as u32;
        }
    }
    trim(r.into_iter().map(|x| (x % q as u32) as u8).collect())
}

fn powp(a: &P, mut k: u64, q: u8) -> P {
    let mut r: P = vec![1];
    let mut b = a.clone();
    while k > 0 {
        if k & 1 == 1 {
            r = mul(&r, &b, q);
        }
        k >>= 1;
        if k > 0 {
            b = mul(&b, &b, q);
        }
    }
    r
}

fn inv(x: u8, q: u8) -> u8 {
    (1..q).find(|&y| (x as u32 * y as u32) % q as u32 == 1).unwrap()
}

/// remainder of a modulo b
fn rem(a: &P, b: &P, q: u8) -> P {
    let mut r = a.clone();
    let db = deg(b);
    let li = inv(*b.last().unwrap(), q);
    while deg(&r) >= db {
        let dr = deg(&r);
        let c = (*r.last().unwrap() as u32 * li as u32 % q as u32) as u8;
        let sh = (dr - db) as usize;
        for (i, &y) in b.iter().enumerate() {
            let v = r[i + sh] as u32 + (q as u32 - (c as u32 * y as u32) % q as u32);
            r[i + sh] = (v % q as u32) as u8;
        }
        r = trim(r);
    }
    r
}

/// base-B digits, least significant first, each as a vector of e coefficients
fn digits(n: &P, b: &P, q: u8, e: usize) -> Vec<Vec<u8>> {
    let mut out = vec![];
    let mut x = n.clone();
    let db = deg(b);
    let li = inv(*b.last().unwrap(), q);
    while !x.is_empty() {
        // divmod by b
        let mut r = x.clone();
        let mut quo = vec![0u8; (deg(&x) - db + 1).max(0) as usize];
        while deg(&r) >= db {
            let dr = deg(&r);
            let c = (*r.last().unwrap() as u32 * li as u32 % q as u32) as u8;
            let sh = (dr - db) as usize;
            quo[sh] = c;
            for (i, &y) in b.iter().enumerate() {
                let v = r[i + sh] as u32 + (q as u32 - (c as u32 * y as u32) % q as u32);
                r[i + sh] = (v % q as u32) as u8;
            }
            r = trim(r);
        }
        let mut d = r.clone();
        d.resize(e, 0);
        out.push(d);
        x = trim(quo);
    }
    out
}

fn code(d: &[u8], q: u8) -> usize {
    d.iter().rev().fold(0usize, |acc, &c| acc * q as usize + c as usize)
}

fn decode(c: usize, q: u8, e: usize) -> P {
    let mut v = vec![0u8; e + 1];
    let mut x = c;
    for t in 0..=e {
        v[t] = (x % q as usize) as u8;
        x /= q as usize;
    }
    trim(v)
}

fn fmt_poly(p: &P) -> String {
    if p.is_empty() {
        return "0".into();
    }
    let mut terms = vec![];
    for t in (0..p.len()).rev() {
        let c = p[t];
        if c == 0 {
            continue;
        }
        let mono = match t {
            0 => String::new(),
            1 => "T".into(),
            _ => format!("T^{t}"),
        };
        terms.push(if t == 0 {
            c.to_string()
        } else if c == 1 {
            mono
        } else {
            format!("{c}{mono}")
        });
    }
    terms.join("+")
}

fn roots_of_bm1(b: &P, q: u8) -> usize {
    let bm1 = add(b, &vec![q - 1], q);
    (0..q)
        .filter(|&a| {
            let mut v = 0u32;
            for &c in bm1.iter().rev() {
                v = (v * a as u32 + c as u32) % q as u32;
            }
            v == 0
        })
        .count()
}

fn irreducible(b: &P, q: u8) -> bool {
    let e = deg(b) as usize;
    for dd in 1..=e / 2 {
        for c in 0..(q as usize).pow(dd as u32) {
            let mut f = decode(c, q, dd);
            f.resize(dd + 1, 0);
            f[dd] = 1;
            if rem(b, &f, q).is_empty() {
                return false;
            }
        }
    }
    true
}

fn bases(q: u8, e: usize, spec: &str) -> Vec<P> {
    if spec == "all" {
        let lo = (q as usize).pow(e as u32);
        (lo..lo * q as usize).map(|c| decode(c, q, e)).collect()
    } else {
        let b = decode(spec.parse().unwrap(), q, e + 4);
        assert_eq!(deg(&b), e as isize, "base has the wrong degree");
        vec![b]
    }
}

// ------------------------------------------------------------------ frob

struct Layout {
    q: usize,
    e: usize,
    m: usize,
    minlen: usize,     // count solutions with at least this many digits
    ncoord: usize,     // number of base-q coordinates (incl. z)
    coord_jt: Vec<(usize, usize)>, // (j, t); j = e means the z coordinate
    n: usize,
}

impl Layout {
    fn new(q: usize, e: usize, m: usize) -> Layout {
        let mut coord_jt = vec![];
        for j in 0..e {
            for t in 0..=j {
                coord_jt.push((j, t));
            }
        }
        if m == 1 {
            coord_jt.push((e, 0));
        }
        let ncoord = coord_jt.len();
        Layout { q, e, m, minlen: 2, ncoord, coord_jt, n: q.pow(ncoord as u32) }
    }
    /// the coordinate index of (j, t)
    fn ci(&self, j: usize, t: usize) -> usize {
        if j == self.e { self.ncoord - 1 } else { j * (j + 1) / 2 + t }
    }
}

struct FrobBase {
    sols: Vec<String>,
    near: Vec<u64>, // per offset (B - 1) g
    noff: usize,
    cond: Vec<u64>, // bitset over idx: the identity mod B - 1 holds
    roots: usize,
    irred: bool,
}

fn frob_base(lay: &Layout, b: &P, lmax0: usize, offdeg: usize) -> FrobBase {
    let q = lay.q;
    let e = lay.e;
    let qq = q as u8;
    // offsets (B - 1) g for the nonzero g of degree < offdeg
    let bm1o = add(b, &vec![qq - 1], qq);
    let offs: Vec<P> = (1..q.pow(offdeg as u32)).map(|c| mul(&bm1o, &decode(c, qq, offdeg), qq)).collect();
    let lmax = offs.iter().map(|o| deg(o) as usize / e + 1).max().unwrap_or(0).max(lmax0);
    let mut oimg = vec![vec![0u8; lmax * e]; offs.len()];
    for (k, o) in offs.iter().enumerate() {
        for (i, d) in digits(o, b, qq, e).iter().enumerate() {
            oimg[k][i * e..i * e + e].copy_from_slice(d);
        }
    }
    let mut near = vec![0u64; offs.len()];
    let mut tmp = vec![0u8; lmax * e];
    // images of the coordinates: digits of F and residue mod B-1
    let bm1 = add(b, &vec![qq - 1], qq);
    let mut img = vec![vec![0u8; lmax * e]; lay.ncoord];
    let mut rimg = vec![vec![0u8; e]; lay.ncoord];
    for (k, &(j, t)) in lay.coord_jt.iter().enumerate() {
        let (f, s): (P, P) = if j == e {
            (vec![1], vec![])
        } else {
            let mut f = vec![0u8; t * q.pow(j as u32) + 1];
            *f.last_mut().unwrap() = 1;
            let mut s = vec![0u8; t + 1];
            s[t] = 1;
            (f, s)
        };
        for (i, d) in digits(&f, b, qq, e).iter().enumerate() {
            img[k][i * e..i * e + e].copy_from_slice(d);
        }
        // identity: F - digit sum == 0 mod B - 1
        let r = rem(&add(&f, &scale(&s, qq - 1, qq), qq), &bm1, qq);
        for (i, &c) in r.iter().enumerate() {
            rimg[k][i] = c;
        }
    }
    let mut cond = vec![0u64; lay.n.div_ceil(64)];
    let mut sols = vec![];
    let mut coord = vec![0usize; lay.ncoord];
    let mut dv = vec![0u8; lmax * e];
    let mut img2 = img.clone();
    for v in img2.iter_mut() {
        v.resize(lmax * e, 0);
    }
    let img = img2;
    let mut rv = vec![0u8; e];
    let mut cls = vec![0u8; (e + 1) * e];
    for idx in 0..lay.n {
        if idx > 0 {
            // increment the counter, adding the image of every coordinate that moves
            let mut k = 0;
            loop {
                coord[k] += 1;
                for (x, &y) in dv.iter_mut().zip(&img[k]) {
                    *x = (*x + y) % qq;
                }
                for (x, &y) in rv.iter_mut().zip(&rimg[k]) {
                    *x = (*x + y) % qq;
                }
                if coord[k] == q {
                    coord[k] = 0;
                    k += 1;
                } else {
                    break;
                }
            }
        }
        if rv.iter().all(|&x| x == 0) {
            cond[idx / 64] |= 1 << (idx % 64);
        }
        if let Some(sl) = fixed(&dv, &coord, lay, lmax, &mut cls) {
            sols.push(sl);
        }
        for (k, o) in oimg.iter().enumerate() {
            for ((t, &x), &y) in tmp.iter_mut().zip(&dv).zip(o) {
                *t = (x + y) % qq;
            }
            if fixed(&tmp, &coord, lay, lmax, &mut cls).is_some() {
                near[k] += 1;
            }
        }
    }
    sols.sort();
    FrobBase { sols, near, noff: offs.len(), cond, roots: roots_of_bm1(b, qq), irred: irreducible(b, qq) }
}

/// if the digit vector dv (at least 2 digits) has class sums coord, its digits
fn fixed(dv: &[u8], coord: &[usize], lay: &Layout, lmax: usize, cls: &mut [u8]) -> Option<String> {
    let e = lay.e;
    let q = lay.q;
    let qq = q as u8;
    let mut len = 0;
    for i in (0..lmax).rev() {
        if dv[i * e..i * e + e].iter().any(|&c| c != 0) {
            len = i + 1;
            break;
        }
    }
    if len < lay.minlen {
        return None;
    }
    cls.iter_mut().for_each(|x| *x = 0);
    let mut z = 0usize;
    for i in 0..len {
        let d = &dv[i * e..i * e + e];
        match d.iter().rposition(|&c| c != 0) {
            None => z += 1,
            Some(j) => {
                for t in 0..=j {
                    cls[j * e + t] = (cls[j * e + t] + d[t]) % qq;
                }
            }
        }
    }
    for (k, &(j, t)) in lay.coord_jt.iter().enumerate() {
        let v = if j == e { z % q } else { cls[j * e + t] as usize };
        if v != coord[k] {
            return None;
        }
    }
    let s: Vec<String> = (0..len).rev().map(|i| code(&dv[i * e..i * e + e], qq).to_string()).collect();
    Some(s.join(","))
}

/// lengths of F over G (independent of B), and the model values v[idx] = P_L(idx)
fn frob_model(lay: &Layout, lmax: usize) -> (Vec<u8>, Vec<f64>) {
    let q = lay.q;
    let e = lay.e;
    // deg F(D, z): the monomials T^(t q^j) of distinct coordinates can coincide
    // (t q^j = t' q^j'), so the coefficients are summed per degree
    let mut lens = vec![0u8; lay.n];
    let mut coord = vec![0usize; lay.ncoord];
    let cdeg: Vec<usize> = lay.coord_jt.iter().map(|&(j, t)| if j == e { 0 } else { t * q.pow(j as u32) }).collect();
    let maxdeg = *cdeg.iter().max().unwrap();
    let mut coef = vec![0usize; maxdeg + 1];
    for idx in 0..lay.n {
        let mut x = idx;
        for k in 0..lay.ncoord {
            coord[k] = x % q;
            x /= q;
        }
        coef.iter_mut().for_each(|c| *c = 0);
        for k in 0..lay.ncoord {
            coef[cdeg[k]] += coord[k];
        }
        let dg = (0..=maxdeg).rev().find(|&g| coef[g] % q != 0);
        lens[idx] = match dg {
            None => 0,
            Some(g) => (g / e + 1) as u8,
        };
    }
    // digit -> group element: block j gets the coefficients, the z block gets 1
    let nd = q.pow(e as u32);
    let mut stride = vec![1usize; lay.ncoord + 1];
    for k in 0..lay.ncoord {
        stride[k + 1] = stride[k] * q;
    }
    let elem = |c: usize| -> Vec<usize> {
        let mut v = vec![0usize; lay.ncoord];
        if c == 0 {
            if lay.m == 1 {
                v[lay.ncoord - 1] = 1;
            }
        } else {
            let d = decode(c, q as u8, e);
            let j = d.len() - 1;
            for t in 0..=j {
                v[lay.ci(j, t)] = d[t] as usize;
            }
        }
        v
    };
    let elems: Vec<Vec<usize>> = (0..nd).map(elem).collect();
    let shift = |idx: usize, g: &[usize], sign: bool| -> usize {
        let mut out = 0;
        let mut x = idx;
        for k in 0..lay.ncoord {
            let c = x % q;
            x /= q;
            let v = if sign { (c + g[k]) % q } else { (c + q - g[k]) % q };
            out += v * stride[k];
        }
        out
    };
    let mut p = vec![0f64; lay.n];
    for c in 1..nd {
        p[shift(0, &elems[c], true)] += 1.0 / (nd - 1) as f64;
    }
    let mut vals = vec![0f64; lay.n];
    for l in 1..=lmax {
        if l > 1 {
            let np: Vec<f64> = (0..lay.n)
                .into_par_iter()
                .map(|idx| {
                    let mut s = 0.0;
                    for g in &elems {
                        s += p[shift(idx, g, false)];
                    }
                    s / nd as f64
                })
                .collect();
            p = np;
        }
        for idx in 0..lay.n {
            if lens[idx] as usize == l {
                vals[idx] = p[idx];
            }
        }
    }
    (lens, vals)
}

fn run_frob(q: usize, e: usize, m: usize, spec: &str, offdeg: usize, minlen: usize) {
    let mut lay = Layout::new(q, e, m);
    lay.minlen = minlen;
    let maxdeg = (e - 1) * q.pow(e as u32 - 1);
    let lmax = maxdeg / e + 1;
    println!("# frob q {q} e {e} m {m}: |G| = {}, max deg F = {maxdeg}, max length {lmax}, min length {minlen}, offsets of degree < {offdeg}", lay.n);
    let t0 = Instant::now();
    let (lens, vals) = frob_model(&lay, lmax);
    let basic: f64 = (0..lay.n).filter(|&i| lens[i] as usize >= minlen).map(|i| vals[i]).sum();
    println!("# model computed in {:.1} s: basic {basic:.6}", t0.elapsed().as_secs_f64());
    let bs = bases(q as u8, e, spec);
    let res: Vec<(P, FrobBase)> = bs.par_iter().map(|b| (b.clone(), frob_base(&lay, b, lmax, offdeg))).collect();
    let qe = q.pow(e as u32) as f64;
    for (b, fb) in &res {
        let refined: f64 = (0..lay.n).filter(|&i| lens[i] as usize >= minlen && fb.cond[i / 64] >> (i % 64) & 1 == 1).map(|i| vals[i]).sum::<f64>() * qe;
        println!(
            "base {} code {} irred {} roots {} sols {} basic {:.4} refined {:.4}",
            fmt_poly(b),
            code(b, q as u8),
            fb.irred as u8,
            fb.roots,
            fb.sols.len(),
            basic,
            refined
        );
        if fb.noff > 0 {
            let v: Vec<String> = fb.near.iter().map(|x| x.to_string()).collect();
            println!("near base {} m {m} offsets {} total {} counts {}", code(b, q as u8), fb.noff, fb.near.iter().sum::<u64>(), v.join(","));
        }
        for s in &fb.sols {
            println!("sol base {} m {m} digits {s}", code(b, q as u8));
        }
    }
    println!("# total {:.1} s", t0.elapsed().as_secs_f64());
}

// ------------------------------------------------------------------ brute

fn run_brute(q: usize, e: usize, m: usize, wmode: &str, spec: &str, lmax_opt: Option<usize>) {
    let qq = q as u8;
    let nd = q.pow(e as u32);
    let w: Vec<P> = (0..nd)
        .map(|c| {
            if c == 0 {
                return if m == 0 { vec![] } else { vec![1] };
            }
            let d = decode(c, qq, e);
            let j = deg(&d) as u32;
            let k = match wmode {
                "frob" => (q as u64).pow(j),
                "deg" => j as u64,
                _ => panic!("unknown weights"),
            };
            powp(&d, k, qq)
        })
        .collect();
    let maxdeg = w.iter().map(deg).max().unwrap().max(0) as usize;
    let lmax = lmax_opt.unwrap_or(maxdeg / e + 1);
    println!("# brute q {q} e {e} m {m} weights {wmode}: max deg F = {maxdeg}, lengths 2..{lmax}");
    let bs = bases(qq, e, spec);
    for b in &bs {
        let bm1 = add(b, &vec![qq - 1], qq);
        let mut sols: Vec<String> = vec![];
        let (mut basic, mut refined) = (0f64, 0f64);
        for l in 2..=lmax {
            let mut lf = vec![0f64; l + 1];
            for k in 1..=l {
                lf[k] = lf[k - 1] + (k as f64).ln();
            }
            let p0 = (lf[l] - ((nd - 1) as f64).ln() - (l as f64 - 1.0) * (nd as f64).ln()).exp();
            let mut c = vec![0usize; nd];
            rec(&w, b, &bm1, qq, e, l, nd - 1, l, &vec![], &vec![], p0, &lf, &mut c, &mut sols, &mut basic, &mut refined);
        }
        sols.sort();
        println!(
            "base {} code {} irred {} roots {} sols {} basic {:.4} refined {:.4}",
            fmt_poly(b),
            code(b, qq),
            irreducible(b, qq) as u8,
            roots_of_bm1(b, qq),
            sols.len(),
            basic,
            refined * nd as f64
        );
        for s in &sols {
            println!("sol base {} m {m} digits {s}", code(b, qq));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn rec(w: &[P], b: &P, bm1: &P, q: u8, e: usize, l: usize, x: usize, r: usize, f: &P, s: &P, p: f64, lf: &[f64], c: &mut [usize], sols: &mut Vec<String>, basic: &mut f64, refined: &mut f64) {
    if x == 0 {
        c[0] = r;
        let f2 = add(f, &scale(&w[0], (r % q as usize) as u8, q), q);
        let pc = p * (-lf[r]).exp() * (l - r) as f64 / l as f64;
        let dg = deg(&f2);
        if dg >= (e * (l - 1)) as isize && dg < (e * l) as isize {
            *basic += pc;
            let id = rem(&add(&f2, &scale(s, q - 1, q), q), bm1, q);
            if id.is_empty() {
                *refined += pc;
                let ds = digits(&f2, b, q, e);
                let mut h = vec![0usize; c.len()];
                for d in &ds {
                    h[code(d, q)] += 1;
                }
                if h[..] == c[..] {
                    let st: Vec<String> = ds.iter().rev().map(|d| code(d, q).to_string()).collect();
                    sols.push(st.join(","));
                }
            }
        }
        c[0] = 0;
        return;
    }
    let dx = decode(x, q, e);
    for k in 0..=r {
        c[x] = k;
        let kk = (k % q as usize) as u8;
        let f2 = add(f, &scale(&w[x], kk, q), q);
        let s2 = add(s, &scale(&dx, kk, q), q);
        rec(w, b, bm1, q, e, l, x - 1, r - k, &f2, &s2, p * (-lf[k]).exp(), lf, c, sols, basic, refined);
    }
    c[x] = 0;
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    match a[1].as_str() {
        "frob" => {
            let mut offdeg = 0;
            let mut minlen = 2;
            let mut i = 6;
            while i + 1 < a.len() {
                match a[i].as_str() {
                    "--offdeg" => offdeg = a[i + 1].parse().unwrap(),
                    "--minlen" => minlen = a[i + 1].parse().unwrap(),
                    o => panic!("unknown option {o}"),
                }
                i += 2;
            }
            run_frob(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), &a[5], offdeg, minlen)
        }
        "brute" => {
            let lmax = if a.len() > 8 && a[7] == "--lmax" { Some(a[8].parse().unwrap()) } else { None };
            run_brute(a[2].parse().unwrap(), a[3].parse().unwrap(), a[4].parse().unwrap(), &a[5], &a[6], lmax)
        }
        _ => panic!("unknown mode"),
    }
}
