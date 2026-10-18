//! Every k-digit Munchausen number in every base, for digits up to M.
//!
//! A digit string s is a solution in base b exactly when b > max(s) is a
//! root of Q(r) = sum s_i r^i - F(s). If Q has no root modulo some integer q,
//! no base works. The program enumerates strings with digits up to M,
//! discards those that fail this test for one of a list of moduli, and finds
//! the integer root of the few that remain with exact arithmetic.
//!
//! The test is cheap because Q mod q splits over positions: for a fixed
//! prefix, the values of the prefix part over all residues r form a bit
//! mask, and the last digit x passes if w(x) - x (minus the zero count under
//! 0^0 = 0) is in the mask. The tables hold w(x) mod q for every digit up to
//! M, so any modulus up to 128 works, prime or not.
//!
//! Prefix values are kept for all moduli down to the digit of exponent 1. The
//! mask of each modulus for the last digit is built only while some last
//! digit is still alive, in the order of the list, so later moduli are cheap.
//!
//! A k-digit solution in base b only uses digits x with x^x < b^k, so the
//! output is complete for every base b with b^k <= (M+1)^(M+1). With an
//! offset D >= 0 the same bound holds for the strings with P_s(b) = F(s) + D.
//!
//! usage: kdigit <k> <M> [--survivors] [--offset D] [--moduli q1,q2,...] [--stats]
//! prints "k mode base digits" lines, like analysis/kdigit.py. With
//! --survivors it prints "k mode digits" for every string that passes the
//! test instead, for other uses of the polynomial (negative roots, say).
//! --offset D finds the strings with P_s(b) - F(s) = D in place of 0.
//! --moduli replaces the default list of moduli (each from 2 to 128), and
//! --stats prints how many candidates each modulus removes, in order.

use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};
use rayon::prelude::*;
use std::sync::Mutex;

// 32, 27, 25 and 49 in place of 2, 3, 5 and 7 cut the survivors by 2x, and the
// primes from 67 on by 70x more; masks late in the list are rarely built, so
// they cost little.
const DEFAULT_MODULI: [u64; 31] = [
    32, 27, 25, 49, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127,
];

struct Tables {
    k: usize,
    m: usize,
    qs: Vec<u64>,
    off: Vec<usize>, // start of each modulus in a concatenated residue array
    len: usize,      // sum of the moduli
    qlane: Vec<u8>,  // modulus of each lane of the concatenated array
    // c[(e * (m+1) + x) * len + off[qi] + r] = x r^e - w(x) mod q
    c: Vec<u8>,
    // need[qi * (m+1) + x] = w(x) - x + D mod q, with 0^0 = 1
    need: Vec<u8>,
    // zmod[qi * (k+1) + z] = z mod q
    zmod: Vec<u8>,
    w: Vec<BigUint>, // x^x, with 0^0 = 1
    offset: BigInt,
}

fn pow_mod(mut a: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1 % p;
    a %= p;
    while e > 0 {
        if e & 1 == 1 {
            r = r * a % p;
        }
        a = a * a % p;
        e >>= 1;
    }
    r
}

impl Tables {
    fn new(k: usize, m: usize, qs: Vec<u64>, offset: i64) -> Self {
        let mut off = vec![];
        let mut len = 0;
        for &q in &qs {
            off.push(len);
            len += q as usize;
        }
        let qlane: Vec<u8> = qs.iter().flat_map(|&q| std::iter::repeat_n(q as u8, q as usize)).collect();
        let wm = |x: usize, q: u64| if x == 0 { 1 % q } else { pow_mod(x as u64, x as u64, q) };
        let mut c = vec![0u8; k * (m + 1) * len];
        for e in 0..k {
            for x in 0..=m {
                for (qi, &q) in qs.iter().enumerate() {
                    for r in 0..q {
                        let v = ((x as u64 % q) * pow_mod(r, e as u64, q) + q - wm(x, q)) % q;
                        c[(e * (m + 1) + x) * len + off[qi] + r as usize] = v as u8;
                    }
                }
            }
        }
        let mut need = vec![];
        let mut zmod = vec![];
        for &q in &qs {
            let d = offset.rem_euclid(q as i64) as u64;
            for x in 0..=m {
                need.push(((wm(x, q) + q - x as u64 % q + d) % q) as u8);
            }
            for z in 0..=k {
                zmod.push((z as u64 % q) as u8);
            }
        }
        let w = (0..=m).map(|x| if x == 0 { BigUint::one() } else { BigUint::from(x).pow(x as u32) }).collect();
        Tables { k, m, qs, off, len, qlane, c, need, zmod, w, offset: BigInt::from(offset) }
    }

    fn cslice(&self, e: usize, x: usize) -> &[u8] {
        let s = (e * (self.m + 1) + x) * self.len;
        &self.c[s..s + self.len]
    }
}

// dst = src + c, lane by lane modulo the lane's modulus. All values are below
// q <= 128, so the sum fits a byte and min(t, t - q) reduces it.
#[inline]
fn add_mod(dst: &mut [u8], src: &[u8], c: &[u8], q: &[u8]) {
    for (((d, &s), &c), &q) in dst.iter_mut().zip(src).zip(c).zip(q) {
        let t = s.wrapping_add(c);
        *d = t.min(t.wrapping_sub(q));
    }
}

// floor(n^(1/r)) by Newton's method from above
fn iroot(n: &BigUint, r: u32) -> BigUint {
    if r == 1 || *n < BigUint::from(2u32) {
        return n.clone();
    }
    let bits = n.bits();
    let mut x = BigUint::one() << ((bits + r as u64 - 1) / r as u64);
    loop {
        let y = ((&x * (r - 1)) + n / x.pow(r - 1)) / r;
        if y >= x {
            return x;
        }
        x = y;
    }
}

// The base b > max(s) with P_s(b) = f, or None (port of analysis/kdigit.py).
fn base_for(s: &[usize], f: &BigUint) -> Option<BigUint> {
    let k = s.len();
    let lo = BigUint::from(*s.iter().max().unwrap() + 1);
    let mut b = iroot(&(f / s[0]), (k - 1) as u32);
    if b < lo {
        return None;
    }
    loop {
        // v = P_s(b), dv = P_s'(b)
        let (mut v, mut dv) = (BigUint::zero(), BigUint::zero());
        for &c in s {
            dv = &dv * &b + &v;
            v = &v * &b + c;
        }
        if v == *f {
            return Some(b);
        }
        if v < *f {
            return None;
        }
        let step = (&v - f) / &dv;
        let step = if step.is_zero() { BigUint::one() } else { step };
        if step > b || &b - &step < lo {
            return None;
        }
        b -= step;
    }
}

struct Out {
    survivors_only: bool,
    passed: Mutex<Vec<(u32, Vec<usize>)>>,
    found: Mutex<Vec<(u32, BigUint, Vec<usize>)>>,
    // strings, survivors, then per modulus: masks built, candidates tested, removed
    stats: Mutex<Vec<u64>>,
}

struct Local {
    strings: u64,
    survivors: u64,
    per_q: Vec<[u64; 3]>,
    cand: Vec<u32>,
    found: Vec<(u32, BigUint, Vec<usize>)>,
    passed: Vec<(u32, Vec<usize>)>,
}

impl Local {
    fn new(n: usize) -> Self {
        Local { strings: 0, survivors: 0, per_q: vec![[0; 3]; n], cand: vec![], found: vec![], passed: vec![] }
    }

    fn flush(self, out: &Out) {
        let mut st = out.stats.lock().unwrap();
        st[0] += self.strings;
        st[1] += self.survivors;
        for (qi, v) in self.per_q.iter().enumerate() {
            for j in 0..3 {
                st[2 + 3 * qi + j] += v[j];
            }
        }
        drop(st);
        out.found.lock().unwrap().extend(self.found);
        out.passed.lock().unwrap().extend(self.passed);
    }
}

// The last two positions: a holds the prefix part of Q for the digits before
// the digit y of exponent 1; the last digit x has exponent 0.
fn last(t: &Tables, s: &mut Vec<usize>, a: &[u8], y: usize, zeros: usize, out: &Out, loc: &mut Local) {
    let m = t.m;
    let zy = zeros + (y == 0) as usize;
    let cy = t.cslice(1, y);
    let mut cand = std::mem::take(&mut loc.cand);
    cand.clear();
    for x in 0..=m {
        // a candidate is x | mode << 16 | zero count << 17
        let z = zy + (x == 0) as usize;
        cand.push(x as u32 | 1 << 16 | (z as u32) << 17);
        if z > 0 {
            // without zeros, 0^0 = 0 gives the same equation as 0^0 = 1
            cand.push(x as u32 | (z as u32) << 17);
        }
    }
    loc.strings += (m + 1) as u64;
    for (qi, &q) in t.qs.iter().enumerate() {
        if cand.is_empty() {
            break;
        }
        let o = t.off[qi];
        let qb = q as u8;
        let (aq, cq) = (&a[o..o + q as usize], &cy[o..o + q as usize]);
        let mut mask = 0u128;
        if q <= 64 {
            let mut m64 = 0u64;
            for (&av, &cv) in aq.iter().zip(cq) {
                let v = av.wrapping_add(cv);
                m64 |= 1u64 << v.min(v.wrapping_sub(qb));
            }
            mask = m64 as u128;
        } else {
            for (&av, &cv) in aq.iter().zip(cq) {
                let v = av.wrapping_add(cv);
                mask |= 1u128 << v.min(v.wrapping_sub(qb));
            }
        }
        let need = &t.need[qi * (m + 1)..];
        let zmod = &t.zmod[qi * (t.k + 1)..];
        let before = cand.len();
        // keep the candidates whose need is in the mask, without branches
        let mut j = 0;
        for idx in 0..before {
            let cv = cand[idx];
            let x = (cv & 0xffff) as usize;
            let n1 = need[x];
            // under 0^0 = 0, F is smaller by the zero count z: need w - x - z
            let z = zmod[(cv >> 17) as usize] * (1 - (cv >> 16 & 1) as u8);
            let n = n1.wrapping_sub(z);
            let n = n.min(n.wrapping_add(qb));
            cand[j] = cv;
            j += (mask >> n & 1) as usize;
        }
        cand.truncate(j);
        let st = &mut loc.per_q[qi];
        st[0] += 1;
        st[1] += before as u64;
        st[2] += (before - cand.len()) as u64;
    }
    loc.survivors += cand.len() as u64;
    s.push(y);
    for &cv in &cand {
        let x = (cv & 0xffff) as usize;
        let mode = cv >> 16 & 1;
        let z = (cv >> 17) as usize;
        s.push(x);
        if out.survivors_only {
            loc.passed.push((mode, s.clone()));
        } else {
            let mut f: BigUint = s.iter().map(|&v| &t.w[v]).sum();
            if mode == 0 {
                f -= z;
            }
            let fd = BigInt::from(f) + &t.offset;
            if fd.sign() == Sign::Plus {
                if let Some(b) = base_for(s, &fd.to_biguint().unwrap()) {
                    loc.found.push((mode, b, s.clone()));
                }
            }
        }
        s.pop();
    }
    s.pop();
    loc.cand = cand;
}

// Depth-first over positions; a[i] holds the prefix part of Q for s[..i],
// for all moduli side by side.
fn rec(t: &Tables, s: &mut Vec<usize>, a: &mut [Vec<u8>], zeros: usize, out: &Out, loc: &mut Local) {
    let i = s.len();
    let k = t.k;
    let lo = if i == 0 { 1 } else { 0 };
    if i == k - 2 {
        for y in lo..=t.m {
            last(t, s, &a[i], y, zeros, out, loc);
        }
        return;
    }
    let e = k - 1 - i; // exponent of this position
    for x in lo..=t.m {
        let (head, tail) = a.split_at_mut(i + 1);
        add_mod(&mut tail[0], &head[i], t.cslice(e, x), &t.qlane);
        s.push(x);
        rec(t, s, a, zeros + (x == 0) as usize, out, loc);
        s.pop();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let usage = || -> ! {
        eprintln!("usage: kdigit <k> <M> [--survivors] [--offset D] [--moduli q1,q2,...] [--stats]");
        std::process::exit(2);
    };
    if args.len() < 3 {
        usage();
    }
    let k: usize = args[1].parse().expect("k must be a number");
    let m: usize = args[2].parse().expect("M must be a number");
    let (mut survivors_only, mut offset, mut stats) = (false, 0i64, false);
    let mut qs: Vec<u64> = DEFAULT_MODULI.to_vec();
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--survivors" => survivors_only = true,
            "--stats" => stats = true,
            "--offset" => {
                i += 1;
                offset = args.get(i).unwrap_or_else(|| usage()).parse().expect("D must be an integer");
            }
            "--moduli" => {
                i += 1;
                let l = args.get(i).unwrap_or_else(|| usage());
                qs = l.split(',').map(|v| v.parse().expect("moduli must be numbers")).collect();
            }
            _ => usage(),
        }
        i += 1;
    }
    assert!(k >= 2, "k must be at least 2");
    assert!(m < 1 << 16, "M must be below 65536");
    assert!(!qs.is_empty() && qs.iter().all(|&q| (2..=128).contains(&q)), "each modulus must be from 2 to 128");
    let nq = qs.len();
    let t = Tables::new(k, m, qs, offset);
    let out = Out { survivors_only, passed: Mutex::new(vec![]), found: Mutex::new(vec![]), stats: Mutex::new(vec![0; 2 + 3 * nq]) };
    let start = std::time::Instant::now();
    let zero = vec![0u8; t.len];
    if k == 2 {
        (1..=m).into_par_iter().for_each(|y| {
            let mut loc = Local::new(nq);
            last(&t, &mut vec![], &zero, y, 0, &out, &mut loc);
            loc.flush(&out);
        });
    } else {
        // split the work over the first digit, and the second one for k >= 4
        let firsts: Vec<(usize, usize)> = if k == 3 { (1..=m).map(|x| (x, 0)).collect() } else { (1..=m).flat_map(|x| (0..=m).map(move |y| (x, y))).collect() };
        firsts.par_iter().for_each(|&(x, y)| {
            let mut loc = Local::new(nq);
            let mut a = vec![zero.clone(); k - 1];
            let mut s = vec![x];
            add_mod(&mut a[1], &zero, t.cslice(k - 1, x), &t.qlane);
            if k == 3 {
                rec(&t, &mut s, &mut a, 0, &out, &mut loc);
            } else {
                let (head, tail) = a.split_at_mut(2);
                add_mod(&mut tail[0], &head[1], t.cslice(k - 2, y), &t.qlane);
                s.push(y);
                rec(&t, &mut s, &mut a, (y == 0) as usize, &out, &mut loc);
            }
            loc.flush(&out);
        });
    }
    let st = out.stats.into_inner().unwrap();
    let (strings, surv) = (st[0], st[1]);
    if stats {
        eprintln!("# modulus, masks built, candidates tested, removed, share removed");
        for (qi, &q) in t.qs.iter().enumerate() {
            let (mk, te, re) = (st[2 + 3 * qi], st[3 + 3 * qi], st[4 + 3 * qi]);
            eprintln!("# {q} {mk} {te} {re} {:.4}", re as f64 / te.max(1) as f64);
        }
    }
    let qlist: Vec<String> = t.qs.iter().map(|q| q.to_string()).collect();
    let desc = if t.qs[..] == DEFAULT_MODULI[..] { "the default moduli".to_string() } else { format!("moduli {}", qlist.join(",")) };
    let off_desc = if offset != 0 { format!(" offset D={offset};") } else { String::new() };
    if survivors_only {
        let mut v = out.passed.into_inner().unwrap();
        v.sort();
        for (md, s) in v {
            let ds: Vec<String> = s.iter().map(|x| x.to_string()).collect();
            println!("{k} {md} {}", ds.join(","));
        }
        return;
    }
    let mut found = out.found.into_inner().unwrap();
    // a string without zeros solves both conventions
    let mut lines = vec![];
    for (mode, b, s) in found.drain(..) {
        let z = s.iter().filter(|&&v| v == 0).count();
        let modes: Vec<u32> = if mode == 1 && z == 0 { vec![0, 1] } else { vec![mode] };
        for md in modes {
            lines.push((md, b.clone(), s.clone()));
        }
    }
    lines.sort();
    for (md, b, s) in &lines {
        let ds: Vec<String> = s.iter().map(|v| v.to_string()).collect();
        println!("{k} {md} {b} {}", ds.join(","));
    }
    let bound = (m as f64 + 1.0) * (m as f64 + 1.0).log10() / k as f64;
    eprintln!(
        "# k={k} M={m}:{off_desc} {} solutions; {strings} strings, {surv} passed the test with {desc} ({:.2e}); {:.1}s; complete for bases b with b^{k} <= {}^{}, that is b <= about 10^{bound:.1}",
        lines.len(),
        surv as f64 / (2.0 * strings as f64),
        start.elapsed().as_secs_f64(),
        m + 1,
        m + 1
    );
}
