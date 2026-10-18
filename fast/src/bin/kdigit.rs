//! Every k-digit Munchausen number in every base, for digits up to M.
//!
//! A digit string s is a solution in base b exactly when b > max(s) is a
//! root of Q(r) = sum s_i r^i - F(s). If Q has no root modulo some prime p,
//! no base works. The program enumerates strings with digits up to M,
//! discards those that fail this test for one of a list of primes, and finds
//! the integer root of the few that remain with exact arithmetic.
//!
//! The test is cheap because Q mod p splits over positions: for a fixed
//! prefix, the values of the prefix part over all residues r form a bit
//! mask, and the last digit x passes if w(x) - x (minus the zero count under
//! 0^0 = 0) is in the mask.
//!
//! A k-digit solution in base b only uses digits x with x^x < b^k, so the
//! output is complete for every base b with b^k <= (M+1)^(M+1).
//!
//! usage: kdigit <k> <M> [--survivors]
//! prints "k mode base digits" lines, like analysis/kdigit.py. With
//! --survivors it prints "k mode digits" for every string that passes the
//! test instead, for other uses of the polynomial (negative roots, say).

use num_bigint::BigUint;
use num_traits::{One, Zero};
use rayon::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

const PRIMES: [u64; 18] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61];

struct Tables {
    k: usize,
    m: usize,
    // wm[pi][x] = x^x mod p, with 0^0 taken as 1
    wm: Vec<Vec<u64>>,
    // pw[pi][e][r] = r^e mod p
    pw: Vec<Vec<Vec<u64>>>,
    w: Vec<BigUint>, // x^x, with 0^0 = 1
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
    fn new(k: usize, m: usize) -> Self {
        let wm = PRIMES.iter().map(|&p| (0..=m).map(|x| if x == 0 { 1 % p } else { pow_mod(x as u64, x as u64, p) }).collect()).collect();
        let pw = PRIMES.iter().map(|&p| (0..k).map(|e| (0..p).map(|r| pow_mod(r, e as u64, p)).collect()).collect()).collect();
        let w = (0..=m).map(|x| if x == 0 { BigUint::one() } else { BigUint::from(x).pow(x as u32) }).collect();
        Tables { k, m, wm, pw, w }
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
    survivors: AtomicU64,
    strings: AtomicU64,
}

// Depth-first over positions 0..k-2; a[pi][r] holds the prefix part of Q mod p.
fn rec(t: &Tables, s: &mut Vec<usize>, a: &mut Vec<Vec<Vec<u64>>>, zeros: usize, out: &Out) {
    let i = s.len();
    let k = t.k;
    if i == k - 1 {
        // bit masks of the prefix values over all residues r
        let masks: Vec<u64> = (0..PRIMES.len()).map(|pi| a[i][pi].iter().fold(0u64, |acc, &v| acc | (1 << v))).collect();
        let mut local = 0u64;
        for x in 0..=t.m {
            let z = zeros + (x == 0) as usize;
            for mode in [1u32, 0] {
                if mode == 0 && z == 0 {
                    continue; // same equation as 0^0 = 1
                }
                let pass = PRIMES.iter().enumerate().all(|(pi, &p)| {
                    // need A(r) + x - w(x) + (1 - mode) z == 0 mod p for some r
                    let mut need = (t.wm[pi][x] + p - (x as u64 % p)) % p;
                    if mode == 0 {
                        need = (need + p - (z as u64 % p)) % p;
                    }
                    masks[pi] >> need & 1 == 1
                });
                if !pass {
                    continue;
                }
                local += 1;
                s.push(x);
                if out.survivors_only {
                    out.passed.lock().unwrap().push((mode, s.clone()));
                    s.pop();
                    continue;
                }
                let mut f: BigUint = s.iter().map(|&v| &t.w[v]).sum();
                if mode == 0 {
                    f -= z;
                }
                if let Some(b) = base_for(s, &f) {
                    out.found.lock().unwrap().push((mode, b, s.clone()));
                }
                s.pop();
            }
        }
        out.survivors.fetch_add(local, Ordering::Relaxed);
        out.strings.fetch_add((t.m + 1) as u64, Ordering::Relaxed);
        return;
    }
    let e = k - 1 - i; // exponent of this position
    for x in (if i == 0 { 1 } else { 0 })..=t.m {
        for (pi, &p) in PRIMES.iter().enumerate() {
            let wx = t.wm[pi][x];
            for r in 0..p as usize {
                let prev = a[i][pi][r];
                a[i + 1][pi][r] = (prev + (x as u64 % p) * t.pw[pi][e][r] + p - wx) % p;
            }
        }
        s.push(x);
        rec(t, s, a, zeros + (x == 0) as usize, out);
        s.pop();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let survivors_only = args.len() == 4 && args[3] == "--survivors";
    if args.len() != 3 && !survivors_only {
        eprintln!("usage: kdigit <k> <M> [--survivors]");
        std::process::exit(2);
    }
    let k: usize = args[1].parse().expect("k must be a number");
    let m: usize = args[2].parse().expect("M must be a number");
    assert!(k >= 2, "k must be at least 2");
    let t = Tables::new(k, m);
    let out = Out { survivors_only, passed: Mutex::new(vec![]), found: Mutex::new(vec![]), survivors: AtomicU64::new(0), strings: AtomicU64::new(0) };
    let start = std::time::Instant::now();
    // split the work over the first two digits
    let firsts: Vec<(usize, usize)> = (1..=m).flat_map(|x| (0..=m).map(move |y| (x, y))).collect();
    firsts.par_iter().for_each(|&(x, y)| {
        let zero = PRIMES.iter().map(|&p| vec![0u64; p as usize]).collect::<Vec<_>>();
        let mut a = vec![zero; k];
        let mut s = vec![];
        // position 0 (exponent k-1)
        for (pi, &p) in PRIMES.iter().enumerate() {
            for r in 0..p as usize {
                a[1][pi][r] = ((x as u64 % p) * t.pw[pi][k - 1][r] + p - t.wm[pi][x]) % p;
            }
        }
        s.push(x);
        if k == 2 {
            if y == 0 {
                // the last digit is the only one left; rec handles it at depth 1
                rec(&t, &mut s, &mut a, 0, &out);
            }
            return;
        }
        for (pi, &p) in PRIMES.iter().enumerate() {
            let wy = t.wm[pi][y];
            for r in 0..p as usize {
                a[2][pi][r] = (a[1][pi][r] + (y as u64 % p) * t.pw[pi][k - 2][r] + p - wy) % p;
            }
        }
        s.push(y);
        rec(&t, &mut s, &mut a, (y == 0) as usize, &out);
    });
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
    let strings = out.strings.load(Ordering::Relaxed);
    let surv = out.survivors.load(Ordering::Relaxed);
    let bound = (m as f64 + 1.0) * (m as f64 + 1.0).log10() / k as f64;
    eprintln!(
        "# k={k} M={m}: {} solutions; {strings} strings, {surv} passed the test mod primes <= 61 ({:.2e}); {:.1}s; complete for bases b with b^{k} <= {}^{}, that is b <= about 10^{bound:.1}",
        lines.len(),
        surv as f64 / (2.0 * strings as f64),
        start.elapsed().as_secs_f64(),
        m + 1,
        m + 1
    );
}
