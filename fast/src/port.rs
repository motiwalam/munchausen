// A faithful port of the python search in src/munchausen.py + src/common.py.
// It enumerates exactly the same digit combinations (gcwr + testbd0) so that
// it serves as a like-for-like baseline for the language change alone.
use rayon::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering};

// smallest x >= 1 with x^x >= num/den (python's fm, computed exactly)
fn fm(num: u128, den: u128) -> u32 {
    let mut x = 1u32;
    while den * (x as u128).pow(x) < num {
        x += 1;
    }
    x
}

fn digits_be(mut n: u128, b: u32) -> Vec<u32> {
    let mut v = vec![];
    while n > 0 {
        v.push((n % b as u128) as u32);
        n /= b as u128;
    }
    v.reverse();
    v
}

// testbd0: length of the "next number with all digits < mx" after n*r^r must be d
fn testbd0(b: u32, d: u32, mx: u32, r: u32, n: u32) -> bool {
    let mut vc = vec![0u32];
    vc.extend(digits_be(n as u128 * (r as u128).pow(r), b));
    for i in (1..vc.len()).rev() {
        if vc[i] >= mx {
            vc[i] = 0;
            vc[i - 1] += 1;
        }
    }
    let len = vc.len() - (vc[0] == 0) as usize;
    len == d as usize
}

struct Task {
    d: u32,
    mx: u32,
    r: u32,
    n: u32,
    first: u32,
}

// enumerate non-decreasing sequences of `left` digits from [lo, mx)
fn cwr(t: &Task, w: &[u128], b: u32, lo: u32, left: u32, s: u128, hist: &mut [u32; 64], found: &mut Vec<u128>, count: &mut u64) {
    if left == 0 {
        *count += 1;
        let mut h = [0u32; 64];
        let mut x = s;
        let mut len = 0;
        while x > 0 {
            h[(x % b as u128) as usize] += 1;
            x /= b as u128;
            len += 1;
        }
        if len == t.d && h[..b as usize] == hist[..b as usize] {
            found.push(s);
        }
        return;
    }
    for x in lo..t.mx {
        hist[x as usize] += 1;
        cwr(t, w, b, x, left - 1, s + w[x as usize], hist, found, count);
        hist[x as usize] -= 1;
    }
}

pub fn search(b: u32, mode: u32) -> (Vec<u128>, u64) {
    let w: Vec<u128> = (0..b).map(|k| if k == 0 { mode as u128 } else { (k as u128).pow(k) }).collect();
    let bb = b as u128;
    let mut tasks = vec![];
    for d in 2..=b {
        let t = fm(bb.pow(d - 1), d as u128);
        let mx = fm(bb.pow(d), 1);
        for r in t..mx {
            let n = if b == 2 { 0 } else { bb.pow(d - 1).div_ceil((r as u128).pow(r)) as u32 };
            if n <= d && testbd0(b, d, mx, r, n) {
                if n == d {
                    tasks.push(Task { d, mx, r, n, first: u32::MAX });
                } else {
                    for first in 0..mx {
                        tasks.push(Task { d, mx, r, n, first });
                    }
                }
            }
        }
    }
    let total = AtomicU64::new(0);
    let mut found: Vec<u128> = tasks
        .par_iter()
        .flat_map_iter(|t| {
            let mut hist = [0u32; 64];
            hist[t.r as usize] += t.n;
            let mut s = t.n as u128 * w[t.r as usize];
            let mut out = vec![];
            let mut count = 0;
            if t.first == u32::MAX {
                cwr(t, &w, b, 0, 0, s, &mut hist, &mut out, &mut count);
            } else {
                hist[t.first as usize] += 1;
                s += w[t.first as usize];
                cwr(t, &w, b, t.first, t.d - t.n - 1, s, &mut hist, &mut out, &mut count);
            }
            total.fetch_add(count, Ordering::Relaxed);
            out
        })
        .collect();
    // d = 1: python hard-codes these
    found.push(1);
    if mode == 0 {
        found.push(0);
    }
    found.sort();
    (found, total.into_inner())
}
