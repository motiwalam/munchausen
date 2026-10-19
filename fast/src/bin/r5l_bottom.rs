// Question 79: exact node counts of the toy count trees of
// analysis/r5l_bottom.py, for bases b = 2^k up to 32 with d = b-1 and
// 0^0 = 1. Same orders, same interval test, same bottom check; numbers are
// 192-bit integers, so a base-b digit is a group of k bits.
//
// Usage: r5l_bottom <b> <order>[,<order>...] [<levels>]
//   orders: plain, plain+bot, hybrid, odd-first; <levels> counts only the top levels
// The count is split over the children of the root with rayon
// (RAYON_NUM_THREADS sets the thread count).

use rayon::prelude::*;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct U192([u64; 3]); // little-endian limbs

impl Ord for U192 {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        (self.0[2], self.0[1], self.0[0]).cmp(&(o.0[2], o.0[1], o.0[0]))
    }
}

impl PartialOrd for U192 {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

impl U192 {
    fn from_u64(x: u64) -> U192 {
        U192([x, 0, 0])
    }
    fn add(self, o: U192) -> U192 {
        let (a0, c0) = self.0[0].overflowing_add(o.0[0]);
        let (a1, c1a) = self.0[1].overflowing_add(o.0[1]);
        let (a1, c1b) = a1.overflowing_add(c0 as u64);
        let a2 = self.0[2].wrapping_add(o.0[2]).wrapping_add((c1a || c1b) as u64);
        U192([a0, a1, a2])
    }
    fn mul_small(self, m: u64) -> U192 {
        let mut out = [0u64; 3];
        let mut carry = 0u128;
        for i in 0..3 {
            let v = self.0[i] as u128 * m as u128 + carry;
            out[i] = v as u64;
            carry = v >> 64;
        }
        assert!(carry == 0, "overflow");
        U192(out)
    }
    fn bits(self, lo: u32, n: u32) -> u64 {
        // n <= 7 bits starting at bit lo
        let mut v = 0u64;
        for j in 0..n {
            let p = lo + j;
            let bit = (self.0[(p / 64) as usize] >> (p % 64)) & 1;
            v |= bit << j;
        }
        v
    }
    fn xor(self, o: U192) -> U192 {
        U192([self.0[0] ^ o.0[0], self.0[1] ^ o.0[1], self.0[2] ^ o.0[2]])
    }
    fn top_bit(self) -> Option<u32> {
        for i in (0..3).rev() {
            if self.0[i] != 0 {
                return Some(i as u32 * 64 + 63 - self.0[i].leading_zeros());
            }
        }
        None
    }
    fn pow2(p: u32) -> U192 {
        let mut o = [0u64; 3];
        o[(p / 64) as usize] = 1 << (p % 64);
        U192(o)
    }
}

struct Toy {
    b: usize,
    k: u32,
    d: u32,
    w: Vec<U192>,
    b0: U192,
    b1: U192,
    vals: Vec<usize>,
    bottom: bool,
    need: Vec<u64>, // need[L]: bitmask of the values that fix the bottom L digits
    max_depth: usize,
}

fn v2(mut x: usize) -> u32 {
    let mut n = 0;
    while x % 2 == 0 {
        x /= 2;
        n += 1;
    }
    n
}

impl Toy {
    fn new(b: usize, bottom: bool) -> Toy {
        let k = b.trailing_zeros();
        assert!(1 << k == b && k * (b as u32) <= 190);
        let d = b as u32 - 1;
        let mut w = vec![U192::from_u64(1)]; // 0^0 = 1
        for v in 1..b {
            let mut x = U192::from_u64(1);
            for _ in 0..v {
                x = x.mul_small(v as u64);
            }
            w.push(x);
        }
        let b0 = U192::pow2(k * (d - 1));
        let b1 = U192::pow2(k * d).add(U192([u64::MAX; 3])); // 2^(kd) - 1
        let vals: Vec<usize> = (0..b).filter(|&v| w[v] <= b1).collect();
        let mut need = vec![0u64; d as usize + 1];
        for l in 1..=d {
            for &v in &vals {
                if !(v > 0 && v % 2 == 0 && v as u32 * v2(v) >= k * l) {
                    need[l as usize] |= 1 << v;
                }
            }
        }
        let max_depth = std::env::args().nth(3).map_or(usize::MAX, |x| x.parse().unwrap());
        Toy { b, k, d, w, b0, b1, vals, bottom, need, max_depth }
    }

    fn digit(&self, x: U192, i: u32) -> usize {
        x.bits(i * self.k, self.k) as usize
    }

    // cnt[v] for revealed v (mask bit set); t = sum of revealed weights
    fn ok(&self, cnt: &[u32; 64], mask: u64, t: U192, rf: i64) -> bool {
        if rf < 0 {
            return false;
        }
        let rf = rf as u64;
        let u: Vec<usize> = self.vals.iter().copied().filter(|&v| mask >> v & 1 == 0).collect();
        let d = self.d;
        if rf == 0 || u.len() <= 1 {
            let mut c = *cnt;
            let mut s = t;
            if rf > 0 {
                if u.is_empty() {
                    return false;
                }
                c[u[0]] += rf as u32;
                s = s.add(self.w[u[0]].mul_small(rf));
            }
            if s < self.b0 || s > self.b1 {
                return false;
            }
            let mut h = [0u32; 64];
            for i in 0..d {
                h[self.digit(s, i)] += 1;
            }
            for v in 0..self.b {
                let cv = if mask >> v & 1 == 1 || (rf > 0 && v == u[0]) { c[v] } else { 0 };
                if h[v] != cv {
                    return false;
                }
            }
            return true;
        }
        let wmin = u.iter().map(|&v| self.w[v]).min().unwrap();
        let wmax = u.iter().map(|&v| self.w[v]).max().unwrap();
        let mut lo = t.add(wmin.mul_small(rf));
        let mut hi = t.add(wmax.mul_small(rf));
        if lo < self.b0 {
            lo = self.b0;
        }
        if hi > self.b1 {
            hi = self.b1;
        }
        if lo > hi {
            return false;
        }
        let mut known = [u8::MAX; 64]; // digit at position i, or MAX
        let first_diff = match lo.xor(hi).top_bit() {
            None => 0,
            Some(p) => p / self.k + 1,
        };
        for i in first_diff..d {
            known[i as usize] = self.digit(lo, i) as u8;
        }
        if self.bottom {
            let mut l = 0usize;
            while l < d as usize && self.need[l + 1] & !mask == 0 {
                l += 1;
            }
            for i in 0..l {
                let x = self.digit(t, i as u32) as u8;
                if known[i] != u8::MAX && known[i] != x {
                    return false;
                }
                known[i] = x;
            }
        }
        let mut h = [0u32; 64];
        for i in 0..d as usize {
            if known[i] != u8::MAX {
                h[known[i] as usize] += 1;
            }
        }
        let mut out = 0u64;
        for v in 0..self.b {
            if h[v] == 0 {
                continue;
            }
            if mask >> v & 1 == 1 {
                if h[v] > cnt[v] {
                    return false;
                }
            } else {
                out += h[v] as u64;
            }
        }
        out <= rf
    }

    fn count(&self, order: &[usize], i: usize, cnt: &mut [u32; 64], mask: u64, t: U192, rf: i64) -> u64 {
        let v = order[i];
        let mut n = 0;
        let mut te = t;
        for e in 0..=rf {
            cnt[v] = e as u32;
            if self.ok(cnt, mask | 1 << v, te, rf - e) {
                n += 1;
                if i + 1 < order.len().min(self.max_depth) {
                    n += self.count(order, i + 1, cnt, mask | 1 << v, te, rf - e);
                }
            }
            te = te.add(self.w[v]);
        }
        cnt[v] = 0;
        n
    }

    fn order(&self, name: &str) -> Vec<usize> {
        let b = self.b;
        let top: Vec<usize> = self.vals.iter().rev().copied().collect();
        let mut unlock: Vec<usize> = self.vals.iter().copied().filter(|&v| v > 0 && v % 2 == 0).collect();
        unlock.sort_by_key(|&v| (v as u32 * v2(v), std::cmp::Reverse(v)));
        let has0 = self.vals.contains(&0);
        match name {
            "plain" | "plain+bot" => top,
            "odd-first" => {
                let mut o: Vec<usize> = top.iter().copied().filter(|v| v % 2 == 1).collect();
                if has0 {
                    o.push(0);
                }
                o.extend(unlock);
                o
            }
            "hybrid" => {
                let mut o: Vec<usize> = top.iter().copied().filter(|&v| v >= b / 2).collect();
                o.extend(top.iter().copied().filter(|&v| v < b / 2 && v % 2 == 1));
                if has0 {
                    o.push(0);
                }
                o.extend(unlock.iter().copied().filter(|&v| v < b / 2));
                o
            }
            _ => panic!("unknown order {name}"),
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let b: usize = args[1].parse().unwrap();
    for name in args[2].split(',') {
        let toy = Toy::new(b, name != "plain");
        let order = toy.order(name);
        let t0 = std::time::Instant::now();
        // split over the children of the root and of its first child level
        let v = order[0];
        let d = toy.d as i64;
        let firsts: Vec<i64> = (0..=d).collect();
        let n: u64 = 1 + firsts
            .par_iter()
            .map(|&e| {
                let mut cnt = [0u32; 64];
                cnt[v] = e as u32;
                let t = toy.w[v].mul_small(e as u64);
                if !toy.ok(&cnt, 1 << v, t, d - e) {
                    return 0;
                }
                1 + if order.len().min(toy.max_depth) > 1 { toy.count(&order, 1, &mut cnt, 1 << v, t, d - e) } else { 0 }
            })
            .sum::<u64>();
        println!("{name}: {n} nodes ({:.1} s)", t0.elapsed().as_secs_f64());
    }
}
