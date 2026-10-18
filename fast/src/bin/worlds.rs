//! Munchausen-type fixed points n = F(n) + offset in a positive base b or a
//! negative base -b, with digits 0..b-1 and a choice of weights:
//!   pow0, pow1   w(x) = x^x, with w(0) = 0 or 1
//!   powt:T:M     w(x) = x^(x+T), with w(0) = M
//!   fact         w(x) = x!  (factorions)
//!
//! Two engines:
//!   brute  enumerates every digit multiset whose sum can have d digits. It
//!          prunes only by the range of the partial sum, filters by the
//!          digit-sum identity mod (b - sigma), and checks the rest exactly.
//!          It also sums the probabilistic model of chapter 5 exactly: for
//!          each length d, the chance that a random d-digit string has a sum
//!          with d digits (basic), the same with the identity (refined), and
//!          the refined part from multisets without zeros.
//!   tree   decides the digit counts from the largest digit down. In base
//!          sigma*b the integers with a fixed top part form an interval, so
//!          the common top digits of the range [lo, hi] of the sum must
//!          belong to the multiset, as in fast/src/search.rs.
//!
//! In base -b the integers with at most j digits are exactly the interval
//! [-negmin_j, max_j] of b^j integers. So n and n' share their digits at
//! positions >= j exactly when floor((n + negmin_j) / b^j) agrees.
//!
//! usage: worlds <brute|tree> <base> <weights> [--offset K] [--offset-per-digit K]
//!        [--dmin D] [--dmax D]
//! base is signed: -12 means base -12. The offset is K + K' (d - 1), which
//! covers the imaginary bases ci under 0^0 = 1 (K' = 1, base -c^2).
//! Arithmetic is u128; the program stops if a value does not fit.

#[allow(dead_code)]
#[path = "../digits.rs"]
mod digits;

use rayon::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

const MAXB: usize = 64;

struct Cfg {
    b: u64,
    neg: bool,
    d: usize,
    w: Vec<u128>,
    wmin: Vec<u128>, // wmin[k] = min of w[0..k]
    wmax: Vec<u128>, // wmax[k] = max of w[0..k]
    pw: Vec<u128>,   // b^j
    negmin: Vec<u128>,
    wl: u128, // window of values with exactly d digits, clipped to reachable sums
    wu: u128,
    kmax: usize,
    off: u128,
    modulus: u64,
    wres: Vec<u64>, // (w[x] - x) mod modulus
    offres: u64,
}

fn signed_digits(n: u128, b: u64, neg: bool) -> Vec<u8> {
    let mut out = vec![];
    if !neg {
        let mut x = n;
        while x > 0 {
            out.push((x % b as u128) as u8);
            x /= b as u128;
        }
    } else {
        let mut x = n as i128;
        let bb = b as i128;
        while x != 0 {
            let r = x.rem_euclid(bb);
            out.push(r as u8);
            x = -((x - r) / bb);
        }
    }
    out
}

fn weights(spec: &str, b: u64) -> Vec<u128> {
    let mut w = vec![0u128; b as usize];
    let parts: Vec<&str> = spec.split(':').collect();
    for x in 0..b as usize {
        w[x] = match parts[0] {
            "pow0" | "pow1" | "powt" => {
                let (t, m) = match parts[0] {
                    "pow0" => (0i64, 0u128),
                    "pow1" => (0, 1),
                    _ => (parts[1].parse().unwrap(), parts[2].parse().unwrap()),
                };
                if x == 0 {
                    m
                } else {
                    let e = x as i64 + t;
                    assert!(e >= 0);
                    let mut v: u128 = 1;
                    for _ in 0..e {
                        v = v.checked_mul(x as u128).expect("weight does not fit in u128");
                    }
                    v
                }
            }
            "fact" => {
                let mut v: u128 = 1;
                for i in 2..=x as u128 {
                    v = v.checked_mul(i).expect("weight does not fit in u128");
                }
                v
            }
            _ => panic!("unknown weights {spec}"),
        };
    }
    w
}

impl Cfg {
    fn new(b: u64, neg: bool, d: usize, w: &[u128], off: u128) -> Option<Cfg> {
        let bb = b as u128;
        if neg && d % 2 == 0 {
            return None; // Proposition 12.2: these are negative
        }
        let mut pw = vec![1u128];
        for j in 0..d {
            pw.push(pw[j].checked_mul(bb).expect("b^d does not fit in u128"));
        }
        // max_j and negmin_j for j = 0..=d
        let mut maxv = vec![0u128; d + 1];
        let mut negmin = vec![0u128; d + 1];
        for j in 1..=d {
            let term = (bb - 1) * pw[j - 1];
            maxv[j] = maxv[j - 1];
            negmin[j] = negmin[j - 1];
            if !neg || (j - 1) % 2 == 0 {
                maxv[j] += term;
            } else {
                negmin[j] += term;
            }
        }
        let wl = maxv[d - 1] + 1;
        let top = w.iter().copied().max().unwrap().checked_mul(d as u128).and_then(|v| v.checked_add(off)).expect("sum does not fit in u128");
        let wu = maxv[d].min(top);
        if wl > wu {
            return None;
        }
        let kmax = (0..b as usize).filter(|&x| w[x] + off <= wu).max().unwrap_or(0);
        let mut wmin = vec![u128::MAX; b as usize + 1];
        let mut wmax = vec![0u128; b as usize + 1];
        for k in 1..=b as usize {
            wmin[k] = wmin[k - 1].min(w[k - 1]);
            wmax[k] = wmax[k - 1].max(w[k - 1]);
        }
        let modulus = if neg { b + 1 } else { b - 1 }.max(1);
        let wres = (0..b as usize).map(|x| ((w[x] % modulus as u128) as u64 + modulus - x as u64 % modulus) % modulus).collect();
        let offres = (off % modulus as u128) as u64;
        Some(Cfg { b, neg, d, w: w.to_vec(), wmin, wmax, pw, negmin, wl, wu, kmax, off, modulus, wres, offres })
    }

    #[inline]
    fn block(&self, n: u128, j: usize) -> u128 {
        (n + self.negmin[j]) / self.pw[j]
    }

    #[inline]
    fn digit_at(&self, blk: u128, j: usize) -> usize {
        // the digit at position j is the last digit of m = sigma^j * blk
        let bb = self.b as u128;
        if !self.neg || j % 2 == 0 {
            (blk % bb) as usize
        } else {
            ((bb - blk % bb) % bb) as usize
        }
    }

    fn check(&self, n: u128, c: &[u8]) -> Option<Vec<u8>> {
        let ds = signed_digits(n, self.b, self.neg);
        if ds.len() != self.d {
            return None;
        }
        let mut h = [0u8; MAXB];
        for &x in &ds {
            h[x as usize] += 1;
        }
        if h[..self.b as usize] == c[..self.b as usize] {
            let mut s = ds.clone();
            s.reverse();
            Some(s)
        } else {
            None
        }
    }
}

// ---------------------------------------------------------------- brute

struct BruteOut {
    sols: Vec<Vec<u8>>,
    leaves: u64,
    e_basic: f64,
    e_ref: f64,
    e_ref_zf: f64,
}

fn brute(cfg: &Cfg) -> BruteOut {
    // tasks: counts of the top two digit values
    let k0 = cfg.kmax + 1;
    let d = cfg.d;
    let mut lfact = vec![0f64; d + 2];
    for i in 1..d + 2 {
        lfact[i] = lfact[i - 1] + (i as f64).ln();
    }
    let inv_fact: Vec<f64> = (0..=d).map(|i| (-lfact[i]).exp()).collect();
    // P(c) = (d - c0)/d * d! prod 1/c_x! / ((b-1) b^(d-1))
    let base_p = (lfact[d] - ((cfg.b - 1) as f64).ln() - (d as f64 - 1.0) * (cfg.b as f64).ln()).exp();
    let out = Mutex::new(BruteOut { sols: vec![], leaves: 0, e_basic: 0.0, e_ref: 0.0, e_ref_zf: 0.0 });
    let mut tasks = vec![];
    for c1 in 0..=d {
        if k0 >= 2 {
            for c2 in 0..=d - c1 {
                tasks.push((c1, c2));
            }
        } else {
            tasks.push((c1, usize::MAX));
        }
    }
    tasks.par_iter().for_each(|&(c1, c2)| {
        let mut st = BruteState { c: [0u8; MAXB], sols: vec![], leaves: 0, e_basic: 0.0, e_ref: 0.0, e_ref_zf: 0.0 };
        let mut k = k0;
        let mut t = cfg.off;
        let mut r = d;
        let mut res = cfg.offres;
        let mut p = base_p;
        let mut ok = true;
        for &cc in &[c1, c2] {
            if cc == usize::MAX {
                continue;
            }
            if k == 0 || cc > r {
                ok = false;
                break;
            }
            k -= 1;
            if k == 0 && cc != r {
                ok = false;
                break;
            }
            st.c[k] = cc as u8;
            t += cc as u128 * cfg.w[k];
            r -= cc;
            res = (res + cc as u64 * cfg.wres[k]) % cfg.modulus;
            p *= inv_fact[cc];
        }
        if ok {
            brute_rec(cfg, &mut st, k, t, r, res, p, &inv_fact);
        }
        let mut o = out.lock().unwrap();
        o.sols.extend(st.sols);
        o.leaves += st.leaves;
        o.e_basic += st.e_basic;
        o.e_ref += st.e_ref;
        o.e_ref_zf += st.e_ref_zf;
    });
    let mut o = out.into_inner().unwrap();
    o.sols.sort();
    o
}

struct BruteState {
    c: [u8; MAXB],
    sols: Vec<Vec<u8>>,
    leaves: u64,
    e_basic: f64,
    e_ref: f64,
    e_ref_zf: f64,
}

#[allow(clippy::too_many_arguments)]
fn brute_rec(cfg: &Cfg, st: &mut BruteState, k: usize, t: u128, r: usize, res: u64, p: f64, inv_fact: &[f64]) {
    if k == 0 {
        if r != 0 {
            return;
        }
        st.leaves += 1;
        if t < cfg.wl || t > cfg.wu {
            return;
        }
        let d = cfg.d as f64;
        let pc = p * (d - st.c[0] as f64) / d;
        st.e_basic += pc;
        if res == 0 {
            let m = cfg.modulus as f64;
            st.e_ref += pc * m;
            if st.c[0] == 0 {
                st.e_ref_zf += pc * m;
            }
            if let Some(s) = cfg.check(t, &st.c) {
                st.sols.push(s);
            }
        }
        return;
    }
    let x = k - 1;
    if x == 0 {
        st.c[0] = r as u8;
        let t2 = t + r as u128 * cfg.w[0];
        let res2 = (res + r as u64 * cfg.wres[0]) % cfg.modulus;
        brute_rec(cfg, st, 0, t2, 0, res2, p * inv_fact[r], inv_fact);
        st.c[0] = 0;
        return;
    }
    for e in 0..=r {
        let t2 = t + e as u128 * cfg.w[x];
        let rr = (r - e) as u128;
        let lo = t2 + rr * cfg.wmin[x];
        if lo > cfg.wu {
            break;
        }
        let hi = t2 + rr * cfg.wmax[x];
        if hi < cfg.wl {
            continue;
        }
        st.c[x] = e as u8;
        let res2 = (res + e as u64 * cfg.wres[x]) % cfg.modulus;
        brute_rec(cfg, st, x, t2, r - e, res2, p * inv_fact[e], inv_fact);
    }
    st.c[x] = 0;
}

// ---------------------------------------------------------------- tree

#[derive(Clone, Copy)]
struct Node {
    k: usize,       // counts of digits >= k are decided
    r: usize,       // free slots, to hold digits < k
    t: u128,        // offset + decided digits + forced digits
    j: usize,       // positions >= j are known (common to the whole range)
    c: [u8; MAXB],  // decided counts (x >= k) and forced counts (x < k)
    h: [u8; MAXB],  // histogram of the known top digits
}

/// Narrow the node to its fixpoint. Returns false if it cannot hold a solution.
#[inline]
fn settle(cfg: &Cfg, n: &mut Node) -> bool {
    loop {
        let rr = n.r as u128;
        let lo = if n.k == 0 { n.t } else { n.t + rr * cfg.wmin[n.k] }.max(cfg.wl);
        let hi = if n.k == 0 { n.t } else { n.t + rr * cfg.wmax[n.k] }.min(cfg.wu);
        if lo > hi {
            return false;
        }
        let mut forced = false;
        while n.j > 0 {
            let j = n.j - 1;
            let bl = cfg.block(lo, j);
            if bl != cfg.block(hi, j) {
                break;
            }
            let x = cfg.digit_at(bl, j);
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
            return true;
        }
    }
}

struct TreeOut {
    sols: Mutex<Vec<Vec<u8>>>,
    nodes: AtomicU64,
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

fn dfs(cfg: &Cfg, n: &Node, out: &TreeOut, cnt: &mut u64) {
    *cnt += 1;
    if n.k == 0 {
        if let Some(s) = cfg.check(n.t, &n.c) {
            out.sols.lock().unwrap().push(s);
        } else {
            panic!("leaf that is not a solution: t = {}", n.t);
        }
        return;
    }
    children(cfg, n, |ch| dfs(cfg, &ch, out, cnt));
}

fn tree(cfg: &Cfg) -> (Vec<Vec<u8>>, u64) {
    let mut root = Node { k: cfg.kmax + 1, r: cfg.d, t: cfg.off, j: cfg.d, c: [0; MAXB], h: [0; MAXB] };
    let out = TreeOut { sols: Mutex::new(vec![]), nodes: AtomicU64::new(0) };
    if !settle(cfg, &mut root) {
        return (vec![], 1);
    }
    let mut front = vec![root];
    let mut extra = 0u64;
    while front.len() < 4000 && front.iter().all(|n| n.k > 2) {
        let mut next = vec![];
        for n in &front {
            children(cfg, n, |ch| next.push(ch));
        }
        extra += front.len() as u64;
        if next.is_empty() {
            return (vec![], extra);
        }
        front = next;
    }
    front.par_iter().for_each(|n| {
        let mut cnt = 0;
        dfs(cfg, n, &out, &mut cnt);
        out.nodes.fetch_add(cnt, Ordering::Relaxed);
    });
    let mut s = out.sols.into_inner().unwrap();
    s.sort();
    (s, out.nodes.load(Ordering::Relaxed) + extra)
}

// ---------------------------------------------------------------- lanes

/// The tree engine on digit vectors (fast/src/digits.rs), for values beyond
/// u128. In base -b it stores u = n + negmin_d instead of n. The base-b digits
/// of u are the base -b digits of n, with the odd positions replaced by
/// b-1 minus the digit. So the known top digits are the common top lanes of
/// the two ends of the range, as in a positive base.
mod lanes {
    use super::digits::{Base, DV, big_to_lanes};
    use num_bigint::BigUint;
    use rayon::prelude::*;
    use std::cmp::Ordering;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicU64, Ordering as AO};

    type V = DV<2>;
    const MAXB: usize = 64;

    pub struct LCfg {
        b: u32,
        neg: bool,
        d: usize,
        base: Base,
        kmax: usize,
        tw: Vec<V>,
        loadd: Vec<V>,
        hiadd: Vec<V>,
        wl: V,
        wu: V,
        t0: V,
        negmin: BigUint,
        w: Vec<BigUint>,
    }

    fn lanes(x: &BigUint, b: u32) -> V {
        V::from_bytes(&big_to_lanes(x, b))
    }

    fn cmp(a: &V, b: &V) -> Ordering {
        let ne = !a.eq_mask(b);
        if ne == 0 {
            Ordering::Equal
        } else {
            let i = 63 - ne.leading_zeros();
            a.lane(i).cmp(&b.lane(i))
        }
    }

    impl LCfg {
        pub fn new(b: u32, neg: bool, d: usize, w: &[BigUint], off: &BigUint) -> Option<LCfg> {
            if neg && d % 2 == 0 {
                return None;
            }
            assert!(d + 2 <= 64, "too many digits for 64 lanes");
            let bb = BigUint::from(b);
            let (mut maxv, mut negmin) = (vec![BigUint::from(0u32); d + 1], vec![BigUint::from(0u32); d + 1]);
            for j in 1..=d {
                let term = (&bb - 1u32) * bb.pow(j as u32 - 1);
                maxv[j] = maxv[j - 1].clone();
                negmin[j] = negmin[j - 1].clone();
                if !neg || (j - 1) % 2 == 0 {
                    maxv[j] += term;
                } else {
                    negmin[j] += term;
                }
            }
            let wl = &maxv[d - 1] + 1u32;
            let top = w.iter().max().unwrap() * d + off;
            let wu = maxv[d].clone().min(top);
            if wl > wu {
                return None;
            }
            let kmax = (0..b as usize).filter(|&x| &w[x] + off <= wu).max().unwrap_or(0);
            let nm = negmin[d].clone();
            let mut tw = vec![];
            for x in 0..=kmax {
                for m in 0..=d {
                    tw.push(lanes(&(&w[x] * m), b));
                }
            }
            let (mut loadd, mut hiadd) = (vec![], vec![]);
            for k in 0..=kmax + 1 {
                let (mn, mx) = if k == 0 { (BigUint::from(0u32), BigUint::from(0u32)) } else { (w[..k].iter().min().unwrap().clone(), w[..k].iter().max().unwrap().clone()) };
                for r in 0..=d {
                    loadd.push(lanes(&(&mn * r), b));
                    hiadd.push(lanes(&(&mx * r), b));
                }
            }
            Some(LCfg {
                b,
                neg,
                d,
                base: Base::new(b),
                kmax,
                tw,
                loadd,
                hiadd,
                wl: lanes(&(&wl + &nm), b),
                wu: lanes(&(&wu + &nm), b),
                t0: lanes(&(off + &nm), b),
                negmin: nm,
                w: w.to_vec(),
            })
        }
    }

    #[derive(Clone, Copy)]
    struct Node {
        t: V,
        k: usize,
        r: usize,
        j: usize,
        c: [u8; MAXB],
        h: [u8; MAXB],
    }

    #[inline]
    fn settle(cfg: &LCfg, n: &mut Node) -> bool {
        let d1 = cfg.d + 1;
        loop {
            let (lo0, hi0) = if n.k == 0 { (n.t, n.t) } else { (n.t.add(&cfg.loadd[n.k * d1 + n.r], &cfg.base), n.t.add(&cfg.hiadd[n.k * d1 + n.r], &cfg.base)) };
            let lo = if cmp(&lo0, &cfg.wl) == Ordering::Less { cfg.wl } else { lo0 };
            let hi = if cmp(&hi0, &cfg.wu) == Ordering::Greater { cfg.wu } else { hi0 };
            if cmp(&lo, &hi) == Ordering::Greater {
                return false;
            }
            let below = if n.j == 0 { 0 } else { !lo.eq_mask(&hi) & ((1u64 << n.j) - 1) };
            let jn = if below == 0 { 0 } else { 64 - below.leading_zeros() as usize };
            if jn == n.j {
                return true;
            }
            let mut bytes = [0u8; 64];
            lo.to_bytes(&mut bytes);
            let mut forced = false;
            while n.j > jn {
                let j = n.j - 1;
                let l = bytes[j] as usize;
                let x = if !cfg.neg || j % 2 == 0 { l } else { cfg.b as usize - 1 - l };
                n.j = j;
                n.h[x] += 1;
                if n.h[x] > n.c[x] {
                    if x >= n.k || n.r == 0 {
                        return false;
                    }
                    n.c[x] += 1;
                    n.t = n.t.add(&cfg.tw[x * d1 + 1], &cfg.base);
                    n.r -= 1;
                    forced = true;
                    break;
                }
            }
            if !forced {
                return true;
            }
        }
    }

    fn children(cfg: &LCfg, n: &Node, mut f: impl FnMut(Node)) {
        let d1 = cfg.d + 1;
        let x = n.k - 1;
        let (e0, e1) = if x == 0 { (n.r, n.r) } else { (0, n.r) };
        for e in e0..=e1 {
            let t2 = n.t.add(&cfg.tw[x * d1 + e], &cfg.base);
            let rr = n.r - e;
            if x > 0 {
                if cmp(&t2.add(&cfg.loadd[x * d1 + rr], &cfg.base), &cfg.wu) == Ordering::Greater {
                    break;
                }
                if cmp(&t2.add(&cfg.hiadd[x * d1 + rr], &cfg.base), &cfg.wl) == Ordering::Less {
                    continue;
                }
            }
            let mut ch = *n;
            ch.k = x;
            ch.r = rr;
            ch.t = t2;
            ch.c[x] += e as u8;
            if settle(cfg, &mut ch) {
                f(ch);
            }
        }
    }

    fn leaf(cfg: &LCfg, n: &Node) -> Vec<u8> {
        // exact check with big integers: F(c) written in base sigma*b
        let mut bytes = [0u8; 64];
        n.t.to_bytes(&mut bytes);
        let u = BigUint::from_radix_le(&bytes, cfg.b).unwrap();
        let val = &u - &cfg.negmin;
        let mut f = BigUint::from(0u32);
        for x in 0..cfg.b as usize {
            f += &cfg.w[x] * n.c[x];
        }
        let digits: Vec<u8> = (0..cfg.d).rev().map(|j| if !cfg.neg || j % 2 == 0 { bytes[j] } else { cfg.b as u8 - 1 - bytes[j] }).collect();
        let mut h = [0u8; MAXB];
        for &x in &digits {
            h[x as usize] += 1;
        }
        // val = F + offset, and the digits of u give back val
        let bs = if cfg.neg { -(cfg.b as i64) } else { cfg.b as i64 };
        let mut v = num_bigint::BigInt::from(0);
        for &x in &digits {
            v = v * bs + x as i64;
        }
        assert!(h == n.c && v == num_bigint::BigInt::from(val.clone()) && val >= f, "bad leaf");
        digits
    }

    fn dfs(cfg: &LCfg, n: &Node, out: &Mutex<Vec<Vec<u8>>>, cnt: &mut u64) {
        *cnt += 1;
        if n.k == 0 {
            out.lock().unwrap().push(leaf(cfg, n));
            return;
        }
        children(cfg, n, |ch| dfs(cfg, &ch, out, cnt));
    }

    pub fn tree(cfg: &LCfg) -> (Vec<Vec<u8>>, u64) {
        let mut root = Node { t: cfg.t0, k: cfg.kmax + 1, r: cfg.d, j: cfg.d, c: [0; MAXB], h: [0; MAXB] };
        if !settle(cfg, &mut root) {
            return (vec![], 1);
        }
        let out = Mutex::new(vec![]);
        let nodes = AtomicU64::new(0);
        let mut front = vec![root];
        let mut extra = 0u64;
        while front.len() < 20000 && front.iter().all(|n| n.k > 2) {
            let mut next = vec![];
            for n in &front {
                children(cfg, n, |ch| next.push(ch));
            }
            extra += front.len() as u64;
            if next.is_empty() {
                return (vec![], extra);
            }
            front = next;
        }
        front.par_iter().for_each(|n| {
            let mut cnt = 0;
            dfs(cfg, n, &out, &mut cnt);
            nodes.fetch_add(cnt, AO::Relaxed);
        });
        let mut s = out.into_inner().unwrap();
        s.sort();
        (s, nodes.load(AO::Relaxed) + extra)
    }
}

fn big_weights(spec: &str, b: u64) -> Vec<num_bigint::BigUint> {
    use num_bigint::BigUint;
    let parts: Vec<&str> = spec.split(':').collect();
    (0..b as u32)
        .map(|x| match parts[0] {
            "pow0" | "pow1" | "powt" => {
                let (t, m) = match parts[0] {
                    "pow0" => (0i64, 0u32),
                    "pow1" => (0, 1),
                    _ => (parts[1].parse().unwrap(), parts[2].parse().unwrap()),
                };
                if x == 0 { BigUint::from(m) } else { BigUint::from(x).pow((x as i64 + t) as u32) }
            }
            "fact" => (2..=x).fold(BigUint::from(1u32), |a, i| a * i),
            _ => panic!("unknown weights {spec}"),
        })
        .collect()
}

fn main() {
    use num_bigint::BigUint;
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: worlds <brute|tree|lanes> <base> <weights> [--offset K] [--offset-per-digit K] [--dmin D] [--dmax D]");
        std::process::exit(2);
    }
    let engine = args[1].as_str();
    let bs: i64 = args[2].parse().unwrap();
    let (b, neg) = (bs.unsigned_abs(), bs < 0);
    assert!((2..MAXB as u64).contains(&b));
    let wb = big_weights(&args[3], b);
    let (mut k0, mut k1, mut dmin, mut dmax) = (0u64, 0u64, 2usize, usize::MAX);
    let mut i = 4;
    while i < args.len() {
        let v = args.get(i + 1).expect("missing value");
        match args[i].as_str() {
            "--offset" => k0 = v.parse().unwrap(),
            "--offset-per-digit" => k1 = v.parse().unwrap(),
            "--dmin" => dmin = v.parse().unwrap(),
            "--dmax" => dmax = v.parse().unwrap(),
            a => panic!("unknown option {a}"),
        }
        i += 2;
    }
    let wtop = wb.iter().max().unwrap().clone();
    let total = Instant::now();
    let mut count = 0;
    let mut d = dmin.max(2);
    let bb = BigUint::from(b);
    while d <= dmax {
        let off = k0 + k1 * (d as u64 - 1);
        // every d-digit number is at least b^(d-2) / (b+1), in either sign;
        // once d * wtop + off is below that, it stays below for larger d
        if &wtop * d + off < bb.pow(d as u32 - 2) / (b + 1) {
            break;
        }
        if neg && d % 2 == 0 {
            d += 1;
            continue;
        }
        let t0 = Instant::now();
        let name = &args[3];
        let print = |s: &Vec<Vec<u8>>| {
            for s in s {
                println!("sol base {bs} w {name} d {d} digits {}", s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","));
            }
        };
        if engine == "lanes" {
            let Some(cfg) = lanes::LCfg::new(b as u32, neg, d, &wb, &BigUint::from(off)) else {
                d += 1;
                continue;
            };
            let (s, nodes) = lanes::tree(&cfg);
            print(&s);
            count += s.len();
            println!("len base {bs} w {name} d {d} sols {} nodes {nodes} secs {:.2}", s.len(), t0.elapsed().as_secs_f64());
            d += 1;
            continue;
        }
        let w = weights(name, b);
        let Some(cfg) = Cfg::new(b, neg, d, &w, off as u128) else {
            d += 1;
            continue;
        };
        match engine {
            "brute" => {
                let o = brute(&cfg);
                print(&o.sols);
                count += o.sols.len();
                println!(
                    "len base {bs} w {name} d {d} sols {} leaves {} basic {:.6e} refined {:.6e} refined_zerofree {:.6e} secs {:.2}",
                    o.sols.len(),
                    o.leaves,
                    o.e_basic,
                    o.e_ref,
                    o.e_ref_zf,
                    t0.elapsed().as_secs_f64()
                );
            }
            "tree" => {
                let (s, nodes) = tree(&cfg);
                print(&s);
                count += s.len();
                println!("len base {bs} w {name} d {d} sols {} nodes {nodes} secs {:.2}", s.len(), t0.elapsed().as_secs_f64());
            }
            _ => panic!("unknown engine"),
        }
        d += 1;
    }
    println!("total base {bs} w {} sols {count} secs {:.2}", args[3], total.elapsed().as_secs_f64());
}
