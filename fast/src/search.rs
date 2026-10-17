// Exhaustive search for Munchausen numbers in base b, for both conventions
// (0^0 = 0 and 0^0 = 1) in a single pass.
//
// For a fixed number of digits d we decide the digit counts c_{b-1}, c_{b-2},
// ..., c_1 from the largest digit down (the multiset is all that matters for
// the Munchausen sum). After the counts of all digits >= k are fixed, the
// final sum S lies in an interval [lo, hi]; every number in that interval
// shares a common run of leading digits, and those digits must belong to the
// multiset:
//   * a leading digit x >= k may not appear more often than c_x,
//   * a leading digit x < k forces c_x >= (its occurrences); we add its weight
//     to the running sum right away, which narrows [lo, hi] further, possibly
//     exposing more leading digits (iterated to a fixpoint).
// The interval only ever shrinks while descending, so the leading-digit
// histogram is maintained incrementally and only new lanes are inspected.
//
// The two conventions only differ in what each zero contributes (0 or 1), so
// the interval used for pruning is the union over both:
//     lo = t                      (free slots all zeros, 0^0 = 0)
//     hi = t + z + rf * w_{k-1}   (free slots all k-1, plus 1 per known zero)
// where t is the sum over all known non-zero digits, z the number of known
// zeros and rf the number of digit slots not accounted for yet. The two
// conventions are told apart only at the leaves.
use crate::digits::{Base, DV, big_to_lanes};
use num_bigint::BigUint;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

/// Largest supported base: lane sums reach 2b-1, which must fit in a byte.
pub const MAX_BASE: usize = 127;

/// A count for every digit value.
type Hist = [u8; 128];

pub struct Params<const N: usize> {
    pub d: u32,
    base: Base,
    w: Vec<DV<N>>,   // w[j] = j^j for j >= 1, w[0] = 0 (zeros are tracked by count)
    dhi: Vec<DV<N>>, // step of hi when c_j grows by one: w[j] - w[j-1] (w[0] taken as 1)
    tw: Vec<DV<N>>,  // tw[j * (d + 1) + m] = m * w[j] (w[0] taken as 1, i.e. just m)
    pow_lo: DV<N>,   // b^(d-1)
    max_v: DV<N>,    // b^d - 1
    dmask: u64,      // lanes < d
    kmax: usize,     // largest digit with j^j < b^d
}

impl<const N: usize> Params<N> {
    pub fn new(b: u32, d: u32) -> Self {
        assert!(d >= 2 && d + 2 <= 32 * N as u32);
        let bb = BigUint::from(b);
        // weights used for upper bounds: a zero is worth at most 1
        let w_hi: Vec<BigUint> = (0..b).map(|j| if j == 0 { BigUint::from(1u32) } else { BigUint::from(j).pow(j) }).collect();
        let limit = bb.pow(d);
        let kmax = (1..b as usize).filter(|&j| w_hi[j] < limit).max().unwrap();
        let lanes = |x: &BigUint| DV::<N>::from_bytes(&big_to_lanes(x, b));
        let mut tw = vec![];
        // digits above kmax never appear, and their weights need more lanes
        for j in 0..=kmax {
            for m in 0..=d {
                tw.push(lanes(&(&w_hi[j] * m)));
            }
        }
        let w = (0..=kmax).map(|j| if j == 0 { DV::zero() } else { lanes(&w_hi[j]) }).collect();
        let dhi = (0..=kmax).map(|j| if j == 0 { DV::zero() } else { lanes(&(&w_hi[j] - &w_hi[j - 1])) }).collect();
        Params {
            d,
            base: Base::new(b),
            w,
            dhi,
            tw,
            pow_lo: lanes(&bb.pow(d - 1)),
            max_v: lanes(&(limit - 1u32)),
            dmask: (1u64 << d) - 1,
            kmax,
        }
    }

    #[inline(always)]
    fn mul_w(&self, j: usize, m: u32) -> &DV<N> {
        unsafe { self.tw.get_unchecked(j * (self.d as usize + 1) + m as usize) }
    }

    // t + z + rf * w_{k-1}
    #[inline(always)]
    fn hi(&self, t: &DV<N>, z: u32, k: usize, rf: u32) -> DV<N> {
        t.add(self.mul_w(k - 1, rf), &self.base).add(self.mul_w(0, z), &self.base)
    }
}

#[derive(Clone, Copy)]
struct Node<const N: usize> {
    t: DV<N>,      // sum over decided non-zero digits and forced lower digits
    occ: Hist,     // histogram of the known leading digits (occ[0] = known zeros)
    pp: u32,       // known leading digits occupy lanes [pp, d)
    rf: u32,       // digit slots not yet accounted for
}

#[derive(Default)]
struct Local {
    nodes: u64,
    evals: u64,
}

pub struct Search<const N: usize> {
    pub params: Vec<Params<N>>,
    pub par_depth: u32,
    /// (convention, number of digits, digits with the least significant first)
    pub found: Mutex<Vec<(u32, u32, [u8; 64])>>,
    pub nodes: AtomicU64,
    pub evals: AtomicU64,
    /// called (from worker threads) as soon as a solution is found
    pub on_found: Option<Box<dyn Fn(u32, u32, &[u8; 64]) + Send + Sync>>,
}

/// An independent piece of the search: a subtree rooted at depth `unit_depth`.
pub struct Unit<const N: usize> {
    pi: usize,
    k: usize,
    n: Node<N>,
    cnt: Hist,
}

impl<const N: usize> Search<N> {
    pub fn new(b: u32, max_digits: u32, par_depth: u32) -> Self {
        Search {
            params: (2..=b.min(max_digits)).rev().map(|d| Params::new(b, d)).collect(),
            par_depth,
            found: Mutex::new(vec![]),
            nodes: AtomicU64::new(0),
            evals: AtomicU64::new(0),
            on_found: None,
        }
    }

    fn flush(&self, l: &Local) {
        self.nodes.fetch_add(l.nodes, Ordering::Relaxed);
        self.evals.fetch_add(l.evals, Ordering::Relaxed);
    }

    /// Split the search into subtrees by expanding every root `depth` levels.
    /// The order is deterministic, so unit indices are stable between runs.
    pub fn units(&self, depth: u32) -> Vec<Unit<N>> {
        let mut out = vec![];
        let mut l = Local::default();
        for (pi, p) in self.params.iter().enumerate() {
            let root = Node { t: DV::zero(), occ: [0; 128], pp: p.d, rf: p.d };
            let mut frontier = vec![Unit { pi, k: p.kmax, n: root, cnt: [0; 128] }];
            for _ in 0..depth {
                let mut next = vec![];
                for u in frontier {
                    if u.k == 1 {
                        next.push(u);
                        continue;
                    }
                    l.nodes += 1;
                    self.expand(p, u.k, &u.n, &u.cnt, &mut l, |_, c, ck| {
                        let mut cnt = u.cnt;
                        cnt[u.k] = ck;
                        next.push(Unit { pi, k: u.k - 1, n: c, cnt });
                    });
                }
                frontier = next;
            }
            out.extend(frontier);
        }
        self.flush(&l);
        out
    }

    /// Search every unit for which `skip` is false, in parallel, calling
    /// `done` after each one completes.
    pub fn run_units(&self, units: &[Unit<N>], skip: impl Fn(usize) -> bool + Sync, done: impl Fn(usize) + Sync) {
        use rayon::prelude::*;
        units.par_iter().enumerate().with_max_len(1).for_each(|(i, u)| {
            if skip(i) {
                return;
            }
            let p = &self.params[u.pi];
            rayon::scope(|s| self.rec(s, p, u.k, u.n, u.cnt, 0));
            done(i);
        });
    }

    // Enumerate c_k = occ[k] + e for e = 0, 1, ... (k >= 2) and emit every
    // child whose interval survives the leading-digit test. cnt[x] holds c_x
    // for x > k.
    #[inline(always)]
    fn expand(&self, p: &Params<N>, k: usize, n: &Node<N>, cnt: &Hist, l: &mut Local, mut emit: impl FnMut(&mut Local, Node<N>, u8)) {
        let base = &p.base;
        let dm = p.dmask;
        let top = !(dm >> 1); // lanes >= d-1
        let occk = n.occ[k] as u32;
        let (wk, dhi) = unsafe { (p.w.get_unchecked(k), p.dhi.get_unchecked(k)) };
        let mut te = n.t;
        let mut hi = p.hi(&te, n.occ[0] as u32, k, n.rf);
        for e in 0..=n.rf {
            if e > 0 {
                te = te.add(wk, base);
                hi = hi.add(dhi, base);
            }
            l.evals += 1;
            let nlo = te.nonzero_mask();
            if nlo & !dm != 0 {
                break; // lo >= b^d, and it only grows with e
            }
            let nhi = hi.nonzero_mask();
            if nhi & top == 0 {
                continue; // hi < b^(d-1)
            }
            let ck = (occk + e) as u8;
            let mut clo = if nlo & top == 0 { p.pow_lo } else { te };
            let mut chi = if nhi & !dm != 0 { p.max_v } else { hi };
            let mut npp = 64 - (!clo.eq_mask(&chi) & dm).leading_zeros();
            if npp >= n.pp {
                emit(l, Node { t: te, occ: n.occ, pp: n.pp, rf: n.rf - e }, ck);
                continue;
            }
            let mut c = Node { t: te, occ: n.occ, pp: n.pp, rf: n.rf - e };
            let ok = 'fix: loop {
                let mut ld = [0u8; 64];
                clo.to_bytes(&mut ld);
                let mut forced = false;
                for lane in npp..c.pp {
                    // lanes < d <= 62 and digits < b <= 62, so indices stay in bounds
                    let x = unsafe { *ld.get_unchecked(lane as usize) } as usize;
                    let o = unsafe { c.occ.get_unchecked_mut(x) };
                    *o += 1;
                    if x >= k {
                        let lim = if x == k { ck } else { unsafe { *cnt.get_unchecked(x) } };
                        if *o > lim {
                            break 'fix false;
                        }
                    } else {
                        if c.rf == 0 {
                            break 'fix false;
                        }
                        c.rf -= 1;
                        if x > 0 {
                            c.t = c.t.add(unsafe { p.w.get_unchecked(x) }, base);
                        }
                        forced = true;
                    }
                }
                c.pp = npp;
                if !forced {
                    break true;
                }
                let hi2 = p.hi(&c.t, c.occ[0] as u32, k, c.rf);
                let (n1, n2) = (c.t.nonzero_mask(), hi2.nonzero_mask());
                if n1 & !dm != 0 || n2 & top == 0 {
                    break false;
                }
                clo = if n1 & top == 0 { p.pow_lo } else { c.t };
                chi = if n2 & !dm != 0 { p.max_v } else { hi2 };
                npp = 64 - (!clo.eq_mask(&chi) & dm).leading_zeros();
                if npp >= c.pp {
                    break true;
                }
            };
            if ok {
                emit(l, c, ck);
            }
        }
    }

    // All digits >= 2 are decided; the free slots hold ones and zeros. With
    // c_1 = occ[1] + e ones and c_0 = occ[0] + rf - e zeros the sum is
    // t + e (0^0 = 0) or t + e + c_0 (0^0 = 1). Check every candidate exactly.
    fn leaf(&self, p: &Params<N>, n: &Node<N>, cnt: &mut Hist) {
        let d = p.d as usize;
        let (o0, o1) = (n.occ[0] as u32, n.occ[1] as u32);
        let check = |mode: u32, s: DV<N>, e: u32, cnt: &mut Hist| {
            let nz = s.nonzero_mask();
            if nz & !p.dmask != 0 || nz & (1 << (d - 1)) == 0 {
                return; // not a d-digit number
            }
            cnt[1] = (o1 + e) as u8;
            cnt[0] = (o0 + n.rf - e) as u8;
            let mut x = [0u8; 64];
            s.to_bytes(&mut x);
            let mut h = [0u8; 128];
            for &v in &x[..d] {
                h[v as usize] += 1;
            }
            if h == *cnt {
                if let Some(f) = &self.on_found {
                    f(mode, p.d, &x);
                }
                self.found.lock().unwrap().push((mode, p.d, x));
            }
        };
        // 0^0 = 1: every free slot is worth 1 whatever it holds
        let one = p.mul_w(0, 1);
        let s1 = n.t.add(p.mul_w(0, o0 + n.rf), &p.base);
        let mut s0 = n.t;
        for e in 0..=n.rf {
            check(1, s1, e, cnt);
            check(0, s0, e, cnt);
            s0 = s0.add(one, &p.base);
        }
        cnt[0] = 0;
        cnt[1] = 0;
    }

    fn rec<'s>(&'s self, s: &rayon::Scope<'s>, p: &'s Params<N>, k: usize, n: Node<N>, mut cnt: Hist, depth: u32) {
        let mut l = Local::default();
        if depth < self.par_depth && k > 1 {
            l.nodes += 1;
            self.expand(p, k, &n, &cnt.clone(), &mut l, |_, c, ck| {
                cnt[k] = ck;
                let cnt = cnt;
                s.spawn(move |s| self.rec(s, p, k - 1, c, cnt, depth + 1))
            });
        } else {
            self.rec_seq(p, k, &n, &mut cnt, &mut l);
        }
        self.flush(&l);
    }

    fn rec_seq(&self, p: &Params<N>, k: usize, n: &Node<N>, cnt: &mut Hist, l: &mut Local) {
        l.nodes += 1;
        if k == 1 {
            self.leaf(p, n, cnt);
            return;
        }
        let snapshot = *cnt;
        self.expand(p, k, n, &snapshot, l, |l, c, ck| {
            cnt[k] = ck;
            self.rec_seq(p, k - 1, &c, cnt, l)
        });
    }
}
