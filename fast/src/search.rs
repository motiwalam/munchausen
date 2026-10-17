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
    // shift[k * (kmax + 1) + x] = w[x] - w[k-1] for x < k (w[0] taken as 1),
    // stored modulo b^(32 N), so adding it subtracts w[k-1] - w[x]: the step
    // of hi when a free slot (worth up to w[k-1]) turns out to hold x
    shift: Vec<DV<N>>,
    pow_lo: DV<N>,   // b^(d-1)
    max_v: DV<N>,    // b^d - 1
    dmask: u64,      // lanes < d
    kmax: usize,     // largest digit with j^j < b^d
    cap: u32,        // inexact search: no digit may occur more often than this
    band_lo: Vec<u32>, // inexact search: bounds on the number of digits >= k
    band_hi: Vec<u32>,
    deficit: f64,
    uniform: bool,
    ln_eps: f64,
    ln_ratio: f64,
    track_ln: bool,    // whether the model's expected counts are needed at all
    ln_fact: Vec<f64>, // ln(n!) for n <= d
    ln_k: Vec<f64>,    // ln(k) for k <= kmax
    ln_b: f64,
}

/// Pruning rules for the inexact search. Both are off by default.
#[derive(Clone, Copy)]
pub struct Prune {
    /// largest allowed count of any digit 2 or more
    pub cap: u32,
    /// allowed deviation, in standard deviations, of the number of digits >= k
    /// from its mean for a random d-digit string
    pub z: f64,
    /// allowed shortfall, in standard deviations, of the number of digits >= k
    /// seen in the known leading digits, against a random arrangement
    pub deficit: f64,
    /// skip a subtree when the model's expected number of solutions in it is
    /// below this (0 disables the rule)
    pub epsilon: f64,
    /// skip a child when its expected number of solutions is below this
    /// fraction of its parent's (0 disables the rule)
    pub ratio: f64,
    /// band and deficit tests measured on the scale of a whole Brownian bridge
    /// (sqrt(d)/2 and sqrt(m)/2) instead of the pointwise standard deviation
    pub uniform: bool,
    /// experiment: replace each weight x^x (x >= 2) by x^x + a pseudo-random
    /// amount below x^x / 4, chosen from this seed (0 keeps the true weights)
    pub perturb: u64,
    /// with perturb: make the amount a multiple of 2(b-1), which keeps the
    /// weights' residues modulo 2 and modulo b-1
    pub keep_residues: bool,
}

impl Prune {
    pub const NONE: Prune = Prune { cap: u32::MAX, z: f64::INFINITY, deficit: f64::INFINITY, epsilon: 0.0, ratio: 0.0, uniform: false, perturb: 0, keep_residues: false };
}

impl<const N: usize> Params<N> {
    pub fn new(b: u32, d: u32, prune: Prune) -> Self {
        assert!(d >= 2 && d + 2 <= 32 * N as u32);
        let bb = BigUint::from(b);
        // weights used for upper bounds: a zero is worth at most 1
        let mut w_hi: Vec<BigUint> = (0..b).map(|j| if j == 0 { BigUint::from(1u32) } else { BigUint::from(j).pow(j) }).collect();
        if prune.perturb != 0 {
            for j in 2..b as usize {
                let room: BigUint = &w_hi[j] / 4u32 + 1u32;
                let mut state = prune.perturb ^ ((b as u64) << 32) ^ (j as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
                let limbs: Vec<u32> = (0..room.bits() / 32 + 2)
                    .map(|_| {
                        // splitmix64
                        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
                        let mut z = state;
                        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                        (z ^ (z >> 31)) as u32
                    })
                    .collect();
                let mut delta = BigUint::from_slice(&limbs) % &room;
                if prune.keep_residues {
                    let step = BigUint::from(2 * (b - 1));
                    delta = &delta / &step * &step;
                }
                w_hi[j] += delta;
            }
        }
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
        let modulus = bb.pow(32 * N as u32);
        let mut shift = vec![];
        for k in 0..=kmax {
            for x in 0..=kmax {
                shift.push(if k >= 1 && x < k { lanes(&((&modulus - &w_hi[k - 1] + &w_hi[x]) % &modulus)) } else { DV::zero() });
            }
        }
        let dhi = (0..=kmax).map(|j| if j == 0 { DV::zero() } else { lanes(&(&w_hi[j] - &w_hi[j - 1])) }).collect();
        // the number of digits >= k in a random d-digit string (leading digit
        // nonzero) has this mean and variance
        let (mut band_lo, mut band_hi) = (vec![0; kmax + 1], vec![d; kmax + 1]);
        if prune.z.is_finite() {
            for k in 1..=kmax {
                let q1 = (b as f64 - k as f64) / (b as f64 - 1.0);
                let q = (b as f64 - k as f64) / b as f64;
                let mean = q1 + (d as f64 - 1.0) * q;
                let sd = if prune.uniform {
                    (d as f64).sqrt() / 2.0
                } else {
                    (q1 * (1.0 - q1) + (d as f64 - 1.0) * q * (1.0 - q)).sqrt()
                };
                band_lo[k] = (mean - prune.z * sd).floor().max(0.0) as u32;
                band_hi[k] = ((mean + prune.z * sd).ceil() as u32).min(d);
            }
        }
        Params {
            d,
            base: Base::new(b),
            w,
            dhi,
            tw,
            shift,
            pow_lo: lanes(&bb.pow(d - 1)),
            max_v: lanes(&(limit - 1u32)),
            dmask: (1u64 << d) - 1,
            kmax,
            cap: prune.cap,
            band_lo,
            band_hi,
            deficit: prune.deficit,
            uniform: prune.uniform,
            ln_eps: if prune.epsilon > 0.0 { prune.epsilon.ln() } else { f64::NEG_INFINITY },
            ln_ratio: if prune.ratio > 0.0 { prune.ratio.ln() } else { f64::NEG_INFINITY },
            track_ln: prune.epsilon > 0.0 || prune.ratio > 0.0,
            ln_fact: (0..=d).scan(0.0, |acc, n| {
                if n > 0 {
                    *acc += (n as f64).ln();
                }
                Some(*acc)
            }).collect(),
            ln_k: (0..=kmax).map(|k| (k as f64).ln()).collect(),
            ln_b: (b as f64).ln(),
        }
    }

    /// Inexact search: under a random arrangement of the digits, the known
    /// leading digits should contain about their share of the m digits >= k.
    #[inline(always)]
    fn plausible(&self, c: &Node<N>, clo: &DV<N>, k: usize) -> bool {
        if !self.deficit.is_finite() {
            return true;
        }
        // how many of the known leading digits are >= k
        let oh = (clo.ge_mask(k as u8) & self.known(c.pp)).count_ones();
        let d = self.d as f64;
        let len = d - c.pp as f64; // number of known leading digits
        let q = c.m as f64 / d;
        let mean = len * q;
        let var = if self.uniform {
            c.m as f64 * (1.0 - q) / 4.0
        } else {
            len * q * (1.0 - q) * (d - len) / (d - 1.0)
        };
        oh as f64 + 0.5 >= mean - self.deficit * var.sqrt()
    }

    /// Inexact search: the model's expected number of solutions below this node.
    /// The pp unknown digits must hold the missing copies of every decided
    /// digit plus rf digits below k, in some order. With random digits that
    /// happens with probability pp! k^rf / (prod need_x! * rf! * b^pp).
    #[inline(always)]
    fn likely(&self, c: &mut Node<N>, parent_ln_e: f64, k: usize, l: &mut Local) -> bool {
        if !self.track_ln {
            return true;
        }
        let ln_e = self.ln_fact[c.pp as usize] + c.rf as f64 * self.ln_k[k]
            - c.lneed - self.ln_fact[c.rf as usize] - c.pp as f64 * self.ln_b;
        c.ln_e = ln_e;
        if ln_e < self.ln_eps || ln_e < parent_ln_e + self.ln_ratio {
            l.skipped += ln_e.exp();
            return false;
        }
        true
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

    // lanes [pp, d): the known leading digits
    #[inline(always)]
    fn known(&self, pp: u32) -> u64 {
        self.dmask & !((1u64 << pp) - 1)
    }

    // lo clipped to b^(d-1); its lanes >= pp hold the known leading digits
    #[inline(always)]
    fn clip_lo(&self, t: &DV<N>) -> DV<N> {
        if t.nonzero_mask() & !(self.dmask >> 1) == 0 { self.pow_lo } else { *t }
    }
}

// The first unknown digit of n lies between the digits of lo and hi at that
// position. If every value in that range is a decided digit (>= k) whose copies
// are all placed already, no number in the interval fits the counts.
// cnt[x] holds c_x for every x >= k.
#[inline(always)]
fn first_digit_ok<const N: usize>(p: &Params<N>, lo: &DV<N>, hi: &DV<N>, pp: u32, k: usize, cnt: &Hist) -> bool {
    if pp == 0 {
        return true;
    }
    let x0 = lo.lane(pp - 1);
    if (x0 as usize) < k {
        return true;
    }
    let x1 = hi.lane(pp - 1);
    let known = p.known(pp);
    (x0..=x1).any(|x| lo.count(x, known) < cnt[x as usize] as u32)
}

// The known leading digits are the lanes >= pp of lo (clipped to b^(d-1)).
// Their histogram is not stored: a vector compare counts any digit on demand.
#[derive(Clone, Copy)]
struct Node<const N: usize> {
    t: DV<N>,      // sum over decided non-zero digits and forced lower digits
    pp: u32,       // known leading digits occupy lanes [pp, d)
    rf: u32,       // digit slots not yet accounted for
    m: u32,        // number of decided digits, all >= k
    lneed: f64,    // sum over decided digits x of ln((c_x - occ_x)!)
    ln_e: f64,     // ln of the model's expected number of solutions below the node
}

#[derive(Default)]
#[repr(align(128))]
struct Stats {
    nodes: AtomicU64,
    evals: AtomicU64,
    skipped: Mutex<f64>,
}

#[derive(Default)]
struct Local {
    nodes: u64,
    evals: u64,
    skipped: f64, // expected number of solutions in skipped subtrees
}

pub struct Search<const N: usize> {
    pub params: Vec<Params<N>>,
    pub par_depth: u32,
    /// whether any inexact rule is on; the exact search compiles without them
    inexact: bool,
    /// (convention, number of digits, digits with the least significant first)
    pub found: Mutex<Vec<(u32, u32, [u8; 64])>>,
    /// statistics, one slot per thread so that threads do not share cache lines
    stats: Vec<Stats>,
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
    pub fn new(b: u32, min_digits: u32, max_digits: u32, par_depth: u32, prune: Prune) -> Self {
        Search {
            params: (min_digits.max(2)..=b.min(max_digits)).rev().map(|d| Params::new(b, d, prune)).collect(),
            par_depth,
            inexact: prune.cap != u32::MAX
                || prune.z.is_finite()
                || prune.deficit.is_finite()
                || prune.epsilon > 0.0
                || prune.ratio > 0.0,
            found: Mutex::new(vec![]),
            // slot 0 serves threads outside the pool
            stats: (0..=rayon::current_num_threads()).map(|_| Stats::default()).collect(),
            on_found: None,
        }
    }

    fn flush(&self, l: &Local) {
        let i = rayon::current_thread_index().map_or(0, |i| i + 1);
        let st = &self.stats[i.min(self.stats.len() - 1)];
        st.nodes.fetch_add(l.nodes, Ordering::Relaxed);
        st.evals.fetch_add(l.evals, Ordering::Relaxed);
        if l.skipped > 0.0 {
            *st.skipped.lock().unwrap() += l.skipped;
        }
    }

    /// number of tree nodes visited so far
    pub fn nodes(&self) -> u64 {
        self.stats.iter().map(|s| s.nodes.load(Ordering::Relaxed)).sum()
    }

    /// number of intervals evaluated so far
    pub fn evals(&self) -> u64 {
        self.stats.iter().map(|s| s.evals.load(Ordering::Relaxed)).sum()
    }

    /// expected number of solutions in subtrees skipped by the inexact rules
    pub fn skipped(&self) -> f64 {
        self.stats.iter().map(|s| *s.skipped.lock().unwrap()).sum()
    }

    /// Split the search into subtrees by expanding every root `depth` levels.
    /// The order is deterministic, so unit indices are stable between runs.
    pub fn units(&self, depth: u32) -> Vec<Unit<N>> {
        let mut out = vec![];
        let mut l = Local::default();
        for (pi, p) in self.params.iter().enumerate() {
            let root = Node { t: DV::zero(), pp: p.d, rf: p.d, m: 0, lneed: 0.0, ln_e: p.d as f64 * (((p.kmax + 1) as f64).ln() - p.ln_b) };
            let mut frontier = vec![Unit { pi, k: p.kmax, n: root, cnt: [0; 128] }];
            for _ in 0..depth {
                let mut next = vec![];
                for u in frontier {
                    if u.k == 1 {
                        next.push(u);
                        continue;
                    }
                    l.nodes += 1;
                    let mut cnt = u.cnt;
                    self.expand::<true>(p, u.k, &u.n, &mut cnt, &mut l, |_, c, cnt| {
                        next.push(Unit { pi, k: u.k - 1, n: *c, cnt: *cnt });
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
            if self.inexact {
                rayon::scope(|s| self.rec::<true>(s, p, u.k, u.n, u.cnt, 0));
            } else {
                rayon::scope(|s| self.rec::<false>(s, p, u.k, u.n, u.cnt, 0));
            }
            done(i);
        });
    }

    // Enumerate c_k = occ[k] + e for e = 0, 1, ... (k >= 2) and emit every
    // child whose interval survives the leading-digit test. cnt[x] holds c_x
    // for x > k; expand sets cnt[k] before it emits a child. X enables the
    // inexact rules.
    #[inline(always)]
    fn expand<const X: bool>(&self, p: &Params<N>, k: usize, n: &Node<N>, cnt: &mut Hist, l: &mut Local, mut emit: impl FnMut(&mut Local, &Node<N>, &mut Hist)) {
        let base = &p.base;
        let dm = p.dmask;
        let top = !(dm >> 1); // lanes >= d-1
        let known = p.known(n.pp);
        let nlo = p.clip_lo(&n.t);
        let occk = nlo.count(k as u8, known);
        let z = nlo.count(0, known);
        let (wk, dhi) = unsafe { (p.w.get_unchecked(k), p.dhi.get_unchecked(k)) };
        let mut te = n.t;
        let mut hi = p.hi(&te, z, k, n.rf);
        for e in 0..=n.rf {
            if e > 0 {
                te = te.add(wk, base);
                hi = hi.add(dhi, base);
            }
            l.evals += 1;
            let ck = occk + e;
            let mk = n.m + ck;
            if X {
                if ck > p.cap || mk > p.band_hi[k] {
                    break; // both only grow with e
                }
                if mk < p.band_lo[k] {
                    continue;
                }
            }
            let nlo = te.nonzero_mask();
            if nlo & !dm != 0 {
                break; // lo >= b^d, and it only grows with e
            }
            let nhi = hi.nonzero_mask();
            if nhi & top == 0 {
                continue; // hi < b^(d-1)
            }
            cnt[k] = ck as u8;
            let mut clo = if nlo & top == 0 { p.pow_lo } else { te };
            let mut chi = if nhi & !dm != 0 { p.max_v } else { hi };
            let lneed = if X && p.track_ln { n.lneed + p.ln_fact[e as usize] } else { 0.0 };
            let mut c = Node { t: te, pp: n.pp, rf: n.rf - e, m: mk, lneed, ln_e: 0.0 };
            if self.settle::<X>(p, k, &mut c, &mut clo, &mut chi, hi, cnt)
                && first_digit_ok(p, &clo, &chi, c.pp, k, cnt)
                && (!X || (p.plausible(&c, &clo, k) && p.likely(&mut c, n.ln_e, k, l)))
            {
                emit(l, &c, cnt);
            }
        }
    }

    // The leading-digit test with forced digits, iterated to a fixpoint.
    // [clo, chi] is the clipped interval of c, and z the number of known
    // zeros. Every new leading digit x >= k must stay within c_x = cnt[x];
    // every new leading digit below k takes a free slot and adds its weight
    // to t, which narrows the interval and can expose more leading digits.
    // Returns false if the node fails.
    #[inline(always)]
    fn settle<const X: bool>(&self, p: &Params<N>, k: usize, c: &mut Node<N>, clo: &mut DV<N>, chi: &mut DV<N>, mut hi: DV<N>, cnt: &Hist) -> bool {
        let base = &p.base;
        let dm = p.dmask;
        let top = !(dm >> 1);
        loop {
            let npp = 64 - (!clo.eq_mask(chi) & dm).leading_zeros();
            if npp >= c.pp {
                return true;
            }
            let known = p.known(npp);
            let new = known & ((1u64 << c.pp) - 1);
            let forced = new & !clo.ge_mask(k as u8);
            let f = forced.count_ones();
            if f > c.rf {
                return false;
            }
            let mut ld = [0u8; 64];
            clo.to_bytes(&mut ld);
            let mut big = new & !forced;
            while big != 0 {
                let i = big.trailing_zeros();
                big &= big - 1;
                // lanes < d <= 62 and digits < b <= 127, so indices stay in bounds
                let x = unsafe { *ld.get_unchecked(i as usize) };
                let lim = unsafe { *cnt.get_unchecked(x as usize) };
                if clo.count(x, known) > lim as u32 {
                    return false;
                }
                if X && p.track_ln {
                    // copies of x among the known digits up to lane i, in the
                    // order the counts were once built lane by lane
                    let o = clo.count(x, known & !(((1u64 << c.pp) - 1) & !((2u64 << i) - 1)));
                    // one fewer copy of x still has to appear in the suffix
                    c.lneed -= ((lim as u32 - o + 1) as f64).ln();
                }
            }
            c.pp = npp;
            if f == 0 {
                return true;
            }
            c.rf -= f;
            let row = k * (p.kmax + 1);
            let mut fl = forced;
            while fl != 0 {
                let i = fl.trailing_zeros();
                fl &= fl - 1;
                let x = unsafe { *ld.get_unchecked(i as usize) } as usize;
                if x > 0 {
                    c.t = c.t.add(unsafe { p.w.get_unchecked(x) }, base);
                }
                hi = hi.add(unsafe { p.shift.get_unchecked(row + x) }, base);
            }
            let (n1, n2) = (c.t.nonzero_mask(), hi.nonzero_mask());
            if n1 & !dm != 0 || n2 & top == 0 {
                return false;
            }
            *clo = if n1 & top == 0 { p.pow_lo } else { c.t };
            *chi = if n2 & !dm != 0 { p.max_v } else { hi };
        }
    }

    // All digits >= 2 are decided; the free slots hold ones and zeros. With
    // c_1 = occ[1] + e ones and c_0 = occ[0] + rf - e zeros the sum is
    // t + e (0^0 = 0) or t + e + c_0 (0^0 = 1). Check every candidate exactly.
    fn leaf(&self, p: &Params<N>, n: &Node<N>, cnt: &mut Hist) {
        let d = p.d as usize;
        let known = p.known(n.pp);
        let nlo = p.clip_lo(&n.t);
        let (o0, o1) = (nlo.count(0, known), nlo.count(1, known));
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

    // A parallel task: search the subtree below n.
    fn rec<'s, const X: bool>(&'s self, s: &rayon::Scope<'s>, p: &'s Params<N>, k: usize, n: Node<N>, mut cnt: Hist, depth: u32) {
        let mut l = Local::default();
        self.rec_seq::<X>(s, p, k, &n, &mut cnt, &mut l, depth);
        self.flush(&l);
    }

    // Depth-first search below n. Down to par_depth levels below the unit,
    // a node whose thread has no queued tasks left hands its children to
    // the pool as tasks, so idle threads can steal them. Otherwise the
    // children run here, which avoids the cost of a task per node.
    fn rec_seq<'s, const X: bool>(&'s self, s: &rayon::Scope<'s>, p: &'s Params<N>, k: usize, n: &Node<N>, cnt: &mut Hist, l: &mut Local, depth: u32) {
        l.nodes += 1;
        if k == 1 {
            self.leaf(p, n, cnt);
            return;
        }
        if depth < self.par_depth && rayon_core::current_thread_has_pending_tasks() != Some(true) {
            self.expand::<X>(p, k, n, cnt, l, |_, c, cnt| {
                let (c, cnt) = (*c, *cnt);
                s.spawn(move |s| self.rec::<X>(s, p, k - 1, c, cnt, depth + 1))
            });
        } else {
            self.expand::<X>(p, k, n, cnt, l, |l, c, cnt| self.rec_seq::<X>(s, p, k - 1, c, cnt, l, depth + 1));
        }
    }
}
