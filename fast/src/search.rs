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
//
// The experiments replace x^x by other weights (see `weights`). The bounds
// stay valid for any weights >= 0: hi uses W_{k-1}, the largest weight of a
// digit below k (w_{k-1} when the weights increase), and 1 above becomes the
// largest weight of 0. A negative weight m for 0 lowers lo by up to |m| d, so
// the root then starts at t = -|m| d, and the leaf adds |m| d back.
use crate::digits::{Base, DV, big_to_lanes};
use num_bigint::BigUint;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

#[cfg(feature = "gpu")]
pub mod gpu;

/// Largest supported base: lane sums reach 2b-1, which must fit in a byte.
pub const MAX_BASE: usize = 127;

/// A count for every digit value.
type Hist = [u8; 128];

pub struct Params<const N: usize> {
    pub d: u32,
    base: Base,
    w: Vec<DV<N>>,   // w[j] = j^j for j >= 1, w[0] = 0 (zeros are tracked by count)
    // Below, w[0] is the largest weight of 0 (1 by default), and W[j] is the
    // largest of w[0..=j]. W[j] = w[j] when the weights increase.
    dhi: Vec<DV<N>>, // step of hi when c_j grows by one: w[j] - W[j-1]
    #[cfg_attr(not(feature = "gpu"), allow(dead_code))]
    tw: Vec<DV<N>>,  // tw[j * (d + 1) + m] = m * w[j], read by the GPU search
    // shift[k * (kmax + 1) + x] = w[x] - W[k-1] for x < k, stored modulo
    // b^(32 N), so adding it subtracts W[k-1] - w[x]: the step of hi when a
    // free slot (worth up to W[k-1]) turns out to hold x
    shift: Vec<DV<N>>,
    // drop[k * (d + 1) + m] = -m * (W[k] - W[k-1]) modulo b^(32 N): turns
    // hi = t + z w[0] + m W[k] into t + z w[0] + m W[k-1]
    drop: Vec<DV<N>>,
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
    root_t: DV<N>,   // t at the root: the experiment's offset (default 0) minus lshift
    root_hi: DV<N>,  // offset + d * W[kmax]; the root stores this plus drop
    zsum: Vec<DV<N>>,
    zstep: [DV<N>; 2],
    // the top lane, if t can be negative (a negative weight for 0), else 0
    negbit: u64,
    zscore: f64,
    // the typical-set test applies at the levels k <= zk
    zk: usize,
    // typical-set test: mean and standard deviation of ln E for a node at level
    // k with pp unknown positions, at index k * (d + 1) + pp, and the
    // threshold mean - zscore * sd
    lik_mean: Vec<f64>,
    lik_sd: Vec<f64>,
    lik_thr: Vec<f64>,
    zoff: Vec<f64>,
    zhist: bool,
    tree_stats: bool,
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
    /// skip a node whose expected number of solutions is more than this many
    /// standard deviations below its mean for a random suffix (typical-set test)
    pub zscore: f64,
    /// experiment: look for n = F(n) + offset instead of n = F(n)
    pub offset: u64,
    /// experiment: the weight of the digit 0 under the second convention
    /// (1 by default, that is 0^0 = 1; the first convention keeps 0^0 = 0)
    pub zero: i64,
    /// experiment: weights x^(x + shift) for x >= 1 (at least -1)
    pub shift: i32,
    /// experiment: weights x! for x >= 1
    pub factorial: bool,
    /// experiment: weights x^power for x >= 1, as in narcissistic numbers
    /// (0 keeps x^x)
    pub power: u32,
    /// experiment: raise each weight w(x), x >= 1, by the least amount that
    /// makes it congruent to x + r modulo b-1 (after --perturb, if given)
    pub set_residue: Option<u32>,
    /// the null law of ln E for --zscore: Poisson (default) or Cond
    pub zlaw: ZLaw,
    /// --zscore applies at the levels k <= zfrom * (kmax + 1)
    pub zfrom: f64,
    /// the threshold of --zscore at level k is zscore + zslope (u - 1/2),
    /// u = k / (kmax + 1)
    pub zslope: f64,
    /// record, per digit count, a histogram of the nodes and interval
    /// evaluations by the smallest z-score on their path
    pub zhist: bool,
    /// record the mean subtree size per level and number of unknown positions
    pub tree_stats: bool,
    /// replace the null law of ln E in these cells: (d, k, pp, mean, sd)
    pub ztable: Option<&'static [(u32, u32, u32, f64, f64)]>,
}

/// The null law of ln E for the typical-set test.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum ZLaw {
    /// independent Poisson cells, minus the entropy and varentropy of the total
    Poisson,
    /// Poisson cells conditioned on their total by linear regression
    Cond,
}

/// Bins of the --zhist histogram: z from ZH_LO in steps of ZH_STEP. The last
/// bin also holds the nodes above every tested level (z = +inf).
pub const ZH_BINS: usize = 480;
pub const ZH_LO: f64 = -16.0;
pub const ZH_STEP: f64 = 0.05;

fn zbin(z: f32) -> usize {
    (((z as f64 - ZH_LO) / ZH_STEP).floor().max(0.0) as usize).min(ZH_BINS - 1)
}

impl Prune {
    pub const NONE: Prune = Prune { cap: u32::MAX, z: f64::INFINITY, deficit: f64::INFINITY, epsilon: 0.0, ratio: 0.0, uniform: false, perturb: 0, keep_residues: false, zscore: f64::INFINITY, offset: 0, zero: 1, shift: 0, factorial: false, power: 0, set_residue: None, zlaw: ZLaw::Poisson, zfrom: 0.75, zslope: 0.0, zhist: false, tree_stats: false, ztable: None };

    /// whether the weights differ from x^x with 0^0 in {0, 1}
    pub fn custom_weights(&self) -> bool {
        self.perturb != 0 || self.zero != 1 || self.shift != 0 || self.factorial || self.power != 0 || self.set_residue.is_some()
    }
}

/// The weight w(x) of every digit x >= 1 (index 0 holds 0), and the weight of
/// the digit 0 under each of the two conventions.
pub fn weights(b: u32, prune: &Prune) -> (Vec<BigUint>, [i64; 2]) {
    assert!(prune.shift >= -1, "weights x^(x+t) need t >= -1");
    let mut w: Vec<BigUint> = (0..b)
        .map(|j| match j {
            0 => BigUint::ZERO,
            _ if prune.factorial => (1..=j).map(BigUint::from).product(),
            _ if prune.power > 0 => BigUint::from(j).pow(prune.power),
            _ => BigUint::from(j).pow((j as i64 + prune.shift as i64) as u32),
        })
        .collect();
    if prune.perturb != 0 {
        for j in 2..b as usize {
            let room: BigUint = &w[j] / 4u32 + 1u32;
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
            w[j] += delta;
        }
    }
    if let Some(r) = prune.set_residue {
        let m = BigUint::from(b - 1);
        for j in 1..b as usize {
            let want = BigUint::from(j as u64 + r as u64) % &m;
            let have = &w[j] % &m;
            w[j] += (&m + want - have) % &m;
        }
    }
    (w, [0, prune.zero])
}

/// The largest number of digits a solution can have: d digits need
/// d * max w + offset >= b^(d-1).
pub fn max_len(b: u32, prune: &Prune) -> u32 {
    let (w, zw) = weights(b, prune);
    let top = w.iter().max().unwrap().clone().max(BigUint::from(zw[1].max(0) as u64));
    let bb = BigUint::from(b);
    (1..=64u32).take_while(|&d| &top * d + prune.offset >= bb.pow(d - 1)).last().unwrap()
}

impl<const N: usize> Params<N> {
    pub fn new(b: u32, d: u32, prune: Prune) -> Self {
        let bb = BigUint::from(b);
        let (wt, zw) = weights(b, &prune);
        // A negative weight for 0 makes the sum smaller than t: the root
        // starts at -lshift, and the leaf adds lshift back.
        let lshift = (-zw[0].min(zw[1])).max(0) as u64 * d as u64;
        // a negative t needs a free top lane to be told apart from a large one
        assert!(d >= 2 && d + 2 + (lshift > 0) as u32 <= 32 * N as u32);
        // weights used for upper bounds: a zero is worth at most max(0, zero)
        let mut w_hi = wt.clone();
        w_hi[0] = BigUint::from(zw[0].max(zw[1]) as u64);
        // wmax[j] = max of w_hi[0..=j], the most a slot holding a digit <= j
        // can add; it equals w_hi[j] when the weights increase
        let wmax: Vec<BigUint> = w_hi.iter().scan(BigUint::ZERO, |m, v| {
            *m = m.clone().max(v.clone());
            Some(m.clone())
        }).collect();
        let limit = bb.pow(d);
        let kmax = (1..b as usize).filter(|&j| w_hi[j] < limit).max().unwrap();
        let lanes = |x: &BigUint| DV::<N>::from_bytes(&big_to_lanes(x, b));
        let modulus = bb.pow(32 * N as u32);
        // the value v - u modulo b^(32 N), for signed u and v
        let modv = |v: &BigUint, u: &BigUint| lanes(&((&modulus + v % &modulus - u % &modulus) % &modulus));
        let signed = |x: i64| if x >= 0 { modv(&BigUint::from(x as u64), &BigUint::ZERO) } else { modv(&BigUint::ZERO, &BigUint::from(x.unsigned_abs())) };
        let mut tw = vec![];
        // digits above kmax never appear, and their weights need more lanes
        for j in 0..=kmax {
            for m in 0..=d {
                tw.push(lanes(&(&w_hi[j] * m)));
            }
        }
        let w = (0..=kmax).map(|j| if j == 0 { DV::zero() } else { lanes(&w_hi[j]) }).collect();
        let mut drop = vec![];
        for k in 0..=kmax {
            for m in 0..=d {
                drop.push(if k >= 1 { modv(&BigUint::ZERO, &((&wmax[k] - &wmax[k - 1]) * m)) } else { DV::zero() });
            }
        }
        let mut shift = vec![];
        for k in 0..=kmax {
            for x in 0..=kmax {
                shift.push(if k >= 1 && x < k { modv(&w_hi[x], &wmax[k - 1]) } else { DV::zero() });
            }
        }
        let dhi = (0..=kmax).map(|j| if j == 0 { DV::zero() } else { modv(&w_hi[j], &wmax[j - 1]) }).collect();
        // leaf: zsum[mode * (d + 1) + c] = lshift + c * (weight of 0), and
        // zstep[mode] = w(1) - (weight of 0), the change when a 0 becomes a 1
        let w1 = i64::try_from(&wt[1]).expect("w(1) too large");
        let zsum = (0..2).flat_map(|m| (0..=d as i64).map(move |c| lshift as i64 + c * zw[m])).map(signed).collect();
        let zstep = [signed(w1 - zw[0]), signed(w1 - zw[1])];
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
        // ln E is the log-probability of the multinomial outcome (need_x for the
        // m digits k..=kmax, rf below k) in pp random positions. Its mean and
        // variance are minus the entropy and the varentropy of that law, here
        // through the Poisson approximation.
        let (mut lik_mean, mut lik_sd) = (vec![], vec![]);
        if prune.zscore.is_finite() {
            let kk = (kmax + 1) as f64;
            for k in 0..=kmax {
                let m = (kmax + 1 - k.max(1)) as f64;
                for pp in 0..=d {
                    let n = pp as f64;
                    match prune.zlaw {
                        ZLaw::Poisson => {
                            let (hh, vh) = poisson_entropy(n / kk);
                            let (hs, vs) = poisson_entropy(n * k as f64 / kk);
                            let (hn, vn) = poisson_entropy(n);
                            let h = m * hh + hs - hn;
                            let v = (m * vh + vs - vn).max(0.0);
                            lik_mean.push(n * (kk / b as f64).ln() - h);
                            lik_sd.push(v.sqrt().max(1e-9));
                        }
                        ZLaw::Cond => {
                            // X = sum over cells of ln n! - n ln p; ln E = ln pp! - X + pp ln(kk / b)
                            let (mean, sd) = if pp == 0 || k == 0 {
                                (0.0, 1e-9)
                            } else {
                                let a = cell_moments(n / kk, -kk.ln());
                                let s = cell_moments(n * k as f64 / kk, (k as f64 / kk).ln());
                                let (ex, vx, cx) = (m * a.0 + s.0, m * a.1 + s.1, m * a.2 + s.2);
                                let lf: f64 = (1..=pp).map(|j| (j as f64).ln()).sum();
                                (lf - ex + n * (kk / b as f64).ln(), (vx - cx * cx / n).max(0.0).sqrt().max(1e-9))
                            };
                            lik_mean.push(mean);
                            lik_sd.push(sd);
                        }
                    }
                }
            }
        }
        if let Some(t) = prune.ztable {
            for &(td, k, pp, mean, sd) in t {
                if td == d && (k as usize) <= kmax && pp <= d && !lik_mean.is_empty() {
                    let i = k as usize * (d as usize + 1) + pp as usize;
                    lik_mean[i] = mean;
                    lik_sd[i] = sd;
                }
            }
        }
        // the shift of the threshold at level k, and the threshold itself
        let zoff: Vec<f64> = (0..=kmax).map(|k| if prune.zslope == 0.0 { 0.0 } else { prune.zslope * (k as f64 / (kmax + 1) as f64 - 0.5) }).collect();
        let lik_thr = lik_mean.iter().zip(&lik_sd).enumerate().map(|(i, (m, s))| m - (prune.zscore + zoff[i / (d as usize + 1)]) * s).collect();
        Params {
            d,
            base: Base::new(b),
            w,
            dhi,
            tw,
            shift,
            drop,
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
            track_ln: prune.epsilon > 0.0 || prune.ratio > 0.0 || prune.zscore.is_finite(),
            ln_fact: (0..=d).scan(0.0, |acc, n| {
                if n > 0 {
                    *acc += (n as f64).ln();
                }
                Some(*acc)
            }).collect(),
            ln_k: (0..=kmax).map(|k| (k as f64).ln()).collect(),
            ln_b: (b as f64).ln(),
            root_t: modv(&BigUint::from(prune.offset), &BigUint::from(lshift)),
            root_hi: lanes(&(&wmax[kmax] * d + prune.offset)),
            zsum,
            zstep,
            negbit: if lshift > 0 { 1u64 << (32 * N - 1) } else { 0 },
            zscore: prune.zscore,
            zk: (prune.zfrom * (kmax + 1) as f64).floor() as usize,
            lik_mean,
            lik_sd,
            lik_thr,
            zoff,
            zhist: prune.zhist,
            tree_stats: prune.tree_stats,
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
    fn likely(&self, c: &mut Node<N>, parent: &Head, k: usize, l: &mut Local) -> bool {
        if !self.track_ln {
            return true;
        }
        let ln_e = self.ln_fact[c.pp as usize] + c.rf as f64 * self.ln_k[k]
            - c.lneed - self.ln_fact[c.rf as usize] - c.pp as f64 * self.ln_b;
        c.ln_e = ln_e;
        c.zmin = parent.zmin;
        // At the top levels only a few digit values are decided, ln E is far
        // from normal, and the tree is narrow anyway, so by default the test
        // starts at 3/4.
        let atypical = self.zscore.is_finite() && k <= self.zk && {
            let i = k * (self.d as usize + 1) + c.pp as usize;
            if self.zhist {
                c.zmin = c.zmin.min(((ln_e - self.lik_mean[i]) / self.lik_sd[i] + self.zoff[k]) as f32);
            }
            ln_e < self.lik_thr[i]
        };
        let parent_ln_e = parent.ln_e;
        if atypical || ln_e < self.ln_eps || ln_e < parent_ln_e + self.ln_ratio {
            l.skipped += ln_e.exp();
            return false;
        }
        true
    }

    #[cfg_attr(not(feature = "gpu"), allow(dead_code))]
    #[inline(always)]
    fn mul_w(&self, j: usize, m: u32) -> &DV<N> {
        unsafe { self.tw.get_unchecked(j * (self.d as usize + 1) + m as usize) }
    }


    // lanes [pp, d): the known leading digits
    #[inline(always)]
    fn known(&self, pp: u32) -> u64 {
        self.dmask & !((1u64 << pp) - 1)
    }

    // lo clipped to b^(d-1); its lanes >= pp hold the known leading digits
    #[inline(always)]
    fn clip_lo(&self, t: &DV<N>) -> DV<N> {
        let nz = t.nonzero_mask();
        if nz & !(self.dmask >> 1) == 0 || nz & self.negbit != 0 { self.pow_lo } else { *t }
    }
}

// E h, Var h and Cov(h, N) for N ~ Poisson(mu) and h(n) = ln n! - n lnp.
fn cell_moments(mu: f64, lnp: f64) -> (f64, f64, f64) {
    if mu <= 0.0 {
        return (0.0, 0.0, 0.0);
    }
    let (mut e1, mut e2, mut en) = (0.0, 0.0, 0.0);
    let (mut lp, mut lf) = (-mu, 0.0);
    let top = (mu + 12.0 * mu.sqrt() + 30.0) as usize;
    for j in 0..=top {
        if j > 0 {
            lp += mu.ln() - (j as f64).ln();
            lf += (j as f64).ln();
        }
        let p = lp.exp();
        let h = lf - j as f64 * lnp;
        e1 += p * h;
        e2 += p * h * h;
        en += p * h * j as f64;
    }
    (e1, e2 - e1 * e1, en - e1 * mu)
}

// Entropy and varentropy (variance of -ln p) of the Poisson law with mean mu.
fn poisson_entropy(mu: f64) -> (f64, f64) {
    if mu <= 0.0 {
        return (0.0, 0.0);
    }
    let (mut s1, mut s2) = (0.0, 0.0);
    let mut lp = -mu; // ln p(0)
    let top = (mu + 12.0 * mu.sqrt() + 30.0) as usize;
    for j in 0..=top {
        if j > 0 {
            lp += mu.ln() - (j as f64).ln();
        }
        let p = lp.exp();
        s1 -= p * lp;
        s2 += p * lp * lp;
    }
    (s1, s2 - s1 * s1)
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
    hi: DV<N>,     // t + z w[0] + rf * W[k-1] for a node that decides c_k (z: known zeros)
    pp: u32,       // known leading digits occupy lanes [pp, d)
    rf: u32,       // digit slots not yet accounted for
    m: u32,        // number of decided digits, all >= k
    lneed: f64,    // sum over decided digits x of ln((c_x - occ_x)!)
    ln_e: f64,     // ln of the model's expected number of solutions below the node
    zmin: f32,     // with --zhist: the smallest z-score on the path to the node
}

#[derive(Default)]
#[repr(align(128))]
struct Stats {
    nodes: AtomicU64,
    evals: AtomicU64,
    skipped: Mutex<f64>,
    // with --zhist: per digit count d, ZH_BINS node counts, then ZH_BINS evaluations
    zh: Mutex<Vec<u64>>,
    // with --tree-stats: per digit count d, the table of Local::ts
    ts: Mutex<Vec<u64>>,
}

#[derive(Default)]
struct Local {
    nodes: u64,
    evals: u64,
    skipped: f64, // expected number of solutions in skipped subtrees
    // with --zhist: the digit count of this task's nodes and their histogram
    d: u32,
    zh: Vec<u64>,
    // with --tree-stats: per (k, pp), the number of nodes and their total
    // subtree size
    ts: Vec<u64>,
}

impl Local {
    fn for_params<const N: usize>(p: &Params<N>) -> Local {
        Local {
            d: p.d,
            zh: if p.zhist { vec![0; 2 * ZH_BINS] } else { vec![] },
            ts: if p.tree_stats { vec![0; 2 * 64 * 64] } else { vec![] },
            ..Local::default()
        }
    }

    fn subtree<const N: usize>(&mut self, p: &Params<N>, k: usize, pp: u32, size: u64) {
        let i = 2 * (k.min(63) * 64 + pp as usize);
        let _ = p;
        self.ts[i] += 1;
        self.ts[i + 1] += size;
    }

    #[inline(always)]
    fn node(&mut self, zmin: f32) {
        self.nodes += 1;
        if !self.zh.is_empty() {
            self.zh[zbin(zmin)] += 1;
        }
    }

    #[inline(always)]
    fn eval(&mut self, zmin: f32) {
        self.evals += 1;
        if !self.zh.is_empty() {
            self.zh[ZH_BINS + zbin(zmin)] += 1;
        }
    }
}

pub struct Search<const N: usize> {
    pub params: Vec<Params<N>>,
    pub par_depth: u32,
    /// whether any inexact rule is on; the exact search compiles without them
    inexact: bool,
    /// whether the only inexact rule is the typical-set test, which the GPU
    /// search also runs
    #[cfg_attr(not(feature = "gpu"), allow(dead_code))]
    zscore_only: bool,
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
    /// (digit count, digit k decided next, free slots, known leading digits) of a unit
    pub fn unit_info(&self, u: &Unit<N>) -> (u32, usize, u32, u32) {
        let d = self.params[u.pi].d;
        (d, u.k, u.n.rf, d - u.n.pp)
    }

    pub fn new(b: u32, min_digits: u32, max_digits: u32, par_depth: u32, prune: Prune) -> Self {
        Search {
            params: {
                use rayon::prelude::*;
                let ds: Vec<u32> = (min_digits.max(2)..=max_len(b, &prune).min(max_digits)).rev().collect();
                ds.into_par_iter().map(|d| Params::new(b, d, prune)).collect()
            },
            par_depth,
            inexact: prune.cap != u32::MAX
                || prune.z.is_finite()
                || prune.deficit.is_finite()
                || prune.epsilon > 0.0
                || prune.ratio > 0.0
                || prune.zscore.is_finite()
                || prune.tree_stats
                // the generic path also handles a negative t
                || prune.zero < 0,
            zscore_only: prune.cap == u32::MAX
                && !prune.z.is_finite()
                && !prune.deficit.is_finite()
                && prune.epsilon <= 0.0
                && prune.ratio <= 0.0
                && prune.zero >= 0
                && !prune.zhist
                && !prune.tree_stats,
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
        if !l.zh.is_empty() {
            let mut h = st.zh.lock().unwrap();
            if h.is_empty() {
                h.resize(65 * 2 * ZH_BINS, 0);
            }
            let o = l.d as usize * 2 * ZH_BINS;
            for (a, v) in h[o..o + 2 * ZH_BINS].iter_mut().zip(&l.zh) {
                *a += v;
            }
        }
        if !l.ts.is_empty() {
            let mut h = st.ts.lock().unwrap();
            if h.is_empty() {
                h.resize(65 * 2 * 64 * 64, 0);
            }
            let o = l.d as usize * 2 * 64 * 64;
            for (a, v) in h[o..o + 2 * 64 * 64].iter_mut().zip(&l.ts) {
                *a += v;
            }
        }
    }

    /// with --tree-stats: (d, k, pp, nodes, total subtree size) for every
    /// node of level k (digits >= k decided) with pp unknown positions whose
    /// subtree ran in one task
    pub fn tree_stats(&self) -> Vec<(u32, usize, usize, u64, u64)> {
        let sz = 2 * 64 * 64;
        let mut tot = vec![0u64; 65 * sz];
        for s in &self.stats {
            for (a, v) in tot.iter_mut().zip(s.ts.lock().unwrap().iter()) {
                *a += v;
            }
        }
        let mut out = vec![];
        for p in &self.params {
            let o = p.d as usize * sz;
            for k in 0..64 {
                for pp in 0..64 {
                    let i = o + 2 * (k * 64 + pp);
                    if tot[i] > 0 {
                        out.push((p.d, k, pp, tot[i], tot[i + 1]));
                    }
                }
            }
        }
        out
    }

    /// with --zhist: per digit count d, the nodes and the interval evaluations
    /// by bin of the smallest z-score on their path
    pub fn zhist(&self) -> Vec<(u32, Vec<u64>, Vec<u64>)> {
        let mut tot = vec![0u64; 65 * 2 * ZH_BINS];
        for s in &self.stats {
            for (a, v) in tot.iter_mut().zip(s.zh.lock().unwrap().iter()) {
                *a += v;
            }
        }
        self.params
            .iter()
            .map(|p| {
                let o = p.d as usize * 2 * ZH_BINS;
                (p.d, tot[o..o + ZH_BINS].to_vec(), tot[o + ZH_BINS..o + 2 * ZH_BINS].to_vec())
            })
            .collect()
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
        for (pi, p) in self.params.iter().enumerate() {
            let mut l = Local::for_params(p);
            let hi = p.root_hi.add(&p.drop[p.kmax * (p.d as usize + 1) + p.d as usize], &p.base);
            let root = Node { t: p.root_t, hi, pp: p.d, rf: p.d, m: 0, lneed: 0.0, ln_e: p.d as f64 * (((p.kmax + 1) as f64).ln() - p.ln_b), zmin: f32::INFINITY };
            let mut frontier = vec![Unit { pi, k: p.kmax, n: root, cnt: [0; 128] }];
            for _ in 0..depth {
                let mut next = vec![];
                for u in frontier {
                    if u.k == 1 {
                        next.push(u);
                        continue;
                    }
                    l.node(u.n.zmin);
                    let mut cnt = u.cnt;
                    self.expand::<true>(p, u.k, &u.n, &mut cnt, &mut l, |_, c, cnt| {
                        next.push(Unit { pi, k: u.k - 1, n: *c, cnt: *cnt });
                    });
                }
                frontier = next;
            }
            out.extend(frontier);
            self.flush(&l);
        }
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
    // for x > k; the cursor sets cnt[k] before it hands out a child.
    #[inline(always)]
    fn expand<const X: bool>(&self, p: &Params<N>, k: usize, n: &Node<N>, cnt: &mut Hist, l: &mut Local, mut emit: impl FnMut(&mut Local, &Node<N>, &mut Hist)) {
        let mut cur = Cursor::new(p, k, n);
        while let Some(c) = self.next_child::<X>(p, &mut cur, cnt, l) {
            emit(l, &c, cnt);
        }
    }

    // Advance the cursor to its next child that survives every test. X
    // enables the inexact rules.
    #[inline(always)]
    fn next_child<const X: bool>(&self, p: &Params<N>, cur: &mut Cursor<N>, cnt: &mut Hist, l: &mut Local) -> Option<Node<N>> {
        let base = &p.base;
        let dm = p.dmask;
        let top = !(dm >> 1); // lanes >= d-1
        let k = cur.k;
        let n = &cur.h;
        let (wk, dhi) = unsafe { (p.w.get_unchecked(k), p.dhi.get_unchecked(k)) };
        while cur.e <= n.rf {
            let e = cur.e;
            cur.e += 1;
            let (te, hi) = (cur.te, cur.hi);
            // The sums for e + 1 come before the branches below, so that a
            // mispredicted branch does not throw them away.
            cur.te = te.add(wk, base);
            cur.hi = hi.add(dhi, base);
            if X { l.eval(n.zmin) } else { l.evals += 1 }
            let ck = cur.occk + e;
            let mk = n.m + ck;
            if X {
                if ck > p.cap || mk > p.band_hi[k] {
                    break; // both only grow with e
                }
                if mk < p.band_lo[k] {
                    continue;
                }
            }
            let mut nlo = te.nonzero_mask();
            if X && nlo & p.negbit != 0 {
                nlo = 0; // lo < 0: clip it to b^(d-1)
            }
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
            let mut c = Node { t: te, hi, pp: n.pp, rf: n.rf - e, m: mk, lneed, ln_e: 0.0, zmin: f32::INFINITY };
            if self.settle::<X>(p, k, &mut c, &mut clo, &mut chi, cnt) && {
                // hi for the child's own cursor, before the branches below
                c.hi = c.hi.add(unsafe { p.drop.get_unchecked((k - 1) * (p.d as usize + 1) + c.rf as usize) }, base);
                first_digit_ok(p, &clo, &chi, c.pp, k, cnt)
            }
                && (!X || (p.plausible(&c, &clo, k) && p.likely(&mut c, n, k, l)))
            {
                return Some(c);
            }
        }
        cur.e = n.rf + 1;
        None
    }

    // The leading-digit test with forced digits, iterated to a fixpoint.
    // [clo, chi] is the clipped interval of c, and z the number of known
    // zeros. Every new leading digit x >= k must stay within c_x = cnt[x];
    // every new leading digit below k takes a free slot and adds its weight
    // to t, which narrows the interval and can expose more leading digits.
    // Returns false if the node fails.
    #[inline(always)]
    fn settle<const X: bool>(&self, p: &Params<N>, k: usize, c: &mut Node<N>, clo: &mut DV<N>, chi: &mut DV<N>, cnt: &Hist) -> bool {
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
            // The forced digits go in before the checks of the digits >= k, so
            // that a mispredicted branch there does not discard the sums.
            // w[0] is zero, so a forced zero adds nothing to t.
            let row = k * (p.kmax + 1);
            let mut fl = forced;
            while fl != 0 {
                let i = fl.trailing_zeros();
                fl &= fl - 1;
                let x = unsafe { *ld.get_unchecked(i as usize) } as usize;
                c.t = c.t.add(unsafe { p.w.get_unchecked(x) }, base);
                c.hi = c.hi.add(unsafe { p.shift.get_unchecked(row + x) }, base);
            }
            let mut big = new & !forced;
            while big != 0 {
                let i = big.trailing_zeros();
                big &= big - 1;
                // lanes < d <= 62 and digits < b <= 127, so indices stay in bounds
                let x = unsafe { *ld.get_unchecked(i as usize) };
                let lim = unsafe { *cnt.get_unchecked(x as usize) };
                if (clo.eq_mask_at(&ld, i as usize) & known).count_ones() > lim as u32 {
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
            let (mut n1, n2) = (c.t.nonzero_mask(), c.hi.nonzero_mask());
            if X && n1 & p.negbit != 0 {
                n1 = 0;
            }
            if n1 & !dm != 0 || n2 & top == 0 {
                return false;
            }
            *clo = if n1 & top == 0 { p.pow_lo } else { c.t };
            *chi = if n2 & !dm != 0 { p.max_v } else { c.hi };
        }
    }

    // All digits >= 2 are decided; the free slots hold ones and zeros. With
    // c_1 = occ[1] + e ones and c_0 = occ[0] + rf - e zeros the sum is
    // t + e w(1) + c_0 w(0), with w(0) = 0 for convention 0 and 1 (or the
    // value of --zero) for convention 1. Check every candidate exactly.
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
        let c0 = (o0 + n.rf) as usize;
        let mut s0 = n.t.add(unsafe { p.zsum.get_unchecked(c0) }, &p.base);
        let mut s1 = n.t.add(unsafe { p.zsum.get_unchecked(d + 1 + c0) }, &p.base);
        for e in 0..=n.rf {
            check(1, s1, e, cnt);
            check(0, s0, e, cnt);
            s0 = s0.add(&p.zstep[0], &p.base);
            s1 = s1.add(&p.zstep[1], &p.base);
        }
        cnt[0] = 0;
        cnt[1] = 0;
    }

    // A parallel task: search the subtree below n.
    fn rec<'s, const X: bool>(&'s self, s: &rayon::Scope<'s>, p: &'s Params<N>, k: usize, n: Node<N>, mut cnt: Hist, depth: u32) {
        let mut l = Local::for_params(p);
        self.rec_seq::<X>(s, p, k, &n, &mut cnt, &mut l, depth);
        self.flush(&l);
    }

    // Depth-first search below n, with an explicit stack of cursors instead
    // of recursion. Down to par_depth levels below the unit, a node whose
    // thread has no queued tasks left hands its children to the pool as
    // tasks, so idle threads can steal them. Otherwise the children run
    // here, which avoids the cost of a task per node.
    fn rec_seq<'s, const X: bool>(&'s self, s: &rayon::Scope<'s>, p: &'s Params<N>, k: usize, n: &Node<N>, cnt: &mut Hist, l: &mut Local, depth: u32) {
        // with --tree-stats: the node count when each cursor's node was
        // counted, to measure its subtree; split marks a node whose children
        // went to other tasks
        let ts = X && p.tree_stats;
        let mut starts = [0u64; 64];
        let (mut cur_start, mut split) = (l.nodes, false);
        if X { l.node(n.zmin) } else { l.nodes += 1 }
        if k == 1 {
            self.leaf(p, n, cnt);
            return;
        }
        // the cursors of the ancestors; k decreases by one per level
        let mut stack: [std::mem::MaybeUninit<Cursor<N>>; 64] = [const { std::mem::MaybeUninit::uninit() }; 64];
        let mut sp = 0;
        let mut cur = Cursor::new(p, k, n);
        loop {
            let ck = cur.k;
            let level = depth + (k - ck) as u32;
            let child = if cur.e == 0 && level < self.par_depth && rayon_core::current_thread_has_pending_tasks() != Some(true) {
                // hand every child to the pool and drop this node
                self.expand::<X>(p, ck, &cur.node0(), cnt, l, |_, c, cnt| {
                    let (c, cnt) = (*c, *cnt);
                    s.spawn(move |s| self.rec::<X>(s, p, ck - 1, c, cnt, level + 1))
                });
                if ts {
                    split = true;
                }
                None
            } else {
                self.next_child::<X>(p, &mut cur, cnt, l)
            };
            match child {
                Some(c) => {
                    let before = l.nodes;
                    if X { l.node(c.zmin) } else { l.nodes += 1 }
                    if ck == 2 {
                        self.leaf(p, &c, cnt);
                    } else {
                        // a node has at most 62 ancestors below the root
                        unsafe { stack.get_unchecked_mut(sp) }.write(cur);
                        if ts {
                            starts[sp] = cur_start;
                            cur_start = before;
                        }
                        sp += 1;
                        cur = Cursor::new(p, ck - 1, &c);
                    }
                }
                None => {
                    if ts {
                        if !split {
                            l.subtree(p, ck + 1, cur.h.pp, l.nodes - cur_start);
                        }
                        split = false;
                    }
                    if sp == 0 {
                        return;
                    }
                    sp -= 1;
                    cur = unsafe { stack.get_unchecked(sp).assume_init_read() };
                    if ts {
                        cur_start = starts[sp];
                    }
                }
            }
        }
    }
}

// The state of expand at one node: the node without its sums, the next
// value of e, and the interval [te, hi] of the child for that e (before its
// forced digits).
struct Cursor<const N: usize> {
    te: DV<N>,
    hi: DV<N>,
    h: Head,
    k: usize,
    e: u32,
    occk: u32,
}

// the fields of a node that its cursor still needs
#[derive(Clone, Copy)]
struct Head {
    pp: u32,
    rf: u32,
    m: u32,
    lneed: f64,
    ln_e: f64,
    zmin: f32,
}

impl<const N: usize> Cursor<N> {
    #[inline(always)]
    fn new(p: &Params<N>, k: usize, n: &Node<N>) -> Self {
        let occk = p.clip_lo(&n.t).count(k as u8, p.known(n.pp));
        Cursor { te: n.t, hi: n.hi, h: Head { pp: n.pp, rf: n.rf, m: n.m, lneed: n.lneed, ln_e: n.ln_e, zmin: n.zmin }, k, e: 0, occk }
    }

    // the node of a cursor that has not started yet
    fn node0(&self) -> Node<N> {
        let h = &self.h;
        Node { t: self.te, hi: self.hi, pp: h.pp, rf: h.rf, m: h.m, lneed: h.lneed, ln_e: h.ln_e, zmin: h.zmin }
    }
}
