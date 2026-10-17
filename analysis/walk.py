"""Replay the search path of one solution and apply the inexact pruning rules.

The exact search reaches a solution through one node per level k: the counts
of the digits >= k are the solution's own counts, and the known leading
digits are the solution's own leading digits. This module replays that path
with the same interval and forced-digit logic as fast/src/search.rs, so it can
tell, without a search, whether a pruning rule would cut the solution.

The same replay works for a "planted" solution: a random arrangement of a
random digit multiset, treated as if it were a solution. Under the
probabilistic model, real solutions look like this, so the planted miss rate
estimates the miss rate in bases far beyond the exhaustive data.
"""
import math
import random
from collections import Counter


class Rules:
    def __init__(self, cap=None, band=None, deficit=None, ratio=None, uniform=False, zscore=None):
        self.cap, self.band, self.deficit, self.ratio = cap, band, deficit, ratio
        self.uniform, self.zscore = uniform, zscore

    def typical_ok(self, b, kmax, k, pp, ln_e):
        """The typical-set test of the engine's --zscore option."""
        if self.zscore is None or 4 * k > 3 * (kmax + 1):
            return True
        mean, sd = likelihood_law(b, kmax, k, pp)
        return ln_e >= mean - self.zscore * sd

    def band_ok(self, b, d, k, m):
        if self.band is None:
            return True
        q1 = (b - k) / (b - 1)
        q = (b - k) / b
        mean = q1 + (d - 1) * q
        sd = math.sqrt(d) / 2 if self.uniform else math.sqrt(q1 * (1 - q1) + (d - 1) * q * (1 - q))
        return math.floor(mean - self.band * sd) <= m <= min(math.ceil(mean + self.band * sd), d)

    def deficit_ok(self, d, known, m, oh):
        if self.deficit is None:
            return True
        q = m / d
        mean = known * q
        var = m * (1 - q) / 4 if self.uniform else known * q * (1 - q) * (d - known) / (d - 1)
        return oh + 0.5 >= mean - self.deficit * math.sqrt(var)


def poisson_entropy(mu):
    """Entropy and varentropy of the Poisson law with mean mu."""
    if mu <= 0:
        return 0.0, 0.0
    s1 = s2 = 0.0
    lp = -mu
    for j in range(int(mu + 12 * math.sqrt(mu) + 30) + 1):
        if j > 0:
            lp += math.log(mu) - math.log(j)
        p = math.exp(lp)
        s1 -= p * lp
        s2 += p * lp * lp
    return s1, s2 - s1 * s1


def likelihood_law(b, kmax, k, pp):
    """Mean and standard deviation of ln E for a random suffix of pp digits,
    as in fast/src/search.rs."""
    kk = kmax + 1
    m = kk - max(k, 1)
    hh, vh = poisson_entropy(pp / kk)
    hs, vs = poisson_entropy(pp * k / kk)
    hn, vn = poisson_entropy(pp)
    return pp * math.log(kk / b) - (m * hh + hs - hn), math.sqrt(max(m * vh + vs - vn, 0.0)) or 1e-9


def replay(b, digits, rules, mode=1):
    """Return the level k at which the rules cut this solution, or None.

    digits: the solution, most significant first. Under the union interval
    used by the engine the convention only matters at the leaves, so `mode`
    is not used for the path itself.
    """
    d = len(digits)
    c = Counter(digits)
    lo_b, hi_b = b ** (d - 1), b ** d - 1
    w = lambda x: 0 if x == 0 else x ** x       # weights summed into t
    whi = lambda x: 1 if x == 0 else x ** x     # weights for the upper bound
    kmax = max(x for x in range(1, b) if x ** x <= hi_b)
    occ = Counter()
    t, rf, m, oh, known = 0, d, 0, 0, 0
    ln_e_parent = d * (math.log(kmax + 1) - math.log(b))
    for k in range(kmax, 1, -1):
        ck = c[k]
        e = ck - occ[k]
        assert e >= 0
        if rules.cap is not None and ck > rules.cap:
            return k
        t += e * w(k)
        rf -= e
        m += ck
        oh += occ[k]
        if not rules.band_ok(b, d, k, m):
            return k
        while True:
            lo = max(t, lo_b)
            hi = min(t + occ[0] + rf * whi(k - 1), hi_b)
            # common leading digits of lo and hi, as positions from the top
            p = 0
            while p < d and lo // b ** (d - 1 - p) == hi // b ** (d - 1 - p):
                p += 1
            forced = False
            for pos in range(known, p):
                x = digits[pos]
                occ[x] += 1
                if x >= k:
                    oh += 1
                else:
                    rf -= 1
                    t += w(x)
                    forced = True
            known = max(known, p)
            if not forced:
                break
        if not rules.deficit_ok(d, known, m, oh):
            return k
        if rules.ratio is not None or rules.zscore is not None:
            pp = d - known
            lneed = sum(math.lgamma(c[x] - occ[x] + 1) for x in range(k, kmax + 1))
            ln_e = math.lgamma(pp + 1) + rf * math.log(k) - lneed - math.lgamma(rf + 1) - pp * math.log(b)
            if rules.ratio is not None and ln_e < ln_e_parent + math.log(rules.ratio):
                return k
            if not rules.typical_ok(b, kmax, k, pp, ln_e):
                return k
            ln_e_parent = ln_e
    return None


def planted(b, d, rng):
    """A random d-digit string whose Munchausen sum has d digits (the model's
    distribution of a solution), returned as its digit list."""
    while True:
        digs = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(d - 1)]
        s = sum(x ** x if x else 1 for x in digs)
        if b ** (d - 1) <= s < b ** d:
            return digs


def planted_lengths(b, rng):
    """Pick a digit length with the model's weights for base b (d = b-j)."""
    weights = [0.080, 0.552, 0.232, 0.086, 0.032, 0.012, 0.006]
    j = rng.choices(range(len(weights)), weights)[0]
    return b - j
