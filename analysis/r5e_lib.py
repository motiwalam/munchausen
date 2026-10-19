"""Round 5 evidence: shared tools for clustered near-solution counts.

A near-solution event is (cluster, offset). Events of one cluster are not
independent: a digit multiset can be a near-solution at several offsets
(the swap lemma), and twins put two events at the same offset.

- cluster_stats: design effects from a list of events.
- p_low / p_high: P values for N_0 against the offset total, with the
  calibration error included and inflated by the design effects.
- swap_free_ks: offsets with no two a single transposition apart.
"""
import math
from collections import defaultdict

from scipy import stats


def cluster_stats(events):
    """events: iterable of (cluster_key, offset). Returns a dict with
    n (events), clusters, phi (sum K^2 / sum K over the whole offset set),
    psi (the same within one offset), shared (share of events whose cluster
    reaches another offset)."""
    per = defaultdict(lambda: defaultdict(int))
    for c, d in events:
        per[c][d] += 1
    n = sum(sum(v.values()) for v in per.values())
    if n == 0:
        return dict(n=0, clusters=0, phi=1.0, psi=1.0, shared=0.0, distinct=0)
    k2 = sum(sum(v.values()) ** 2 for v in per.values())
    w2 = sum(x * x for v in per.values() for x in v.values())
    shared = sum(sum(v.values()) for v in per.values() if len(v) >= 2)
    return dict(n=n, clusters=len(per), phi=k2 / n, psi=w2 / n, shared=shared / n,
                distinct=len(per) / n)


def _nb_cdf(x, r, p):
    """P(X <= x) for X negative binomial with real r: P(X = k) =
    C(k+r-1, k) p^r (1-p)^k. Uses the regularized incomplete beta."""
    if x < 0:
        return 0.0
    return float(stats.beta.cdf(p, r, math.floor(x) + 1))


def predictive(n0, total, J, phi=1.0, psi=1.0):
    """Predictive law of N_0 given the offset total `total` over J offsets.
    Counts are divided by psi (clumps at one offset) and the total by phi
    (clumps across offsets); lambda gets the Jeffreys posterior
    Gamma(T/phi + 1/2, rate J psi/phi). Returns (x, r, p) with x = n0/psi
    and N_0/psi ~ NB(r, p)."""
    Je = J * psi / phi
    r = total / phi + 0.5
    p = Je / (Je + 1.0)
    return n0 / psi, r, p


def p_low(n0, total, J, phi=1.0, psi=1.0):
    x, r, p = predictive(n0, total, J, phi, psi)
    return _cdf_interp(x, r, p)


def p_high(n0, total, J, phi=1.0, psi=1.0):
    x, r, p = predictive(n0, total, J, phi, psi)
    return 1.0 - _cdf_interp(x - 1.0, r, p)


def _cdf_interp(x, r, p):
    """P(X <= x) for real x: linear in x between integers, so that a count
    divided by psi stays continuous."""
    lo = math.floor(x)
    a = _nb_cdf(lo, r, p)
    if x == lo:
        return a
    b = _nb_cdf(lo + 1, r, p)
    return a + (x - lo) * (b - a)


def poisson_low(n0, lam):
    return float(stats.poisson.cdf(n0, lam))


def poisson_high(n0, lam):
    return float(stats.poisson.sf(n0 - 1, lam))


def rank_p_low(t0, totals):
    """Exchangeable rank test: (1 + #{offsets with total <= t0}) / (J + 1).
    Valid under exchangeability whatever the dependence."""
    return (1 + sum(1 for t in totals if t <= t0)) / (len(totals) + 1)


def rank_p_high(t0, totals):
    return (1 + sum(1 for t in totals if t >= t0)) / (len(totals) + 1)


def transposition_ks(b, kmax):
    """All |Delta| / (b-1) <= kmax for one transposition of two digits:
    t b^i R_s with 1 <= t <= b-1, i >= 0, s >= 1, R_s = (b^s - 1)/(b-1)."""
    out = set()
    i = 0
    while b ** i <= kmax:
        s = 1
        while True:
            R = (b ** s - 1) // (b - 1)
            base = b ** i * R
            if base > kmax:
                break
            for t in range(1, b):
                v = t * base
                if v > kmax:
                    break
                out.add(v)
            s += 1
        i += 1
    return out


def swap_free_ks(b, count, even=True, kmax=None):
    """Greedy offsets k (D = (b-1) k), starting at 0, such that no two
    differ by a transposition value. With even=True every k is even, so D
    stays in the class of 0 mod 2(b-1)."""
    kmax = kmax or 400 * b
    bad = transposition_ks(b, kmax)
    chosen = [0]
    k = 0
    while len(chosen) < count:
        k += 2 if even else 1
        if k > kmax:
            raise ValueError("kmax too small")
        if all((k - c) not in bad for c in chosen):
            chosen.append(k)
    return chosen


def clump_sizes(events):
    """events: (cluster, offset). Law of the clump size at one offset."""
    from collections import Counter
    c = Counter(events)
    s = Counter(c.values())
    tot = sum(s.values())
    return {k: v / tot for k, v in s.items()} if tot else {1: 1.0}


def compound_cdf(n, lam, sizes, kmax=None):
    """P(X <= n) for X a sum of Poisson(lam / E[size]) clumps with the given
    size law."""
    mean = sum(k * p for k, p in sizes.items())
    mu = lam / mean
    kmax = kmax or int(n) + 1
    # Panjer recursion for the compound Poisson law
    g = [0.0] * (kmax + 1)
    g[0] = math.exp(-mu * (1 - sizes.get(0, 0.0)))
    for s in range(1, kmax + 1):
        g[s] = mu / s * sum(k * sizes.get(k, 0.0) * g[s - k] for k in range(1, s + 1))
    return sum(g[:int(math.floor(n)) + 1])


def _gamma_nodes(T, J, phi, npts=400):
    a, rate = T / phi + 0.5, J / phi
    qs = [(i + 0.5) / npts for i in range(npts)]
    return [float(stats.gamma.ppf(u, a, scale=1 / rate)) for u in qs]


def p_low_c(n0, T, J, phi=1.0, sizes=None):
    """P(N_0 <= n0): compound Poisson with clump law `sizes`, rate from the
    offset total T over J offsets with design effect phi (Jeffreys gamma)."""
    sizes = sizes or {1: 1.0}
    lams = _gamma_nodes(T, J, phi)
    return sum(compound_cdf(n0, l, sizes) for l in lams) / len(lams)


def p_high_c(n0, T, J, phi=1.0, sizes=None):
    if n0 <= 0:
        return 1.0
    return 1.0 - p_low_c(n0 - 1, T, J, phi, sizes)
