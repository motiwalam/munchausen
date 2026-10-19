"""Null laws of ln E for the typical-set rule (--zscore, --zlaw).

At a node of level k with pp unknown positions, ln E = ln pp! - sum ln need_x!
- ln rf! + rf ln k - pp ln b. Under the model the suffix is a multinomial
draw of pp digits from the kk = kmax + 1 usable values: m = kk - k decided
values with need_x ~ 1/kk each, and the bucket of the k values below k.

poisson: the engine's default (--zlaw poisson). Entropy and varentropy of
independent Poisson cells, minus those of the total.
cond:    the same cells, conditioned on the total by linear regression:
         Var(X | S) = Var X - Cov(X, S)^2 / Var S, with X = sum of the cell
         terms h(n) = ln n! - n ln p (--zlaw cond).
"""
import math
from functools import lru_cache


@lru_cache(maxsize=None)
def poisson_entropy(mu):
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


@lru_cache(maxsize=None)
def cell_moments(mu, lnp):
    """E h, Var h, Cov(h, N) for N ~ Poisson(mu), h(n) = ln n! - n lnp."""
    if mu <= 0:
        return 0.0, 0.0, 0.0
    e1 = e2 = en = 0.0
    lp = -mu
    lf = 0.0
    for j in range(int(mu + 12 * math.sqrt(mu) + 30) + 1):
        if j > 0:
            lp += math.log(mu) - math.log(j)
            lf += math.log(j)
        p = math.exp(lp)
        h = lf - j * lnp
        e1 += p * h
        e2 += p * h * h
        en += p * h * j
    return e1, e2 - e1 * e1, en - e1 * mu


def poisson_law(b, kmax, k, pp):
    kk = kmax + 1
    m = kk - max(k, 1)
    hh, vh = poisson_entropy(pp / kk)
    hs, vs = poisson_entropy(pp * k / kk)
    hn, vn = poisson_entropy(pp)
    return pp * math.log(kk / b) - (m * hh + hs - hn), math.sqrt(max(m * vh + vs - vn, 0.0)) or 1e-9


def cond_law(b, kmax, k, pp):
    kk = kmax + 1
    m = kk - max(k, 1)
    if pp == 0:
        return 0.0, 1e-9
    a = cell_moments(pp / kk, -math.log(kk))
    s = cell_moments(pp * k / kk, math.log(k / kk))
    ex = m * a[0] + s[0]
    vx = m * a[1] + s[1]
    cx = m * a[2] + s[2]
    v = max(vx - cx * cx / pp, 0.0)
    # E[-ln P_mult] = E X - ln pp!; ln E = ln P_mult + pp ln(kk / b)
    mean = -(ex - math.lgamma(pp + 1)) + pp * math.log(kk / b)
    return mean, math.sqrt(v) or 1e-9


def ln_e(b, k, pp, rf, lneed):
    return math.lgamma(pp + 1) + rf * math.log(k) - lneed - math.lgamma(rf + 1) - pp * math.log(b)


def read_traces(path):
    """Yield (d, kmax, weight, [(k, pp, rf, lneed)]) per planted string."""
    for line in open(path):
        f = line.split()
        d, kmax, wgt = int(f[0]), int(f[1]), float(f[2])
        if wgt == 0:
            yield d, kmax, 0.0, []
            continue
        recs = [tuple(map(float, r.split(','))) for r in f[3:]]
        yield d, kmax, wgt, [(int(k), int(pp), int(rf), ln) for k, pp, rf, ln in recs]
