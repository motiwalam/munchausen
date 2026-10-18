"""The coupled model of question 22: means, the Chen-Stein error, correlation.

The coupled model (draft complexity-and-poisson.md, section 2.1): for each
upper part u = (c_2, ..., c_{b-1}) let V(u) = sum c_x x^x and let Y_u be a
uniform random number with as many digits as V(u) and, in the refined
model, with Y_u = V(u) (mod b-1). The multiset c = (c_0, c_1, u) is a model
solution under convention m when the digits of Y_u + c_1 + m c_0 form c.

For each base this script estimates by sampling:
- lam_s, lam_0, lam_1: expected numbers of zero-free solutions (shared by
  both conventions) and of solutions with a zero under m = 0 and m = 1;
- b2 = sum_alpha p_alpha Gamma_alpha, the expected number of ordered pairs
  of distinct model solutions that share an upper part, split into twins
  (delta = +-1 on a last digit 0/1) and other pairs.

Sampling: draw the top d-1 digits of a d-digit string uniformly (leading
digit nonzero) and sum exactly over the last digit x. Given the multiset,
the arrangement is uniform, as the model requires.

Usage:
    python thy_poisson.py means B0 B1 [SAMPLES]   # per-base table
    python thy_poisson.py corr                    # sample correlation, bases 10-41
"""
import math
import sys

import numpy as np

RNG = np.random.default_rng(22)
JMAX = 14          # lengths d = b - JMAX .. b; the rest is below 1e-4 in the limit


def rho(b, m):
    q = b - 1
    return np.array([((pow(x, x, q) if x > 0 else m) - x) % q for x in range(b)], dtype=np.int64)


def change(s, delta, b):
    """Digits removed and added when delta is added to the digit list s (low first).

    Returns None if the carry or borrow reaches the leading digit.
    """
    removed, added = [], []
    i, carry = 0, delta
    while carry != 0:
        if i >= len(s) - 1:
            return None
        v = s[i] + carry
        carry, nv = divmod(v, b)
        if nv != s[i]:
            removed.append(s[i])
            added.append(nv)
        i += 1
    return removed, added


def partners(s, c0, c1, j, b):
    """Model solutions other than alpha in alpha's cluster, given the string s.

    alpha is a solution with string s = Y_u + j. A partner beta has
    j_beta = j + delta and the digits of s + delta form c_beta, with the same
    upper part. Returns (twins, others).
    """
    twins = others = 0
    for delta in range(-2 * b - 2, 2 * b + 3):
        if delta == 0:
            continue
        ch = change(s, delta, b)
        if ch is None:
            continue
        rem, add = ch
        if sorted(x for x in rem if x >= 2) != sorted(x for x in add if x >= 2):
            continue
        n0 = c0 - rem.count(0) + add.count(0)
        n1 = c1 - rem.count(1) + add.count(1)
        jb = j + delta
        hits = 0
        if n1 == jb:
            hits += 1
        if n0 > 0 and n1 + n0 == jb:
            hits += 1
        if hits:
            if abs(delta) == 1 and len(rem) == 1 and {rem[0], add[0]} == {0, 1}:
                twins += hits
            else:
                others += hits
    return twins, others


def base_stats(b, samples, refined=True, pairs=True):
    q = b - 1
    x = np.arange(b, dtype=float)
    logw = np.where(x >= 2, x * np.log(np.maximum(x, 1)), -np.inf)
    rh = [rho(b, 0), rho(b, 1)]
    out = dict(ls=0.0, l0=0.0, l1=0.0, tw=0.0, ot=0.0)
    for d in range(max(3, b - JMAX), b + 1):
        scale = (d - 1) * math.log(b)
        w = np.exp(np.minimum(logw - scale, 700.0))     # V contribution / b^(d-1)
        n = samples
        top = RNG.integers(0, b, size=(n, d - 1))
        top[:, -1] = RNG.integers(1, b, size=n)          # leading digit
        counts = np.zeros((n, b), dtype=np.int64)
        for col in range(d - 1):
            np.add.at(counts, (np.arange(n), top[:, col]), 1)
        vpart = counts @ w
        res = [counts @ rh[m] for m in (0, 1)]
        V = vpart[:, None] + w[None, :]                  # n x b, last digit x
        lenok = (V >= 1.0) & (V < b)
        okm = []
        for m in (0, 1):
            r = (res[m][:, None] + rh[m][None, :]) % q
            okm.append(lenok & ((r == 0) if refined else True))
        weight = (q if refined else 1.0) / b / n
        c0 = counts[:, 0][:, None] + (x[None, :] == 0)
        zero_free = (c0 == 0)
        out['ls'] += weight * np.count_nonzero(okm[0] & zero_free)
        out['l0'] += weight * np.count_nonzero(okm[0] & ~zero_free)
        out['l1'] += weight * np.count_nonzero(okm[1] & ~zero_free)
        if not pairs:
            continue
        rows, cols = np.nonzero(okm[0] | okm[1])
        for r_, xv in zip(rows, cols):
            s = [int(xv)] + [int(v) for v in top[r_]]
            cc0 = int(counts[r_, 0]) + (xv == 0)
            cc1 = int(counts[r_, 1]) + (xv == 1)
            js = []
            if cc0 == 0:
                js.append(cc1)
            else:
                if okm[0][r_, xv]:
                    js.append(cc1)
                if okm[1][r_, xv]:
                    js.append(cc1 + cc0)
            for j in js:
                t, o = partners(s, cc0, cc1, j, b)
                out['tw'] += weight * t
                out['ot'] += weight * o
    return out


def means(b0, b1, samples):
    print("base   lam_s   lam_0   lam_1    N0 mean  N1 mean  corr   b2 twins  b2 other  b*b2/lam")
    for b in range(b0, b1 + 1):
        st = base_stats(b, samples)
        lam = st['ls'] + st['l0'] + st['l1']
        n0, n1 = st['ls'] + st['l0'], st['ls'] + st['l1']
        corr = st['ls'] / math.sqrt(n0 * n1)
        b2 = st['tw'] + st['ot']
        print(f"{b:4d}  {st['ls']:6.3f}  {st['l0']:6.3f}  {st['l1']:6.3f}   {n0:6.3f}   {n1:6.3f}  {corr:5.3f}"
              f"   {st['tw']:7.4f}   {st['ot']:7.4f}   {b * b2 / lam:6.2f}", flush=True)


def corr(samples=4000, sims=200_000):
    """Distribution of the sample correlation over bases 10-41 in the model."""
    sys.path.insert(0, '.')
    from catalog import exhaustive_bases
    sols = exhaustive_bases()
    lams = []
    obs0, obs1 = [], []
    for b in range(10, 42):
        st = base_stats(b, samples, pairs=False)
        lams.append((st['ls'], st['l0'], st['l1']))
        obs0.append(len(sols[(0, b)]))
        obs1.append(len(sols[(1, b)]))
    lams = np.array(lams)
    zs = RNG.poisson(lams[None, :, 0], size=(sims, len(lams)))
    z0 = RNG.poisson(lams[None, :, 1], size=(sims, len(lams)))
    z1 = RNG.poisson(lams[None, :, 2], size=(sims, len(lams)))
    a, c = zs + z0, zs + z1
    a = a - a.mean(axis=1, keepdims=True)
    c = c - c.mean(axis=1, keepdims=True)
    den = np.sqrt((a * a).sum(axis=1) * (c * c).sum(axis=1))
    ok = den > 0
    r = (a * c).sum(axis=1)[ok] / den[ok]
    ro = np.corrcoef(obs0, obs1)[0, 1]
    tot = lams.sum(axis=0)
    print(f"model totals, bases 10-41: shared {tot[0]:.2f}, zero under 0^0=0 {tot[1]:.2f}, "
          f"zero under 0^0=1 {tot[2]:.2f}")
    print(f"observed: N0 {sum(obs0)}, N1 {sum(obs1)}; correlation {ro:.3f}")
    print(f"model sample correlation: mean {r.mean():.3f}, median {np.median(r):.3f}, "
          f"5%-95% {np.quantile(r, 0.05):.3f} to {np.quantile(r, 0.95):.3f}, "
          f"P(r >= observed) {np.mean(r >= ro):.3f}")


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'means'
    if what == 'means':
        means(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 4000)
    elif what == 'corr':
        corr()
