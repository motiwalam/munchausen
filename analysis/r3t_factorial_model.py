"""The model for Munchausen numbers in the factorial number system (question 62).

E_L = P(L! <= F(n) < (L+1)!) for n uniform in [L!, (L+1)!), that is, for
independent digits d_i uniform on [0, i] (i < L) and d_L uniform on [1, L].
The largest digit v decides the size of F: F >= v^v, and F <= L v^v. So only
the few v with v^v < (L+1)! and L v^v >= L! contribute. For each such v the
script computes P(max digit = v) exactly and P(F in window | max = v) by
sampling (rejection on max = v), with F in floating point.
usage: python3 r3t_factorial_model.py [Lmax] [samples]
"""
import sys
import numpy as np
from math import lgamma, log

Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 120
S = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
rng = np.random.default_rng(62)


def pmax_le(L, v):
    """P(all digits <= v), digits uniform on [0, i] for i < L, [1, L] at L."""
    if v < 1:
        return 0.0
    p = min(L, v) / L
    for i in range(1, L):
        p *= (min(i, v) + 1) / (i + 1)
    return p


def sample(L, v, m, n):
    """n strings with every digit <= v and at least one digit = v; returns F."""
    out = []
    caps = np.array([min(i, v) for i in range(1, L)], dtype=np.int64)
    w = np.array([float(m)] + [float(d) ** d for d in range(1, v + 1)])
    while sum(len(o) for o in out) < n:
        k = 2 * n
        low = (rng.random((k, L - 1)) * (caps + 1)).astype(np.int64)
        top = 1 + (rng.random(k) * min(L, v)).astype(np.int64)
        mx = np.maximum(low.max(axis=1), top)
        keep = mx == v
        f = w[low[keep]].sum(axis=1) + w[top[keep]]
        out.append(f)
    return np.concatenate(out)[:n]


print(f"# model E_L for the factorial number system, {S} samples per (L, v)")
tot = {0: 0.0, 1: 0.0}
for L in range(2, Lmax + 1):
    lo = lgamma(L + 1)      # ln L!
    hi = lgamma(L + 2)      # ln (L+1)!
    row = {}
    for m in (0, 1):
        e = 0.0
        for v in range(1, L + 1):
            lv = v * log(v)
            if lv >= hi or log(L) + lv < lo - log(2):
                continue
            pv = pmax_le(L, v) - pmax_le(L, v - 1)
            if pv <= 0:
                continue
            f = sample(L, v, m, S)
            lf = np.log(f)
            e += pv * np.mean((lf >= lo) & (lf < hi))
        row[m] = e
        tot[m] += e
    print(f"L {L} E0 {row[0]:.4e} E1 {row[1]:.4e} cum0 {tot[0]:.4f} cum1 {tot[1]:.4f}", flush=True)
