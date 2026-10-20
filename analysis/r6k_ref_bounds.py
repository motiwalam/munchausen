"""Round 6, k-length, referee: recompute the bound X_T of Theorem K.4.

Written separately from r6k_thue_bound.gp. It reads only n, f and log eta
from data/r6k_thue_bound.txt (the unit is checked there to have norm +-1),
evaluates the inequality of Theorem K.4 with mpmath at 50 digits, scans x
on a geometric grid from 10^3 to 10^30 for the last point where it holds,
refines by bisection, and compares with the gp value. It also evaluates
the two side bounds (m = 0 by Liouville; a_1, a_2 dependent).

usage: r6k_ref_bounds.py data/r6k_thue_bound.txt
"""
import sys
from mpmath import mp, mpf, log, sqrt

mp.dps = 50
L3 = log(3)


def w(d, m):
    return m if d == 0 else d ** d


def main_gap(x, p, q, Wt, n, f, le, D):
    R = q ** 3 + 27 * p * p * (Wt + x)
    lR = log(R)
    g = 2  # residue field F_3 (fL = 1): g <= 3 - 1
    A1 = max(mpf(2) / 3 * (lR + le), L3 / D)
    A2 = max(mpf(2) / 3 * le, L3 / D)
    logaV = log(3 * f) + log(n) / 3 + x / mpf(3) * log(x)
    M = (L3 + 2 * logaV) / le + mpf(1) / 2
    bp = 1 / (D * A2) + M / (D * A1)
    C = mpf(24) * 3 * g / (2 * L3 ** 4) * D ** 4
    rhs = C * max(log(bp) + log(L3) + mpf("0.4"), 10 * L3 / D, 10) ** 2 * A1 * A2
    lhs = x / mpf(3) + mpf(3) / 2 - lR / L3
    return rhs - lhs


def m0_gap(x, p, q, Wt, n, f, le):
    R = q ** 3 + 27 * p * p * (Wt + x)
    lR = log(R)
    hbeta = (lR + le) / 3
    return 6 * (2 * hbeta + log(2)) / L3 - (x / mpf(3) + mpf(3) / 2 - lR / L3)


def last_true(fn):
    xs = [mpf(10) ** (mpf(e) / 10) for e in range(30, 301)]
    last = None
    for a, b in zip(xs, xs[1:]):
        if fn(a) >= 0 and fn(b) < 0:
            last = (a, b)
    if last is None:
        return mpf(1000) if fn(mpf(1000)) < 0 else None
    a, b = last
    for _ in range(200):
        c = (a + b) / 2
        if fn(c) >= 0:
            a = c
        else:
            b = c
    return b


def main():
    worst = 0
    for line in open(sys.argv[1]):
        if line.startswith("#"):
            continue
        t = line.split()
        p, q, r, m, n, f = map(int, t[:6])
        le = mpf(t[6])
        Xgp = int(t[10])
        Wt = w(p, m) + w(q, m) + w(r, m)
        X6 = last_true(lambda x: main_gap(x, p, q, Wt, n, f, le, 6))
        X3 = last_true(lambda x: main_gap(x, p, q, Wt, n, f, le, 3))
        Xm0 = last_true(lambda x: m0_gap(x, p, q, Wt, n, f, le))
        rel = abs(X6 - Xgp) / Xgp
        worst = max(worst, max(X6, X3, Xm0))
        print(p, q, r, m, "X_T(D=6) %.6e  gp %.6e  rel diff %.1e  D=3 %.3e  m=0 side %.1f"
              % (float(X6), Xgp, float(rel), float(X3), float(Xm0)))
    print("# largest %.6e" % float(worst))


if __name__ == "__main__":
    main()
