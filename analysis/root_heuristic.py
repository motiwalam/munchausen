"""Expected number of short solutions from the integer-root heuristic.

A k-digit string s is a solution in base b exactly when b is a root of
P_s(b) = sum s_i b^i - F(s) and b exceeds every digit. P_s is increasing for
b >= 1 when the leading digit is positive, so there is at most one real root
b* > max digit. Treat the event "b* is an integer" as having probability
1 / P_s'(b*), the spacing of P_s near its root. Summing over strings gives
the expected number of k-digit solutions with digits up to a bound, which is
compared with the solutions actually found (data/k<k>.txt).
"""
import itertools
import math
import sys
from collections import Counter


def w(x, mode):
    return mode if x == 0 else x ** x


def root(s, F):
    """Real root b* of P_s(b) = F with b* > max(s), or None. s: most significant first."""
    lo = max(s) + 1
    P = lambda b: sum(c * b ** (len(s) - 1 - i) for i, c in enumerate(s))
    if P(lo) > F:
        return None
    hi = lo
    while P(hi) < F:
        hi *= 2
    x0, x1 = float(lo), float(hi)
    for _ in range(200):
        m = (x0 + x1) / 2
        if P(m) < F:
            x0 = m
        else:
            x1 = m
    return (x0 + x1) / 2


def expected(k, X, mode):
    e = 0.0
    by_max = Counter()
    for s in itertools.product(range(X + 1), repeat=k):
        if s[0] == 0:
            continue
        F = sum(w(x, mode) for x in s)
        r = root(s, F)
        if r is None:
            continue
        dP = sum((k - 1 - i) * c * r ** (k - 2 - i) for i, c in enumerate(s[:-1]))
        p = min(1.0, 1.0 / dP)
        e += p
        by_max[max(s)] += p
    return e, by_max


def observed(k, X, mode):
    out = []
    for line in open(f'data/k{k}.txt'):
        if line.startswith('#'):
            continue
        kk, m, b, ds = line.split()
        ds = tuple(map(int, ds.split(',')))
        if int(m) == mode and max(ds) <= X:
            out.append((int(b), ds))
    return out


if __name__ == '__main__':
    for k, X in ((3, 60), (4, 22), (5, 11)):
        for mode in (1, 0):
            e, by_max = expected(k, X, mode)
            obs = observed(k, X, mode)
            tail = sum(v for x, v in by_max.items() if x > X // 2)
            print(f"k={k}, digits <= {X}, 0^0={mode}: expected {e:.2f}, observed {len(obs)}; "
                  f"expected with largest digit > {X // 2}: {tail:.2e}", flush=True)
