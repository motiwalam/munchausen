"""Integer-root heuristic with local factors, for short solutions.

For a k-digit string s, Q_s(x) = sum s_i x^i - F(s) has integer
coefficients, and s is a solution in base b exactly when Q_s(b) = 0 with
b > max(s). If Q_s has no root modulo some prime p, no base works: a proven
local obstruction. Otherwise the chance that the real root is an integer is
taken as prod_p rho_s(p) / Q_s'(b*), where rho_s(p) is the number of roots
of Q_s mod p (its average over random polynomials is 1).
"""
import itertools
import sys
from collections import Counter
from root_heuristic import w, root, observed

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]


def rho(s, F, p):
    k = len(s)
    Fp = F % p
    cnt = 0
    for r in range(p):
        v = 0
        for c in s:
            v = (v * r + c) % p
        if v == Fp:
            cnt += 1
    return cnt


def run(k, X, mode):
    e_plain = e_local = 0.0
    strings = blocked = 0
    for s in itertools.product(range(X + 1), repeat=k):
        if s[0] == 0:
            continue
        F = sum(w(x, mode) for x in s)
        r = root(s, F)
        if r is None:
            continue
        strings += 1
        dP = sum((k - 1 - i) * c * r ** (k - 2 - i) for i, c in enumerate(s[:-1]))
        S = 1.0
        for p in PRIMES:
            S *= rho(s, F, p)
            if S == 0:
                break
        if S == 0:
            blocked += 1
        e_plain += min(1.0, 1.0 / dP)
        e_local += min(1.0, S / dP)
    return strings, blocked, e_plain, e_local


if __name__ == '__main__':
    for k, X in ((3, 60), (4, 22), (5, 11)):
        for mode in (1, 0):
            strings, blocked, ep, el = run(k, X, mode)
            print(f"k={k}, digits <= {X}, 0^0={mode}: {strings} strings with a root above their digits, "
                  f"{blocked} ({blocked / strings:.0%}) have no root mod some p <= 31; "
                  f"expected solutions: plain {ep:.2f}, with local factors {el:.2f}; observed {len(observed(k, X, mode))}",
                  flush=True)
