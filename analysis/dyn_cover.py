"""Covering congruences with prime powers, longer strings and two parameters.

Extends analysis/cover.py (question 14). A family fixes all digits of a
k-digit string but one (x) or two (x, y). For a prime power q = p^e,
Q_s(r) = sum s_i r^i - F(s) mod q depends on a varying digit x only through
x mod q and x^x mod q, so through x mod P(q) = lcm(q, lambda(q)) once
x >= e. If Q_s has no root mod q, the string is not a solution in any base.
A family is covered if every class of its parameters is excluded by some q.

By Proposition 14.1 the congruences of section 1.6 exclude a string in
every base exactly when Q_s has no root mod 2. The script reports for each
covered family a minimal set of moduli (greedy, then pruned) and whether
parity alone covers it.

Small parameter values (below the largest exponent e) are checked exactly.

usage: python3 analysis/dyn_cover.py <k> <fixed digit bound> <m> [two]
"""
import math
import sys
from itertools import product

import numpy as np

QS = [2, 4, 8, 16, 32, 3, 9, 27, 5, 25, 7, 49, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
CAP = 4_000_000


def carmichael(q):
    p = min(d for d in range(2, q + 1) if q % d == 0)
    e = round(math.log(q, p))
    if p == 2:
        return 1 if e == 1 else 2 if e == 2 else 2 ** (e - 2)
    return (p - 1) * p ** (e - 1)


def period(q):
    return q * carmichael(q) // math.gcd(q, carmichael(q))


def wmod(xs, q, m):
    """x^x mod q for an array of representatives x (all >= 6, or the digit itself if 0)."""
    return np.array([pow(int(x), int(x), q) if x else m % q for x in xs], dtype=np.int64)


def excluded_1(fixed, pos, q, m):
    """Boolean array over x mod P(q): True if Q has no root mod q (and the
    residues r of the roots that would exist otherwise do not matter)."""
    P = period(q)
    k = len(fixed) + 1
    reps = np.arange(P) + 6 * P  # representatives >= 6 > e
    r = np.arange(q)
    A = np.zeros(q, dtype=np.int64)
    F0 = 0
    j = 0
    for i in range(k):
        if i == pos:
            continue
        d = fixed[j]
        j += 1
        A = (A + d * pow_arr(r, k - 1 - i, q)) % q
        F0 += (pow(d, d, q) if d else m) % q
    rp = pow_arr(r, k - 1 - pos, q)
    lhs = (A[None, :] + (reps % q)[:, None] * rp[None, :]) % q
    rhs = (wmod(reps, q, m) + F0) % q
    hit = (lhs == rhs[:, None])
    return ~hit.any(axis=1), hit


def pow_arr(r, e, q):
    out = np.ones_like(r) % q
    for _ in range(e):
        out = (out * r) % q
    return out


def cover_1(fixed, pos, m, qs=QS):
    """Greedy covering of one parameter. Returns (covered, moduli used, density left)."""
    ex = {q: excluded_1(fixed, pos, q, m)[0] for q in qs}
    L, alive = 1, np.ones(1, dtype=bool)
    used = []
    remaining = [q for q in qs if ex[q].any()]
    while remaining and alive.any():
        best, best_score = None, -1
        for q in remaining:
            P = period(q)
            L2 = L * P // math.gcd(L, P)
            if L2 > CAP:
                continue
            a2 = np.tile(alive, L2 // L) & np.tile(~ex[q], L2 // P)
            score = 1 - a2.mean() / max(alive.mean(), 1e-300)
            if score > best_score:
                best, best_score, best_a, best_L = q, score, a2, L2
        if best is None or best_score <= 0:
            break
        alive, L = best_a, best_L
        used.append(best)
        remaining.remove(best)
    return (not alive.any()), used, alive.mean()


def is_covered_by(fixed, pos, m, qs):
    ex = {q: excluded_1(fixed, pos, q, m)[0] for q in qs}
    L = 1
    for q in qs:
        L = L * period(q) // math.gcd(L, period(q))
    alive = np.ones(L, dtype=bool)
    for q in qs:
        alive &= np.tile(~ex[q], L // period(q))
    return not alive.any()


def minimal(fixed, pos, m, used):
    """Drop moduli from a covering set while it still covers."""
    cur = list(used)
    for q in list(used):
        trial = [x for x in cur if x != q]
        if trial and is_covered_by(fixed, pos, m, trial):
            cur = trial
    return cur


def parity_only(fixed, pos, m):
    """True if q = 2 alone covers the family. By Proposition 14.1 these are
    exactly the families that the congruences of section 1.6 exclude."""
    return bool(excluded_1(fixed, pos, 2, m)[0].all())


def exact_small(fixed, pos, m, xmax=8):
    """Exact check: values x < xmax for which the string is a solution in some base."""
    out = []
    for x in range(1 if pos == 0 else 0, xmax):
        s = list(fixed)
        s.insert(pos, x)
        F = sum((d ** d if d else m) for d in s)
        lo = max(s) + 1
        if lo < 2:
            lo = 2
        val = lambda b: sum(d * b ** (len(s) - 1 - i) for i, d in enumerate(s))
        if val(lo) > F:
            continue
        hi = lo
        while val(hi) < F:
            hi *= 2
        while lo < hi:
            mid = (lo + hi) // 2
            if val(mid) < F:
                lo = mid + 1
            else:
                hi = mid
        if val(lo) == F:
            out.append((x, lo))
    return out


def main_1(k, fmax, m):
    fams = 0
    covered = []
    for pos in range(k):
        for fixed in product(range(fmax + 1), repeat=k - 1):
            if pos != 0 and fixed[0] == 0:
                continue
            fams += 1
            ok, used, dens = cover_1(fixed, pos, m)
            if ok:
                mn = minimal(fixed, pos, m, used)
                covered.append((pos, fixed, mn, parity_only(fixed, pos, m), exact_small(fixed, pos, m)))
    beyond = [c for c in covered if not c[3]]
    print(f'k={k}, fixed digits <= {fmax}, 0^0={m}: {fams} one-parameter families, '
          f'{len(covered)} covered, {len(covered) - len(beyond)} by parity alone, '
          f'{len(beyond)} need another modulus')
    for pos, fixed, mn, par, small in beyond:
        s = list(map(str, fixed))
        s.insert(pos, 'x')
        print(f'  ({",".join(s)}): moduli {mn}; small solutions (x < 8): {small}')
    return covered


if __name__ == '__main__':
    k, fmax, m = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    main_1(k, fmax, m)
