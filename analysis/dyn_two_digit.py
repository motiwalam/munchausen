"""Two-digit solutions: bases with two of them (question 13) and 2-digit
cores in perfect-power bases with a self-paying digit (question 16).

A 2-digit string (a, c) is a solution in base b = (a^a + g(c)) / a, where
g(c) = w(c) - c, w(c) = c^c and w(0) = m (Proposition 2.6).

Part 1 lists every base that has two 2-digit solutions, for leading digits
up to A and last digits up to C, under both conventions, and checks the
inequalities used in the proof of Theorem 13.1 on a grid.

Part 2 lists the 2-digit solutions whose base is a perfect power r^t with a
self-paying digit (by Proposition 15.8: t has a prime factor that does not
divide r), and marks the swaps c = a^a.

usage: python3 analysis/dyn_two_digit.py [A] [C]
"""
import sys
from collections import defaultdict

import gmpy2
from sympy import primefactors

A = int(sys.argv[1]) if len(sys.argv) > 1 else 40
C = int(sys.argv[2]) if len(sys.argv) > 2 else 400


def g(c, m):
    return (m if c == 0 else c ** c) - c


def two_digit(m):
    """All 2-digit solutions (a, c, b) with a <= A, c <= C."""
    out = []
    for a in range(1, A + 1):
        aa = a ** a
        for c in range(0, C + 1):
            gm = (m - c) % a if c == 0 else (pow(c, c, a) - c) % a
            if (aa + gm) % a:
                continue
            num = aa + g(c, m)
            if num % a:
                continue
            b = num // a
            if b > max(a, c):
                out.append((a, c, b))
    return out


def part1():
    print('Part 1: bases with two 2-digit solutions, a <= %d, c <= %d' % (A, C))
    for m in (0, 1):
        by_base = defaultdict(list)
        for a, c, b in two_digit(m):
            by_base[b].append((a, c))
        multi = {b: v for b, v in by_base.items() if len(v) >= 2}
        twins = [b for b, v in multi.items() if sorted(v) == [(v[0][0], 0), (v[0][0], 1)]]
        other = {b: v for b, v in multi.items() if b not in twins}
        print(f'  0^0 = {m}: {len(by_base)} bases with a 2-digit solution; '
              f'{len(multi)} with two or more; twins (a,0),(a,1): {len(twins)}; others: {other}')
    # the inequalities of the proof, for 2 <= A' <= 60 and 1 <= a < A'
    bad = 0
    for Ap in range(2, 61):
        g_lo = (Ap - 1) ** (Ap - 1) - (Ap - 1)          # g(A'-1)
        g_hi = (Ap + 1) ** (Ap + 1) - (Ap + 1)          # g(A'+1)
        for a in range(1, Ap):
            low = a * Ap ** (Ap - 1) - a ** a           # lower bound for g(c)
            high = (a * Ap ** (Ap - 1) - a ** a) * Ap // (Ap - a) + 1  # upper bound for g(c)
            if not (low > g_lo and high < g_hi):
                bad += 1
            # last step: A'^(A'-1) (2a - A') = a^a + a - A' has no solution with a < A' < 2a
            if a < Ap < 2 * a and Ap ** (Ap - 1) * (2 * a - Ap) == a ** a + a - Ap:
                bad += 1
    print(f'  proof inequalities violated on the grid A\' <= 60: {bad}')


def power_decomp(n):
    """(r, t) with n = r^t and r not a perfect power, or None if n is not a power."""
    n = gmpy2.mpz(n)
    if not gmpy2.is_power(n):
        return None
    r, t = n, 1
    changed = True
    while changed:
        changed = False
        for p in range(2, int(gmpy2.bit_length(r)) + 1):
            if not gmpy2.is_prime(p):
                continue
            root, exact = gmpy2.iroot(r, p)
            if exact:
                r, t = root, t * p
                changed = True
                break
    return int(r), t


def self_paying(r, t):
    """Self-paying digits r^s of base r^t with their positions (Proposition 2.2)."""
    return [(s, s * (r ** s - 1) // t) for s in range(1, t) if (s * (r ** s - 1)) % t == 0] if t < 400 else None


def part2():
    print('Part 2: 2-digit solutions in perfect-power bases, a <= %d, c <= %d, 0^0 = 0' % (A, C))
    rows = []
    for a, c, b in two_digit(0):
        if c in (0, 1) and b == a ** (a - 1):
            continue  # (a,0), (a,1): the self-paying digit a itself, not a core
        pd = power_decomp(b)
        if pd is None:
            continue
        r, t = pd
        has_sp = any(p for p in primefactors(t) if r % p)
        rows.append((a, c, r, t, has_sp, c == a ** a))
    for a, c, r, t, sp, swap in rows:
        tag = 'swap' if swap else ''
        print(f'  (a, c) = ({a}, {c}): base {r}^{t}; self-paying digit: {sp} {tag}')
    nonswap = [x for x in rows if x[4] and not x[5]]
    print(f'  perfect-power bases: {len(rows)}; with a self-paying digit: {sum(1 for x in rows if x[4])}; '
          f'of those not swaps: {len(nonswap)}')


if __name__ == '__main__':
    part1()
    part2()
