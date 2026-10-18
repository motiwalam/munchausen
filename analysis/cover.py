"""Covering congruences for one-parameter families of short digit strings.

Fix all digits of a k-digit string but one, x, at position `pos`. The
polynomial Q_x(r) = sum s_i r^i - F(s) mod p depends on x only through
x mod p and x^x mod p, so through x mod p(p-1). If Q_x has no root mod p,
the string is not a solution in any base. If the classes of x excluded this
way, over several primes, cover all integers, the family has no solution at
all: a proof by covering congruences.

The script tracks the classes of x mod L = lcm(p(p-1)) that no prime has
excluded yet, adding primes one at a time.
"""
import math
import sys
from itertools import product

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def w_mod(x, p, mode):
    if x == 0:
        return mode % p
    return pow(x % p, x, p) if x % p else 0


def excluded(fixed, pos, p, mode):
    """Set of x mod p(p-1) for which Q_x has no root mod p (x >= 1 in the class)."""
    m = p * (p - 1)
    k = len(fixed) + 1
    out = set()
    for x in range(m, 2 * m):  # representatives >= m so x^x behaves like large x
        s = list(fixed)
        s.insert(pos, x)
        F = sum(w_mod(v, p, mode) for v in s) % p
        ok = False
        for r in range(p):
            v = 0
            for c in s:
                v = (v * r + c) % p
            if v == F:
                ok = True
                break
        if not ok:
            out.add(x % m)
    return out


def uncovered_density(fixed, pos, mode, primes=PRIMES, cap=2_000_000):
    """Density of x not excluded by any of the primes, and whether it reached 0."""
    L, alive = 1, [0]
    for p in primes:
        m = p * (p - 1)
        ex = excluded(fixed, pos, p, mode)
        if not ex:
            continue
        L2 = L * m // math.gcd(L, m)
        if len(alive) * (L2 // L) > cap:
            # too many classes to track exactly: estimate by independence
            return len(alive) / L * (1 - len(ex) / m), False, p
        new = []
        for a in alive:
            for t in range(L2 // L):
                x = a + t * L
                if x % m not in ex:
                    new.append(x)
        alive, L = new, L2
        if not alive:
            return 0.0, True, p
    return len(alive) / L, False, None


if __name__ == '__main__':
    k, fmax = int(sys.argv[1]), int(sys.argv[2])
    mode = 1
    covered = []
    dens = []
    for pos in range(k):
        for fixed in product(range(fmax + 1), repeat=k - 1):
            if pos != 0 and fixed[0] == 0:
                continue
            d, full, p = uncovered_density(fixed, pos, mode)
            dens.append(d)
            if full:
                covered.append((pos, fixed, p))
    print(f"k={k}, fixed digits <= {fmax}, 0^0={mode}: {len(dens)} families; "
          f"fully covered: {len(covered)}; median density of the classes left: {sorted(dens)[len(dens) // 2]:.2e}")
    for c in covered[:40]:
        print("  covered:", c)
