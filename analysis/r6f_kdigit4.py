"""4-digit factorions (p, q, s, x) with a large last digit (round 6, question 98).

The string is a factorion in base b exactly when
    G_x(b) = x!,   G_x(r) = r (p r^2 + q r + s) + x - F(t),
with F(t) = w(p) + w(q) + w(s), w = factorial, w(0) = m. For a prime l <= x,
x! == 0 (mod l), so G_x must have a root modulo l. Section 3 of the draft:
under GRH a prime l of size O((log x)^2) without a root exists unless the
Galois group of G_x fixes a root in each of its elements; for a cubic this
means that G_x has a rational root.

For every prefix with digits up to D and every x from 2 to X the script
  - decides exactly whether (p, q, s, x) is a factorion (integer root of a cubic);
  - finds the least prime l <= x at which G_x has no root modulo l;
  - lists the x without such a prime, and checks whether G_x has a rational root.

    python3 analysis/r6f_kdigit4.py 6 1500 > analysis/data/r6f_kdigit4.txt
"""
import math
import sys
from fractions import Fraction
from math import factorial

import gmpy2
import sympy

PRIMES = list(sympy.primerange(2, 2000))


def wf(d, m):
    return m if d == 0 else factorial(d)


def exact(p, q, s, x, F, fx):
    """integer b > max digit with p b^3 + q b^2 + s b + x = F + x!"""
    T = F + fx - x
    if T <= 0:
        return None
    b0 = int(gmpy2.iroot(gmpy2.mpz(T // p), 3)[0])
    for b in range(max(b0 - 3, 1), b0 + 4):
        if p * b ** 3 + q * b * b + s * b == T and b > max(p, q, s, x):
            return b
    return None


def rational_root(p, q, s, c):
    """a rational root of p r^3 + q r^2 + s r + c, or None"""
    if c == 0:
        return Fraction(0)
    for dd in sympy.divisors(p):
        for nn in sympy.divisors(abs(c)) if abs(c) < 10 ** 12 else []:
            for sg in (1, -1):
                r = Fraction(sg * nn, dd)
                if p * r ** 3 + q * r ** 2 + s * r + c == 0:
                    return r
    return None


def main():
    D = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    X = int(sys.argv[2]) if len(sys.argv) > 2 else 1500
    facts = [factorial(x) for x in range(X + 1)]
    print(f"# prefixes (p, q, s) with digits <= {D}, last digit x from 2 to {X}, both conventions")
    print("# per prefix: factorions found; max over x of the least obstructing prime; x with no obstructing prime <= x")
    worst = []
    nofree_total = [0, 0]
    nsol = 0
    hist = {}
    for m in (1, 0):
        for p in range(1, D + 1):
            for q in range(D + 1):
                for s in range(D + 1):
                    F = wf(p, m) + wf(q, m) + wf(s, m)
                    sols, free, maxl = [], [], 0
                    for x in range(2, X + 1):
                        b = exact(p, q, s, x, F, facts[x])
                        if b is not None:
                            sols.append((x, b))
                        c = x - F
                        lo = None
                        for l in PRIMES:
                            if l > x:
                                break
                            pl, ql, sl, cl = p % l, q % l, s % l, c % l
                            if all((((pl * r + ql) * r + sl) * r + cl) % l for r in range(l)):
                                lo = l
                                break
                        if lo is None:
                            rr = rational_root(p, q, s, c)
                            free.append((x, str(rr) if rr is not None else 'none'))
                        else:
                            maxl = max(maxl, lo)
                            hist[lo] = hist.get(lo, 0) + 1
                    nsol += len(sols)
                    big_free = [f for f in free if f[0] >= 50]
                    odd = [f[0] for f in free if f[1] == 'none']
                    nofree_total[0] += len(odd)
                    nofree_total[1] = max(nofree_total[1], max(odd) if odd else 0)
                    print(f"{m} ({p},{q},{s}) sols {sols} maxl {maxl} free {len(free)}: {big_free[:6]}"
                          f"{' ...' if len(big_free) > 6 else ''} | no rational root: {odd}")
                    worst.append((maxl, m, p, q, s))
                    sys.stdout.flush()
    worst.sort(reverse=True)
    print(f"# factorions found: {nsol}")
    print(f"# x without an obstructing prime and without a rational root: {nofree_total[0]}, "
          f"largest {nofree_total[1]}")
    print(f"# largest least obstructing primes: {worst[:8]}")
    print(f"# histogram of the least obstructing prime: {sorted(hist.items())[:30]}")


if __name__ == '__main__':
    main()
