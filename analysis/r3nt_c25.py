"""Question 51: the equation b(b+x) = x^n + 25, the family (1, x, 3).

Section 4 of the round 3 draft. For odd x prime to 5, D = x^2 + 100 and
theta = (x + sqrt D)/2 (norm -25). The script checks:

1. the identities (theta - 5)^2 / theta = sqrt(D) - 10 and
   l = artanh(10 / sqrt D) = arcsinh(10 / x), and the bounds
   10 - 1000/(6 x^2) < x l < 10 - 1000/(6 x^2) + 7500/x^4 (x >= 11);
2. the gap of Proposition 4.4: for s = 1..20, how close s mu can come to 10
   for mu in M = {arcsinh(y/2)} u {arccosh(y/2)}, the possible logarithms of
   a fundamental unit of a real quadratic field;
3. the constant of Theorem 4.5, part A (Laurent);
4. for x = 5^e: the norms of the convergents of sqrt(y^2 + 4), y = 5^(e-1),
   used in Proposition 4.6.

usage: python3 analysis/r3nt_c25.py
"""
from fractions import Fraction
from math import isqrt

from mpmath import acosh, asinh, atanh, log, mp, mpf, sqrt

mp.dps = 50


def part1():
    worst_lo = worst_hi = mpf(1)
    for x in list(range(11, 2000, 2)) + [10 ** 4 + 1, 10 ** 6 + 3, 10 ** 9 + 7]:
        if x % 5 == 0:
            continue
        D = x * x + 100
        th = (x + sqrt(D)) / 2
        e1 = (th - 5) ** 2 / th - (sqrt(D) - 10)
        assert abs(e1) < mpf(10) ** -40, x
        l1, l2 = atanh(10 / sqrt(D)), asinh(mpf(10) / x)
        assert abs(l1 - l2) < mpf(10) ** -40, x
        g = x * l2
        lo = 10 - mpf(1000) / (6 * x * x)
        hi = lo + mpf(7500) / x ** 4
        assert lo < g < hi, x
    print('part 1: identities and bounds for x l hold for odd x in [11, 2000) prime to 5 and three large x')


def mu_values(target, s):
    """Elements s mu with mu in M nearest to target, from below and above."""
    out = []
    # arcsinh(y/2): y near 2 sinh(target/s)
    from mpmath import sinh, cosh
    y0 = int(2 * sinh(mpf(target) / s))
    for y in range(max(1, y0 - 3), y0 + 4):
        out.append((s * asinh(mpf(y) / 2), 'arcsinh', y))
    y1 = int(2 * cosh(mpf(target) / s))
    for y in range(max(3, y1 - 3), y1 + 4):
        out.append((s * acosh(mpf(y) / 2), 'arccosh', y))
    return out


def part2():
    best = None
    for s in range(1, 21):
        vals = mu_values(10, s)
        below = max((v for v in vals if v[0] < 10), key=lambda v: v[0], default=None)
        above = min((v for v in vals if v[0] > 10), key=lambda v: v[0], default=None)
        gap_b = 10 - below[0] if below else None
        gap_a = above[0] - 10 if above else None
        g = min(t for t in (gap_b, gap_a) if t is not None)
        if best is None or g < best[0]:
            best = (g, s, below if gap_b == g else above)
        print(f'  s = {s:2d}: below 10 by {float(gap_b):.3e} ({below[1]} {below[2]}), '
              f'above by {float(gap_a):.3e} ({above[1]} {above[2]})')
    print(f'part 2: smallest gap {float(best[0]):.3e} at s = {best[1]} ({best[2][1]}, y = {best[2][2]})')
    # x with 1000/(6x^2) below the smallest gap
    X1 = int(sqrt(mpf(1000) / 6 / best[0])) + 1
    print(f'  1000/(6 x^2) < smallest gap for x >= {X1}')


def part3():
    # nu < 2 + 403.3 (log(1.0001 nu) + 0.38)^2, with M >= 5
    def rhs(nu):
        M = max(log(mpf('1.0001') * nu) + mpf('0.38'), 5)
        return 2 + mpf('403.3') * M * M
    lo, hi = mpf(1000), mpf(10 ** 6)
    while hi - lo > 1:
        mid = (lo + hi) / 2
        if rhs(mid) > mid:
            lo = mid
        else:
            hi = mid
    print(f'part 3: Laurent leaves nu = n / max(mu0, 1) < {float(hi):.0f}; with n > (mu0 - 1e-8) x / 10.0001 '
          f'this gives x < {float(hi * mpf("10.0001") / (1 - mpf(10) ** -8)):.0f} when mu0 >= 1')


def cf_sqrt(D, nterms):
    a0 = isqrt(D)
    m, d, a = 0, 1, a0
    out = [a0]
    for _ in range(nterms):
        m = d * a - m
        d = (D - m * m) // d
        a = (a0 + m) // d
        out.append(a)
    return out


def part4():
    for e in (2, 3, 4, 5, 6, 7):
        y = 5 ** (e - 1)
        D = y * y + 4
        cf = cf_sqrt(D, 12)
        p0, q0, p1, q1 = 1, 0, cf[0], 1
        norms = [p1 * p1 - D * q1 * q1]
        for a in cf[1:]:
            p0, q0, p1, q1 = p1, q1, a * p1 + p0, a * q1 + q0
            norms.append(p1 * p1 - D * q1 * q1)
        print(f'part 4: e = {e}, y = {y}: cf of sqrt(y^2+4) starts {cf[:7]}; convergent norms {sorted(set(norms))}')


if __name__ == '__main__':
    part1()
    part2()
    part3()
    part4()
