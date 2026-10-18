"""Question 46: the sets T(q) = { x^x - x mod q : x >= 1 } for prime powers q.

For q = p^e, x^x - x mod q depends only on x mod p^e (p - 1) once x >= e,
so x in [1, p^e (p - 1) + e] gives all of T(q). The script compares T(q)
with the laws of section 2 of the round 3 draft:

- p >= 7: T(p^e) = Z/p^e (Theorem 2.3);
- p = 5: T(5^e) = {v : v != 3 mod 5} together with the residues
  A (1 - 25 s / 2) mod 5^e for s a square, where A = 1 - i and i is the
  5-adic square root of -1 with i == 3 mod 5 (Theorem 2.5);
- p = 3: T(3^e) = 3Z together with the v == 2 mod 27, v != 56 mod 81, for
  e >= 4 (Theorem 2.4);
- p = 2: the even residues (Lemma 15.12).

It also checks the lifting Lemma 2.1 class by class, and the first
coefficients of the series of Lemma 2.2.

usage: python3 analysis/r3nt_tq.py
"""
from fractions import Fraction
from math import comb, factorial


def T(p, e):
    q = p ** e
    per = q * (p - 1)
    return {(pow(x, x, q) - x) % q for x in range(1, per + e + 1)}


def sqrt_minus1(e):
    """i mod 5^e with i^2 = -1, i == 3 mod 5 (Hensel)."""
    i = 3
    for k in range(2, e + 1):
        q = 5 ** k
        # i -> i - (i^2 + 1) / (2 i)
        i = (i - (i * i + 1) * pow(2 * i, -1, q)) % q
    return i % 5 ** e


def squares_mod(q):
    return {(s * s) % q for s in range(q)}


def law5(e):
    q = 5 ** e
    out = {v for v in range(q) if v % 5 != 3}
    if e == 1:
        return out | {3}
    A = (1 - sqrt_minus1(e)) % q
    half = pow(2, -1, q)
    for s in squares_mod(5 ** (e - 2)) if e > 2 else {0}:
        # s is defined mod 5^(e-2); 25 s is then defined mod 5^e
        out.add(A * (1 - 25 * s * half) % q)
    return out


def law3(e):
    q = 3 ** e
    out = {v for v in range(q) if v % 3 == 0}
    if e == 1:
        return out | {2}
    if e == 2:
        return out | {2}
    if e == 3:
        return out | {2}
    return out | {v for v in range(q) if v % 27 == 2 and v % 81 != 56}


def lift_check(p, e):
    """Lemma 2.1: a class x0 mod p(p-1) with x0 prime to p and x0^x0 != 1 mod p
    has image f(x0) + pZ mod p^e."""
    q = p ** e
    per = q * (p - 1)
    bad = []
    for x0 in range(1, p * (p - 1) + 1):
        if x0 % p == 0 or pow(x0, x0, p) == 1:
            continue
        img = {(pow(x, x, q) - x) % q for x in range(x0, per + x0 + 1, p * (p - 1))}
        if len(img) != p ** (e - 1):
            bad.append(x0)
    return bad


def series_coeffs(zeta_num, nmax, modulus=None):
    """c_n = (S_n - zeta) / n! with S_n = sum_{m=0}^n C(n,m) zeta^m m^(n-m), 0^0 = 1.

    zeta_num is an integer standing for zeta in the ring considered
    (-1 exactly, or i mod 5^K)."""
    out = []
    for n in range(nmax + 1):
        S = sum(comb(n, m) * zeta_num ** m * (m ** (n - m) if (m or n - m) else 1)
                for m in range(n + 1))
        out.append((S - zeta_num, factorial(n)))
    return out


def main():
    print('p = 2: T(2^e) = even residues:',
          all(T(2, e) == set(range(0, 2 ** e, 2)) for e in range(1, 13)), '(e <= 12)')
    for e in range(1, 11):
        t = T(3, e)
        units = sorted(v for v in t if v % 3)
        print(f'p = 3, e = {e}: |T| = {len(t)} of {3 ** e}; law holds: {t == law3(e)}; '
              f'residues prime to 3: {units[:8]}{" ..." if len(units) > 8 else ""} ({len(units)})')
    for e in range(1, 8):
        t = T(5, e)
        cls3 = sum(1 for v in t if v % 5 == 3)
        print(f'p = 5, e = {e}: |T| = {len(t)} of {5 ** e}; hits in class 3 mod 5: {cls3} '
              f'of {5 ** (e - 1)}; law holds: {t == law5(e)}')
    for p, emax in ((7, 5), (11, 4), (13, 4), (17, 3), (19, 3), (23, 3)):
        print(f'p = {p}: T(p^e) = Z/p^e for e <= {emax}:',
              all(len(T(p, e)) == p ** e for e in range(1, emax + 1)))
    allp = [p for p in range(7, 100) if all(p % d for d in range(2, p))]
    print('T(p^2) = Z/p^2 for all primes 7 <= p < 100:', all(len(T(p, 2)) == p * p for p in allp))
    for p, e in ((3, 6), (5, 5), (7, 4), (11, 3), (13, 3)):
        print(f'Lemma 2.1 at p = {p}, e = {e}: failing classes {lift_check(p, e)}')
    # series of Lemma 2.2 with zeta = -1: c_0..c_6
    cs = series_coeffs(-1, 8)
    print('zeta = -1: c_n = (S_n + 1)/n!:', [str(Fraction(a, b)) for a, b in cs])
    # with zeta = i: work in Z[i] by hand for n <= 4
    def S_gauss(n):
        re = im = 0
        for m in range(n + 1):
            c = comb(n, m) * (m ** (n - m) if (m or n - m) else 1)
            # i^m
            r, s = [(1, 0), (0, 1), (-1, 0), (0, -1)][m % 4]
            re += c * r
            im += c * s
        return re, im
    print('zeta = i: S_n - i for n <= 5 (as a + b i):',
          [(S_gauss(n)[0], S_gauss(n)[1] - 1) for n in range(6)])


if __name__ == '__main__':
    main()
