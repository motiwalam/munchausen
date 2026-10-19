"""Round 5, families: census of power identities Q_s(r) = lam A(r)^j - x^x.

Under 0^0 = 1, a power identity for a k-digit string s = (t, x) is
P_s(r) - E = lam A(r)^j with j >= 2, A in Z[r] primitive of degree
d = (k-1)/j, lam a positive integer, and E = F(s) - x^x = F(t). By Theorem
1.1 of the draft the digit x must be the last one. Then r P_t(r) + C =
lam A(r)^j with C = x - F(t), so the small digits t fix A, lam and C, and
x = F(t) + C. The string is a solution in base b exactly when
x^x = lam A(b)^j with b > x.

Part 1. For every t with digits up to D (k = 3 to 7) the script finds all
(j, A, lam) with r P_t(r) + C = lam A^j for an integer C, by taking the
j-th root of the power series 1 + sum (t_i/t_0) s^i. It then decides the
condition x^x = lam y^j (y an integer) by valuations and an exact integer
root, and the condition A(b) = y: by a congruence when A is linear, and by
root tests modulo the primes up to 600 when deg A >= 2.

Part 2. The family with e = 0: (c^j, 0, ..., 0, x), x = c^(j c^j) + j - 1.
For each j the smallest c with j | x and rad(c) | j - 1, checked modulo 24
primes, and exactly for (8, 0, 0, 2^24 + 2).

    python3 analysis/r5f_identities.py > analysis/data/r5f_identities.txt
"""
import math
import sys
from fractions import Fraction
from itertools import product

import gmpy2
import sympy

sys.set_int_max_str_digits(0)

SMALL_PRIMES = list(sympy.primerange(3, 600))
BIG_PRIMES = [p for p in range(10 ** 9, 10 ** 9 + 2000) if gmpy2.is_prime(p)][:24]
BOUNDS = {3: 120, 4: 60, 5: 30, 6: 16, 7: 10}


def w(d):
    return 1 if d == 0 else d ** d


def series_root(tau, j, n):
    """R = S^(1/j) mod s^n for S = 1 + sum tau_i s^i (tau_0 = 1)"""
    a = Fraction(1, j)
    R = [Fraction(1)]
    for m in range(1, n):
        acc = Fraction(0)
        for k in range(1, m + 1):
            acc += ((a + 1) * k - m) * tau[k] * R[m - k]
        R.append(acc / m)
    return R


def poly_pow_const(B, j, n):
    """coefficient of s^n in B(s)^j, B a list of coefficients"""
    P = [Fraction(1)]
    for _ in range(j):
        Q = [Fraction(0)] * (n + 1)
        for i, u in enumerate(P):
            for k, v in enumerate(B):
                if i + k <= n:
                    Q[i + k] += u * v
        P = Q
    return P[n]


def shapes(t):
    """all (j, A, lam, C) with r P_t(r) + C = lam A(r)^j"""
    n = len(t)
    out = []
    tau = [Fraction(ti, t[0]) for ti in t] + [Fraction(0)]
    for j in range(2, n + 1):
        if n % j:
            continue
        d = n // j
        R = series_root(tau, j, n)
        if any(R[i] != 0 for i in range(d + 1, n)):
            continue
        B = R[:d + 1]
        C = t[0] * poly_pow_const(B, j, n)
        if C.denominator != 1:
            out.append((j, None, None, C))
            continue
        den = 1
        for u in B:
            den = den * u.denominator // math.gcd(den, u.denominator)
        if d >= 2 and all(B[i] == math.comb(d, i) * (B[1] / d) ** i for i in range(d + 1)):
            continue  # A is a power of a linear polynomial: the same identity with exponent j d
        Aint = [int(u * den) for u in B]  # A(r) = sum Aint[i] r^(d-i)
        g = 0
        for u in Aint:
            g = math.gcd(g, u)
        A = [u // g for u in Aint]
        lam = Fraction(t[0]) * Fraction(g, den) ** j
        assert lam.denominator == 1
        out.append((j, A, int(lam), int(C)))
    return out


def vp(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def power_condition(x, lam, j):
    """y with x^x = lam y^j, as (prime part dict, Z, exponent of Z), or None"""
    fl = sympy.factorint(lam)
    rest = x
    pp = {}
    for p, v in fl.items():
        a = vp(x, p)
        if x * a < v or (x * a - v) % j:
            return None
        pp[p] = (x * a - v) // j
        rest //= p ** a
    g = math.gcd(x, j)
    m = j // g
    if m > 1:
        Z, exact = gmpy2.iroot(gmpy2.mpz(rest), m)
        if not exact:
            return None
        Z = int(Z)
    else:
        Z = rest
    return pp, Z, x // g


def y_mod(yrep, mod):
    pp, Z, ez = yrep
    v = pow(Z % mod, ez, mod)
    for p, e in pp.items():
        v = v * pow(p, e, mod) % mod
    return v


def log_y(yrep):
    pp, Z, ez = yrep
    return sum(e * math.log(p) for p, e in pp.items()) + ez * math.log(Z) if Z > 1 else sum(
        e * math.log(p) for p, e in pp.items())


def solve_A(A, yrep, x):
    """decide A(b) = y with b > x; returns ('yes', ...), ('no', reason) or ('open', ...)"""
    if log_y(yrep) <= math.log(max(2, x)) + 2 * math.log(sum(abs(a) for a in A) + 2) and len(A) == 2:
        # small y: solve directly
        pp, Z, ez = yrep
        y = Z ** ez
        for p, e in pp.items():
            y *= p ** e
        al, be = A
        if (y - be) % al == 0 and (y - be) // al > x:
            return ('yes', (y - be) // al)
        return ('no', 'b <= x or not integral')
    if len(A) == 2:
        al, be = A
        if (y_mod(yrep, al) - be) % al:
            return ('no', f'congruence mod {al}')
        return ('yes', 'b = (y - e)/c')
    for ell in SMALL_PRIMES:
        ym = y_mod(yrep, ell)
        if not any((sum(a * pow(r, len(A) - 1 - i, ell) for i, a in enumerate(A)) - ym) % ell == 0 for r in range(ell)):
            return ('no', f'no root mod {ell}')
    return ('open', 'passes all small primes')


def census():
    print("## part 1: power identities r P_t(r) + C = lam A(r)^j, last digit x = F(t) + C")
    for k, D in BOUNDS.items():
        n = k - 1
        stats = {}
        rows = []
        for t in product(range(D + 1), repeat=n):
            if t[0] == 0:
                continue
            for j, A, lam, C in shapes(t):
                key = (j, n // j)
                st = stats.setdefault(key, dict(shapes=0, nonint=0, xbad=0, power=0, members=0, open=0))
                st['shapes'] += 1
                if A is None:
                    st['nonint'] += 1
                    continue
                x = sum(w(ti) for ti in t) + C
                if x < 2:
                    st['xbad'] += 1
                    continue
                yrep = power_condition(x, lam, j)
                if yrep is None:
                    continue
                st['power'] += 1
                res = solve_A(A, yrep, x)
                if res[0] == 'yes':
                    st['members'] += 1
                elif res[0] == 'open':
                    st['open'] += 1
                rows.append((k, t, j, A, lam, x, res))
        print(f"# k = {k}, small digits <= {D}")
        for (j, d), st in sorted(stats.items()):
            print(f"#   j = {j}, deg A = {d}: shapes {st['shapes']}, C not integral {st['nonint']}, x < 2 {st['xbad']}, "
                  f"x^x = lam y^j {st['power']}, members {st['members']}, undecided {st['open']}")
        for k_, t, j, A, lam, x, res in rows:
            xs = str(x) if x < 10 ** 30 else f"~10^{math.log10(x):.2f}"
            kind = 'linear' if len(A) == 2 else 'nonlinear'
            jdiv = 'j|x' if x % j == 0 else 'j!|x'
            print(f"  k={k_} t={t} j={j} A={A} lam={lam} x={xs} {kind} {jdiv}: {res[0]} ({res[1]})")
        sys.stdout.flush()


def rad(n):
    return math.prod(sympy.factorint(n)) if n > 1 else 1


def e0_family(jmax=12, cmax=200):
    print()
    print("## part 2: the family (c^j, 0, ..., 0, x), x = c^(j c^j) + j - 1, base x^(x/j) / c")
    print("# k j c log10(x) log10(log10(b)) check modulo 24 primes")
    for j in range(2, jmax + 1):
        found = None
        for c in range(2, cmax + 1):
            if (j - 1) % rad(c):
                continue
            # j | x  <=>  c^(j c^j) == 1 (mod j)
            if pow(c, j * c ** j, j) != 1 % j:
                continue
            found = c
            break
        if found is None:
            print(f"{j + 1} {j} none with c <= {cmax}")
            continue
        c = found
        e = j * c ** j  # x = c^e + j - 1
        lx = e * math.log10(c)
        llb = lx + math.log10(lx) - math.log10(j)
        ok = True
        for ell in BIG_PRIMES:
            # x mod ell and x mod (ell - 1) are needed for y = x^(x/j) mod ell
            xm = (pow(c, e, ell) + j - 1) % ell
            # x/j mod (ell - 1): x mod j (ell - 1), then divide
            xmj = (pow(c, e, j * (ell - 1)) + j - 1) % (j * (ell - 1))
            assert xmj % j == 0
            ex = xmj // j + (ell - 1)  # exponent of y = x^(x/j); xm != 0 mod ell in practice
            y = pow(xm, ex, ell)
            b = y * pow(c, -1, ell) % ell
            P = (pow(c, j, ell) * pow(b, j, ell) + xm) % ell
            F = (pow(c, j * c ** j, ell) + (j - 1) + pow(xm, (pow(c, e, ell - 1) + j - 1) % (ell - 1) + (ell - 1), ell)) % ell
            ok &= P == F
        print(f"{j + 1} {j} {c} {lx:.2f} {llb:.3f} {ok}")
    # exact check of the smallest 4-digit member
    c, j = 2, 3
    x = gmpy2.mpz(c) ** (j * c ** j) + j - 1
    assert x % j == 0 and x % 2 == 0
    y = x ** (x // j)
    assert y % c == 0
    b = y // c
    P = c ** j * b ** j + x
    F = gmpy2.mpz(c ** j) ** (c ** j) + (j - 1) + x ** x
    print(f"# exact: (8, 0, 0, {int(x)}) in base x^{int(x // j)} / 2 (about 10^{float(gmpy2.log10(b)):.6g}): P == F is {P == F}, b > x is {b > x}")


def main():
    census()
    e0_family()


if __name__ == '__main__':
    main()
