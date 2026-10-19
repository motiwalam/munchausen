"""Census of linear power identities for several weights (round 6, question 96).

Same shapes as r5f_identities.py: for a prefix t of k - 1 digits,
r P_t(r) + C = lam (c r + e)^j with j = k - 1. The string (t, x) with
x = F_w(t) + C is a solution in base b = (y - e)/c exactly when
w(x) = lam y^j, c | y - e and b > x (and b exceeds the digits of t).
The weights: x^x (w(0) = 1), x^(x+1) (w(0) = 0), x! (w(0) = 1), x^2, x^3
(w(0) = 0). For x! the test uses Bertrand's postulate: x! = lam y^j forces every
prime in (x/2, x] to divide lam, so x < 2 lam.

    python3 analysis/r6f_identities.py > analysis/data/r6f_identities.txt
"""
import math
import os
import sys
from itertools import product
from math import factorial

import gmpy2
import sympy

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r5f_identities import shapes  # noqa: E402

sys.set_int_max_str_digits(0)

WEIGHTS = {
    'x^x': (lambda d: 1 if d == 0 else d ** d, lambda x: x),
    'x^(x+1)': (lambda d: d ** (d + 1), lambda x: x + 1),
    'x!': (lambda d: factorial(d), None),
    'x^2': (lambda d: d ** 2, lambda x: 2),
    'x^3': (lambda d: d ** 3, lambda x: 3),
}


def power_y(x, E, lam, j):
    """y with x^E = lam y^j as (y mod function, log y), or None"""
    fl = sympy.factorint(lam)
    rest = x
    pp = {}
    for p, v in fl.items():
        a = 0
        while rest % p == 0:
            rest //= p
            a += 1
        if E * a < v or (E * a - v) % j:
            return None
        pp[p] = (E * a - v) // j
    g = math.gcd(E, j)
    mm = j // g
    if mm > 1:
        Z, exact = gmpy2.iroot(gmpy2.mpz(rest), mm)
        if not exact:
            return None
        Z = int(Z)
    else:
        Z = rest
    ez = E // g  # y = prod p^pp[p] * Z^ez
    logy = sum(e * math.log(p) for p, e in pp.items()) + (ez * math.log(Z) if Z > 1 else 0)

    def ymod(mod):
        v = pow(Z % mod, ez, mod)
        for p, e in pp.items():
            v = v * pow(p, e, mod) % mod
        return v
    return ymod, logy


def factorial_y(x, lam, j):
    if x >= 2 * lam + 2:
        return None  # a prime in (x/2, x] divides x! once and does not divide lam
    f = factorial(x)
    if f % lam:
        return None
    y, exact = gmpy2.iroot(gmpy2.mpz(f // lam), j)
    if not exact:
        return None
    y = int(y)
    return (lambda mod: y % mod), (math.log(y) if y > 0 else -1)


def main():
    bounds = {3: 60, 4: 20}
    print("# linear identities r P_t(r) + C = lam (c r + e)^(k-1), member: w(x) = lam y^j, c | y - e, b > x")
    for k, D in bounds.items():
        rows = []
        for t in product(range(D + 1), repeat=k - 1):
            if t[0] == 0:
                continue
            for j, A, lam, C in shapes(t):
                if A is None or len(A) != 2:
                    continue
                rows.append((t, j, A, lam, C))
        print(f"## k = {k}, prefix digits <= {D}: {len(rows)} linear shapes with integral C")
        for name, (w, Ef) in WEIGHTS.items():
            power = members = 0
            ex = []
            for t, j, A, lam, C in rows:
                x = sum(w(d) for d in t) + C
                if x < 2:
                    continue
                res = factorial_y(x, lam, j) if Ef is None else power_y(x, Ef(x), lam, j)
                if res is None:
                    continue
                power += 1
                ymod, logy = res
                c, e = A
                if (ymod(c) - e) % c:
                    continue
                if logy <= math.log(c * max(x, max(t)) + e + 1):
                    continue  # b <= x (approximately; exact for small y below)
                members += 1
                if len(ex) < 4:
                    ex.append((t, x if x < 10 ** 12 else f"~10^{math.log10(x):.1f}", lam))
            print(f"{name}: w(x) = lam y^j for {power} shapes, members {members}, first {ex}")
            sys.stdout.flush()


if __name__ == '__main__':
    main()
