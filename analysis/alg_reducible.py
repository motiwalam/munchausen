"""Reducible Munchausen polynomials Q_s (question 2).

For every string of length k with digits up to M (leading digit >= 1) and
both conventions, factor Q_s(r) = P_s(r) - F(s) over Q with PARI. For each
reducible Q_s print its factor degrees and its class:
- R: a rational root (a linear factor);
- D: no rational root, and P_s is decomposable, P_s = G(h(r)) with
     deg h >= 2 (found with sympy's decompose);
- O: no rational root and P_s indecomposable.
For the strings without a rational root, also test whether Q_s has a root
modulo every prime below 3000 (a candidate for an intersective polynomial).
usage: python3 alg_reducible.py k M
"""
import sys
import itertools
from collections import Counter
import cypari2
from fractions import Fraction
from sympy import Poly, symbols, primerange, QQ, divisors

pari = cypari2.Pari()
r = symbols('r')
PRIMES = list(primerange(2, 3000))


def decompose(s):
    """Return (G, h) with P_s = G(h(r)), deg h >= 2, h monic and h(0) = 0, over Q,
    or None if P_s is indecomposable. h comes from the top coefficients of P_s
    (the d-th root of P_s / s_1), G from the base-h expansion of P_s."""
    n = len(s) - 1
    P = Poly(list(s), r, domain=QQ)
    lead = Fraction(s[0])
    a = [Fraction(c) / lead for c in s]          # a[0] = 1, a[i]: coeff of r^(n-i)
    for e in divisors(n):
        if e < 2 or e == n:
            continue
        d = n // e
        # power series u(z) = (1 + a1 z + a2 z^2 + ...)^(1/d) up to z^(e-1)
        u = [Fraction(1)] + [Fraction(0)] * (e - 1)
        for i in range(1, e):
            # coefficient of z^i in u^d must equal a[i]; solve for u[i]
            ud = [Fraction(0)] * (i + 1)
            ud[0] = Fraction(1)
            for _ in range(d):                   # ud = u^d truncated, with u[i] = 0
                new = [Fraction(0)] * (i + 1)
                for j in range(i + 1):
                    for l in range(i + 1 - j):
                        new[j + l] += ud[j] * u[l]
                ud = new
            u[i] = (a[i] - ud[i]) / d
        h = Poly([QQ(c.numerator, c.denominator) for c in u] + [QQ(0)], r, domain=QQ)
        rest, G = P, []
        ok = True
        for _ in range(d + 1):
            q, rem = rest.div(h)
            if rem.degree() > 0:
                ok = False
                break
            G.append(rem.LC() if not rem.is_zero else QQ(0))
            rest = q
            if rest.is_zero:
                break
        if ok and rest.is_zero:
            return list(reversed(G)), h
    return None


def roots_mod_all(coeffs):
    pol = pari('Pol(' + str(list(coeffs)) + ', r)')
    for p in PRIMES:
        if all(c % p == 0 for c in coeffs):
            continue
        if len(pari.polrootsmod(pol, p)) == 0:
            return p
    return None


if __name__ == '__main__':
    k, M = int(sys.argv[1]), int(sys.argv[2])
    stats = Counter()
    for m in (1, 0):
        W = [m] + [x**x for x in range(1, M + 1)]
        for s in itertools.product(range(M + 1), repeat=k):
            if s[0] == 0:
                continue
            F = sum(W[x] for x in s)
            coeffs = list(s)
            coeffs[-1] -= F
            pol = pari('Pol(' + str(coeffs) + ', r)')
            fa = pari.factor(pol)
            degs = sorted(int(pari.poldegree(f)) * int(e) for f, e in zip(fa[0], fa[1])
                          if int(pari.poldegree(f)) > 0)
            nfac = sum(int(e) for f, e in zip(fa[0], fa[1]) if int(pari.poldegree(f)) > 0)
            if nfac == 1:
                stats[(m, 'irreducible')] += 1
                continue
            split = '+'.join(str(int(pari.poldegree(f))) for f, e in zip(fa[0], fa[1])
                             for _ in range(int(e)) if int(pari.poldegree(f)) > 0)
            lin = [f for f in fa[0] if int(pari.poldegree(f)) == 1]
            if lin:
                rts = sorted(str(-pari.polcoef(f, 0) / pari.polcoef(f, 1)) for f in lin)
                cls = 'R'
                info = 'roots ' + ' '.join(rts)
            else:
                dec = decompose(s)
                cls = 'D' if dec else 'O'
                info = f"P = G(h), G coeffs {[str(c) for c in dec[0]]}, h = {dec[1].as_expr()}" if dec else ''
                bad = roots_mod_all(coeffs)
                info += f"  no root mod {bad}" if bad else "  ROOT MOD EVERY PRIME < 3000"
            stats[(m, cls)] += 1
            facs = ' * '.join(f"({f})" + (f"^{e}" if int(e) > 1 else '') for f, e in zip(fa[0], fa[1]))
            print(f"0^0={m} {s} F={F} split {split} class {cls}: {facs}  {info}", flush=True)
    for key in sorted(stats):
        print('total', key, stats[key])
