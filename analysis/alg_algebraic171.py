"""Algebraic factor pairs of x^x + 1 and the (1,x,1) equation (Theorem 2).

For odd x = s y^2 (s squarefree), x^x + 1 = prod over d | x of Phi_2d(x). The
algebraic factors are the values at t = y of the irreducible factors of
Phi_2d(s t^2) in Z[t]: Phi_2d(x) itself, or its two Aurifeuillian halves.
A (1,x,1) solution is b(b+x) = x^x + 1. This script finds, for every odd x up
to XMAX, the product b of algebraic factors that makes log((x^x+1)/b^2)
smallest. A solution needs that number to be log(1 + x/b), about x^(1-x/2).
It prints the minimum, which Theorem 2 says is near 0 only for x = 3 and 7.
usage: python3 alg_algebraic171.py XMAX
"""
import sys
import math
import itertools
import cypari2
from sympy import divisors, factorint

pari = cypari2.Pari()
pari.allocatemem(10**9)


def algebraic_factors(x):
    f = factorint(x)
    s = math.prod(p for p, e in f.items() if e % 2)
    y = math.isqrt(x // s)
    out = []
    for d in divisors(x):
        v = pari(f"my(f=factor(subst(polcyclo({2*d},z),z,{s}*t^2))[,1]);"
                 f"vector(#f,i,subst(f[i],t,{y}))")
        vals = [abs(int(a)) for a in v]
        assert math.prod(vals) == int(pari(f"polcyclo({2*d},{x})"))
        out += [(d, len(vals), a) for a in vals]
    assert math.prod(a for _, _, a in out) == x**x + 1
    return out


def ln(n):
    k = max(n.bit_length() - 60, 0)
    return math.log(n >> k) + k * math.log(2)


if __name__ == '__main__':
    XMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 201
    for x in range(3, XMAX + 1, 2):
        fac = algebraic_factors(x)
        logs = [ln(a) for _, _, a in fac]
        total = sum(logs)
        best = (math.inf, None)
        for mask in itertools.product((0, 1), repeat=len(fac)):
            lb = sum(l for l, m in zip(logs, mask) if m)
            gap = abs(total - 2 * lb)
            if gap < best[0]:
                best = (gap, mask)
        b = math.prod(a for (_, _, a), m in zip(fac, best[1]) if m)
        exact = b * (b + x) == x**x + 1 or (b - x) * b == x**x + 1
        nsplit = sum(1 for _, n, _ in fac if n == 2) // 2
        print(f"x={x} factors={len(fac)} aurifeuillian_pairs={nsplit} "
              f"min|log(N/b^2)|={best[0]:.4f} log x={math.log(x):.4f} solution={exact}", flush=True)
