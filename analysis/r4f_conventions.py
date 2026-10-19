"""Check Proposition 3.1: the solutions under 0^0 = 1 are the solutions under
0^0 = 0 whose number of zero digits is divisible by p, in every base where
B - 1 has an irreducible factor of degree prime to p.

Reads the census files r4f_census_q{q}e{e}m0.txt (field zeros0) and ...m1.txt,
and reports per (q, e): orbits where the hypothesis holds, whether the counts
agree there, and the share of 0^0 = 0 solutions with p | z, which is the whole
ratio between the two conventions.
usage: python3 r4f_conventions.py q e [q e ...]
"""
import sys
from sympy import Poly, symbols
from r4f_byk import load
from r4f_lib import decode

T = symbols('T')


def hypothesis(code, q, e):
    b = decode(code, q, e + 1)
    b = b + [0] * (e + 1 - len(b))
    b[0] = (b[0] - 1) % q
    f = Poly(list(reversed(b)), T, modulus=q)
    return any(g.degree() % q != 0 for g, _ in f.factor_list()[1])


def main():
    a = list(map(int, sys.argv[1:]))
    for q, e in zip(a[::2], a[1::2]):
        r0 = {r['code']: r for r in load(f'data/r4f_census_q{q}e{e}m0.txt')}
        try:
            r1 = {r['code']: r for r in load(f'data/r4f_census_q{q}e{e}m1.txt')}
        except FileNotFoundError:
            r1 = {}
        hyp = agree = 0
        s0 = z0 = s1 = 0
        for c, r in r0.items():
            if not hypothesis(c, q, e):
                continue
            hyp += r['size']
            s0 += r['sols'] * r['size']
            z0 += r['zeros0'] * r['size']
            if c in r1:
                s1 += r1[c]['sols'] * r['size']
                agree += r['size'] * (r1[c]['sols'] == r['zeros0'])
        nb = sum(r['size'] for r in r0.values())
        msg = f"agree in {agree} of {hyp}" if r1 else "no 0^0 = 1 census"
        print(f"q {q} e {e}: bases {nb}, hypothesis holds in {hyp}; {msg}; "
              f"there 0^0 = 0 solutions {s0}, with p | z {z0} ({z0 / max(s0, 1):.3f}), 0^0 = 1 solutions {s1 if r1 else z0}")


if __name__ == '__main__':
    main()
