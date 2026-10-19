"""Proposition 4.5 in the census: generic x with vanishing lower classes.

For q == 1 (mod e) the block tops have degree e - 1, and on the generic cell
every digit has degree e - 1, so the lower class sums vanish. This script
counts, per factorization type of B - 1 and per base, the full-length x with
D_j = 0 for j < e - 1 that satisfy the identity, how many of them are generic
(every digit outside the forced zeros and the block tops at positions
== R (mod q) has degree e - 1), how many are
solutions, how many generic ones are solutions (the proposition says: all),
and all solutions of the base.
usage: python3 r4f_generic.py q e
"""
import sys
from collections import defaultdict
import numpy as np
from sympy import Poly, symbols
from r4f_lib import World, base_orbits

T = symbols('T')


def ftype(B, q):
    b = list(B)
    b[0] = (b[0] - 1) % q
    f = Poly(list(reversed(b)), T, modulus=q)
    return tuple(sorted((g.degree(), k) for g, k in f.factor_list()[1]))


def main():
    q, e = map(int, sys.argv[1:3])
    W = World(q, e, 0)
    Lf, _ = W.lengths_of_F()
    full = Lf == W.lmax
    R = (e - 1) * q // e
    low = np.ones(W.n, bool)
    for k, (j, t) in enumerate(W.coords):
        if j < e - 1:
            low &= W.X[:, k] == 0
    pos = np.arange(W.lmax)
    forced = np.array([i > 0 and any((i // q ** k) % q > R for k in range(e - 1)) for i in pos])
    # block tops (positions == R mod q) are free in the definition of generic
    forced |= pos % q == R
    agg = defaultdict(lambda: np.zeros(6))
    for B, w in base_orbits(q, e):
        cs, ln, dg, z = W.class_sums(W.digit_vectors(B))
        sol = (cs == W.X).all(axis=1) & (ln >= 2)
        live = (pos[None, :] < ln[:, None]) & ~forced[None, :]
        gen = ((dg == e - 1) | ~live).all(axis=1)
        sel = low & full & W.identity_mask(B)
        agg[ftype(B, q)] += w * np.array([1, sel.sum(), (sel & gen).sum(), (sel & sol).sum(),
                                          (sel & gen & sol).sum(), sol.sum()])
    print(f"# q {q} e {e}, per base: x with D_j = 0 (j < e-1) and the identity | generic | "
          f"solutions | generic solutions | all solutions")
    for t, a in sorted(agg.items()):
        print(f"type {t} bases {int(a[0])} " + ' '.join(f"{v:8.2f}" for v in a[1:] / a[0]))


if __name__ == '__main__':
    main()
