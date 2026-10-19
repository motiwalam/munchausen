"""Degree law of the digits of F(x) by position, against the chapter 5 model.

For full-length x and every base (weighted by orbit), the share of digits at
each position that are zero or of degree 0, ..., e-1. The model gives every
position below the top the shares q^-e and (q-1) q^(j-e).
usage: python3 r4f_positions.py q e
"""
import sys
import numpy as np
from r4f_lib import World, base_orbits


def main():
    q, e = map(int, sys.argv[1:3])
    W = World(q, e, 0)
    Lf, _ = W.lengths_of_F()
    X = W.X[Lf == W.lmax]
    cnt = np.zeros((W.lmax, e + 1))
    for B, w in base_orbits(q, e):
        _, _, dg, _ = W.class_sums(W.digit_vectors(B, X))
        for i in range(W.lmax):
            cnt[i] += w * np.bincount(dg[:, i] + 1, minlength=e + 1)
    cnt /= cnt[0].sum()
    R = (e - 1) * q // e
    print(f"# q {q} e {e}: share of zero digits and of digits of degree 0..{e - 1}, full-length x, all bases")
    print("model  " + ' '.join(f"{v:6.3f}" for v in [q ** -e] + [(q - 1) * q ** (j - e) for j in range(e)]))
    for i in range(W.lmax):
        dq = [(i // q ** k) % q for k in range(e - 1)]
        tag = 'forced zero' if any(d > R for d in dq) and i > 0 else ''
        print(f"pos {i:3d} " + ' '.join(f"{v:6.3f}" for v in cnt[i]) + ('  ' + tag if tag else ''))


if __name__ == '__main__':
    main()
