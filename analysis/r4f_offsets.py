"""Near-solutions n = F(x) + (B - 1) g with random offsets g of growing degree.

The digits of (B - 1) g sit at positions 0 .. deg(g)/e + 1, so an offset of
degree below K changes only the bottom K/e + 2 digits of F(x). For every K
this script averages, over the base orbits (weighted) and random g with
deg g < K, the number of x with class sums of F(x) + (B-1) g equal to x and
the same length as F(x). K = 0 is the census itself. As K grows the offsets
randomize more and more of the low digits; if the structure of the high digits
causes the gap, the count moves from the census to the model only when K
reaches the top digits.
usage: python3 r4f_offsets.py q e m samples K1 K2 ...
"""
import sys
import numpy as np
from r4f_lib import World, base_orbits, digits, padd, pmul, trim, type_index


def main():
    q, e, m, samples = map(int, sys.argv[1:5])
    Ks = list(map(int, sys.argv[5:]))
    rng = np.random.default_rng(1)
    W = World(q, e, m)
    Lf, _ = W.lengths_of_F()
    laws = W.string_laws()
    pl = np.array([laws[L][i] if L >= 1 else 0.0 for i, L in enumerate(Lf)])
    orbs = base_orbits(q, e)
    nb = sum(w for _, w in orbs)
    ref = 0.0
    out = {K: 0.0 for K in Ks}
    for B, w in orbs:
        M = W.digit_matrix(B)
        dv0 = (W.X @ M) % q
        idm = W.identity_mask(B) & (Lf >= 2)
        ref += w * pl[idm].sum() * q ** e
        bm1 = padd(B, [q - 1], q)
        for K in Ks:
            tot = 0
            reps = 1 if K == 0 else samples
            for _ in range(reps):
                g = trim([int(c) for c in rng.integers(0, q, K)])
                off = np.zeros(W.lmax * e, dtype=np.int64)
                for i, d in enumerate(digits(pmul(bm1, g, q), B, q, e)):
                    if i < W.lmax:
                        off[i * e:(i + 1) * e] = d
                dv = ((dv0 + off[None, :]) % q).reshape(W.n, W.lmax, e)
                cs, ln, dg, z = W.class_sums(dv)
                tot += ((cs == W.X).all(axis=1) & (ln == Lf) & (ln >= 2)).sum()
            out[K] += w * tot / reps
    print(f"# q {q} e {e} m {m}: max length {W.lmax}, {samples} offsets per K and orbit")
    print(f"refined model per base {ref / nb:.3f}")
    for K in Ks:
        ch = 0 if K == 0 else (K - 1) // e + 2
        print(f"K {K:3d} (bottom {ch} digits changed) near-solutions per base and offset {out[K] / nb:.3f}")


if __name__ == '__main__':
    main()
