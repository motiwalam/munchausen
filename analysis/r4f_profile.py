"""Which assumption of the chapter 5 model fails in F_q[T]?

For each (q, e, m) and each base orbit, this compares
  real      the census count,
  refined   the chapter 5 model (digits iid uniform, identity mod B - 1),
  profile   the same model, but with the true joint law of the class counts
            (number of zero digits and of digits of each degree), measured in
            that base over all x of the same length; digit values stay uniform
            within their class.
If profile matches real, the model fails only through the law of the counts.
usage: python3 r4f_profile.py q e m
"""
import sys
import numpy as np
from r4f_lib import World, base_orbits, type_index, class_factor


def main(q, e, m):
    W = World(q, e, m)
    Lf, _ = W.lengths_of_F()
    ty = type_index(W, W.X)
    ntype = 3 ** e * (q if m else 1)
    laws = W.string_laws()
    pl = np.array([laws[L][i] if L >= 1 else 0.0 for i, L in enumerate(Lf)])
    tot = dict(real=0.0, refined=0.0, profile=0.0, bases=0)
    byk = {}
    for B, w in base_orbits(q, e):
        dv = W.digit_vectors(B)
        cs, ln, dg, z = W.class_sums(dv)
        real = ((cs == W.X).all(axis=1) & (ln >= 2)).sum()
        idm = W.identity_mask(B) & (Lf >= 2)
        refined = pl[idm].sum() * q ** e
        inside = np.arange(W.lmax)[None, :] < ln[:, None]
        counts = np.stack([z] + [((dg == j) & inside).sum(axis=1) for j in range(e)], axis=1)
        prof = 0.0
        for L in np.unique(Lf[idm]):
            selL = Lf == L
            uc, inv = np.unique(counts[selL], axis=0, return_inverse=True)
            pc = np.bincount(inv.ravel(), minlength=len(uc)) / selL.sum()
            fac = class_factor(W, uc, ntype)
            pt = pc @ fac
            prof += pt[ty[idm & selL]].sum() * q ** e
        kk = int(round(np.log(max(refined, 1e-9)) / np.log(q)))
        for key, v in (('real', real), ('refined', refined), ('profile', prof)):
            tot[key] += w * v
        tot['bases'] += w
        print(f"base {B} size {w} real {real} refined {refined:.2f} profile {prof:.2f}")
    nb = tot['bases']
    print(f"# q {q} e {e} m {m}: bases {nb} per base: real {tot['real']/nb:.4f} refined {tot['refined']/nb:.4f} profile {tot['profile']/nb:.4f}")


if __name__ == '__main__':
    main(*map(int, sys.argv[1:4]))
