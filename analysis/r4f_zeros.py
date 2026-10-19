"""Zero digits of F(x) in F_q[T]: forced by the Frobenius blocks.

For full-length x (the top class sum D_(e-1) of degree e - 1), sampled at
random in every base orbit, this script reports
  Z      the forced zeros of Corollary 1.4: positions 1 <= i < L with a base-q
         digit above R = floor((e-1) q / e),
  mean   the mean number of zero digits of F(x),
  model  the mean in the chapter 5 model, (L - 1) / q^e,
  P0     the share of x with p | z, against Binomial(L - 1, q^-e) in the model.
usage: python3 r4f_zeros.py samples q e [q e ...]
"""
import sys
import numpy as np
from math import comb
from r4f_lib import World, base_orbits


def forced(q, e, L):
    R = (e - 1) * q // e
    n = 0
    for i in range(1, L):
        x = i
        while x:
            if x % q > R:
                n += 1
                break
            x //= q
    return n


def main():
    a = list(map(int, sys.argv[1:]))
    samples = a[0]
    rng = np.random.default_rng(1)
    print("q e   L    Z  Z mod p  mean zeros  model mean   P(p|z)  model P(p|z)")
    for q, e in zip(a[1::2], a[2::2]):
        W = World.__new__(World)
        W.q, W.e, W.m = q, e, 0
        W.coords = [(j, t) for j in range(e) for t in range(j + 1)]
        W.nc = len(W.coords)
        W.maxdeg = (e - 1) * q ** (e - 1)
        W.lmax = W.maxdeg // e + 1
        W.cdeg = [t * q ** j for (j, t) in W.coords]
        L = W.lmax
        top = W.coords.index((e - 1, e - 1))
        tot = zs = p0 = 0.0
        for B, w in base_orbits(q, e):
            X = rng.integers(0, q, (samples, W.nc))
            X[:, top] = rng.integers(1, q, samples)
            dv = ((X @ W.digit_matrix(B)) % q).reshape(samples, L, e)
            _, ln, _, z = W.class_sums(dv)
            assert (ln == L).all()
            tot += w
            zs += w * z.mean()
            p0 += w * (z % q == 0).mean()
        pm = q ** -e
        mp0 = sum(comb(L - 1, k) * pm ** k * (1 - pm) ** (L - 1 - k) for k in range(0, L, q))
        Z = forced(q, e, L)
        print(f"{q:2d} {e} {L:4d} {Z:4d} {Z % q:6d} {zs / tot:11.2f} {(L - 1) * pm:11.3f} {p0 / tot:8.3f} {mp0:13.3f}")


if __name__ == '__main__':
    main()
