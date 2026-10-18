"""A proven upper bound for the density of x that pass the local test of
b(b+x) = x^x + 1 (question 12).

Fix L0 and take the primes p with p - 1 | L0 and p not dividing L0. Let
L = lcm(p - 1). For x == e (mod L), the residue x mod p is independent of e
and of the other primes (CRT), so the share of x == e (mod L) that no prime
excludes is prod_p (1 - kappa_p(e)), where kappa_p(e) is the share of a mod p
with 4 a^e + a^2 + 4 a nonresidue. Averaging over odd e gives the exact
density of odd x that survive this set of primes.
usage: python3 alg_density171.py L0
"""
import sys
import numpy as np
from math import lcm
from sympy import divisors, isprime


def kappa(p):
    sq = np.zeros(p, dtype=bool)
    sq[(np.arange(p, dtype=np.int64) ** 2) % p] = True
    out = np.zeros(p - 1)
    a = np.arange(1, p, dtype=np.int64)
    for e in range(p - 1):
        f = (4 * np.array([pow(int(x), e, p) for x in a], dtype=np.int64) + a * a + 4) % p
        out[e] = np.count_nonzero(~sq[f]) / p
    return out


if __name__ == '__main__':
    L0 = int(sys.argv[1])
    ps = [d + 1 for d in divisors(L0) if isprime(d + 1) and L0 % (d + 1) and d + 1 > 2]
    L = lcm(*[p - 1 for p in ps])
    e = np.arange(1, L, 2, dtype=np.int64)        # odd x
    alive = np.ones(len(e))
    print(f"L0 = {L0}, {len(ps)} primes from {ps[0]} to {ps[-1]}, L = {L}")
    for i, p in enumerate(ps):
        alive *= 1 - kappa(p)[e % (p - 1)]
        if i % 5 == 4 or i == len(ps) - 1:
            print(f"after {i + 1} primes (up to {p}): density of odd x not excluded = {alive.mean():.5f}", flush=True)
    print(f"density (all x, even x excluded) <= {alive.mean() / 2:.5f}")
