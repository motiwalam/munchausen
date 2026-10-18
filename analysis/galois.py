"""Galois statistics of the Munchausen polynomial Q_s(r) = P_s(r) - F(s).

By the Chebotarev density theorem, the share of primes p for which Q_s has no
root mod p equals the share of elements of its Galois group G (acting on the
k-1 roots) with no fixed point. For G = S_n this is the derangement share
D_n / n!: 1/2, 1/3, 3/8, 11/30 for n = 2..5. The script measures the share
over primes 200..20000 for random strings and lists strings that deviate,
which have a smaller group or a factor.
"""
import math
import random
import sys
import numpy as np


def primes(lo, hi):
    sieve = np.ones(hi + 1, bool)
    sieve[:2] = False
    for i in range(2, int(hi ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    return [p for p in range(lo, hi + 1) if sieve[p]]


PR = primes(200, 20000)


def no_root_share(s, F):
    miss = 0
    for p in PR:
        r = np.arange(p, dtype=np.int64)
        v = np.zeros(p, dtype=np.int64)
        for c in s:
            v = (v * r + c) % p
        v = (v - F % p) % p
        miss += not (v == 0).any()
    return miss / len(PR)


def derangement_share(n):
    return sum((-1) ** j / math.factorial(j) for j in range(n + 1))


if __name__ == '__main__':
    rng = random.Random(4)
    mode = 1
    for k in (3, 4, 5, 6):
        target = derangement_share(k - 1)
        shares = []
        odd = []
        for _ in range(60):
            s = [rng.randrange(1, 21)] + [rng.randrange(21) for _ in range(k - 1)]
            F = sum(mode if x == 0 else x ** x for x in s)
            sh = no_root_share(s, F)
            shares.append(sh)
            if abs(sh - target) > 0.08:
                odd.append((tuple(s), round(sh, 3)))
        shares.sort()
        print(f"k={k}: S_{k - 1} predicts {target:.3f}; median over 60 strings {shares[30]:.3f}, "
              f"range {shares[0]:.3f}-{shares[-1]:.3f}; deviating: {odd}", flush=True)
