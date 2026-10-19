"""Question 82: random tests of the first open type of Theorem 2.5.

Draws random monic irreducible P_i of the given degrees over F_q (q prime),
forms M = prod P_i (= B - 1, squarefree), and compares k with omega; also
records deg D, D = M'^(1-q) mod M (k = omega + 1 needs deg D <= 1).

usage: python3 r5m_kB_sample.py q samples deg1 deg2 ...
"""
import sys
from collections import Counter

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r5m_kB_types import k_omega, rabin, deg_D


def random_irreducible(q, f, rng):
    while True:
        P = np.concatenate([rng.integers(0, q, f), [1]]).astype(np.int64)
        if P[0] != 0 and rabin(P, q, f):
            return P


def main():
    q, n = int(sys.argv[1]), int(sys.argv[2])
    degs = [int(x) for x in sys.argv[3:]]
    rng = np.random.default_rng(82)
    stats = Counter()
    dstats = Counter()
    for _ in range(n):
        ps = [random_irreducible(q, f, rng) for f in degs]
        if len({tuple(p) for p in ps}) < len(ps):
            continue
        M = np.array([1], dtype=np.int64)
        for p in ps:
            M = np.convolve(M, p) % q
        k, om = k_omega(M, q)
        stats[k - om] += 1
        dstats[deg_D(M, q)] += 1
        if k != om:
            print("COUNTEREXAMPLE", M.tolist(), k, om)
    print(f"q {q} degrees {degs}: {sum(stats.values())} samples, k - omega counts {dict(stats)}, "
          f"deg D counts {dict(sorted(dstats.items()))}")


if __name__ == '__main__':
    main()
