"""How many k-digit prefixes make the free last digit hopeless (question 14).

For a prefix (s_1, ..., s_{k-1}) and a free last digit x, the string is a
solution in base b only if P(b) - F0 == x^x - x (mod q) for every q, where
P(r) = sum s_i r^(k-i) and F0 is the weight of the prefix. If for every
class of x some modulus q leaves no residue r, no member of the family is a
solution in any base. This script samples random prefixes with digits in
[3, 10^6] (so the density is the density over all prefixes) and measures
the share that are covered by q = 27 alone, by q = 16 alone, by 27 and 16
together, and by 16, 27, 25 and 7 together. The digits are at least 3, so
the convention does not matter.

usage: python3 analysis/dyn_cover_density.py [samples]
"""
import math
import random
import sys

import numpy as np

from dyn_cover import period

N = int(sys.argv[1]) if len(sys.argv) > 1 else 4000


def table(q):
    """For each class of x mod P(q): x^x - x mod q (representatives >= 6)."""
    P = period(q)
    xs = np.arange(P) + 6 * P
    return P, np.array([(pow(int(x), int(x), q) - int(x)) % q for x in xs])


def vset(prefix, q, m):
    k = len(prefix) + 1
    F0 = sum((pow(d, d, q) if d else m) for d in prefix) % q
    vals = set()
    for r in range(q):
        v = 0
        for d in prefix:
            v = (v * r + d) % q
        v = (v * r) % q  # the last digit position is 0, so the prefix is multiplied by r
        vals.add((v - F0) % q)
    return vals


def covered(prefix, qs, m, tabs):
    L = 1
    for q in qs:
        L = L * tabs[q][0] // math.gcd(L, tabs[q][0])
    alive = np.ones(L, dtype=bool)
    for q in qs:
        P, T = tabs[q]
        V = vset(prefix, q, m)
        hit = np.isin(T, list(V))  # x class has a root mod q
        alive &= np.tile(hit, L // P)
        if not alive.any():
            return True
    return False


def main():
    sets = {'27': [27], '16': [16], '27,16': [27, 16], '16,27,25,7': [16, 27, 25, 7]}
    tabs = {q: table(q) for q in (16, 27, 25, 7)}
    print(f'{N} random prefixes per length, digits in [3, 10^6]')
    m = 1  # digits >= 3, so the convention does not matter
    for k in (3, 4, 5, 6):
        res = {}
        for name, qs in sets.items():
            cnt = 0
            rng = random.Random(k)
            for _ in range(N):
                prefix = [rng.randint(3, 10 ** 6) for _ in range(k - 1)]
                cnt += covered(prefix, qs, m, tabs)
            res[name] = cnt / N
        print(f'  k = {k}: ' + ', '.join(f'{n}: {v:.3f}' for n, v in res.items()))


if __name__ == '__main__':
    main()
