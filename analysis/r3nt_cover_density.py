"""Question 46: remeasure the share of covered prefixes (section 15.4.4) with
the moduli 81 and 125 of Theorems 2.4 and 2.5.

Same sampling as analysis/dyn_cover_density.py (random prefixes with digits
in [3, 10^6], last digit free), with more modulus sets.

usage: python3 analysis/r3nt_cover_density.py [samples]
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from dyn_cover_density import covered, table  # noqa: E402

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000

SETS = {
    '27': [27],
    '81': [81],
    '25': [25],
    '125': [125],
    '16,27,25,7': [16, 27, 25, 7],
    '16,81,125,7': [16, 81, 125, 7],
}


def main():
    qs = sorted({q for v in SETS.values() for q in v})
    tabs = {q: table(q) for q in qs}
    print(f'{N} random prefixes per length, digits in [3, 10^6]')
    m = 1
    for k in (3, 4, 5, 6):
        res = {}
        for name, mods in SETS.items():
            cnt = 0
            rng = random.Random(k)
            for _ in range(N):
                prefix = [rng.randint(3, 10 ** 6) for _ in range(k - 1)]
                cnt += covered(prefix, mods, m, tabs)
            res[name] = cnt / N
        print(f'  k = {k}: ' + ', '.join(f'{n}: {v:.4f}' for n, v in res.items()), flush=True)


if __name__ == '__main__':
    main()
