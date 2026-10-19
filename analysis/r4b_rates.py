"""Round 4, blocks: the basic rate of blocks and short solutions per base.

The basic model of chapter 5, applied to an L-digit string t at shift m
(k = L + m; m = 0 is a k-digit solution), says: t is a block in base b with
probability [b^m | F(t)] / (b^(L-1) (b-1)), the chance that F(t) / b^m has
the digits of t. Summed over t,

    E_b(L, m) = N_L(b) / (b^(k-1) (b - 1)),

where N_L(b) is the number of L-digit strings (leading digit >= 1) with
b^(k-1) <= F(t) < b^k. The script computes N_L(b) exactly from the digit
multisets, and sums E_b over base ranges. Local factors are left out; the
ratio of the class means of r4b_spectrum.py to this sum measures them.

    python3 r4b_rates.py > data/r4b_rates.txt
"""
import math
from itertools import combinations_with_replacement
from collections import Counter

RANGES = [(3, 12), (13, 99), (100, 999)]


def count_strings(L, b, lo, hi, mode):
    """number of L-digit strings, leading digit >= 1, with lo <= F < hi"""
    X = 0
    for x in range(1, b):
        if x ** x < hi:
            X = x
        else:
            break
    w = [mode] + [x ** x for x in range(1, X + 1)]
    fL = math.factorial(L)
    n = 0
    for c in combinations_with_replacement(range(X + 1), L):
        F = sum(w[d] for d in c)
        if lo <= F < hi:
            cnt = Counter(c)
            perm = fL
            for v in cnt.values():
                perm //= math.factorial(v)
            z = cnt.get(0, 0)
            n += perm * (L - z) // L
    return n, X


def E_basic(L, m, b, mode):
    k = L + m
    N, X = count_strings(L, b, b ** (k - 1), b ** k, mode)
    return N / (b ** (k - 1) * (b - 1)), X


def main():
    print("# basic model E_b(L, m) = N_L(b) / (b^(k-1) (b-1)), summed over base ranges")
    print("# L m mode | " + " | ".join(f"bases {lo}-{hi}" for lo, hi in RANGES) + " | mean largest digit X in 13-99")
    for (L, m) in [(4, 0), (5, 0), (6, 0), (7, 0), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (2, 2), (3, 2), (4, 2), (5, 2),
                   (2, 3), (3, 3), (4, 3)]:
        for mode in (1, 0):
            sums = []
            xs = []
            for lo, hi in RANGES:
                hi_eff = hi if L + m <= 6 else min(hi, 300)
                s = 0.0
                for b in range(lo, hi_eff + 1):
                    e, X = E_basic(L, m, b, mode)
                    s += e
                    if 13 <= b <= 99:
                        xs.append(X)
                sums.append(s)
            print(f"{L} {m} {mode} | " + " | ".join(f"{s:.4g}" for s in sums) + f" | {sum(xs) / len(xs):.2f}", flush=True)


if __name__ == '__main__':
    main()
