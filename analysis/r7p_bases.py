"""Bases b <= 10^E that have a 2-digit solution (a, c), for both conventions.

Lead for question 170 of docs/library/questions-round7.md: how many bases
provably have a solution. Under 0^0 = 1 the 2-digit solutions are almost the
only known ones, so this count is the counting function of the bases known
to be nonempty, up to O(1) sporadic bases and the binomial family members.
The last column is ln(count) / ln(L / ln L) with L = ln X.

    python3 analysis/r7p_bases.py
"""
import math


def w(x, m):
    return m if x == 0 else x**x


for E in (6, 12, 24, 48, 100, 200):
    X = 10**E
    for m in (1, 0):
        bases = set()
        a = 1
        while a ** (a - 1) <= 2 * X:
            c = 0
            while True:
                wc = w(c, m)
                if wc - c > a * X + a:
                    break
                num = a**a + wc - c
                if num % a == 0:
                    b = num // a
                    if max(a, c) < b <= X:
                        bases.add(b)
                c += 1
            a += 1
        L = E * math.log(10)
        print(f"10^{E} 0^0={m} bases={len(bases)} "
              f"exponent={math.log(len(bases)) / math.log(L / math.log(L)):.2f}")
