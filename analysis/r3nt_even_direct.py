"""Question 52: exact check of b(b+x) = x^n + 1 for x == 0 (mod 8), x <= 10^5,
odd n from 5 to 15 (4 x^n + x^2 + 4 must be a square).

usage: python3 analysis/r3nt_even_direct.py
"""
from math import isqrt

hits = []
count = 0
for x in range(8, 100001, 8):
    for n in range(5, 16, 2):
        f = 4 * x ** n + x * x + 4
        r = isqrt(f)
        count += 1
        if r * r == f:
            hits.append((x, n))
print(f'{count} pairs (x, n) with x == 0 mod 8, x <= 100000, n = 5, 7, ..., 15; solutions: {hits}')
