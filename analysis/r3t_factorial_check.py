"""Brute force check of fast/src/bin/r3t_factorial.rs (question 62).

For every n < X! (default 10!) compute the factorial digits and F(n) under
both conventions, and count the n with n - F(n) = D for D = 0..5, by length.
usage: python3 r3t_factorial_check.py [X]
"""
import sys
from math import factorial

X = int(sys.argv[1]) if len(sys.argv) > 1 else 10
W = [0] + [d ** d for d in range(1, X + 1)]
counts = {}
for n in range(1, factorial(X)):
    x, i, ds = n, 2, []
    while x:
        ds.append(x % i)
        x //= i
        i += 1
    L = len(ds)
    f0 = sum(W[d] for d in ds)
    z = ds.count(0)
    for m, f in ((0, f0), (1, f0 + z)):
        D = n - f
        if 0 <= D <= 5:
            counts[(m, L, D)] = counts.get((m, L, D), 0) + 1
            if D == 0:
                print(f"sol m {m} L {L} n {n} digits {','.join(map(str, reversed(ds)))}")
for m in (0, 1):
    for L in range(1, X):
        row = [counts.get((m, L, D), 0) for D in range(6)]
        print(f"len m {m} L {L} sols {row[0]} near {','.join(map(str, row[1:]))}")
