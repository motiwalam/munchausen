"""Why the model fails in the factorial number system (question 62).

For every n with L digits (L = 7, 8, 9) whose sum F(n) has L digits too, let v
be the largest digit of n. Compare the digits of F(n) with those of a random
integer of the same window: how often is the largest digit at most v, equal
to v, and how often does the digit v occur exactly as often as in n?
The model assumes the two columns agree.
usage: python3 r3t_factorial_diag.py
"""
import random
from math import factorial
from collections import Counter

random.seed(62)
W = [0] + [d ** d for d in range(1, 12)]


def dig(n):
    x, i, ds = n, 2, []
    while x:
        ds.append(x % i)
        x //= i
        i += 1
    return ds[::-1]


print("| L | E_L (exact) | max digit of F <= v: F / random | = v: F / random | count of v equal: F / random |")
print("|---:|---:|---|---|---|")
for L in (7, 8, 9):
    lo, hi = factorial(L), factorial(L + 1)
    hits = 0
    A, B = Counter(), Counter()
    for n in range(lo, hi):
        ds = dig(n)
        f = sum(W[d] for d in ds)
        if not lo <= f < hi:
            continue
        hits += 1
        c, v = Counter(ds), max(ds)
        for C, g in ((A, dig(f)), (B, dig(random.randrange(lo, hi)))):
            cg = Counter(g)
            C['le'] += max(g) <= v
            C['eq'] += max(g) == v
            C['cnt'] += cg[v] == c[v]
    print(f"| {L} | {hits / (hi - lo):.3f} | {A['le']/hits:.3f} / {B['le']/hits:.3f} | "
          f"{A['eq']/hits:.3f} / {B['eq']/hits:.3f} | {A['cnt']/hits:.3f} / {B['cnt']/hits:.3f} |")
