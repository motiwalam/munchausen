"""Munchausen numbers in bijective base b (digits 1 to b, no zero).

n = sum s_i b^i with 1 <= s_i <= b, and n is a solution when n = sum s_i^s_i.
There is no convention for 0^0. The digit b at position b-1 pays for itself,
since b * b^(b-1) = b^b. Brute force over digit multisets. Lead for
question 95 of docs/library/questions-round6.md:

    python3 analysis/r6p_bijective.py 10
"""
import sys
from itertools import combinations_with_replacement


def bij_digits(n, b):
    out = []
    while n > 0:
        r = n % b or b
        out.append(r)
        n = (n - r) // b
    return out[::-1]


def solutions(b):
    w = [0] + [x ** x for x in range(1, b + 1)]
    sols = []
    d = 1
    while d * w[b] >= sum(b ** i for i in range(d)):
        for c in combinations_with_replacement(range(1, b + 1), d):
            ds = bij_digits(sum(w[x] for x in c), b)
            if len(ds) == d and sorted(ds) == list(c):
                sols.append(ds)
        d += 1
    return sols


for b in range(2, int(sys.argv[1]) + 1):
    s = [x for x in solutions(b) if len(x) > 1]
    print(b, len(s), s)
