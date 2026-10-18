"""Brute-force check of the reduction of base 2i to base -4.

Every string with digits 0..3 and up to 9 digits (the bound from base -4:
at most 5 digits there, so 2*5 - 1 here) is written out in base 2i; we keep
those whose value is a positive integer equal to F, for both conventions.
The draft predicts: odd positions all zero, and the even positions form a
base -4 string t with value F_m(t) + m (len(t) - 1).
"""
from itertools import product

for m in (0, 1):
    w = [m, 1, 4, 27]
    found = []
    for k in range(2, 10):
        for s in product(range(4), repeat=k):
            if s[0] == 0:
                continue
            v = 0
            for x in s:
                v = v * 2j + x
            f = sum(w[x] for x in s)
            if v.imag == 0 and v.real == f:
                found.append(s)
    print(f"0^0 = {m}:", found)
