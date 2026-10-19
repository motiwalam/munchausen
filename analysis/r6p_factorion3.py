"""Every 3-digit factorion (p, q, r) with digits up to M, in every base.

A string is a solution in base b when p b^2 + q b + r = w(p) + w(q) + w(r),
w(x) = x! and w(0) = 1 (0! = 1) or 0. A solution with largest digit above M
has b^2 > (M+1)! / (3 (M+1)), so the list is complete for those bases.
Lead for question 97 of docs/library/questions-round6.md:

    python3 analysis/r6p_factorion3.py 80
"""
import sys
from math import factorial, isqrt

M = int(sys.argv[1])
fac = [factorial(x) for x in range(M + 1)]
for m in (1, 0):
    w = fac[:]
    if m == 0:
        w[0] = 0
    sols = []
    for p in range(1, M + 1):
        for q in range(M + 1):
            for r in range(M + 1):
                F = w[p] + w[q] + w[r]
                D = q * q + 4 * p * (F - r)
                if D < 0:
                    continue
                s = isqrt(D)
                if s * s != D or (s - q) % (2 * p):
                    continue
                b = (s - q) // (2 * p)
                if b > max(p, q, r):
                    sols.append((b, (p, q, r)))
    sols.sort()
    print('w(0) = %d: %d solutions: %s' % (m, len(sols), sols))
