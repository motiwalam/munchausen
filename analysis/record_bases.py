"""Smallest bases with many self-paying digits.

A base b = r^t (r not a perfect power) has a self-paying digit r^s at
position s (r^s - 1) / t for each 1 <= s < t with t | s (r^s - 1)
(Proposition 2.2). Each such base has at least 2^(C+1) - 2 nontrivial
solutions under 0^0 = 0 (Corollary 2.4). This lists, for each C, the smallest
base with at least C self-paying digits.
"""
import math


def is_perfect_power(r):
    for e in range(2, r.bit_length() + 1):
        x = round(r ** (1 / e))
        if any(y > 1 and y ** e == r for y in (x - 1, x, x + 1)):
            return True
    return False


def count(r, t):
    return sum(1 for s in range(1, t) if (s * (pow(r, s, t) - 1)) % t == 0)


best = {}
for r in range(2, 200):
    if is_perfect_power(r):
        continue
    for t in range(2, 2000):
        if t * math.log10(r) > 2000:  # bases up to 10^2000
            break
        c = count(r, t)
        size = t * math.log10(r)
        for cc in range(1, c + 1):
            if cc not in best or size < best[cc][0]:
                best[cc] = (size, r, t)
print("C  smallest base with >= C self-paying digits   (log10 of the base)")
for c in sorted(best):
    size, r, t = best[c]
    print(f"{c:2d}  {r}^{t}  ~10^{size:.1f}   at least {2 ** (c + 1) - 2} solutions under 0^0 = 0")
