"""Question 3: how close the real root b*(x) of a one-digit family comes to an
integer.

For a 3-digit family with one varying digit x, b*(x) is the positive root of
s1 r^2 + s2 r + s3 = F(s). For (1, x, 1) under 0^0 = 1 it is
(-x + sqrt(x^2 + 4 (x^x + 1))) / 2. A solution needs ||b*(x)|| = 0. The
spacing heuristic treats the fractional part as uniform, so the smallest
||b*(x)|| for x <= X should be about 1/(2X) if the x behave independently.
This computes ||b*(x)|| exactly with integer square roots, for odd x (even x
is the square class of Theorem 8.3, where b*(x) is just above an integer).
"""
import math
import sys
from fractions import Fraction


def frac_root(s1, s2, s3, F, scale_bits=64):
    """Distance of the root of s1 r^2 + s2 r + s3 - F to the nearest integer."""
    D = s2 * s2 - 4 * s1 * (s3 - F)
    # root = (-s2 + sqrt(D)) / (2 s1); compute sqrt(D) * 2^scale exactly
    sq = math.isqrt(D << (2 * scale_bits))
    num = -s2 * (1 << scale_bits) + sq
    den = 2 * s1 << scale_bits
    q, r = divmod(num, den)
    f = r / den
    return min(f, 1 - f), q


if __name__ == '__main__':
    X = int(sys.argv[1])
    fams = {'(1,x,1)': lambda x: (1, x, 1, 1 + x ** x + 1),
            '(x,1,5) square class': lambda x: (x, 1, 5, x ** x + 1 + 5 ** 5),
            '(6,1,x)': lambda x: (6, 1, x, 6 ** 6 + 1 + x ** x),
            '(2,x,3)': lambda x: (2, x, 3, 4 + x ** x + 27)}
    for name, f in fams.items():
        recs, dists = [], []
        best = 1.0
        for x in range(3, X + 1, 2):
            s1, s2, s3, F = f(x)
            d, q = frac_root(s1, s2, s3, F)
            dists.append(d)
            if d == 0:
                recs.append((x, 'solution'))
            elif d < best:
                best = d
                recs.append((x, f"{d:.2e}", round(d * x, 3)))
        n = len(dists)
        below = {t: sum(d < t for d in dists) / n for t in (0.01, 0.05, 0.25)}
        print(f"{name}, odd x <= {X}: {n} values; share of ||b*|| below 0.01/0.05/0.25: "
              f"{below[0.01]:.4f} {below[0.05]:.4f} {below[0.25]:.4f} (uniform: 0.02 0.10 0.50)")
        print(f"   records (x, ||b*||, x*||b*||): {recs[:6]} ... {recs[-6:]} ({len(recs)} records)", flush=True)
