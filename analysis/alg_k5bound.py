"""Check the explicit bounds of Theorems 4 and 5 (k = 5) numerically.

For a 5-digit string with a = s2/s1, b = s3/s1, c = s4/s1, d = s5/s1, put
B = b - a^2/4, q = c - ab/2 + a^3/8, C = a^2/16 - B/2. Theorem 4: if Q_s is a
product of two quadratics over Q and q != 0, then
    F <= s1 (d - B^2/4 - a q/4 + s1^2 q^2 + max(C, 0)^2).
Theorem 5: if the resolvent cubic of Q_s has a rational root and q != 0, then
    F <= s1 ((a^4/64 + a^2 B/4 - a c + 4 d)/4 + s1^2 q^2).
For each largest digit M, print the largest ratio bound / F(s) over all strings
with that largest digit, for both conventions. A ratio below 1 means the
theorem leaves no such string with that largest digit.
usage: python3 alg_k5bound.py MMAX
"""
import sys
import itertools
from fractions import Fraction as Fr

if __name__ == '__main__':
    MMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    worst = {}
    for s in itertools.product(range(MMAX + 1), repeat=5):
        if s[0] == 0:
            continue
        s1 = s[0]
        a, b, c, d = (Fr(x, s1) for x in s[1:])
        B = b - a * a / 4
        q = c - a * b / 2 + a**3 / 8
        if q == 0:
            continue
        C = a * a / 16 - B / 2
        b4 = s1 * (d - B * B / 4 - a * q / 4 + s1 * s1 * q * q + max(C, 0)**2)
        b5 = s1 * ((a**4 / 64 + a * a * B / 4 - a * c + 4 * d) / 4 + s1 * s1 * q * q)
        M = max(s)
        for m in (0, 1):
            F = sum((m if x == 0 else x**x) for x in s)
            for name, bd in (('thm4', b4), ('thm5', b5)):
                key = (name, m, M)
                worst[key] = max(worst.get(key, 0), float(bd / F))
    for key in sorted(worst):
        print(key, f"{worst[key]:.3g}")
