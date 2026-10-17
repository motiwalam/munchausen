"""3-digit solutions where one digit x varies and the other two are fixed.

For a digit string (s2, s1, s0) the equation s2 b^2 + s1 b + s0 = F is a
quadratic in b, so the string is a solution exactly when
D = s1^2 - 4 s2 (s0 - F) is a perfect square and the root is an integer base
larger than every digit. Fix two digits, let the third one be x, and test x up
to a bound. The bases involved reach about x^(x/2).
"""
import math
import sys


def w(x, mode):
    return mode if x == 0 else x ** x


def solve(s, mode):
    s2, s1, s0 = s
    if s2 == 0:
        return None
    f = w(s2, mode) + w(s1, mode) + w(s0, mode)
    d = s1 * s1 - 4 * s2 * (s0 - f)
    if d < 0:
        return None
    r = math.isqrt(d)
    if r * r != d or (r - s1) % (2 * s2):
        return None
    b = (r - s1) // (2 * s2)
    return b if b > max(s) else None


def scan(xmax, fixed_max, mode):
    hits = []
    for pos in range(3):
        for p in range(fixed_max + 1):
            for q in range(fixed_max + 1):
                for x in range(2, xmax + 1):
                    s = [p, q]
                    s.insert(pos, x)
                    s = tuple(s)
                    b = solve(s, mode)
                    if b is not None:
                        hits.append((s, b, pos))
    return sorted(set(hits))


if __name__ == '__main__':
    xmax, fixed_max = int(sys.argv[1]), int(sys.argv[2])
    for mode in (1, 0):
        hits = scan(xmax, fixed_max, mode)
        print(f"0^0={mode}: {len(hits)} solutions with one digit x in 2..{xmax}, other digits <= {fixed_max}")
        for s, b, pos in hits:
            name = f"{b}" if b < 10 ** 15 else f"~10^{len(str(b)) - 1}"
            print(f"   {s} base {name}")
