"""Round 6, k-length: the power identities inside the Runge classes.

Theorem K.1 leaves, beyond its threshold, only strings with
P - W = l A^g identically (x last, by Lemma K.0). This script lists, for
K-digit prefixes with digits <= B and every prime g | K - 1, the prefixes
whose remainder Rm is constant in r, the x that makes it vanish, and
decides exactly whether the string is a solution when x is an integer in
the Runge class (x^x / l a g-th power): it computes Z = (x^x / l)^(1/g)
and looks for an integer b > x with A(b) = Z.

usage: r6k_identities.py K B
"""
import itertools
import math
import sys
from fractions import Fraction

sys.set_int_max_str_digits(0)
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from r6k_runge import root_part, w, primes_dividing  # noqa: E402


def iroot(n, g):
    r = int(round(n ** (1.0 / g))) if n < 2 ** 1000 else 1 << ((n.bit_length() + g - 1) // g)
    while r ** g > n:
        r = (r + n // r ** (g - 1)) // 2 if r > 1 else 0
    while (r + 1) ** g <= n:
        r += 1
    return r


def is_power(num, den, g):
    a, b = iroot(num, g), iroot(den, g)
    return (a ** g == num and b ** g == den), Fraction(a, b)


def main():
    K, B = int(sys.argv[1]), int(sys.argv[2])
    d = K - 1
    for g in primes_dividing(d):
        for ds in itertools.product(range(B + 1), repeat=d):
            if ds[0] == 0:
                continue
            for m in ((0, 1) if 0 in ds else (1,)):
                W = sum(w(t, m) for t in ds)
                l = ds[0]
                T = [Fraction(c, l) for c in list(ds) + [0]]
                T[-1] -= Fraction(W, l)
                A, Rm = root_part(T, g)
                if any(c != 0 for c in Rm[:-1]):
                    continue
                x = -Rm[-1] * l
                if x.denominator != 1 or x < 2:
                    continue
                x = int(x)
                X = Fraction(x ** x, l)
                ok, Z = is_power(X.numerator, X.denominator, g)
                if not ok:
                    print(ds, "m", m, "g", g, "x", x, ": x^x / l is not a g-th power")
                    continue
                # solve A(b) = Z for an integer b > x: A is increasing for large b
                lo, hi = x + 1, x + 2
                def Ab(b):
                    v = Fraction(0)
                    for c in A:
                        v = v * b + c
                    return v
                while Ab(hi) <= Z:
                    hi *= 2
                while hi - lo > 1:
                    mid = (lo + hi) // 2
                    if Ab(mid) <= Z:
                        lo = mid
                    else:
                        hi = mid
                sol = Ab(lo) == Z
                print(ds, "m", m, "g", g, "x", x, ": in the class,",
                      "a solution in base %d digits long" % len(str(lo)) if sol else "no base")


if __name__ == "__main__":
    main()
