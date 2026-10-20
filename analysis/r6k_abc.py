"""Round 6, k-length: explicit abc for the binomial 4-digit families.

For (p, q, r, x) with q^2 = 3pr and x last, a solution satisfies
Y^3 - 27 p^2 x^x = R0 with Y = 3pb + q and R0 = q^3 + 27p^2 (W - x).
If R0 != 0, the explicit form c < rad(abc)^(7/4) (Laishram and Shorey),
applied after removing g = gcd as in section 33.4.2, gives

    27 p^2 x^x - |R0| < (Y |R0| rad(27 p^2) x)^(7/4),
    Y <= (27 p^2 x^x + |R0|)^(1/3).

The script prints, for every binomial family with p, q, r <= B (any p,
cube or not) and both conventions, the largest x for which this can hold,
and the maximum over the families. R0 = 0 is the identity (Theorem 25.4).

It also shows why the same argument fails for a general prefix: there
E = Q(Y) + C (x - W) has a term of size Y, and the exponent 7/4 exceeds
3/2 = d/(d - 1).

usage: r6k_abc.py B
"""
import math
import sys


def w(d, m):
    return m if d == 0 else d ** d


def rad(n):
    r, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            r *= d
            while n % d == 0:
                n //= d
        d += 1
    return r * (n if n > 1 else 1)


def holds(p, q, W, x):
    R0 = q ** 3 + 27 * p * p * (W - x)
    if R0 == 0:
        return False
    lN = math.log(27 * p * p) + x * math.log(x)
    lR = math.log(abs(R0))
    left = lN + math.log1p(-math.exp(lR - lN)) if lR < lN else -1e300
    lY = (lN + math.log1p(math.exp(lR - lN))) / 3 if lR < lN else lR
    right = 1.75 * (lY + lR + math.log(rad(27 * p * p)) + math.log(rad(x)))
    return left < right


def main():
    B = int(sys.argv[1])
    worst = 0
    for p in range(1, B + 1):
        for q in range(0, B + 1):
            for r in range(0, B + 1):
                if q * q != 3 * p * r:
                    continue
                for m in ((0, 1) if 0 in (q, r) else (1,)):
                    W = w(p, m) + w(q, m) + w(r, m)
                    last = max(x for x in range(2, 5000) if holds(p, q, W, x))
                    worst = max(worst, last)
                    print(p, q, r, m, "x <=", last)
    print("# largest", worst)


if __name__ == "__main__":
    main()
