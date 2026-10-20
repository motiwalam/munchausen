"""Round 6, k-length: the local condition of Proposition K.3.

If a k-digit string with small digits s_i and one large digit x is a
solution, then every prime l | x divides F(b) = Ps(b) - W, where Ps is the
polynomial of the small digits (x replaced by 0) and W their weight. So F
has a root modulo every prime of x. For deg F <= 4 this fails for a
positive density of primes unless F has a rational root (or F is
constant); then the admissible x have density 0. If F is a nonzero
constant, x divides it.

The script classifies every family with K - 1 small digits <= B by the
shape of F: constant, rational root, or no rational root, by position,
and lists the families with a rational root for K = 4, B <= 3.

usage: r6k_density.py K B
"""
import itertools
import sys
from fractions import Fraction


def w(d, m):
    return m if d == 0 else d ** d


def divisors(n):
    n = abs(n)
    return [d for d in range(1, n + 1) if n % d == 0] if n else []


def rational_root(c):
    """c: integer coefficients, highest first. A rational root or None."""
    while c and c[0] == 0:
        c = c[1:]
    if len(c) <= 1:
        return None
    if c[-1] == 0:
        return Fraction(0)
    # a rational root p/q has q | c[0]; find the real roots numerically and
    # test the nearby fractions exactly
    import numpy as np
    roots = np.roots([float(a) for a in c])
    for z in roots:
        if abs(z.imag) > 1e-6 * max(1.0, abs(z)):
            continue
        for q in divisors(c[0]):
            for p in (int(np.floor(z.real * q)) + t for t in (-1, 0, 1, 2)):
                r = Fraction(p, q)
                v = Fraction(0)
                for a in c:
                    v = v * r + a
                if v == 0:
                    return r
    return None


def main():
    K, B = int(sys.argv[1]), int(sys.argv[2])
    names = {0: "last", K - 1: "leading"}
    for j in range(K):
        ix = K - 1 - j
        cnt = {"constant": 0, "zero": 0, "root": 0, "noroot": 0}
        examples = []
        for ds in itertools.product(range(B + 1), repeat=K - 1):
            if ix != 0 and ds[0] == 0:
                continue
            for m in ((0, 1) if 0 in ds else (1,)):
                s = list(ds)
                s.insert(ix, 0)
                W = sum(w(d, m) for d in ds)
                c = list(s)
                c[-1] -= W
                while c and c[0] == 0:
                    c = c[1:]
                if not c:
                    cnt["zero"] += 1
                    continue
                if len(c) == 1:
                    cnt["constant"] += 1
                    continue
                r = rational_root(c)
                if r is None:
                    cnt["noroot"] += 1
                else:
                    cnt["root"] += 1
                    if B <= 3:
                        examples.append((ds, m, str(r)))
        print("K %d B %d position j=%d (%s):" % (K, B, j, names.get(j, "middle")), cnt)
        for e in examples:
            print("   rational root:", e)


if __name__ == "__main__":
    main()
