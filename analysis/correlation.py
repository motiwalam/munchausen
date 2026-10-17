"""Do the leading digits of S(c) fit the multiset c more often than random digits?

For random multisets c (the model distribution, d digits) whose sum has d
digits, compare P(top m digits of S(c) fit inside c) with the same rate for
random top digits.
"""
import random
import sys
from collections import Counter


def fits(digits, c):
    need = Counter(digits)
    return all(c[x] >= k for x, k in need.items())


def run(b, d, samples, mmax, seed=1):
    rng = random.Random(seed)
    w = [0] + [x ** x for x in range(1, b)]
    lo, hi = b ** (d - 1), b ** d
    real = [0] * (mmax + 1)
    fake = [0] * (mmax + 1)
    n = 0
    while n < samples:
        digs = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(d - 1)]
        s = sum(w[x] for x in digs)
        if not lo <= s < hi:
            continue
        n += 1
        c = Counter(digs)
        top = []
        t = s
        while t:
            top.append(t % b)
            t //= b
        top.reverse()
        rnd = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(mmax)]
        for m in range(1, mmax + 1):
            real[m] += fits(top[:m], c)
            fake[m] += fits(rnd[:m], c)
    print(f"base {b}, d={d}, {samples} multisets with a d-digit sum")
    for m in range(1, mmax + 1):
        print(f"  top {m:2d} digits fit: sum {real[m]/n:.4f}  random {fake[m]/n:.4f}  ratio {real[m]/max(fake[m],1):.2f}")


if __name__ == '__main__':
    b = int(sys.argv[1])
    d = int(sys.argv[2]) if len(sys.argv) > 2 else b - 1
    run(b, d, int(sys.argv[3]) if len(sys.argv) > 3 else 100_000, 10)
