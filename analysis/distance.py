"""Is hist(S(c)) closer to c than the histogram of random digits?

For random multisets c with d digits whose sum S(c) has d digits, compare the
distance D = sum |hist(S) - c| with the distance for random digit strings that
obey the same digit-sum identity. A real excess of solutions shows up as a
heavier lower tail of D.
"""
import random
import sys
from collections import Counter


def run(b, d, mode, samples, seed=7):
    rng = random.Random(seed)
    w = [mode] + [x ** x for x in range(1, b)]
    lo, hi = b ** (d - 1), b ** d
    real, fake = Counter(), Counter()
    n = 0
    while n < samples:
        digs = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(d - 1)]
        s = sum(w[x] for x in digs)
        if not lo <= s < hi:
            continue
        c = Counter(digs)
        h = Counter()
        t = s
        while t:
            h[t % b] += 1
            t //= b
        # random digits with the same digit sum modulo b-1 as S
        target = s % (b - 1)
        while True:
            r = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(d - 1)]
            if sum(r) % (b - 1) == target:
                break
        g = Counter(r)
        n += 1
        real[sum(abs(h[x] - c[x]) for x in range(b))] += 1
        fake[sum(abs(g[x] - c[x]) for x in range(b))] += 1
    print(f"base {b} d={d} 0^0={mode}: P(D <= t), real vs random, {samples} samples")
    cr = cf = 0
    for t in range(0, 22, 2):
        cr += real[t] + real[t + 1]
        cf += fake[t] + fake[t + 1]
        print(f"  t={t+1:2d}  real {cr/n:.5f}  random {cf/n:.5f}  ratio {cr/max(cf,1):.2f}")


if __name__ == '__main__':
    b, mode, samples = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    run(b, b - 1, mode, samples)
