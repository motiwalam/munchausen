"""Can iterating n -> F(n) find solutions? Solutions are the fixed points.

From random starting numbers, iterate F until the orbit repeats (Brent's
algorithm) and record the tail length, the cycle length and whether the cycle
is a nontrivial fixed point. F only depends on the digit multiset, so the
orbit lives on multisets; a random-mapping model predicts orbit lengths of
about sqrt(number of reachable multisets) and a tiny chance to end at a
given fixed point.
"""
import random
import statistics
import sys


def digits(n, b):
    out = []
    while n:
        n, r = divmod(n, b)
        out.append(r)
    return out or [0]


def F(n, b, w):
    return sum(w[x] for x in digits(n, b))


def brent(x0, f):
    power = lam = 1
    tort, hare = x0, f(x0)
    while tort != hare:
        if power == lam:
            tort, power, lam = hare, power * 2, 0
        hare = f(hare)
        lam += 1
    tort = hare = x0
    for _ in range(lam):
        hare = f(hare)
    mu = 0
    while tort != hare:
        tort, hare, mu = f(tort), f(hare), mu + 1
    return mu, lam, tort


if __name__ == '__main__':
    mode = 1
    for b in map(int, sys.argv[1:]):
        w = [mode] + [x ** x for x in range(1, b)]
        f = lambda n: F(n, b, w)
        rng = random.Random(b)
        trials = 200
        tails, cycles, fixed = [], [], 0
        cyc_set = set()
        for _ in range(trials):
            n = rng.randrange(b ** (b - 2), b ** (b - 1))
            mu, lam, start = brent(n, f)
            tails.append(mu)
            cycles.append(lam)
            if lam == 1 and start > 1:
                fixed += 1
            # canonical cycle representative
            c, x = [start], f(start)
            while x != start:
                c.append(x)
                x = f(x)
            cyc_set.add(min(c))
        print(f"base {b}: median tail {statistics.median(tails):.0f}, median cycle {statistics.median(cycles):.0f}, "
              f"max tail+cycle {max(t + c for t, c in zip(tails, cycles))}, distinct cycles {len(cyc_set)}, "
              f"orbits ending at a nontrivial fixed point {fixed}/{trials}", flush=True)
