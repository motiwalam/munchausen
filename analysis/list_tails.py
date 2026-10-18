"""Expected number of k-digit solutions missing from the lists, by the
integer-root heuristic (local factors average 1, so they drop out of the
expectation): strings whose largest digit exceeds the list's bound M."""
import math
import random
import sys
from root_heuristic import root

def tail(k, M, mode=1, xs=40, samples=400, rng=random.Random(1)):
    tot = 0.0
    for x in range(M + 1, M + 1 + xs):
        count = (x + 1) ** k - x ** k  # strings with digits <= x and some digit = x
        acc = 0.0
        for _ in range(samples):
            s = [rng.randrange(x + 1) for _ in range(k)]
            s[rng.randrange(k)] = x
            if s[0] == 0:
                s[0] = rng.randrange(1, x + 1)
            F = sum((mode if v == 0 else v ** v) for v in s)
            r = root(tuple(s), F)
            if r is None:
                continue
            dP = sum((k - 1 - i) * c * r ** (k - 2 - i) for i, c in enumerate(s[:-1]))
            acc += min(1.0, 1.0 / dP)
        term = count * acc / samples
        tot += term
        if term < tot * 1e-6:
            break
    return tot

for k, M in [(3, 80), (4, 44), (4, 150), (5, 28), (5, 60), (6, 20), (6, 40), (7, 26)]:
    t = tail(k, M)
    print(f"k={k}, digits <= {M}: expected solutions with a larger digit {t:.1e}", flush=True)
