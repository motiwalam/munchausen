"""Law of the worst typical-set score along a solution's search path.

For each solution (real or planted), replay its path and record the smallest
z = (ln E - mean) / sd over all levels. The --zscore c rule cuts the solution
exactly when z_min < -c, so this law gives the miss rate for every c.
"""
import math
import random
import sys
from walk import Rules, replay, planted, planted_lengths, likelihood_law
from catalog import exhaustive_bases


class Track(Rules):
    def __init__(self):
        super().__init__(zscore=0.0)
        self.zmin = math.inf

    def typical_ok(self, b, kmax, k, pp, ln_e):
        mean, sd = likelihood_law(b, kmax, k, pp)
        if pp > 0 and 4 * k <= 3 * (kmax + 1):
            self.zmin = min(self.zmin, (ln_e - mean) / sd)
        return True


def zmin(b, digits):
    t = Track()
    replay(b, digits, t)
    return t.zmin


def summary(name, zs):
    zs = sorted(zs)
    n = len(zs)
    miss = ", ".join(f"P(z<-{c}) {sum(z < -c for z in zs) / n:.3f}" for c in (2.0, 2.5, 3.0, 3.5, 4.0))
    print(f"{name} ({n}): median z_min {zs[n // 2]:.2f}, 10% {zs[int(0.1 * n)]:.2f}; {miss}", flush=True)


if __name__ == '__main__':
    ex = exhaustive_bases()
    real = [zmin(b, t) for (m, b), ts in ex.items() if b >= 20 for t in ts if len(t) >= b - 6]
    summary("real solutions, bases 20-43, >= b-6 digits", real)
    for b in map(int, sys.argv[1:]):
        rng = random.Random(13)
        n = 400 if b <= 100 else (150 if b <= 200 else 60)
        summary(f"planted, base {b}", [zmin(b, planted(b, planted_lengths(b, rng), rng)) for _ in range(n)])
