"""Distribution of the worst deficit along a planted solution's search path.

The deficit rule cuts a node when the high digits in the known prefix fall
c standard deviations short of their mean. One replay gives the worst
(most negative) standardized shortfall z_min on the whole path, so the miss
rate of the rule for every c is P(z_min < -c). Watching how this law moves
with b tells how c must grow to keep the miss rate fixed.
"""
import math
import random
import sys
from walk import Rules, replay, planted, planted_lengths


class Track(Rules):
    def __init__(self):
        super().__init__(deficit=0.0)
        self.zmin = math.inf

    def deficit_ok(self, d, known, m, oh):
        q = m / d
        var = known * q * (1 - q) * (d - known) / (d - 1)
        if var > 0:
            self.zmin = min(self.zmin, (oh + 0.5 - known * q) / math.sqrt(var))
        return True


if __name__ == '__main__':
    for b in map(int, sys.argv[1:]):
        rng = random.Random(11)
        n = 400 if b <= 100 else (150 if b <= 200 else 60)
        zs = []
        for _ in range(n):
            t = Track()
            replay(b, planted(b, planted_lengths(b, rng), rng), t)
            zs.append(t.zmin)
        zs.sort()
        q = lambda p: zs[int(p * n)]
        miss = {c: sum(z < -c for z in zs) / n for c in (2.0, 2.5, 3.0, 3.5)}
        print(f"base {b} ({n}): median z_min {q(0.5):.2f}, 10% {q(0.1):.2f}, 2% {q(0.02):.2f}; "
              + ", ".join(f"P(z<-{c}) {v:.3f}" for c, v in miss.items()), flush=True)
