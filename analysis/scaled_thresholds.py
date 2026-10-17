"""How the deficit threshold must grow with b to keep the miss rate bounded.

For each deficit threshold c, replays planted solutions in several bases and
reports the fraction that the deficit rule alone would cut.
"""
import random
import sys
from walk import Rules, replay, planted, planted_lengths

if __name__ == '__main__':
    cs = [2.0, 2.5, 3.0, 3.5, 4.0]
    for b in map(int, sys.argv[1:]):
        rng = random.Random(7)
        n = 300 if b <= 100 else 120
        sols = [planted(b, planted_lengths(b, rng), rng) for _ in range(n)]
        cut = {c: sum(replay(b, s, Rules(deficit=c)) is not None for s in sols) / n for c in cs}
        print(f"base {b} ({n} samples): " + ", ".join(f"c={c}: {v:.3f}" for c, v in cut.items()), flush=True)
