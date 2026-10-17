"""Miss rates of the inexact rules: on real solutions, and on planted ones."""
import random
import sys
from walk import Rules, replay, planted, planted_lengths
from catalog import exhaustive_bases

CONFIGS = {
    'ratio 3e-3': Rules(ratio=3e-3),
    'ratio 1e-2': Rules(ratio=1e-2),
    'ratio 1e-2, deficit 2': Rules(ratio=1e-2, deficit=2),
    'ratio 3e-3, deficit 2, band 2.5': Rules(ratio=3e-3, deficit=2, band=2.5),
    'deficit 2, band 2.5': Rules(deficit=2, band=2.5),
}


def real():
    ex = exhaustive_bases()
    out = {}
    for name, r in CONFIGS.items():
        bulk = [0, 0]
        for (m, b), ts in ex.items():
            if b < 20:
                continue
            for t in ts:
                if len(t) >= b - 6:
                    bulk[1] += 1
                    bulk[0] += replay(b, t, r) is not None
        out[name] = bulk
    return out


def plant(b, n, seed=1):
    rng = random.Random(seed)
    sols = [planted(b, planted_lengths(b, rng), rng) for _ in range(n)]
    return {name: sum(replay(b, s, r) is not None for s in sols) / n for name, r in CONFIGS.items()}


if __name__ == '__main__':
    print("real solutions with at least b-6 digits, bases 20-43 (both conventions):")
    for name, (miss, tot) in real().items():
        print(f"  {name:22s} missed {miss}/{tot} = {miss/tot:.3f}")
    for b in map(int, sys.argv[1:]):
        n = 400 if b <= 60 else 200
        res = plant(b, n)
        print(f"planted solutions, base {b} ({n} samples): " + ", ".join(f"{k}: {v:.3f}" for k, v in res.items()), flush=True)
