"""Probability that a base has no nontrivial solution under either convention.

E_union = E_0 + E_1 - E_shared, where E_shared counts zero-free solutions
(solutions under both conventions). Refined model (digit-sum identity) for
each term; P(empty) = exp(-E_union) if solutions occur independently.
"""
import math
import sys
import numpy as np
from model import RNG
from catalog import exhaustive_bases


def expected_parts(b, d, samples=200_000):
    """Refined-model expectations of d-digit solutions: (E0, E1, Eshared)."""
    m = b - 1
    x = np.arange(b, dtype=float)
    logw = np.where(x > 0, x * np.log(np.maximum(x, 1)), 0.0)
    scale = (d - 1) * math.log(b)
    w = np.exp(np.minimum(logw - scale, 700.0))
    u = {mode: np.array([((pow(int(v), int(v), m) if v > 0 else mode) - int(v)) % m for v in range(b)], dtype=np.int64)
         for mode in (0, 1)}
    hits = np.zeros(3)
    done = 0
    while done < samples:
        n = min(50_000, samples - done)
        counts = RNG.multinomial(d - 1, np.full(b, 1.0 / b), size=n)
        lead = RNG.integers(1, b, size=n)
        counts[np.arange(n), lead] += 1
        f0 = counts @ w
        f1 = f0 + counts[:, 0] * math.exp(-scale)
        ok0 = (f0 >= 1.0) & (f0 < b) & ((counts @ u[0]) % m == 0)
        ok1 = (f1 >= 1.0) & (f1 < b) & ((counts @ u[1]) % m == 0)
        hits += [ok0.sum(), ok1.sum(), (ok0 & ok1 & (counts[:, 0] == 0)).sum()]
        done += n
    return hits * m / samples


if __name__ == '__main__':
    b0, b1 = int(sys.argv[1]), int(sys.argv[2])
    ex = exhaustive_bases()
    rows = []
    for b in range(b0, b1 + 1):
        e = sum(expected_parts(b, d, 60_000) for d in range(2, b + 1))
        union = e[0] + e[1] - e[2]
        empty = ex.get((0, b)) is not None and not ex[(0, b)] and not ex[(1, b)]
        rows.append((b, e, union, math.exp(-union), empty))
        print(f"{b:3d}  E0 {e[0]:.2f}  E1 {e[1]:.2f}  shared {e[2]:.2f}  union {union:.2f}  P(empty) {math.exp(-union):.3f}  {'EMPTY' if empty else ''}", flush=True)
    for par, name in ((0, 'even'), (1, 'odd')):
        sel = [r for r in rows if r[0] % 2 == par and (0, r[0]) in ex]
        exp = sum(r[3] for r in sel)
        obs = sum(r[4] for r in sel)
        p0 = math.prod(1 - r[3] for r in sel)
        print(f"{name} bases {b0}-{b1}: expected empty {exp:.2f}, observed {obs}; P(none empty) = {p0:.3f}")
