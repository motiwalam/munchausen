"""Random-digit model for the number of Munchausen numbers.

Model: for a digit multiset c with d digits, treat the digits of its sum
S(c) as independent and uniform (leading digit nonzero). Then the chance that
S(c) has exactly the histogram c is P(hist(n) = c) for a random d-digit
string n. Summing over all c whose sum has d digits gives

    E_d = P( F(n) has exactly d digits ),  n a random d-digit string,

the expected number of d-digit Munchausen numbers. This script estimates E_d
by sampling and compares the totals with the exhaustive results.
"""
import math
import sys
import numpy as np

from solutions import SOL

RNG = np.random.default_rng(1)


def expected(b, d, mode=1, samples=200_000):
    """Monte Carlo estimate of E_d (and its standard error)."""
    x = np.arange(b, dtype=float)
    with np.errstate(divide='ignore'):
        logw = np.where(x > 0, x * np.log(np.maximum(x, 1)), 0.0)
    scale = (d - 1) * math.log(b)
    w = np.exp(np.minimum(logw - scale, 700.0))
    w[0] = mode * math.exp(-scale)
    hits = 0
    done = 0
    while done < samples:
        n = min(50_000, samples - done)
        counts = RNG.multinomial(d - 1, np.full(b, 1.0 / b), size=n).astype(float)
        lead = RNG.integers(1, b, size=n)
        f = counts @ w + w[lead]
        hits += int(np.count_nonzero((f >= 1.0) & (f < b)))
        done += n
    p = hits / samples
    return p, math.sqrt(p * (1 - p) / samples)


def per_base(b, mode, samples, dmin=2):
    return {d: expected(b, d, mode, samples) for d in range(dmin, b + 1)}


def limit_terms(jmax=12):
    """Large-b limit of E_{b-j}: counts become independent Poisson(1)."""
    pois = lambda k: math.exp(-1) / math.factorial(k)
    out = {0: 1 - sum(pois(k) for k in range(3))}  # c_{b-1} >= 3
    for j in range(1, jmax + 1):
        # digits above b-j absent, and 1 <= c_{b-j} < e^j
        upper = min(math.ceil(math.e ** j) - 1, 60)
        out[j] = math.exp(-(j - 1)) * sum(pois(k) for k in range(1, upper + 1))
    return out



def by_offset(b0, b1, samples=60_000, jmax=10):
    """Model vs observed, grouped by j = b - d, for d >= b - jmax."""
    from collections import Counter
    for mode in (0, 1):
        exp = Counter()
        seen = Counter()
        for b in range(b0, b1 + 1):
            for j in range(0, jmax + 1):
                if b - j >= 2:
                    exp[j] += expected(b, b - j, mode, samples)[0]
            for t in SOL[mode][b]:
                seen[b - len(t) if b - len(t) <= jmax else 'small'] += 1
        print(f"0^0={mode}, bases {b0}-{b1}")
        for j in range(jmax + 1):
            print(f"  d=b-{j:<2d} expected {exp[j]:6.2f}  seen {seen[j]}")
        print(f"  d<b-{jmax}  seen {seen['small']}")


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'compare'
    if what == 'limit':
        t = limit_terms()
        for j, v in t.items():
            print(f"d = b-{j}: {v:.4f}")
        print(f"total {sum(t.values()):.6f}")
    elif what == 'compare':
        print("base  E(0^0=0)  seen  E(0^0=1)  seen")
        tot = [0, 0, 0, 0]
        for b in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
            row = []
            for mode in (0, 1):
                e = sum(p for p, _ in per_base(b, mode, 40_000).values())
                seen = len(SOL[mode][b])
                row += [e, seen]
            tot = [a + r for a, r in zip(tot, row)]
            print(f"{b:4d}  {row[0]:8.3f}  {row[1]:4d}  {row[2]:8.3f}  {row[3]:4d}", flush=True)
        print(f"sum   {tot[0]:8.2f}  {tot[1]:4d}  {tot[2]:8.2f}  {tot[3]:4d}")
    elif what == 'offsets':
        by_offset(int(sys.argv[2]), int(sys.argv[3]))
    elif what == 'base':
        b = int(sys.argv[2])
        res = per_base(b, 1, int(sys.argv[3]) if len(sys.argv) > 3 else 100_000, dmin=2)
        for d, (p, se) in res.items():
            if p > 1e-4:
                print(f"d={d:3d} (b-{b-d:2d}): {p:.4f} +/- {se:.4f}")
        print("total", sum(p for p, _ in res.values()))
