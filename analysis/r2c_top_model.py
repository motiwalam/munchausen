"""Question 44: does the scatter of lambda(b) come from the forced top digits?

    python3 r2c_top_model.py [N] [TMAX] > data/r2c_top_model.txt

lambda_m(b) is the mean count of near-solutions n = F(n) + j (b-1), j even,
at least b-6 digits (data/defects_bulk_b1.txt, bases 12 to 32). The refined
model predicts it with the digits of F treated as random. Here, for every
length d from b-6 to b, N random d-digit multisets are drawn as in model.py.
For those whose F has d digits and that meet the identity mod b-1, the top t
digits of F (t = 0..TMAX) are read off F, and the chance that the other
d - t digits complete the multiset replaces the uniform one (the ratio of
forced_top.py). t = 0 is the refined model. All t share one sample, so the
differences between t are not sampling noise of the window.

Lines: "base b m t expected se" and, at the end, the comparison with the
measured lambda: mean ratio, chi-square against the offsets' own standard
error, and correlation.
"""
import math
import os
import sys
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def expected_top(b, d, mode, N, tmax, rng):
    q = b - 1
    scale = (d - 1) * math.log(b)
    x = np.arange(b, dtype=float)
    w = np.exp(np.where(x > 0, x * np.log(np.maximum(x, 1)), 0.0) - scale)
    w[0] = mode * math.exp(-scale)
    u = np.array([((pow(v, v, q) if v > 0 else mode) - v) % q for v in range(b)], dtype=np.int64)
    sums = np.zeros(tmax + 1)
    sq = np.zeros(tmax + 1)
    done = 0
    while done < N:
        n = min(50_000, N - done)
        done += n
        c = rng.multinomial(d - 1, np.full(b, 1.0 / b), size=n)
        lead = rng.integers(1, b, size=n)
        c[np.arange(n), lead] += 1
        f = c @ w
        ok = (f >= 1.0) & (f < b) & ((c @ u) % q == 0)
        c, f = c[ok], f[ok]
        k = len(f)
        if k == 0:
            continue
        rows = np.arange(k)
        base = (d - c[:, 0]) / d
        num = np.ones(k)
        digs = []
        g = f.copy()
        for t in range(1, tmax + 1):
            v = np.floor(g).astype(np.int64) % b
            g = (g - np.floor(g)) * b
            used = np.zeros(k, dtype=np.int64)
            for prev in digs:
                used += (prev == v)
            digs.append(v)
            num = num * np.maximum(0, c[rows, v] - used) / (d - t + 1)
            ratio_t = (b - 1) * float(b) ** (t - 1) * num / base
            sums[t] += ratio_t.sum()
            sq[t] += (ratio_t ** 2).sum()
        sums[0] += k
        sq[0] += k
    mean = sums * q / N
    se = np.sqrt(sq) * q / N
    return mean, se


def measured():
    rows = defaultdict(dict)
    for line in open(os.path.join(HERE, 'data', 'defects_bulk_b1.txt')):
        if line.startswith('#'):
            continue
        b, m, j, n = map(int, line.split())
        rows[(b, m)][j] = n
    out = {}
    for k, d in rows.items():
        ev = [n for j, n in d.items() if j and j % 2 == 0]
        lam = sum(ev) / len(ev)
        var = sum((e - lam) ** 2 for e in ev) / (len(ev) - 1)
        out[k] = (lam, math.sqrt(var / len(ev)))
    return out


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 400_000
    tmax = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    meas = measured()
    rng = np.random.default_rng(44)
    model = {}
    print(f"# N = {N} strings per length, lengths b-6..b, t = 0..{tmax}")
    for (b, m) in sorted(meas):
        tot = np.zeros(tmax + 1)
        var = np.zeros(tmax + 1)
        for d in range(b - 6, b + 1):
            mean, se = expected_top(b, d, m, N, tmax, rng)
            tot += mean
            var += se ** 2
        model[(b, m)] = (tot, np.sqrt(var))
        for t in range(tmax + 1):
            print(f"base {b} {m} {t} {tot[t]:.4f} {math.sqrt(var[t]):.4f}", flush=True)
    for m in (0, 1):
        keys = [k for k in sorted(meas) if k[1] == m]
        lam = np.array([meas[k][0] for k in keys])
        lse = np.array([meas[k][1] for k in keys])
        for t in range(tmax + 1):
            e = np.array([model[k][0][t] for k in keys])
            ese = np.array([model[k][1][t] for k in keys])
            chi = float(np.sum((lam - e) ** 2 / (lse ** 2 + ese ** 2)))
            print(f"summary 0^0={m} t={t}: mean lambda/model {np.mean(lam / e):.3f}, sd of ratio {np.std(lam / e):.3f}, "
                  f"chi2 {chi:.1f} on {len(keys)} bases, correlation {np.corrcoef(lam, e)[0, 1]:.3f}")


if __name__ == '__main__':
    main()
