"""Question 110: a last-digit factor in negative bases?

    python3 r6c_nega_lastdigit.py [N] > data/r6c_nega_lastdigit.txt

In base -b the last digit of n is n mod b. A near-solution n = F + D has
last digit v = (F + D) mod b, and a random arrangement of the multiset c
ends in v with chance c_v / d, against 1/b for a uniform digit. So the
offsets with D == r (mod b) carry the factor

    L(r) = E[ b c_((F + r) mod b) / d ]

over the model's candidates: strings of odd length d whose F has d digits
in base -b and that meet the identity modulo b + 1 (wld_negamodel.py), each
counted with its refined weight. The family `j step b` of section 23.2 has
D == 0 (mod b), so its factor is L(0), as for D = 0 itself. The family
`j step` has D = j step, step = b + 1 (odd b) or 2(b + 1) (even b), so
D == j or 2j (mod b), and its factor is the mean of L over j = 1..20.

The script prints the model's ratio L(0) / mean L(step j) per base and
convention, and the observed ratio of the two families
(data/r2c_nega_offsets.txt, 20 offsets each, at least 3 digits). The same
factor for positive bases (D == 0 mod b against D == j(b-1)) is printed
for comparison.
"""
import math
import os
import sys
from collections import defaultdict

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
J = 20


def factors(b, m, N, rng, negative=True):
    """Weighted mean of b c_v / d for v = (F + r) mod b, r = 0..b-1."""
    M = b + 1 if negative else b - 1
    wf = np.array([float(m)] + [float(x) ** x for x in range(1, b)])
    wmod = np.array([m % b] + [pow(x, x, b) for x in range(1, b)], dtype=np.int64)
    wres = np.array([m % M] + [(pow(x, x, M) - x) % M for x in range(1, b)], dtype=np.int64)
    num = np.zeros(b)
    den = 0.0
    lens = range(3, b + 2, 2) if negative else range(max(2, b - 8), b + 1)
    for d in lens:
        if negative:
            lo = (b ** (d - 1) - 1) // (b + 1)
            hi = (b ** (d + 1) - 1) // (b + 1)
        else:
            lo, hi = b ** (d - 1), b ** d - 1
        done = 0
        while done < N:
            n = min(20_000, N - done)
            done += n
            s = rng.integers(0, b, size=(n, d))
            s[:, 0] = rng.integers(1, b, size=n)
            c = np.zeros((n, b), dtype=np.int64)
            for i in range(d):
                c[np.arange(n), s[:, i]] += 1
            f = c @ wf
            ok = (f > lo) & (f <= hi) if negative else (f >= lo) & (f <= hi)
            ok &= (c @ wres) % M == 0
            if not ok.any():
                continue
            cc = c[ok]
            fm = (cc @ wmod) % b
            k = len(cc)
            den += k
            for r in range(b):
                v = (fm + r) % b
                num[r] += (b * cc[np.arange(k), v] / d).sum()
    return num / den if den else num * float('nan'), den


def observed():
    tot = defaultdict(float)
    for line in open(os.path.join(HERE, 'data', 'r2c_nega_offsets.txt')):
        f = line.split()
        if f[0] != 'off':
            continue
        b, m, fam, j, n = int(f[1]), int(f[2]), f[3], int(f[4]), int(f[5])
        tot[(b, m, fam)] += n
    return tot


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000
    rng = np.random.default_rng(110)
    obs = observed()
    print(f"# N = {N} strings per length; L(0), mean L over the family j step, model ratio, observed stepb / step")
    sums = defaultdict(lambda: [0.0, 0.0, 0.0, 0.0, 0])
    for b in range(10, 28):
        step = b + 1 if b % 2 else 2 * (b + 1)
        for m in (0, 1):
            L, k = factors(b, m, N, rng)
            mean_step = np.mean([L[(j * step) % b] for j in range(1, J + 1)])
            ob_s, ob_b = obs.get((b, m, 'step'), float('nan')), obs.get((b, m, 'stepb'), float('nan'))
            grp = 'mult3' if b % 3 == 0 else 'other'
            sums[(grp, m)][0] += ob_s
            sums[(grp, m)][1] += ob_b
            sums[(grp, m)][2] += L[0]
            sums[(grp, m)][3] += mean_step
            sums[(grp, m)][4] += 1
            print(f"neg {b} {m} L0 {L[0]:.4f} Lstep {mean_step:.4f} ratio {L[0] / mean_step:.4f} "
                  f"obs_step {ob_s:.0f} obs_stepb {ob_b:.0f} obs_ratio {ob_b / ob_s if ob_s else float('nan'):.3f} "
                  f"Lmin {L.min():.3f} Lmax {L.max():.3f} n {k:.0f}", flush=True)
    for (grp, m), v in sorted(sums.items()):
        print(f"group {grp} m {m}: observed step {v[0]:.0f} stepb {v[1]:.0f} ratio {v[1] / v[0]:.3f}; "
              f"model mean L0 {v[2] / v[4]:.4f} mean Lstep {v[3] / v[4]:.4f} ratio {v[2] / v[3]:.4f}")
    for b in (10, 16, 20, 26):
        for m in (0, 1):
            L, k = factors(b, m, N, rng, negative=False)
            mean_other = np.mean([L[(j * (b - 1)) % b] for j in range(1, J + 1)])
            print(f"pos {b} {m} L0 {L[0]:.4f} Lshift {mean_other:.4f} ratio {L[0] / mean_other:.4f} "
                  f"Lmin {L.min():.3f} Lmax {L.max():.3f}", flush=True)


if __name__ == '__main__':
    main()
