"""Calibration of the null laws of ln E on planted search paths.

    python3 r5p_calib.py <base> [<base> ...]

For each law (poisson, cond) and each model order, prints the weighted mean
and standard deviation of z = (ln E - mean) / sd by level fraction
u = k / (kmax + 1), and the planted miss rate P(z_min < -c) for the rule
that starts at u <= 3/4.
"""
import math
import sys
from collections import defaultdict

from r5p_law import poisson_law, cond_law, ln_e, read_traces

LAWS = {'poisson': poisson_law, 'cond': cond_law}


def zs(b, kmax, recs, law):
    out = []
    for k, pp, rf, lneed in recs:
        if pp == 0:
            continue
        mu, sd = law(b, kmax, k, pp)
        out.append((k / (kmax + 1), (ln_e(b, k, pp, rf, lneed) - mu) / sd))
    return out


def main():
    for b in map(int, sys.argv[1:]):
        for order in (1, 2):
            data = list(read_traces(f'data/r5p_trace_b{b}_o{order}.txt'))
            for name, law in LAWS.items():
                acc = defaultdict(lambda: [0.0, 0.0, 0.0])
                mins = []
                for d, kmax, w, recs in data:
                    if w == 0:
                        continue
                    z = zs(b, kmax, recs, law)
                    for u, v in z:
                        a = acc[min(int(u * 10), 9)]
                        a[0] += w
                        a[1] += w * v
                        a[2] += w * v * v
                    mins.append((w, min((v for u, v in z if u <= 0.75), default=99)))
                row = []
                for i in sorted(acc):
                    W, s1, s2 = acc[i]
                    m = s1 / W
                    row.append(f"{i / 10:.1f}:{m:+.2f}/{math.sqrt(s2 / W - m * m):.2f}")
                W = sum(w for w, _ in mins)
                miss = " ".join(f"c={c}:{sum(w for w, z in mins if z < -c) / W:.4f}" for c in (2, 2.5, 3, 3.5, 4, 5))
                print(f"b={b} order={order} law={name} n={len(mins)}\n  mean/sd of z by u: {' '.join(row)}\n  miss: {miss}", flush=True)


if __name__ == '__main__':
    main()
