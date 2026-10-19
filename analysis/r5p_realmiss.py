"""Misses of the typical-set rules on the real solutions (data/r5p_trace_real.txt).

    python3 r5p_realmiss.py

For each rule and threshold, lists the real solutions in bases 10 to 43 that
the rule cuts, by replaying their paths (r5p_real.py).
"""
import math
import os

from r5p_law import poisson_law, cond_law
from r5p_curves import zmin

HERE = os.path.dirname(os.path.abspath(__file__))
RULES = [('poisson', '0.75', '0', c) for c in (2.5, 2.94, 3.0, 3.33)] + \
        [('cond', '0.75', '0', c) for c in (2.75, 3.0, 3.37, 3.82)] + \
        [('cond', '1', '2', c) for c in (3.1, 3.42, 3.83)]
LAWS = {'poisson': poisson_law, 'cond': cond_law}


def main():
    rows = []
    for line in open(os.path.join(HERE, 'data', 'r5p_trace_real.txt')):
        f = line.split()
        b, d, kmax = int(f[0]), int(f[1]), int(f[2])
        recs = [tuple(map(float, r.split(','))) for r in f[4:]]
        recs = [(int(k), int(pp), int(rf), ln) for k, pp, rf, ln in recs]
        rows.append((b, d, kmax, recs))
    long_ = [r for r in rows if r[1] >= r[0] - 6]
    print(f"{len(rows)} distinct solutions with >= 3 digits in bases 10-41 and 43, {len(long_)} with >= b-6 digits")
    for law, zf, sl, c in RULES:
        cut = [(b, d) for b, d, kmax, recs in rows if zmin(b, kmax, recs, LAWS[law], zf, sl) < -c]
        cl = [(b, d) for b, d in cut if d >= b - 6]
        print(f"{law} zfrom {zf} zslope {sl} c {c}: cuts {len(cut)}, {len(cl)} of them with >= b-6 digits: {cut}")


if __name__ == '__main__':
    main()
