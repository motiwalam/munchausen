"""How far is the census from the refined model, in units of its own scatter?

Solutions in F_q[T] come in linear families, so the count of one base is a
clumped draw, and bases in one orbit of T -> aT + b have equal counts. This
script treats each orbit as one independent draw whose variance is the
variance of the counts among orbits with the same k(B), and reports the mean
per base, the refined model, and the z-score of the difference.
usage: python3 r4f_dispersion.py file...
"""
import re
import sys
from collections import defaultdict
from r4f_byk import load


def main():
    print("q e m  bases  orbits  census/base  refined/base  ratio  sd/base  z")
    for path in sys.argv[1:]:
        q, e, m = map(int, re.search(r'q(\d+)e(\d+)m(\d+)', path).groups())
        rows = load(path)
        nb = sum(r['size'] for r in rows)
        byk = defaultdict(list)
        for r in rows:
            byk[r['k']].append(r)
        var = 0.0
        for k, rs in byk.items():
            w = sum(r['size'] for r in rs)
            # variance of the per-base residual N - E among orbits of this k, base-weighted
            res = [(r['sols'] - r['refined'], r['size']) for r in rs]
            mu = sum(x * s for x, s in res) / w
            v = sum(s * (x - mu) ** 2 for x, s in res) / w
            var += sum(r['size'] ** 2 for r in rs) * v
        mean = sum(r['sols'] * r['size'] for r in rows) / nb
        ref = sum(r['refined'] * r['size'] for r in rows) / nb
        sd = var ** 0.5 / nb
        print(f"{q:2d} {e} {m} {nb:6d} {len(rows):6d} {mean:12.3f} {ref:13.3f} {mean / ref:6.3f} {sd:8.3f} {(mean - ref) / sd:5.1f}")


if __name__ == '__main__':
    main()
