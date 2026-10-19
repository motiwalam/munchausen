"""Census counts split by k(B), from analysis/data/r4f_census_q*e*m*.txt.

For each k: bases, mean solutions per base divided by q(q-1) (the number of
families of q translates and q - 1 scalings under 0^0 = 0), the refined model
on the same scale, q^k / (q(q-1)), and the solution lengths.
usage: python3 r4f_byk.py file...
"""
import re
import sys
from collections import Counter, defaultdict


def load(path):
    rows = []
    for line in open(path):
        m = re.match(r'orbit (\d+) size (\d+) k (\d+) sols (\d+) basic (\S+) refined (\S+) lengths (\S*)(?: zeros0 (\d+))?', line)
        if m:
            lens = Counter()
            for part in m.group(7).split(','):
                if part:
                    a, b = part.split(':')
                    lens[int(a)] += int(b)
            rows.append(dict(code=int(m.group(1)), size=int(m.group(2)), k=int(m.group(3)), sols=int(m.group(4)),
                             basic=float(m.group(5)), refined=float(m.group(6)), lens=lens, zeros0=int(m.group(8)) if m.group(8) else None))
    return rows


def main():
    for path in sys.argv[1:]:
        q, e, mm = map(int, re.search(r'q(\d+)e(\d+)m(\d+)', path).groups())
        rows = load(path)
        norm = q * (q - 1)
        print(f"# q {q} e {e} m {mm}")
        byk = defaultdict(list)
        for r in rows:
            byk[r['k']].append(r)
        for k in sorted(byk):
            rs = byk[k]
            w = sum(r['size'] for r in rs)
            s = sum(r['sols'] * r['size'] for r in rs) / w
            ref = sum(r['refined'] * r['size'] for r in rs) / w
            lens = Counter()
            for r in rs:
                for L, v in r['lens'].items():
                    lens[L] += v * r['size']
            print(f"k {k} bases {w} sols/base {s:.3f} refined {ref:.3f} ratio {s / ref:.3f} "
                  f"sols/q(q-1) {s / norm:.4f} q^k/q(q-1) {q ** k / norm:.4f} lengths {sorted(lens.items())}")


if __name__ == '__main__':
    main()
