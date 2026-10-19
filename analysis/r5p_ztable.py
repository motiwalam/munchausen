"""A cost-aware null law for --ztable: cut a node when E / T is small.

    python3 r5p_ztable.py <tree-stats file> <base> <scale> > <ztable file>

E is the model's expected number of solutions below a node, and T(d, k, pp)
the mean size of a subtree at that cell of the search tree (fast search
--tree-stats). Keeping the nodes with the largest E / T is the greedy
solution of the knapsack: most expected solutions per node visited. The
table sets mean = ln T + M and sd = scale, so the z-score of a node is
(ln E - ln T - M) / scale. M is the median, over planted solutions of this
base, of the smallest ln E - ln T on their path, so z = 0 is a typical
worst value. Cells without data take the mean subtree size of their level.
"""
import math
import os
import statistics
import sys
from collections import defaultdict

from r5p_law import ln_e, read_traces

HERE = os.path.dirname(os.path.abspath(__file__))


def load_t(path):
    cell, lev = {}, defaultdict(lambda: [0, 0])
    for line in open(path):
        if line.startswith('#'):
            continue
        d, k, pp, n, s = map(int, line.split())
        cell[(d, k, pp)] = math.log(s / n)
        lev[(d, k)][0] += n
        lev[(d, k)][1] += s
    return cell, {key: math.log(s / n) for key, (n, s) in lev.items()}


def ln_t(cell, lev, d, k, pp):
    return cell.get((d, k, pp), lev.get((d, k), 0.0))


def path_min(b, d, recs, cell, lev):
    return min((ln_e(b, k, pp, rf, lneed) - ln_t(cell, lev, d, k, pp) for k, pp, rf, lneed in recs if pp > 0), default=math.inf)


def offset(b, cell, lev):
    vals = [path_min(b, d, recs, cell, lev) for d, kmax, w, recs in read_traces(os.path.join(HERE, 'data', f'r5p_trace_b{b}_o1.txt'))]
    return statistics.median(v for v in vals if v < math.inf)


def main():
    path, b, scale = sys.argv[1], int(sys.argv[2]), float(sys.argv[3])
    cell, lev = load_t(path)
    m = offset(b, cell, lev)
    print(f"# E/T law from {os.path.basename(path)}, base {b}: mean = ln T + {m:.4f}, sd = {scale}")
    ds = sorted({d for d, k in lev})
    for d in ds:
        for k in range(2, d + 2):
            for pp in range(1, d + 1):
                print(f"{d} {k} {pp} {ln_t(cell, lev, d, k, pp) + m:.6f} {scale}")


if __name__ == '__main__':
    main()
