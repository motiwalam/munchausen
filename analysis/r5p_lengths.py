"""What a length window saves, against what the z-score threshold saves.

    python3 r5p_lengths.py <base> [<base> ...]

The share of nodes and evaluations per J = b - d comes from the --zhist
histograms (data/r5p_zhist/). A window keeps the lengths with J in [j0, j1].
Its planted miss rate counts the planted solutions outside the window or cut
by the rule. The alternative spends the same extra miss rate on a smaller
threshold c over all lengths. Both are compared at the base rule
(law, zfrom, c).
"""
import math
import sys

from r5p_law import poisson_law, cond_law
from r5p_curves import GRID, hist, planted_zmins, at_miss
from r5p_trace import planted_lengths  # noqa: F401  (documents the length law)
import os
from r5p_law import read_traces

HERE = os.path.dirname(os.path.abspath(__file__))
LAWS = {'poisson': poisson_law, 'cond': cond_law}
WINDOWS = [(1, 99), (0, 3), (1, 3), (0, 2), (1, 2), (0, 4)]


def lengths(b):
    return [d for d, kmax, w, recs in read_traces(os.path.join(HERE, 'data', f'r5p_trace_b{b}_o1.txt'))]


def main():
    for b in map(int, sys.argv[1:]):
        ds = lengths(b)
        for law, zf, c0 in (('poisson', '0.75', 3.0), ('cond', '0.75', 3.35)):
            h = hist(b, law, zf, '0', by_d=True)
            if h is None:
                continue
            i0 = min(range(len(GRID)), key=lambda i: abs(GRID[i] - c0))
            tot_n = sum(v[i0][0] for v in h.values())
            tot_e = sum(v[i0][1] for v in h.values())
            zm = planted_zmins(b, 1, LAWS[law], zf)
            share = {}
            for d in ds:
                share[b - d] = share.get(b - d, 0) + 1 / len(ds)
            print(f"base {b}, {law} zfrom {zf} c {GRID[i0]}: {tot_n} nodes")
            print("  J: share of nodes / evals / planted solutions")
            print("   " + " ".join(f"J{b - d}:{h[d][i0][0] / tot_n:.3f}/{h[d][i0][1] / tot_e:.3f}/{share.get(b - d, 0):.3f}" for d in sorted(h, reverse=True) if b - d <= 8))
            m_all = [sum(1 for z in zm if z[1] < -c) / len(zm) for c in GRID]
            n_all = [sum(v[i][0] for v in h.values()) for i in range(len(GRID))]
            base_miss = m_all[i0]
            for j0, j1 in WINDOWS:
                keep = [d for d in h if j0 <= b - d <= j1]
                n_w = sum(h[d][i0][0] for d in keep)
                e_w = sum(h[d][i0][1] for d in keep)
                miss_w = sum(1 for d, (w, z) in zip(ds, zm) if not (j0 <= b - d <= j1) or z < -GRID[i0]) / len(zm)
                c_alt, n_alt = at_miss(m_all, n_all, miss_w)
                alt = f"threshold c={c_alt:.2f} at the same miss rate saves {tot_n / n_alt:.2f}x" if c_alt else ""
                print(f"  window J in [{j0}, {j1}]: saves {tot_n / n_w:.2f}x nodes, {tot_e / e_w:.2f}x evals; "
                      f"planted miss {base_miss:.4f} -> {miss_w:.4f}; {alt}", flush=True)


if __name__ == '__main__':
    main()
