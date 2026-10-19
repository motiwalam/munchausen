"""Trade-off curves of the typical-set rule: nodes against miss rate.

    python3 r5p_curves.py <base> [<base> ...]

For each configuration (law, zfrom) with a histogram in data/r5p_zhist/
(written by fast search --zscore 5 --zhist), the nodes and interval
evaluations at threshold c are the bins with z >= -c. The miss rate at c is
the share of planted solutions (r5p_trace.py, both model orders) whose
smallest z on the tested levels is below -c. Then, for a set of target miss
rates, the threshold and the nodes of each configuration.
"""
import bisect
import math
import os
import sys
from collections import defaultdict

from r5p_law import poisson_law, cond_law, ln_e, read_traces

HERE = os.path.dirname(os.path.abspath(__file__))
LAWS = {'poisson': poisson_law, 'cond': cond_law}
CONFIGS = [('poisson', '0.75', '0'), ('cond', '0.75', '0'), ('cond', '1', '0'), ('poisson', '1', '0')]
CONFIGS += [('cond', zf, s) for s in ('-4', '-2', '2', '4', '6') for zf in ('0.75', '1')]
CONFIGS += [('table', '1', '0')]
GRID = [round(1.0 + 0.05 * i, 2) for i in range(81)]  # 1.0 .. 5.0


def table_law(b):
    """the law of data/r5p_ztable_b<b>.txt, falling back to cond"""
    t = {}
    path = os.path.join(HERE, 'data', f'r5p_ztable_b{b}.txt')
    if os.path.exists(path):
        for line in open(path):
            if not line.startswith('#'):
                d, k, pp, m, sd = line.split()
                t[(int(d), int(k), int(pp))] = (float(m), float(sd))
    return lambda b, kmax, k, pp, d: t.get((d, k, pp)) or cond_law(b, kmax, k, pp)


def zmin(b, kmax, recs, law, zfrom, slope='0', d=None):
    zk = math.floor(float(zfrom) * (kmax + 1))
    s = float(slope)
    z = math.inf
    for k, pp, rf, lneed in recs:
        if k <= zk:
            mu, sd = law(b, kmax, k, pp, d) if d is not None else law(b, kmax, k, pp)
            z = min(z, (ln_e(b, k, pp, rf, lneed) - mu) / sd + s * (k / (kmax + 1) - 0.5))
    return z


def planted_zmins(b, order, law, zfrom, slope='0'):
    out = []
    for d, kmax, w, recs in read_traces(os.path.join(HERE, 'data', f'r5p_trace_b{b}_o{order}.txt')):
        out.append((w, zmin(b, kmax, recs, law, zfrom, slope, d if law.__name__ == '<lambda>' else None) if w > 0 else math.inf))
    return out


def hist_path(b, law, zfrom, slope='0'):
    tail = '' if slope == '0' else f'_s{slope}'
    return os.path.join(HERE, 'data', 'r5p_zhist', f'b{b}_{law}_{zfrom}{tail}.txt')


def miss(zm, c):
    W = sum(w for w, _ in zm)
    return sum(w for w, z in zm if z < -c) / W


def hist(b, law, zfrom, slope='0', by_d=False):
    """cumulative nodes and evals at each c of GRID (all lengths, or per d)"""
    path = hist_path(b, law, zfrom, slope)
    if not os.path.exists(path):
        return None
    rows = defaultdict(list)
    for line in open(path):
        if line.startswith('#'):
            continue
        d, z, n, e = line.split()
        rows[int(d) if by_d else 0].append((float(z), int(n), int(e)))
    out = {}
    for key, r in rows.items():
        out[key] = [(sum(n for z, n, e in r if z >= -c - 1e-9), sum(e for z, n, e in r if z >= -c - 1e-9)) for c in GRID]
    return out if by_d else out[0]


def at_miss(curve_miss, curve_nodes, target):
    """nodes at the smallest c (largest cut) whose miss rate is <= target, by linear interpolation in c"""
    for i in range(len(GRID)):
        if curve_miss[i] <= target:
            if i == 0:
                return GRID[0], curve_nodes[0]
            m0, m1 = curve_miss[i - 1], curve_miss[i]
            f = (m0 - target) / (m0 - m1) if m0 > m1 else 1.0
            c = GRID[i - 1] + f * (GRID[i] - GRID[i - 1])
            n = math.exp(math.log(curve_nodes[i - 1]) + f * (math.log(curve_nodes[i]) - math.log(curve_nodes[i - 1])))
            return c, n
    return None, None


def main():
    targets = [0.005, 0.01, 0.02, 0.03, 0.05]
    for b in map(int, sys.argv[1:]):
        print(f"base {b}")
        res = {}
        for law, zf, sl in CONFIGS:
            h = hist(b, law, zf, sl)
            if h is None:
                continue
            lf = table_law(b) if law == 'table' else LAWS[law]
            zm1 = planted_zmins(b, 1, lf, zf, sl)
            zm2 = planted_zmins(b, 2, lf, zf, sl)
            m1 = [miss(zm1, c) for c in GRID]
            m2 = [miss(zm2, c) for c in GRID]
            res[(law, zf, sl)] = (m1, m2, h)
            print(f"  {law} zfrom {zf} zslope {sl}: c, miss order 1, miss order 2, nodes, evals")
            for i, c in enumerate(GRID):
                if abs(c * 4 - round(c * 4)) < 1e-9:
                    print(f"    {c:.2f} {m1[i]:.4f} {m2[i]:.4f} {h[i][0]} {h[i][1]}")
        print("  at equal planted miss rate (order 1): threshold c and nodes; ratio to poisson 0.75")
        for t in targets:
            line = f"    miss {t:.3f}:"
            ref = None
            for key, (m1, m2, h) in res.items():
                c, n = at_miss(m1, [x[0] for x in h], t)
                _, e = at_miss(m1, [x[1] for x in h], t)
                if c is None:
                    line += f"\n      {'/'.join(key)} -"
                    continue
                if key == ('poisson', '0.75', '0'):
                    ref = (n, e)
                line += f"\n      {'/'.join(key)} c={c:.2f} n={n:.3g} e={e:.3g}"
                if ref and key != ('poisson', '0.75', '0'):
                    line += f" ({ref[0] / n:.2f}x nodes, {ref[1] / e:.2f}x evals)"
            print(line, flush=True)


if __name__ == '__main__':
    main()
