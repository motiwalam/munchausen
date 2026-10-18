"""Question 53: statistics of the class orders d of mixed ideals B of norm x
in Q(sqrt(x^2 + 4)), from analysis/data/r3nt_mixed_orders.txt (written by
r3nt_mixed_orders.gp; GRH class groups).

For each x the file lists one d per conjugate pair of mixed ideals.
Corollary 18.11 leaves open a mixed B whose order d divides x with
x / d < 3.3e4 log x. The script reports, per range of x:

- the share of mixed pairs and of x with d | x (d > 1);
- the cofactors g = x / d that occur, and how often;
- the share of x with some d | x and d >= x / C for C = 10, 100, 1000;
- the largest d / x and the largest h / x;

and fits the share of x with some d | x against x.

usage: python3 analysis/r3nt_mixed_stats.py
"""
import math
import os
from collections import Counter

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
DATA = os.path.join(ROOT, 'analysis', 'data', 'r3nt_mixed_orders.txt')


def load():
    rows = []
    for line in open(DATA):
        if line.startswith('#') or not line.strip():
            continue
        x, h, rest = line.split(' ', 2)
        cyc, ds = rest.rsplit(' [', 1)
        ds = [int(t) for t in ds.strip().rstrip(']').split(',') if t.strip()]
        rows.append((int(x), int(h), ds))
    return rows


def omega(x):
    n, w, p = x, 0, 2
    while p * p <= n:
        if n % p == 0:
            w += 1
            while n % p == 0:
                n //= p
        p += 1
    return w + (n > 1)


def main():
    rows = load()
    bins = [(3, 10 ** 4), (10 ** 4, 10 ** 5), (10 ** 5, 2 * 10 ** 5), (2 * 10 ** 5, 3.5 * 10 ** 5),
            (3.5 * 10 ** 5, 5 * 10 ** 5), (5 * 10 ** 5, 6.5 * 10 ** 5), (6.5 * 10 ** 5, 8 * 10 ** 5),
            (8 * 10 ** 5, 10 ** 6 + 2)]
    print(f'{len(rows)} values of x, {sum(len(r[2]) for r in rows)} mixed pairs; '
          f'x from {rows[0][0]} to {rows[-1][0]}')
    gs = Counter()
    gs_by_omega = Counter()
    tot_by_omega = Counter()
    print('range of x            values  pairs   pairs d|x  share   x with d|x  share   '
          'd|x,d>=x/10  d|x,d>=x/100  d|x,d>=x/1000  max d/x  max h/x')
    fit = []
    for lo, hi in bins:
        sel = [r for r in rows if lo <= r[0] < hi]
        if not sel:
            continue
        npairs = sum(len(r[2]) for r in sel)
        pdiv = sum(1 for r in sel for d in r[2] if d > 1 and r[0] % d == 0)
        xdiv = sum(1 for r in sel if any(d > 1 and r[0] % d == 0 for d in r[2]))
        big = {}
        for C in (10, 100, 1000):
            big[C] = sum(1 for r in sel if any(d > 1 and r[0] % d == 0 and d * C >= r[0] for d in r[2]))
        mdx = max(max(r[2]) / r[0] for r in sel if r[2])
        mhx = max(r[1] / r[0] for r in sel)
        print(f'[{lo:>8.0f}, {hi:>8.0f})  {len(sel):6d}  {npairs:6d}  {pdiv:9d}  {pdiv / npairs:.4f}  '
              f'{xdiv:9d}  {xdiv / len(sel):.4f}  {big[10]:11d}  {big[100]:12d}  {big[1000]:13d}  '
              f'{mdx:.4f}   {mhx:.4f}')
        fit.append(((lo + hi) / 2, xdiv / len(sel)))
    for x, h, ds in rows:
        w = omega(x)
        for d in ds:
            tot_by_omega[w] += 1
            if d > 1 and x % d == 0:
                gs[x // d] += 1
                gs_by_omega[w] += 1
    print('cofactors g = x/d with d | x, d > 1 (g: count), the 25 most common:')
    print('  ', sorted(gs.items(), key=lambda t: -t[1])[:25])
    print('  smallest g that occur:', sorted(gs)[:20])
    print('share of mixed pairs with d | x by omega(x):',
          {w: f'{gs_by_omega[w]}/{tot_by_omega[w]}' for w in sorted(tot_by_omega)})
    # fit share(x) = A x^(-beta) on the bins
    xs = [math.log(t[0]) for t in fit if t[1] > 0]
    ys = [math.log(t[1]) for t in fit if t[1] > 0]
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    beta = -sum((a - mx) * (b - my) for a, b in zip(xs, ys)) / sum((a - mx) ** 2 for a in xs)
    A = math.exp(my + beta * mx)
    print(f'fit: share of x with some mixed d | x, d > 1, is about {A:.3g} x^(-{beta:.3f})')
    # records: largest d with d | x
    # share of x with a mixed d | x and cofactor g = x/d <= G, times x / G
    print('share of x with some mixed d | x and x/d <= G, multiplied by x/G (bin centre):')
    for G in (100, 1000, 10000):
        out = []
        for lo, hi in bins:
            sel = [r for r in rows if lo <= r[0] < hi]
            if not sel:
                continue
            k = sum(1 for r in sel if any(d > 1 and r[0] % d == 0 and r[0] // d <= G for d in r[2]))
            out.append(f'{k / len(sel) * ((lo + hi) / 2) / G:.3f}')
        print(f'  G = {G}: ' + ', '.join(out))
    med = []
    for lo, hi in bins:
        v = sorted(math.log(x // d) / math.log(x) for x, h, ds in rows if lo <= x < hi
                   for d in set(ds) if d > 1 and x % d == 0)
        if v:
            med.append(f'{v[len(v) // 2]:.3f}')
    print('median of log(x/d) / log x over pairs with d | x, by range:', ', '.join(med))
    rec = sorted({(d, x, h) for x, h, ds in rows for d in ds if d > 1 and x % d == 0}, reverse=True)[:10]
    print('largest d with d | x: (d, x, h):', rec)
    rec2 = sorted({(x // d, d, x) for x, h, ds in rows for d in ds if d > 1 and x % d == 0})[:10]
    print('smallest x/d with d | x: (x/d, d, x):', rec2)


if __name__ == '__main__':
    main()
