"""A second-order model: the refined model times the forced-top-digit
correction C_t(b, d) of analysis/forced_top.py, compared with each base's
measured lambda from the defect spectrum (lengths b-6 to b)."""
import math
import sys
from collections import defaultdict
import numpy as np
from forced_top import correction
from model import expected_refined

t = int(sys.argv[1]) if len(sys.argv) > 1 else 2
rows = defaultdict(dict)
for line in open('data/defects_bulk_b1.txt'):
    if line.startswith('#'):
        continue
    b, m, j, n = map(int, line.split())
    rows[(b, m)][j] = n
res = []
for (b, m), d in sorted(rows.items()):
    ev = [n for j, n in d.items() if j and j % 2 == 0]
    lam = sum(ev) / len(ev)
    first = second = 0.0
    for dd in range(b - 6, b + 1):
        e = expected_refined(b, dd, m, 20000)[0]
        _, cs = correction(b, dd, m, t_max=t, N=15000, seed=b * 7 + dd)
        first += e
        second += e * cs[t - 1]
    res.append((b, m, lam, first, second))
    print(f"{b:3d} {m}  measured {lam:.2f}  refined {first:.2f}  second order {second:.2f}", flush=True)
for m in (0, 1):
    a = np.array([(r[2], r[3], r[4]) for r in res if r[1] == m])
    for k, name in ((1, 'refined'), (2, 'second order')):
        rel = a[:, 0] / a[:, k]
        print(f"0^0={m} {name:12s}: mean ratio {rel.mean():.3f}, sd of ratio {rel.std():.3f}, "
              f"correlation with measured {np.corrcoef(a[:, 0], a[:, k])[0, 1]:.2f}")
