"""Compare D = 0 (solutions) with the other offsets of the defect spectrum."""
import math
import sys
from collections import defaultdict
from catalog import exhaustive_bases

rows = defaultdict(dict)
for line in open(sys.argv[1] if len(sys.argv) > 1 else 'data/defects.txt'):
    if line.startswith('#'):
        continue
    b, m, j, n = map(int, line.split())
    rows[(b, m)][j] = n

def group(sel, title):
    obs0 = ctrl = nctrl = odd = nodd = 0
    for (b, m), d in rows.items():
        if not sel(b, m):
            continue
        obs0 += d.get(0, 0)
        for j, n in d.items():
            if j == 0:
                continue
            if j % 2 == 0:
                ctrl += n; nctrl += 1
            else:
                odd += n; nodd += 1
    nb = sum(1 for k in rows if sel(*k))
    per_base_even = ctrl / max(1, nctrl) * nb
    per_base_odd = odd / max(1, nodd) * nb
    print(f"{title:34s} bases {nb:2d}: D=0 count {obs0:3d}; same-residue offsets predict {per_base_even:6.2f}; "
          f"odd multiples of b-1 predict {per_base_odd:6.2f}")

for m in (0, 1):
    group(lambda b, mm: mm == m and b % 2 == 0, f"0^0={m}, even bases")
    group(lambda b, mm: mm == m and b % 2 == 1, f"0^0={m}, odd bases")
print()
print("per base, 0^0=1: base, D=0 count, mean over even j>0, mean over odd j")
for (b, m), d in sorted(rows.items()):
    if m != 1:
        continue
    ev = [n for j, n in d.items() if j and j % 2 == 0]
    od = [n for j, n in d.items() if j % 2 == 1]
    print(f"  {b:2d}  {d.get(0, 0)}  {sum(ev) / len(ev):.2f}  {sum(od) / len(od):.2f}")
