"""Empty bases against each base's own defect spectrum.

For each base and convention, the mean count over offsets D = j (b-1) with j
even and j > 0 estimates the expected number of solutions lambda in that
base, with the true weights. In a Poisson law the base has no solution under
that convention with probability exp(-lambda). Summing gives the expected
number of bases without solutions, by parity, to compare with the data.
"""
import math
import sys
from collections import defaultdict

rows = defaultdict(dict)
for line in open(sys.argv[1]):
    if line.startswith('#'):
        continue
    b, m, j, n = map(int, line.split())
    rows[(b, m)][j] = n

bases = sorted({b for b, m in rows})
print("base  lambda0  lambda1   N0 N1")
tot = defaultdict(lambda: [0.0, 0])
for b in bases:
    lam, obs = {}, {}
    for m in (0, 1):
        d = rows[(b, m)]
        ev = [n for j, n in d.items() if j and j % 2 == 0]
        lam[m] = sum(ev) / len(ev)
        obs[m] = d.get(0, 0)
    print(f"{b:4d}  {lam[0]:7.2f}  {lam[1]:7.2f}   {obs[0]:2d} {obs[1]:2d}")
    par = 'even' if b % 2 == 0 else 'odd'
    for m in (0, 1):
        t = tot[(par, m)]
        t[0] += math.exp(-lam[m])
        t[1] += obs[m] == 0
for (par, m), (e, o) in sorted(tot.items()):
    print(f"{par:4s} bases, 0^0={m}: expected bases without a solution {e:.2f}, observed {o}")
