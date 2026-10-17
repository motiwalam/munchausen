"""Per-base counts in the exhaustive range, and how they relate.

For every base searched completely, report the number of nontrivial
solutions under each convention, how many are shared (no zero digit), the
longest solution, and the refined model's expectation.
"""
import math
import sys
from collections import Counter

from catalog import exhaustive_bases
from model import expected_refined

sols = exhaustive_bases()
bases = sorted({b for (_, b) in sols})
want_model = len(sys.argv) > 1

rows = []
for b in bases:
    s0, s1 = sols.get((0, b), set()), sols.get((1, b), set())
    shared = {t for t in s0 if 0 not in t}
    assert shared == {t for t in s1 if 0 not in t}, b
    longest = max((len(t) for t in s0 | s1), default=0)
    e = [None, None]
    if want_model and b >= 3:
        for m in (0, 1):
            e[m] = sum(expected_refined(b, d, m, 60_000)[0] for d in range(2, b + 1))
    rows.append((b, len(s0), len(s1), len(shared), longest, e))

print("base  n0  n1  shared  longest  E0     E1")
for b, n0, n1, sh, lg, e in rows:
    es = f"{e[0]:5.2f}  {e[1]:5.2f}" if e[0] is not None else ""
    print(f"{b:4d}  {n0:2d}  {n1:2d}  {sh:4d}    {lg:4d}    {es}")

for m in (0, 1):
    hist = Counter(r[1 + m] for r in rows if r[0] >= 10)
    print(f"0^0={m}, bases 10-{bases[-1]}: bases with exactly n nontrivial solutions:",
          dict(sorted(hist.items())))
    for n in sorted(hist):
        print(f"   n={n}:", [r[0] for r in rows if r[0] >= 10 and r[1 + m] == n])
both_empty = [r[0] for r in rows if r[1] == 0 and r[2] == 0]
print("bases with no nontrivial solution under either convention:", both_empty)
if want_model:
    for m in (0, 1):
        zs = [r for r in rows if r[0] >= 10]
        exp_empty = sum(math.exp(-r[5][m]) for r in zs)
        exp_hist = Counter()
        for r in zs:
            lam = r[5][m]
            for n in range(8):
                exp_hist[n] += math.exp(-lam) * lam ** n / math.factorial(n)
        print(f"0^0={m}: Poisson expectation of bases with n solutions:",
              {n: round(v, 1) for n, v in sorted(exp_hist.items())}, f"(empty: {exp_empty:.1f})")
