"""The Pisot base eps_x (question 59): census against the model.

Reads analysis/data/r3t_pisot_search.txt, r3t_pisot_search12.txt and analysis/data/r3t_pisot_model.txt.
Per x: nontrivial solutions per convention, twin pairs (N, N+1) under 0^0 = 0,
the refined model, and the mean number of near-solutions N = F(N) + j x,
j = 1..J. Then totals for even x against odd x, for x >= 2.
usage: python3 r3t_pisot_summary.py
"""
import re
from math import exp, factorial

sols = {}
near = {}
done = set()
for line in open('analysis/data/r3t_pisot_search.txt').read().splitlines() + open('analysis/data/r3t_pisot_search12.txt').read().splitlines():
    m = re.match(r'sol x (\d+) m (\d) T (\d+) N (\d+) digits (\S+)', line)
    if m:
        x, mm, T, N = map(int, m.groups()[:4])
        sols.setdefault((x, mm), []).append(N)
    m = re.match(r'near x (\d+) m (\d) step \d+ counts (\S+)', line)
    if m:
        c = list(map(int, m.group(3).split(',')))
        near[(int(m.group(1)), int(m.group(2)))] = sum(c) / len(c)
    m = re.match(r'done search x (\d+)', line)
    if m:
        done.add(int(m.group(1)))
model = {}
for line in open('analysis/data/r3t_pisot_model.txt'):
    m = re.match(r'model x (\d+) basic0 (\S+) refined0 (\S+) zerofree0 (\S+) basic1 (\S+) refined1 (\S+)', line)
    if m:
        model[int(m.group(1))] = tuple(map(float, m.groups()[1:]))


def pois_le(k, lam):
    return sum(exp(-lam) * lam ** i / factorial(i) for i in range(k + 1))


print("| x | eps | sols 0^0=0 | twin pairs | E_0 | basic | near_0 | sols 0^0=1 | E_1 | near_1 |")
print("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
rows = []
for x in sorted(done):
    s0 = sorted(sols.get((x, 0), []))
    s1 = sorted(sols.get((x, 1), []))
    tw = sum(1 for n in s0 if n + 1 in s0)
    b0, r0, z0, b1, r1 = model.get(x, (0, 0, 0, 0, 0))
    eps = (x + (x * x + 4) ** 0.5) / 2
    print(f"| {x} | {eps:.3f} | {len(s0)} | {tw} | {r0:.2f} | {b0:.2f} | {near.get((x,0),0):.2f} | {len(s1)} | {r1:.2f} | {near.get((x,1),0):.2f} |")
    rows.append((x, len(s0), tw, r0, b0, near.get((x, 0), 0), len(s1), r1, near.get((x, 1), 0)))
print()
print("| x >= 2 | bases | sols 0^0=0 | twin pairs | E_0 | basic | near_0 per base | sols 0^0=1 | E_1 | near_1 per base |")
print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
for name, par in (("even", 0), ("odd", 1)):
    R = [r for r in rows if r[0] >= 2 and r[0] % 2 == par]
    if not R:
        continue
    t = [sum(r[i] for r in R) for i in range(1, 9)]
    print(f"| {name} | {len(R)} | {t[0]} | {t[1]} | {t[2]:.1f} | {t[3]:.1f} | {t[4]/len(R):.2f} | {t[5]} | {t[6]:.1f} | {t[7]/len(R):.2f} |")
