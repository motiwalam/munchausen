"""Rational bases p/q (question 60): census against the model.

Reads analysis/data/r3t_afs_search.txt (r3t_afs search) and
analysis/data/r3t_afs_model.txt (r3t_afs model). Prints one row per base,
then totals for the bases with p and q both odd against the others, for
q > 1, under both conventions. "near" is the mean number of near-solutions
N = F(N) + j (p - q) over j = 1..30.
usage: python3 r3t_afs_summary.py
"""
import re
from math import exp, factorial

sols = {}
near = {}
for line in open('analysis/data/r3t_afs_search.txt'):
    m = re.match(r'done p/q (\d+)/(\d+) sols0 (\d+) sols1 (\d+) nodes (\d+)', line)
    if m:
        p, q, s0, s1, nodes = map(int, m.groups())
        sols[(p, q)] = (s0, s1, nodes)
    m = re.match(r'near p/q (\d+)/(\d+) m (\d) step \d+ counts (\S+)', line)
    if m:
        p, q, mm = map(int, m.groups()[:3])
        c = list(map(int, m.group(4).split(',')))
        near[(p, q, mm)] = sum(c) / len(c)
model = {}
for line in open('analysis/data/r3t_afs_model.txt'):
    m = re.match(r'model p/q (\d+)/(\d+) basic0 (\S+) refined0 (\S+) zerofree0 (\S+) basic1 (\S+) refined1 (\S+)', line)
    if m:
        p, q = int(m.group(1)), int(m.group(2))
        model[(p, q)] = tuple(map(float, m.groups()[2:]))


def pois_le(k, lam):
    return sum(exp(-lam) * lam ** i / factorial(i) for i in range(k + 1))


print("| base | p-q | odd/odd | sols 0^0=0 | E_0 | near_0 | sols 0^0=1 | E_1 | near_1 | tree nodes |")
print("|---|---:|---|---:|---:|---:|---:|---:|---:|---:|")
for (p, q) in sorted(sols):
    if (p, q) not in model:
        continue
    s0, s1, nodes = sols[(p, q)]
    b0, r0, z0, b1, r1 = model[(p, q)]
    oo = 'yes' if p % 2 and q % 2 else ''
    print(f"| {p}/{q} | {p-q} | {oo} | {s0} | {r0:.2f} | {near.get((p,q,0),0):.2f} | {s1} | {r1:.2f} | {near.get((p,q,1),0):.2f} | {nodes:.2e} |")

print()
print("Totals over the bases with q > 1:")
print("| group | bases | sols 0^0=0 | refined E_0 | basic | mean near_0 | sols 0^0=1 | refined E_1 | mean near_1 | P(X <= obs), 0^0=0 |")
print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
for name, sel in (("p, q odd", lambda p, q: p % 2 == 1 and q % 2 == 1),
                  ("others", lambda p, q: not (p % 2 == 1 and q % 2 == 1))):
    B = [(p, q) for (p, q) in sols if q > 1 and sel(p, q) and (p, q) in model]
    S0 = sum(sols[b][0] for b in B)
    S1 = sum(sols[b][1] for b in B)
    E0 = sum(model[b][1] for b in B)
    E1 = sum(model[b][4] for b in B)
    BA = sum(model[b][0] for b in B)
    N0 = sum(near.get((p, q, 0), 0) for p, q in B)
    N1 = sum(near.get((p, q, 1), 0) for p, q in B)
    print(f"| {name} | {len(B)} | {S0} | {E0:.1f} | {BA:.1f} | {N0:.1f} | {S1} | {E1:.1f} | {N1:.1f} | {pois_le(S0, E0):.2f} |")
