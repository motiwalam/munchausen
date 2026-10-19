"""Eisenstein bases -n + omega (question 63), with -2 + i as a control.

Reads the r3t_eisen outputs in analysis/data/ and prints, per base and
convention: the solutions, the refined model summed over the searched lengths,
the model over all lengths (sampled, n = 3), and the mean number of
near-solutions z = F(z) + j M, j = 1..30, M the identity modulus.
usage: python3 r3t_eisen_summary.py
"""
import re
from collections import defaultdict

files = ['analysis/data/r3t_eisen12.txt', 'analysis/data/r3t_eisen3_m0.txt',
         'analysis/data/r3t_eisen3_m1.txt', 'analysis/data/r3t_gauss2_offsets.txt']
ref = defaultdict(float)
sols = defaultdict(list)
near = {}
dmax = {}
modulus = {}
for f in files:
    try:
        lines = open(f).read().splitlines()
    except FileNotFoundError:
        continue
    for line in lines:
        m = re.match(r'# base (\S+), 0\^0 = (\d).* modulus (\d+)', line)
        if m:
            modulus[m.group(1)] = int(m.group(3))
        m = re.match(r'len base (\S+) m (\d) d (\d+) sols \d+ leaves \d+ basic \S+ refined (\S+)', line)
        if m:
            b, mm, d, r = m.group(1), int(m.group(2)), int(m.group(3)), float(m.group(4))
            ref[(b, mm)] += r
            dmax[(b, mm)] = d
        m = re.match(r'sol base (\S+) m (\d) d (\d+) digits (\S+)', line)
        if m:
            sols[(m.group(1), int(m.group(2)))].append((int(m.group(3)), m.group(4)))
        m = re.match(r'total base (\S+) m (\d) d \S+ sols \d+ near (\S+)', line)
        if m:
            c = list(map(int, m.group(3).split(',')))
            near[(m.group(1), int(m.group(2)))] = sum(c) / len(c)
mc = defaultdict(float)
for line in open('analysis/data/r3t_eisen3_mc.txt'):
    m = re.match(r'mc base (\S+) m (\d) d (\d+) samples \d+ basic \S+ refined (\S+)', line)
    if m:
        mc[(m.group(1), int(m.group(2)))] += float(m.group(4))

print("| base | M | 0^0 | lengths searched | solutions (lengths) | refined model, searched | model, all lengths | near-solutions per offset |")
print("|---|---:|---:|---|---|---:|---:|---:|")
for key in sorted(ref):
    b, mm = key
    s = sols.get(key, [])
    lens = ', '.join(str(d) for d, _ in s) if s else 'none'
    allm = mc.get(key, ref[key])
    print(f"| {b} | {modulus.get(b, '')} | {mm} | 2..{dmax[key]} | {len(s)} ({lens}) | {ref[key]:.2f} | {allm:.2f} | {near.get(key, float('nan')):.2f} |")
for key in sorted(sols):
    for d, digs in sols[key]:
        print(f"sol {key[0]} 0^0={key[1]} d={d} {digs}")
