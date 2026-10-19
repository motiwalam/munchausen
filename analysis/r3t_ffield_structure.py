"""Structure of the F_q[T] solutions under 0^0 = 0 (question 61).

From analysis/data/r3t_ffield_frob.txt: per (q, e), the number of solutions,
of families (solutions with the same digits except the last one; under
0^0 = 0 every family has exactly q members, n + c for c in F_q), of self-paying digits (a single
nonzero digit d at position k >= 1, so d^(|d|) = d B^k), and of bases with at
least one self-paying digit. Lengths are counted too.
usage: python3 r3t_ffield_structure.py
"""
import re
from collections import defaultdict, Counter

cur = None
sols = defaultdict(lambda: defaultdict(list))
for line in open('analysis/data/r3t_ffield_frob.txt'):
    m = re.match(r'# frob q (\d+) e (\d+) m (\d+)', line)
    if m:
        cur = tuple(map(int, m.groups()))
        continue
    m = re.match(r'sol base (\d+) m (\d) digits (\S+)', line)
    if m and cur[2] == 0:
        sols[cur[:2]][int(m.group(1))].append(list(map(int, m.group(3).split(','))))

print("| q | e | solutions | families | family sizes | self-paying digits | bases with one | lengths |")
print("|---:|---:|---:|---:|---|---:|---:|---|")
for (q, e) in sorted(sols):
    S = sols[(q, e)]
    n = sum(len(v) for v in S.values())
    fam = Counter()
    selfpay = 0
    bases_sp = 0
    lens = Counter()
    for b, L in S.items():
        has = False
        for d in L:
            lens[len(d)] += 1
            fam[(b, tuple(d[:-1]))] += 1
            if sum(1 for x in d if x) == 1 and d[-1] == 0:
                selfpay += 1
                has = True
        bases_sp += has
    sizes = dict(sorted(Counter(fam.values()).items()))
    print(f"| {q} | {e} | {n} | {len(fam)} | {sizes} | {selfpay} | {bases_sp} | {dict(sorted(lens.items()))} |")
