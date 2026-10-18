"""Question 41: long factorions at D = 0 against near-factorions at offsets.

    python3 r2c_fact_compare.py [offset files...]

Reads the census and the model of branch q-weights
(data/r2c_qw_factorial.txt, made by wgt_family.py) and offset files in the
format "off b j mode count [solutions]". "Long" means at least L(b) - 5
digits, L(b) the length of (b-1)!. For each file the table gives, per
parity of b and convention, the solutions at D = 0, the model, and the mean
count per offset over bases 14 to 36.
"""
import math
import os
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
BASES = range(14, 37)


def ref_len(b):
    n, k = math.factorial(b - 1), 0
    while n:
        n //= b
        k += 1
    return k


def census(path):
    sol = defaultdict(int)
    exp = defaultdict(float)
    for line in open(path):
        p = line.split()
        if not p or p[0] not in ('sol', 'exp'):
            continue
        b, m, d = int(p[1]), int(p[2]), int(p[3])
        if d < ref_len(b) - 5:
            continue
        if p[0] == 'sol':
            sol[b, m] += int(p[4])
        else:
            exp[b, m] += float(p[5])
    return sol, exp


def offsets(path):
    off = defaultdict(list)
    for line in open(path):
        p = line.split()
        if p and p[0] == 'off':
            off[int(p[1]), int(p[3])].append(int(p[4]))
    return off


def main():
    files = sys.argv[1:] or [os.path.join(HERE, 'data', f) for f in
                             ('r2c_qw_offsets_factorial.txt', 'r2c_fact_offsets_bb1.txt')]
    sol, exp = census(os.path.join(HERE, 'data', 'r2c_qw_factorial.txt'))
    offs = [(os.path.basename(f), offsets(f)) for f in files if os.path.exists(f)]
    print("bases 14-36, at least L(b)-5 digits; offsets: mean count per offset, summed over bases")
    print("parity m | D=0 observed | model | " + " | ".join(n for n, _ in offs))
    for par, lab in ((0, 'even'), (1, 'odd')):
        for m in (0, 1):
            bs = [b for b in BASES if b % 2 == par]
            o = sum(sol[b, m] for b in bs)
            e = sum(exp[b, m] for b in bs)
            cols = []
            for _, off in offs:
                cols.append(f"{sum(sum(off[b, m]) / len(off[b, m]) for b in bs if off[b, m]):.2f}")
            print(f"{lab:4s} {m} | {o:3d} | {e:6.2f} | " + " | ".join(cols))
    print()
    print("per base (odd), m = 0 / m = 1: D=0, model, offset means")
    for b in BASES:
        row = f"{b:3d} L={ref_len(b):2d}"
        for m in (0, 1):
            row += f" | m={m}: {sol[b, m]} {exp[b, m]:.2f}"
            for _, off in offs:
                if off[b, m]:
                    row += f" {sum(off[b, m]) / len(off[b, m]):.2f}"
        print(row)


if __name__ == '__main__':
    main()
