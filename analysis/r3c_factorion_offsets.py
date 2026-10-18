"""Question 57: the factorion shortfall in the offset class D = j b (b-1).

These offsets keep n mod (b-1) and n mod b, so they also keep the last digit
of n. For each base and j = 1..J the script counts the solutions of
n = F(n) + D with weights x! and at least ref-5 digits, where ref is the
number of digits of (b-1)!, as in analysis/wgt_offsets.py.

    python3 r3c_factorion_offsets.py b0 b1 J [step] > data/r3c_factorion_offsets.txt
    python3 r3c_factorion_offsets.py report data/r3c_factorion_offsets.txt

The default step 2 visits the odd bases from an odd b0. Lines: off b j mode count.
"""
import math
import sys
from collections import defaultdict

from wgt_model import run_fast


def ref_len(b):
    n, k = math.factorial(b - 1), 0
    while n:
        n //= b
        k += 1
    return k


def run(b0, b1, J, step):
    print(f"# --factorial, bases {b0}-{b1} step {step}, offsets j b (b-1) for j = 1..{J}, bulk d >= ref-5")
    for b in range(b0, b1 + 1, step):
        r = ref_len(b)
        for j in range(1, J + 1):
            res, _ = run_fast(b, b, ['--factorial', '--offset', str(j * b * (b - 1)), '--min-digits', str(max(2, r - 5))])
            for mode in (0, 1):
                print(f"off {b} {j} {mode} {len(res[b, mode])}", flush=True)


def load_off(path):
    c = defaultdict(int)
    js = defaultdict(set)
    for line in open(path):
        p = line.split()
        if p and p[0] == 'off':
            b, j, mode, n = map(int, p[1:])
            c[b, mode] += n
            js[b].add(j)
    return c, {b: len(v) for b, v in js.items()}


def load_family(path):
    """observed solutions and refined model per base and mode, bulk d >= ref-5"""
    sol = defaultdict(int)
    exp = defaultdict(float)
    for line in open(path):
        p = line.split()
        if not p or p[0] not in ('sol', 'exp'):
            continue
        b, mode, d = int(p[1]), int(p[2]), int(p[3])
        if d < ref_len(b) - 5:
            continue
        if p[0] == 'sol':
            sol[b, mode] += int(p[4])
        else:
            exp[b, mode] += float(p[5])
    return sol, exp


def report(path):
    narrow, nj = load_off(path)
    wide, wj = load_off('data/wgt_offsets_factorial.txt')
    sol, exp = load_family('data/wgt_factorial.txt')
    bases = sorted(nj)
    print("| base | mode | D = 0 | model | per offset, j b (b-1) | per offset, j (b-1) |")
    print("|---:|---:|---:|---:|---:|---:|")
    tot = defaultdict(float)
    for b in bases:
        for mode in (0, 1):
            n0, m = sol[b, mode], exp[b, mode]
            pn = narrow[b, mode] / nj[b]
            pw = wide[b, mode] / wj[b] if b in wj else float('nan')
            print(f"| {b} | {mode} | {n0} | {m:.2f} | {pn:.2f} | {pw:.2f} |")
            for key, v in (('n0', n0), ('m', m), ('pn', pn), ('pw', pw)):
                tot[mode, key] += v
    print()
    print("| mode | D = 0 | model | mean over j b (b-1) | mean over j (b-1) | P(N <= observed) with the narrow mean |")
    print("|---:|---:|---:|---:|---:|---:|")
    for mode in (0, 1):
        lam = tot[mode, 'pn']
        k = int(tot[mode, 'n0'])
        p = sum(math.exp(-lam) * lam ** i / math.factorial(i) for i in range(k + 1))
        print(f"| {mode} | {k} | {tot[mode, 'm']:.2f} | {lam:.2f} | {tot[mode, 'pw']:.2f} | {p:.4f} |")
    # the spread of the per-offset totals, to see where D = 0 falls
    print()
    for mode in (0, 1):
        per_j = defaultdict(int)
        for line in open(path):
            p = line.split()
            if p and p[0] == 'off' and int(p[3]) == mode:
                per_j[int(p[2])] += int(p[4])
        v = sorted(per_j.values())
        below = sum(1 for x in v if x <= tot[mode, 'n0'])
        print(f"mode {mode}: totals over the bases per offset j: min {v[0]}, median {v[len(v) // 2]}, max {v[-1]}; "
              f"offsets with a total <= {int(tot[mode, 'n0'])} (the D = 0 count): {below} of {len(v)}")


if __name__ == '__main__':
    if sys.argv[1] == 'report':
        report(sys.argv[2])
    else:
        b0, b1, J = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
        step = int(sys.argv[4]) if len(sys.argv) > 4 else 2
        run(b0, b1, J, step)
