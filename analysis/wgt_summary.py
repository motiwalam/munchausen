"""Tables for questions 9 and 10 from the files written by wgt_family.py.

    python3 wgt_summary.py data/wgt_shift_1.txt ...

For each file and convention: observed and expected totals by base parity,
the length law (j = reference length - d), and the Poisson tests.
"""
import math
import sys
from collections import defaultdict


def ref_len(name, b):
    """The length that plays the part of b - 1 + 1 = b for x^x."""
    if 'factorial' in name:
        return len(str_base(math.factorial(b - 1), b))
    if 'shift_' in name:
        return b + int(name.split('shift_')[1].split('.')[0])
    return b


def str_base(n, b):
    out = []
    while n:
        out.append(n % b)
        n //= b
    return out


def load(path):
    sol = defaultdict(int)       # (b, mode, d) -> count
    exp = defaultdict(float)     # (b, mode, d) -> refined
    basic = defaultdict(float)
    bases = set()
    for line in open(path):
        p = line.split()
        if not p or p[0].startswith('#'):
            continue
        if p[0] == 'sol':
            sol[int(p[1]), int(p[2]), int(p[3])] += int(p[4])
        elif p[0] == 'exp':
            k = (int(p[1]), int(p[2]), int(p[3]))
            basic[k] += float(p[4])
            exp[k] += float(p[5])
        elif p[0] == 'time':
            bases.add(int(p[1]))
    return sorted(bases), sol, exp, basic


def summary(path):
    name = path.split('/')[-1]
    bases, sol, exp, basic = load(path)
    print(f"== {name}, bases {bases[0]}-{bases[-1]}")
    for mode in (0, 1):
        print(f" mode {mode}")
        for par, label in ((0, 'even'), (1, 'odd')):
            bs = [b for b in bases if b % 2 == par]
            o = sum(v for (b, m, d), v in sol.items() if m == mode and b in bs)
            e = sum(v for (b, m, d), v in exp.items() if m == mode and b in bs)
            eb = sum(v for (b, m, d), v in basic.items() if m == mode and b in bs)
            print(f"  {label:4s} bases ({len(bs)}): observed {o:3d}  refined {e:6.2f}  basic {eb:6.2f}  ratio refined/basic {e / eb:5.3f}")
        # length law
        lo = defaultdict(int)
        le = defaultdict(float)
        for (b, m, d), v in sol.items():
            if m == mode:
                lo[min(ref_len(name, b) - d, 6)] += v
        for (b, m, d), v in exp.items():
            if m == mode:
                le[min(ref_len(name, b) - d, 6)] += v
        to, te = sum(lo.values()), sum(le.values())
        row = "  length j = ref - d:"
        for j in sorted(set(lo) | set(le)):
            lab = f"{j}" if j < 6 else ">=6"
            row += f"  [{lab}] {lo[j]}/{le[j]:.1f} ({100 * le[j] / te:.0f}%)"
        print(row + f"  (observed/expected, expected share)")
        # Poisson tests over bases
        x2 = 0.0
        empty_o = 0
        empty_e = 0.0
        for b in bases:
            lam = sum(v for (bb, m, d), v in exp.items() if bb == b and m == mode)
            n = sum(v for (bb, m, d), v in sol.items() if bb == b and m == mode)
            x2 += (n - lam) ** 2 / lam
            empty_o += n == 0
            empty_e += math.exp(-lam)
        print(f"  Poisson: sum (N - lambda)^2 / lambda = {x2:.1f} over {len(bases)} bases;"
              f" empty bases observed {empty_o}, expected {empty_e:.1f}")


for path in sys.argv[1:]:
    summary(path)
