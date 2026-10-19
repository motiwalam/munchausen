"""Round 5, question 74: the Pisot defect spectrum by brute force.

Reads data/r5e_pisot_defects_x<x>.txt (r3t_pisot defects: every N <= Nmax,
D = N - F(N) with |D| <= 40 x and x | D, per convention and length T) and
compares N_0 with four calibrations per x and convention:

    all    D = j x, j = 1..30            (section 21.4)
    even   D = 2 j x, j = 1..15          (the class of 0 mod 2x)
    both   D = +-2 j x, j = 1..20        (both signs, class mod 2x)
    odd    D = (2j - 1) x, j = 1..15     (the other class)
    local  D = +-2 j x, j = 1..3         (both signs, class mod 2x, near 0)
    far    D = +-2 j x, j = 11..20       (both signs, class mod 2x, far)

Counts include every length T >= 2, as the census does. The brute force covers N <= Nmax,
which holds every known solution for x <= 8. Output:
data/r5e_pisot_defects.txt.
"""
import glob
import os
import re
from collections import defaultdict

from r5e_lib import p_high, poisson_high

HERE = os.path.dirname(os.path.abspath(__file__))


def load(path):
    h = defaultdict(int)
    nmax = None
    for line in open(path):
        m = re.match(r'def x (\d+) m (\d) T (\d+) D (-?\d+) count (\d+)', line)
        if m:
            x, mm, T, D, c = map(int, m.groups())
            if T >= 2:
                h[mm, T, D] += c
        m = re.match(r'done defects x (\d+) Nmax (\d+)', line)
        if m:
            nmax = int(m.group(2))
    return h, nmax


def main():
    out = ["# r5e_pisot_defects.py: N_0 against per-offset means; P(N >= N_0) clustered with phi 2.5"]
    out.append("# x m Nmax | N_0 | all j | even j | both signs, even j | odd j | local | far | P(>= N_0) by all, even")
    tot = defaultdict(lambda: defaultdict(float))
    for path in sorted(glob.glob(os.path.join(HERE, 'data', 'r5e_pisot_defects_x*.txt')),
                       key=lambda p: int(re.search(r'x(\d+)', p).group(1))):
        x = int(re.search(r'x(\d+)\.txt', path).group(1))
        h, nmax = load(path)
        if nmax is None:
            continue
        for m in (0, 1):
            def at(D):
                return sum(v for (mm, T, d), v in h.items() if mm == m and d == D)
            n0 = at(0)
            a = sum(at(j * x) for j in range(1, 31)) / 30
            e = sum(at(2 * j * x) for j in range(1, 16)) / 15
            bth = sum(at(2 * j * x) + at(-2 * j * x) for j in range(1, 21)) / 40
            o = sum(at((2 * j - 1) * x) for j in range(1, 16)) / 15
            loc = sum(at(2 * j * x) + at(-2 * j * x) for j in range(1, 4)) / 6
            far = sum(at(2 * j * x) + at(-2 * j * x) for j in range(11, 21)) / 20
            out.append(f"{x} {m} {nmax} | {n0} | {a:.2f} | {e:.2f} | {bth:.2f} | {o:.2f} | {loc:.2f} | {far:.2f} | "
                       f"{poisson_high(n0, a):.3f}, {poisson_high(n0, e):.3f}")
            g = ('even' if x % 2 == 0 else 'odd', m)
            for k, v in (('n0', n0), ('all', a), ('even', e), ('both', bth), ('odd', o), ('loc', loc), ('far', far)):
                tot[g][k] += v
    out.append("# groups x = 2..8: N_0 | all | even | both | odd | local | far | P fixed (all, even, both) | "
               "P clustered phi 2.5, psi 1.4 for 0^0 = 0 (all J=30, even J=15, both J=40, local J=6)")
    for g in sorted(tot):
        t = tot[g]
        psi = 1.4 if g[1] == 0 else 1.0
        out.append(f"{g[0]} x, 0^0={g[1]}: {t['n0']:.0f} | {t['all']:.2f} | {t['even']:.2f} | {t['both']:.2f} | "
                   f"{t['odd']:.2f} | {t['loc']:.2f} | {t['far']:.2f} | {poisson_high(t['n0'], t['all']):.4f}, {poisson_high(t['n0'], t['even']):.4f}, "
                   f"{poisson_high(t['n0'], t['both']):.4f} | "
                   f"{p_high(t['n0'], t['all'] * 30, 30, 2.5, psi):.4f}, "
                   f"{p_high(t['n0'], t['even'] * 15, 15, 2.5, psi):.4f}, "
                   f"{p_high(t['n0'], t['both'] * 40, 40, 2.5, psi):.4f}, "
                   f"{p_high(t['n0'], t['loc'] * 6, 6, 2.5, psi):.4f}")
    with open(os.path.join(HERE, 'data', 'r5e_pisot_defects.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
