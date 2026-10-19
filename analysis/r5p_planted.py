"""Planted miss rates of matched rules from base 30 to 200.

    python3 r5p_planted.py > data/r5p_planted.txt

For each base with traces (r5p_trace.py) and each rule, the share of planted
solutions that the rule cuts, for both model orders. The thresholds are the
ones that match a planted miss rate of 1% and 2% at bases 32 to 38.
"""
import os

from r5p_law import poisson_law, cond_law
from r5p_curves import planted_zmins, miss

HERE = os.path.dirname(os.path.abspath(__file__))
RULES = [('poisson', '0.75', '0', 3.0), ('poisson', '0.75', '0', 2.93), ('cond', '0.75', '0', 3.35),
         ('poisson', '0.75', '0', 3.33), ('cond', '0.75', '0', 3.82)]
LAWS = {'poisson': poisson_law, 'cond': cond_law}

for b in (30, 32, 34, 35, 36, 38, 40, 45, 50, 60, 80, 100, 150, 200):
    if not os.path.exists(os.path.join(HERE, 'data', f'r5p_trace_b{b}_o1.txt')):
        continue
    out = []
    for law, zf, sl, c in RULES:
        m1 = miss(planted_zmins(b, 1, LAWS[law], zf, sl), c)
        m2 = miss(planted_zmins(b, 2, LAWS[law], zf, sl), c)
        out.append(f"{law} c={c}: {m1:.4f} {m2:.4f}")
    print(f"base {b}: " + "; ".join(out), flush=True)
