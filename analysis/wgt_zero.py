"""Question 9: the counts N_m(b) for 0^0 = m, against the refined model.

A solution without the digit 0 is a solution for every m, so the script
splits the counts into solutions without zeros (shared by all m) and
solutions with zeros (one m each). It reads the files of wgt_family.py.

    python3 wgt_zero.py > data/wgt_zero_summary.txt
"""
import math
import numpy as np
from collections import defaultdict

MS = [-2, -1, 0, 1, 2, 3]
FILES = {m: (f'data/wgt_zero_{m}.txt', 1) for m in (-2, -1, 2, 3)}
FILES[0] = ('data/wgt_true.txt', 0)
FILES[1] = ('data/wgt_true.txt', 1)
B0, B1 = 10, 30
SAMPLES = 100_000


def observed():
    out = {}
    for m, (path, mode) in FILES.items():
        sols = set()
        for line in open(path):
            p = line.split()
            if p and p[0] == 'raw' and int(p[2]) == mode:
                sols |= {(int(p[1]), tuple(map(int, t.split(',')))) for t in p[3:] if ',' in t}
        out[m] = sols
    return out


def model():
    """exp[m, b] = (refined total, refined without zeros)."""
    rng = np.random.default_rng(9)
    exp = defaultdict(lambda: [0.0, 0.0])
    for b in range(B0, B1 + 1):
        q = b - 1
        u = np.array([0] + [(x ** x - x) % q for x in range(1, b)], dtype=np.int64)
        for d in range(2, b + 1):
            scale = float(b) ** (d - 1)
            w = np.array([0.0] + [x ** x / scale for x in range(1, b)])
            counts = rng.multinomial(d - 1, np.full(b, 1.0 / b), size=SAMPLES)
            lead = rng.integers(1, b, size=SAMPLES)
            counts[np.arange(SAMPLES), lead] += 1
            base = counts @ w
            r = counts @ u
            c0 = counts[:, 0]
            for m in MS:
                f = base + c0 * m / scale
                ok = (f >= 1.0) & (f < b) & ((r + c0 * m) % q == 0)
                exp[m, b][0] += q * np.count_nonzero(ok) / SAMPLES
                exp[m, b][1] += q * np.count_nonzero(ok & (c0 == 0)) / SAMPLES
    return exp


obs = observed()
exp = model()
print(f"# bases {B0}-{B1}, nontrivial solutions under 0^0 = m; observed / refined model")
print("# m  parity  all: obs pred | with zeros: obs pred | no zeros: obs pred | odd/even factor of the model")
for m in MS:
    row = []
    for par in (0, 1):
        bs = [b for b in range(B0, B1 + 1) if b % 2 == par]
        o = [s for s in obs[m] if s[0] in bs]
        oz = [s for s in o if 0 in s[1]]
        e = sum(exp[m, b][0] for b in bs)
        ez = sum(exp[m, b][0] - exp[m, b][1] for b in bs)
        row.append((len(o), e, len(oz), ez, len(o) - len(oz), e - ez, len(bs)))
    fac = (row[1][1] / row[1][6]) / (row[0][1] / row[0][6])
    for (par, r) in zip(('even', 'odd'), row):
        print(f"{m:3d} {par:4s}  all {r[0]:3d} {r[1]:6.2f} | zeros {r[2]:3d} {r[3]:6.2f} | no zeros {r[4]:3d} {r[5]:6.2f}"
              + (f" | factor {fac:.3f}" if par == 'odd' else ""))
# chance of the observed count with zeros or more, Poisson, pooled by the parity of m
for name, group in (('even m', (-2, 0, 2)), ('odd m', (-1, 1, 3))):
    for par in (0, 1):
        bs = [b for b in range(B0, B1 + 1) if b % 2 == par]
        o = sum(1 for m in group for s in obs[m] if s[0] in bs and 0 in s[1])
        e = sum(exp[m, b][0] - exp[m, b][1] for m in group for b in bs)
        p = 1 - sum(math.exp(-e) * e ** k / math.factorial(k) for k in range(o))
        print(f"# {name}, {'odd' if par else 'even'} bases, with zeros: observed {o}, expected {e:.1f}, P(>= observed) {p:.3f}")
