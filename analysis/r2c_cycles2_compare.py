"""Question 35: 2-cycles at D = 0 against near-2-cycles at offsets D = j(b-1).

    python3 r2c_cycles2_compare.py [summary_dir]

Reads the summaries of fast/src/bin/r2c_cycles2.rs (default
fast/target/r2c/cyc/sum_<b>_<m>.txt, copied to data/r2c_cycles2.txt) and the
model E_2 of data/dyn_cycle_model.txt (bases up to 17). For base 18 it
computes E_2 from the transition matrix with analysis/dyn_cycle_model.py.

A_j counts the n with F(F(n)) = n - j(b-1) and F(n) != n (multiset level),
so A_0 = 2 * (2-cycles) and the mean of A_j / 2 over j = 1..30 estimates the
base's own expected number of 2-cycles. B_j is the same for fixed points
(at least 2 digits), as a control.
"""
import math
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SUMDIR = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'fast', 'target', 'r2c', 'cyc')
DATA = os.path.join(HERE, 'data', 'r2c_cycles2.txt')


def load_summaries():
    out = {}
    if not os.path.isdir(SUMDIR):
        for line in open(DATA):
            if line.startswith('summary'):
                b = int(re.search(r' b=(\d+)', line).group(1))
                m = int(re.search(r' m=(\d+)', line).group(1))
                A = list(map(int, re.search(r' A=([\d,]+)', line).group(1).split(',')))
                B = list(map(int, re.search(r' B=([\d,]+)', line).group(1).split(',')))
                out[b, m] = (A, B)
        return out
    for fn in sorted(os.listdir(SUMDIR)):
        m = re.match(r'sum_(\d+)_(\d)\.txt$', fn)
        if not m:
            continue
        for line in open(os.path.join(SUMDIR, fn)):
            if line.startswith('summary'):
                A = list(map(int, re.search(r' A=([\d,]+)', line).group(1).split(',')))
                B = list(map(int, re.search(r' B=([\d,]+)', line).group(1).split(',')))
                out[int(m.group(1)), int(m.group(2))] = (A, B)
    return out


def load_model():
    e = {}
    for line in open(os.path.join(HERE, 'data', 'dyn_cycle_model.txt')):
        p = line.split('|')
        if len(p) < 3 or not p[0].strip()[:1].isdigit():
            continue
        b, m = map(int, p[0].split())
        ev = list(map(float, p[2].split()))
        e[b, m] = (ev[0], ev[1])
    return e


def model_from_matrix(b, m):
    sys.path.insert(0, HERE)
    import dyn_cycle_model as dcm
    dcm.MATDIR = SUMDIR
    W, coll = dcm.load_matrix(b, m)
    W2, c2, triv = dcm.lump(W, coll, b, b - 1)
    M, ev, neffs = dcm.model(W2, c2, triv)
    return dcm.predicted(M, ev, neffs, 1), dcm.predicted(M, ev, neffs, 2)


def pois_le(k, lam):
    return sum(math.exp(-lam) * lam ** i / math.factorial(i) for i in range(k + 1))


def main():
    S = load_summaries()
    E = load_model()
    for line in open(DATA):
        mm = re.match(r'model b=(\d+) m=(\d) E1=([\d.]+) E2=([\d.]+)', line)
        if mm:
            E[int(mm.group(1)), int(mm.group(2))] = (float(mm.group(3)), float(mm.group(4)))
    for (b, m) in S:
        if (b, m) not in E and os.path.exists(os.path.join(SUMDIR, f'mat_{b}_{m}.txt')):
            E[b, m] = model_from_matrix(b, m)
    print("base m | 2-cycles | E_2 | offsets: mean A_j/2 (all j), (even j) | fixed points | E_1 | mean B_j")
    groups = defaultdict(lambda: [0, 0.0, 0.0, 0.0, 0, 0.0, 0.0])
    for (b, m) in sorted(S):
        A, B = S[b, m]
        aj = [a / 2 for a in A[1:]]
        ae = [A[j] / 2 for j in range(2, len(A), 2)]
        e1, e2 = E.get((b, m), (float('nan'), float('nan')))
        print(f"{b:3d} {m} | {A[0] // 2} | {e2:.2f} | {sum(aj) / len(aj):.2f} {sum(ae) / len(ae):.2f} | "
              f"{B[0]} | {e1:.2f} | {sum(B[1:]) / len(B[1:]):.2f}")
        if b >= 4:
            g = groups[('odd' if b % 2 else 'even'), m]
            g[0] += A[0] // 2
            g[1] += e2
            g[2] += sum(aj) / len(aj)
            g[3] += sum(ae) / len(ae)
            g[4] += B[0]
            g[5] += e1
            g[6] += sum(B[1:]) / len(B[1:])
    print()
    print("group (bases 4 and up) | 2-cycles | E_2 | P(X <= obs) | offsets all j | even j | fixed points | E_1 | offsets")
    for k in sorted(groups):
        g = groups[k]
        print(f"{k[0]:4s} m={k[1]} | {g[0]} | {g[1]:.2f} | {pois_le(g[0], g[1]):.3f} | {g[2]:.2f} | {g[3]:.2f} | "
              f"{g[4]} | {g[5]:.2f} | {g[6]:.2f}")


if __name__ == '__main__':
    main()


def empirical():
    """Group totals of A_j / 2 for each offset j: the law of the D = 0 count."""
    S = load_summaries()
    print()
    print("group totals of A_j / 2 per offset j = 1..30 (bases 4 and up)")
    for par in (0, 1):
        for m in (0, 1):
            keys = [k for k in S if k[0] >= 4 and k[0] % 2 == par and k[1] == m]
            J = min(len(S[k][0]) for k in keys) - 1
            tot = [sum(S[k][0][j] for k in keys) / 2 for j in range(1, J + 1)]
            o = sum(S[k][0][0] // 2 for k in keys)
            mean = sum(tot) / J
            var = sum((t - mean) ** 2 for t in tot) / (J - 1)
            print(f"{'odd' if par else 'even':4s} m={m}: mean {mean:.2f}, variance {var:.2f}, min {min(tot)}, "
                  f"D=0 has {o}; offsets with at most {o}: {sum(1 for t in tot if t <= o)} of {J}")


if __name__ == '__main__':
    empirical()
