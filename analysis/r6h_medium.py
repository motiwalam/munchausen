"""Question 92: the two heuristics at medium lengths, lengths 6 to 12 in
bases 7 to 20.

For every base b and length k (k <= b) and both conventions:

  root   the root heuristic of sections 11.4 and 19.3, restricted to the
         strings whose real root b* lies in [b - 1/2, b + 1/2) and whose
         digits are below b. Monte Carlo over uniform strings with digits
         up to X = min(b - 1, max{x : x^x < (b + 1/2)^k}). Three versions:
         spacing only, local factors mod the primes up to 31, and p-adic
         (roots mod 64, 81, 125 for 2, 3, 5).
  ref    the refined per-base model (identity mod b - 1), exact
         (r6q_lib.refined_by_zeros), and the same with the top t = 1, 2, 3
         digits of F forced (the ratio of r2c_top_model.expected_top).
  win    the window calibration of section 22.4.1 (r4b_spectrum.c), class
         mean modulo 2(b - 1), read from the raw files in the directory
         given as the last argument (lengths 6 to 10).
  obs    the census of output/b2-41-<m>.txt.

    python3 r6h_medium.py run N SPECDIR [MODES] > data/r6h_medium.txt
        (the data file was made with N = 1500000 for 0^0 = 1 and
        N = 600000, MODES = 0, appended without its header, for 0^0 = 0)
    python3 r6h_medium.py report data/r6h_medium.txt > data/r6h_medium_report.txt
"""
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import r6q_lib as R  # noqa: E402
from r6h_shortref import census  # noqa: E402

PRIMES = [7, 11, 13, 17, 19, 23, 29, 31]
PADIC = [64, 81, 125]
SMALL = [2, 3, 5]
BASES = range(7, 21)
LENGTHS = range(6, 13)


def roots_count(S, Fq, q):
    """number of r mod q with P_s(r) == F (mod q), per row of S"""
    n, k = S.shape
    r = np.arange(q, dtype=np.int64)
    v = np.zeros((n, q), dtype=np.int64)
    for j in range(k):
        v = (v * r + S[:, j:j + 1]) % q
    return (v == (Fq[:, None] % q)).sum(axis=1)


def root_cell(b, k, m, N, rng):
    X = 1
    while X + 1 <= b - 1 and (X + 1) * math.log(X + 1) < k * math.log(b + 0.5):
        X += 1
    total = X * (X + 1) ** (k - 1)
    wf = np.array([float(m)] + [float(x) ** x for x in range(1, X + 1)])
    acc = np.zeros(3)
    acc2 = np.zeros(3)
    inwin = 0
    done = 0
    while done < N:
        n = min(200_000, N - done)
        done += n
        S = rng.integers(0, X + 1, size=(n, k))
        S[:, 0] = rng.integers(1, X + 1, size=n)
        F = wf[S].sum(axis=1)
        pw = np.vander(np.array([b - 0.5, b + 0.5]), k)  # rows: powers r^(k-1)..1
        lo = S @ pw[0]
        hi = S @ pw[1]
        ok = (lo <= F) & (F < hi)
        if not ok.any():
            continue
        S, F = S[ok], F[ok]
        inwin += len(F)
        # Newton for P_s(r) = F from r = b
        rr = np.full(len(F), float(b))
        ex = np.arange(k - 1, -1, -1)
        for _ in range(30):
            P = (S * rr[:, None] ** ex).sum(axis=1)
            dP = (S[:, :-1] * ex[:-1] * rr[:, None] ** (ex[:-1] - 1)).sum(axis=1)
            rr -= (P - F) / dP
        dP = (S[:, :-1] * ex[:-1] * rr[:, None] ** (ex[:-1] - 1)).sum(axis=1)
        # exact residues of F
        Fint = [sum((int(x) ** int(x) if x else m) for x in row) for row in S]
        sp = np.ones(len(F))
        pa = np.ones(len(F))
        for q in PRIMES:
            Fq = np.array([f % q for f in Fint], dtype=np.int64)
            c = roots_count(S, Fq, q)
            sp *= c
            pa *= c
        for q in SMALL:
            Fq = np.array([f % q for f in Fint], dtype=np.int64)
            sp *= roots_count(S, Fq, q)
        for q in PADIC:
            Fq = np.array([f % q for f in Fint], dtype=np.int64)
            pa *= roots_count(S, Fq, q)
        for i, fac in enumerate((np.ones(len(F)), sp, pa)):
            wgt = np.minimum(1.0, fac / dP)
            acc[i] += wgt.sum()
            acc2[i] += (wgt ** 2).sum()
    mean = acc / N
    se = np.sqrt(np.maximum(acc2 / N - mean ** 2, 0) / N)
    return total * mean, total * se, inwin, X


def top_ratio(b, d, m, N, rng, tmax=3):
    """Mean over the candidate multisets that meet the identity of the
    forced-top factor of forced_top.py, t = 0..tmax. As in
    r2c_top_model.expected_top, but the digits are drawn from 0..X, X the
    largest digit with X^X < b^d: larger digits never give a d-digit F, so
    this is the same conditional law with far fewer rejections."""
    q = b - 1
    X = 1
    while X + 1 <= b - 1 and (X + 1) * math.log(X + 1) < d * math.log(b):
        X += 1
    scale = (d - 1) * math.log(b)
    x = np.arange(b, dtype=float)
    w = np.exp(np.where(x > 0, x * np.log(np.maximum(x, 1)), 0.0) - scale)
    w[0] = m * math.exp(-scale)
    u = np.array([((pow(v, v, q) if v > 0 else m) - v) % q for v in range(b)], dtype=np.int64)
    p = np.zeros(b)
    p[:X + 1] = 1.0 / (X + 1)
    sums = np.zeros(tmax + 1)
    acc = 0
    done = 0
    while done < N:
        n = min(50_000, N - done)
        done += n
        c = rng.multinomial(d - 1, p, size=n)
        lead = rng.integers(1, X + 1, size=n)
        c[np.arange(n), lead] += 1
        f = c @ w
        ok = (f >= 1.0) & (f < b) & ((c @ u) % q == 0)
        c, f = c[ok], f[ok]
        k = len(f)
        if k == 0:
            continue
        acc += k
        rows = np.arange(k)
        base = (d - c[:, 0]) / d
        num = np.ones(k)
        digs = []
        g = f.copy()
        sums[0] += k
        for t in range(1, tmax + 1):
            v = np.floor(g).astype(np.int64) % b
            g = (g - np.floor(g)) * b
            used = np.zeros(k, dtype=np.int64)
            for prev in digs:
                used += (prev == v)
            digs.append(v)
            num = num * np.maximum(0, c[rows, v] - used) / (d - t + 1)
            sums[t] += ((b - 1) * float(b) ** (t - 1) * num / base).sum()
    return [sums[t] / sums[0] if sums[0] else float('nan') for t in range(tmax + 1)], acc


def ref_cell(b, k, m, Ntop, rng):
    w = R.weights(b, m)
    ref = max(float(R.refined_by_zeros(b, k, w).sum()), 0.0)
    ratios, _ = top_ratio(b, k, m, Ntop, rng)
    return ref, ratios


def spec(specdir, k, m, b):
    from r4b_spectrum import parse, estimates
    path = os.path.join(specdir, f'spec_L{k}_z{m}.txt')
    if not os.path.exists(path):
        return float('nan')
    d = parse(path).get(b)
    if d is None:
        return float('nan')
    return estimates(d)['2(b-1)']


def run(N, specdir, modes=(1, 0)):
    rng = np.random.default_rng(92)
    obs = census()
    print("# b k m obs ref ref_t1 ref_t2 ref_t3 win root_plain root_prime root_padic se_padic inwin X")
    for m in modes:
        for b in BASES:
            for k in LENGTHS:
                if k > b:
                    continue
                o = obs.get((m, b), []).count(k)
                ref, ratios = ref_cell(b, k, m, 1_000_000, rng)
                win = spec(specdir, k, m, b)
                E, se, inwin, X = root_cell(b, k, m, N, rng)
                print(f"{b} {k} {m} {o} {ref:.5f} {ref * ratios[1]:.5f} {ref * ratios[2]:.5f} {ref * ratios[3]:.5f} "
                      f"{win:.5f} {E[0]:.5f} {E[1]:.5f} {E[2]:.5f} {se[2]:.5f} {inwin} {X}", flush=True)


def report(path):
    rows = []
    for line in open(path):
        if line.startswith('#') or not line.strip():
            continue
        p = line.split()
        rows.append([int(p[0]), int(p[1]), int(p[2]), int(p[3])] + [float(v) for v in p[4:13]])
    cols = ['obs', 'ref', 'ref_t1', 'ref_t2', 'ref_t3', 'win', 'plain', 'prime', 'padic']
    print("# totals per convention and length, bases 7..20 (win: lengths 6..10 only, bases with a class mean)")
    print("# m k " + " ".join(cols))
    for m in (1, 0):
        for k in list(LENGTHS) + ['all']:
            sel = [r for r in rows if r[2] == m and (k == 'all' or r[1] == k)]
            tot = []
            for i in range(len(cols)):
                vals = [r[3 + i] for r in sel if not math.isnan(r[3 + i])]
                tot.append(sum(vals))
            print(f"{m} {k} " + " ".join(f"{v:.3f}" for v in tot))
    print("# same, split by base parity (all lengths)")
    for m in (1, 0):
        for par in (0, 1):
            sel = [r for r in rows if r[2] == m and r[0] % 2 == par]
            tot = [sum(r[3 + i] for r in sel if not math.isnan(r[3 + i])) for i in range(len(cols))]
            print(f"{m} {'even' if par == 0 else 'odd'} " + " ".join(f"{v:.3f}" for v in tot))
    print("# cells with a window estimate (lengths 6..10): totals and cell-by-cell agreement with win")
    for m in (1, 0):
        sel = [r for r in rows if r[2] == m and not math.isnan(r[9]) and r[1] <= 10]
        tot = [sum(r[3 + i] for r in sel) for i in range(len(cols))]
        print(f"{m} win-cells({len(sel)}) " + " ".join(f"{v:.3f}" for v in tot))
        for par in (0, 1):
            sp = [r for r in sel if r[0] % 2 == par]
            tp = [sum(r[3 + i] for r in sp) for i in range(len(cols))]
            print(f"{m} win-cells {'even' if par == 0 else 'odd'}({len(sp)}) " + " ".join(f"{v:.3f}" for v in tp))
        w = np.array([r[9] for r in sel])
        for name, i in (('ref', 4), ('ref_t1', 5), ('ref_t3', 7), ('plain', 10), ('prime', 11), ('padic', 12)):
            x = np.array([r[i] for r in sel])
            sad = float(np.abs(x - w).sum())
            print(f"   {name}: correlation with win {np.corrcoef(x, w)[0, 1]:.3f}, sum |x - win| {sad:.3f}")
    print("# cell by cell: correlation over cells of log(root_padic / ref_t3)")
    for m in (1, 0):
        sel = [r for r in rows if r[2] == m and r[7] > 0 and r[12] > 0]
        lr = np.array([math.log(r[12] / r[7]) for r in sel])
        print(f"m={m}: {len(sel)} cells, mean log ratio {lr.mean():.3f}, sd {lr.std():.3f}, "
              f"median ratio {math.exp(float(np.median(lr))):.3f}")


def main():
    if sys.argv[1] == 'run':
        modes = tuple(int(v) for v in sys.argv[4].split(',')) if len(sys.argv) > 4 else (1, 0)
        run(int(sys.argv[2]), sys.argv[3], modes)
    else:
        report(sys.argv[2])


if __name__ == '__main__':
    main()
