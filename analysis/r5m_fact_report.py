"""Question 84: summary of the top-digit model of r5m_fact_model.py.

Reads data/r5m_fact_model_m{0,1}.txt and the near-solution counts of
data/r3t_factorial_near1000.txt (offsets D = 1000 j, j = 1..100, L = 10..26).
Prints, per convention: the open lengths (adaptive model EA > threshold),
the sums of the plain model E0, of E_K for fixed K and of EA over
L = 3..33, 34..40, 34..100, with standard errors for EA, and the per-length
comparison with the near-solutions.

usage: python3 r5m_fact_report.py [threshold]
"""
import math
import re
import sys

HERE = __file__.rsplit('/', 1)[0]


def load(m):
    rows = {}
    for line in open(f'{HERE}/data/r5m_fact_model_m{m}.txt'):
        if not line.startswith('L '):
            continue
        f = line.split()
        d = {f[i]: f[i + 1] for i in range(2, len(f) - 1, 2)}
        rows[int(f[1])] = {k: float(v) for k, v in d.items()}
    return rows


def near(m):
    out = {}
    for line in open(f'{HERE}/data/r3t_factorial_near1000.txt'):
        mm = re.match(r'len m (\d) L (\d+) sols \d+ nodes \d+ near (\S+)', line)
        if mm and int(mm.group(1)) == m:
            v = [int(x) for x in mm.group(3).split(',')]
            out[int(mm.group(2))] = (sum(v), sum(1 for x in v if x))
    return out


def main():
    thr = float(sys.argv[1]) if len(sys.argv) > 1 else 0.01
    for m in (0, 1):
        rows = load(m)
        nr = near(m)
        print(f"# 0^0 = {m}: lengths {min(rows)}..{max(rows)}")
        ks = ['E0', 'E3', 'E6', 'E8', 'EA']
        for lo, hi in ((3, 33), (34, 40), (34, 100), (41, 100)):
            Ls = [L for L in rows if lo <= L <= hi]
            sums = {k: sum(rows[L].get(k, 0.0) for L in Ls) for k in ks}
            se = math.sqrt(sum(rows[L]['EA_se'] ** 2 for L in Ls))
            terms = sum(int(rows[L]['EA_terms']) for L in Ls)
            print(f"L {lo}..{hi}: " + ' '.join(f"{k} {v:.3f}" for k, v in sums.items())
                  + f"  (EA standard error {se:.3f}, {terms} nonzero terms)")
        openL = [L for L in sorted(rows) if rows[L]['EA'] > thr]
        print(f"open lengths (EA > {thr}), L <= 33: {[L for L in openL if L <= 33]}")
        print(f"open lengths (EA > {thr}), 34 <= L <= 100: {[L for L in openL if L >= 34]}")
        closed = [L for L in sorted(rows) if rows[L]['EA'] == 0.0]
        print(f"lengths with EA = 0 exactly: {len(closed)} of {len(rows)}")
        print("near-solutions D = 1000 j (j = 1..100) against 100 * model, L = 10..26:")
        print("  L near(total, offsets hit) 100*E0 100*EA")
        for L in range(10, 27):
            if L in nr and L in rows:
                print(f"  {L} {nr[L][0]} {nr[L][1]} {100 * rows[L]['E0']:.1f} {100 * rows[L]['EA']:.1f}")
        tot_near = sum(nr[L][0] for L in nr)
        print(f"  total near {tot_near}, 100*E0 {100 * sum(rows[L]['E0'] for L in nr):.1f}, "
              f"100*EA {100 * sum(rows[L]['EA'] for L in nr):.1f}")
        ea33 = sum(rows[L]['EA'] for L in rows if L <= 33)
        e033 = sum(rows[L]['E0'] for L in rows if 3 <= L <= 33)
        print(f"P(no solution with 3 <= L <= 33): plain {math.exp(-e033):.3f}, top-digit model {math.exp(-ea33):.3f}\n")


if __name__ == '__main__':
    main()
