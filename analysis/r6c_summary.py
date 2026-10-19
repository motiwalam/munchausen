"""Question 104: the predictions of r6c_predict.py as tables, and, once the
outputs exist, the comparison with the exact census.

    python3 r6c_summary.py            # predictions only
    python3 r6c_summary.py compare    # also read output/b<b>-<m>.txt

Model: the refined model with the forced top three digits (t = 3). The
calibrated variant multiplies the 0^0 = 1 counts by 1.12 (section 11.2a).
Base 44 was searched before with --deficit 2 --band 2.5 (section 9.3), which
found one 43-digit solution under 0^0 = 1 and none under 0^0 = 0, and misses
about 15% of solutions. "Fresh" expectations for base 44 count only what that
run could have missed.
"""
import math
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
BASES = (42, 44, 45, 46)
CLASSES = ('b', 'b-1', 'b-2', 'b-3', '<=b-4')
MISS44 = 0.15
CAL1 = 1.12


def load():
    e = defaultdict(dict)
    zf = defaultdict(dict)
    total = {}
    for line in open(os.path.join(HERE, 'data', 'r6c_predict_census.txt')):
        f = line.split()
        b, m, cls = int(f[1]), int(f[3]), f[4]
        kv = dict(zip(f[5::2], map(float, f[6::2])))
        if cls == 'total':
            total[(b, m)] = kv
        else:
            e[(b, m)][cls] = kv['t3']
            zf[(b, m)][cls] = kv['zerofree_t3']
    return e, zf, total


def pois_cdf(k, lam):
    return sum(math.exp(-lam) * lam ** i / math.factorial(i) for i in range(k + 1))


def interval(lam, lo=0.05, hi=0.95):
    a = 0
    while pois_cdf(a, lam) < lo:
        a += 1
    c = a
    while pois_cdf(c, lam) < hi:
        c += 1
    return a, c


def observed():
    """Nontrivial solutions by (base, convention): list of digit tuples."""
    obs = {}
    for b in BASES:
        for m in (0, 1):
            p = os.path.join(HERE, '..', 'output', f'b{b}-{m}.txt')
            if not os.path.exists(p):
                continue
            line = open(p).read().strip()
            sols = [tuple(map(int, t.split(','))) for t in re.findall(r'\(([\d,]+?),?\)', line)]
            obs[(b, m)] = [s for s in sols if len(s) > 1]
    return obs


def cls_of(b, d):
    j = b - d
    return CLASSES[j] if j <= 3 else '<=b-4'


def main():
    e, zf, total = load()
    print("Per base and convention, model t = 3 (calibrated 0^0 = 1 in brackets)")
    print("| base | conv. | " + " | ".join(CLASSES) + " | total | zero-free | mean zeros | P(none) |")
    for b in BASES:
        for m in (0, 1):
            k = 1.0 if m == 0 else CAL1
            row = [f"{e[(b, m)][c]:.3f}" for c in CLASSES]
            t = total[(b, m)]['t3']
            cal = f" ({t * k:.2f})" if m == 1 else ""
            print(f"| {b} | {m} | " + " | ".join(row) +
                  f" | {t:.2f}{cal} | {total[(b, m)]['zerofree_t3']:.2f} | {total[(b, m)]['meanzeros_t3']:.2f} "
                  f"| {math.exp(-t):.2f} |")
    print()
    print("Empty bases (no nontrivial solution under either convention)")
    for b in BASES:
        e0, e1 = total[(b, 0)]['t3'], total[(b, 1)]['t3']
        es = total[(b, 0)]['zerofree_t3']
        u = e0 + e1 - es
        uc = e0 + CAL1 * e1 - es
        print(f"base {b}: E0 {e0:.2f} E1 {e1:.2f} shared {es:.2f} union {u:.2f} "
              f"P(empty) {math.exp(-u):.3f} calibrated {math.exp(-uc):.3f}")
    e0_44 = total[(44, 0)]['t3']
    print(f"base 44 given the inexact run: P(no solution under 0^0 = 0) = "
          f"{math.exp(-e0_44) / math.exp(-(1 - MISS44) * e0_44):.3f}")
    print()
    for m in (0, 1):
        k = 1.0 if m == 0 else CAL1
        tot = sum(total[(b, m)]['t3'] for b in BASES)
        fresh = sum(total[(b, m)]['t3'] for b in BASES if b != 44) + MISS44 * total[(44, m)]['t3']
        for name, lam in (('all four bases', tot), ('fresh', fresh)):
            print(f"0^0 = {m}, {name}: model {lam:.2f} 90% {interval(lam)}; calibrated {lam * k:.2f} 90% {interval(lam * k)}")
        for c in ('b', 'b-1'):
            lam = sum(e[(b, m)][c] for b in BASES)
            print(f"0^0 = {m}, class {c}: model {lam:.3f}, P(none) {math.exp(-lam):.3f}")
    if len(sys.argv) < 2 or sys.argv[1] != 'compare':
        return
    obs = observed()
    print()
    print("Observed against model")
    for m in (0, 1):
        k = 1.0 if m == 0 else CAL1
        n_tot = lam_tot = lam_fresh = 0.0
        n_fresh = 0
        bycls = defaultdict(int)
        lamcls = defaultdict(float)
        zeros = []
        zerofree = 0
        for b in BASES:
            if (b, m) not in obs:
                continue
            sols = obs[(b, m)]
            t = total[(b, m)]['t3']
            print(f"base {b} 0^0 = {m}: {len(sols)} observed, {t:.2f} expected, lengths {[len(s) for s in sols]}, "
                  f"zeros {[s.count(0) for s in sols]}")
            n_tot += len(sols)
            lam_tot += t
            if b == 44:
                known = 1 if m == 1 else 0
                n_fresh += len(sols) - known
                lam_fresh += MISS44 * t
            else:
                n_fresh += len(sols)
                lam_fresh += t
            for s in sols:
                bycls[cls_of(b, len(s))] += 1
                zeros.append(s.count(0))
                zerofree += s.count(0) == 0
            for c in CLASSES:
                lamcls[c] += e[(b, m)][c]
        print(f"0^0 = {m}: total {int(n_tot)} vs {lam_tot:.2f} (P(>=) {1 - pois_cdf(int(n_tot) - 1, lam_tot):.3f}, "
              f"P(<=) {pois_cdf(int(n_tot), lam_tot):.3f}); fresh {n_fresh} vs {lam_fresh:.2f} "
              f"(P(>=) {1 - pois_cdf(n_fresh - 1, lam_fresh):.3f}); calibrated fresh {lam_fresh * k:.2f}")
        for c in CLASSES:
            print(f"   class {c}: {bycls[c]} vs {lamcls[c]:.3f}")
        print(f"   zero-free {zerofree}, mean zeros {sum(zeros) / max(1, len(zeros)):.2f}")
    for b in BASES:
        if (b, 0) in obs and (b, 1) in obs:
            empty = not obs[(b, 0)] and not obs[(b, 1)]
            print(f"base {b}: {'EMPTY' if empty else 'not empty'}")


if __name__ == '__main__':
    main()
