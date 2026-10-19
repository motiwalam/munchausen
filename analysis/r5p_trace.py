"""Search paths of planted solutions, level by level, for rule design.

    python3 r5p_trace.py <base> <count> <order> <seed> > data/r5p_trace_b<base>_o<order>.txt

order 1: a planted solution is a uniform random digit string whose sum F has
d digits (walk.planted, the model of chapter 9).
order 2: the same multiset c, but the top 3 digits of the string are the top
3 digits of F(c), as for a real solution, and the other digits are a random
arrangement of the rest of c. The line carries the importance weight of the
forced-top model (forced_top.py): 0 if the top digits of F(c) do not fit in
c. Weighted averages over order-2 lines follow the second-order model.

Each line: d kmax weight, then one record k,pp,rf,lneed per level k = kmax..2,
after the forced digits of that level (the state that the engine tests).
"""
import math
import random
import sys
from collections import Counter

from walk import planted, planted_lengths


def trace(b, digits):
    d = len(digits)
    c = Counter(digits)
    lo_b, hi_b = b ** (d - 1), b ** d - 1
    w = lambda x: 0 if x == 0 else x ** x
    whi = lambda x: 1 if x == 0 else x ** x
    kmax = max(x for x in range(1, b) if x ** x <= hi_b)
    occ = Counter()
    t, rf, known = 0, d, 0
    pw = [b ** (d - 1 - p) for p in range(d)]
    out = []
    for k in range(kmax, 1, -1):
        e = c[k] - occ[k]
        t += e * w(k)
        rf -= e
        while True:
            lo = max(t, lo_b)
            hi = min(t + occ[0] + rf * whi(k - 1), hi_b)
            p = known
            while p < d and lo // pw[p] == hi // pw[p]:
                p += 1
            forced = False
            for pos in range(known, p):
                x = digits[pos]
                occ[x] += 1
                if x < k:
                    rf -= 1
                    t += w(x)
                    forced = True
            known = max(known, p)
            if not forced:
                break
        lneed = sum(math.lgamma(c[x] - occ[x] + 1) for x in range(k, kmax + 1))
        out.append((k, d - known, rf, lneed))
    return kmax, out


def second_order(b, s, rng, t=3):
    d = len(s)
    c = Counter(s)
    F = sum((x ** x if x else 1) for x in s)
    top = []
    for p in range(t):
        top.append(F // b ** (d - 1 - p) % b)
    rest = c.copy()
    num = 1.0
    for v in top:
        num *= max(0, rest[v])
        rest[v] -= 1
    if num == 0:
        return 0.0, None
    den = math.prod(d - i for i in range(t))
    wgt = (b - 1) * b ** (t - 1) * num / den / ((d - c[0]) / d)
    tail = [x for x, n in rest.items() for _ in range(n)]
    rng.shuffle(tail)
    return wgt, top + tail


def main():
    b, n, order, seed = map(int, sys.argv[1:5])
    rng = random.Random(seed)
    for _ in range(n):
        s = planted(b, planted_lengths(b, rng), rng)
        wgt = 1.0
        if order == 2:
            wgt, s2 = second_order(b, s, rng)
            if s2 is None:
                print(f"{len(s)} 0 0")
                continue
            s = s2
        kmax, recs = trace(b, s)
        print(f"{len(s)} {kmax} {wgt:.6g} " + " ".join(f"{k},{pp},{rf},{ln:.6f}" for k, pp, rf, ln in recs), flush=True)


if __name__ == '__main__':
    main()
