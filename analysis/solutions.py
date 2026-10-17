"""Load the exhaustive results and print structural statistics."""
import math
from collections import Counter

def load(path):
    out = {}
    for line in open(path):
        b, m, n, ns = line.strip().split(':', 3)
        tuples = eval('(' + ns + ',)') if ns.strip() else ()
        out[int(b)] = [t for t in tuples if t not in ((0,), (1,))]
    return out

def value(t, b):
    v = 0
    for x in t:
        v = v * b + x
    return v

import os
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'output')
SOL = {m: load(os.path.join(ROOT, f'b2-38-{m}.txt')) for m in (0, 1)}

if __name__ == '__main__':
    # where the solutions live: d - b
    for mode in (0, 1):
        off = Counter()
        for b, ts in SOL[mode].items():
            if b < 20:
                continue
            for t in ts:
                off[b - len(t)] += 1
        tot = sum(off.values())
        print(f"0^0={mode}, bases 20-38: {tot} solutions; b-d:",
              {k: off[k] for k in sorted(off)})
    # twins in 0^0 = 0: n ending in 0 <-> n+1 ending in 1
    tw = 0
    for b, ts in SOL[0].items():
        s = set(ts)
        for t in ts:
            if t[-1] == 0:
                u = t[:-1] + (1,)
                assert u in s, (b, t)
                tw += 1
    print("0^0=0 solutions ending in 0, each with its twin ending in 1:", tw)
    # leading digit vs prediction from the largest digit present
    print("\nbase d lead  predicted-lead  (sum of x^x / b^(d-1) over the top two digit values)")
    for b in range(30, 39):
        for t in SOL[1][b]:
            d = len(t)
            c = Counter(t)
            pred = sum(c[x] * math.exp(x * math.log(x) - (d - 1) * math.log(b)) for x in c if x > 0)
            print(b, d, t[0], f"{pred:.2f}", "max digit", max(t), "count", c[max(t)])
