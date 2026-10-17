"""Search short lengths in large bases, to test the missing-lengths conjecture.

Under 0^0 = 1, no base up to 127 has a solution with 9, 18, 21, 22, 24, 26 or
28 digits. This runs the exact tree search of tree.py for those lengths in
bases 128 to B. Only digits with x^x < b^k can occur, so the weights are
computed for those digits alone.

Usage: missing_lengths.py B [lengths...]
"""
import math
import sys
import time

from tree import Tree


class Short(Tree):
    def __init__(self, b, d, mode=1):
        self.b, self.d = b, d
        limit = d * math.log(b)
        xmax = 1
        while (xmax + 1) * math.log(xmax + 1) < limit + 1e-9:
            xmax += 1
        self.w = [mode] + [x ** x for x in range(1, xmax + 1)]
        self.lo_b, self.hi_b = b ** (d - 1), b ** d - 1
        self.kmax = max(x for x in range(1, xmax + 1) if self.w[x] <= self.hi_b)
        self.nodes = {}
        self.stats = {}
        self.found = []

    def rec(self, k, cnt, t, rf, occ):
        self.nodes[k] = self.nodes.get(k, 0) + 1
        base = occ[k]
        for e in range(rf + 1):
            c2 = dict(cnt)
            c2[k] = base + e
            r = self.refine(k, c2, t + e * self.w[k], rf - e, occ)
            if r is None:
                continue
            t2, rf2, occ3, _ = r
            if k == 1:
                from collections import Counter
                c3 = dict(c2)
                c3[0] = occ3[0] + rf2
                s = t2 + rf2 * self.w[0]
                if self.lo_b <= s <= self.hi_b and Counter(self.digits(s)) == +Counter(c3):
                    self.found.append(s)
                continue
            self.rec(k - 1, c2, t2, rf2, occ3)


if __name__ == '__main__':
    top = int(sys.argv[1])
    lengths = [int(x) for x in sys.argv[2:]] or [9, 18, 21, 22, 24, 26, 28]
    for k in lengths:
        start = time.time()
        nodes = 0
        found = []
        for b in range(max(128, k + 1), top + 1):
            tr = Short(b, k).run()
            nodes += sum(tr.nodes.values())
            found += [(b, s) for s in tr.found]
        print(f"length {k}: bases 128-{top}, {nodes} nodes, {time.time() - start:.0f} s, solutions: {found}", flush=True)
