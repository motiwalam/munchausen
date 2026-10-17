"""Readable version of the prefix-pruned count search, for experiments.

It searches one digit length d of one base under 0^0 = 1 and records
statistics about the search tree. It mirrors fast/src/search.rs (forced
digits included) but uses plain Python integers.
"""
import sys
from collections import Counter, defaultdict


class Tree:
    def __init__(self, b, d, mode=1):
        self.b, self.d = b, d
        self.w = [mode] + [x ** x for x in range(1, b)]
        self.lo_b, self.hi_b = b ** (d - 1), b ** d - 1
        self.kmax = max(x for x in range(1, b) if self.w[x] <= self.hi_b)
        self.nodes = defaultdict(int)   # level k -> nodes
        self.stats = defaultdict(list)  # level k -> (high digits, free slots, prefix length)
        self.found = []

    def digits(self, n):
        out = []
        for _ in range(self.d):
            out.append(n % self.b)
            n //= self.b
        return out[::-1]  # most significant first

    def prefix(self, lo, hi):
        lo, hi = max(lo, self.lo_b), min(hi, self.hi_b)
        if lo > hi:
            return None
        a, c = self.digits(lo), self.digits(hi)
        p = 0
        while p < self.d and a[p] == c[p]:
            p += 1
        return a[:p]

    def refine(self, k, cnt, t, rf, occ):
        """Fixpoint of the leading-digit test. Returns (t, rf, occ, prefix length) or None."""
        occ = Counter(occ)
        while True:
            hi_w = self.w[k - 1] if k >= 1 else 0
            lo, hi = t + rf * min(self.w[:k] or [0]), t + rf * hi_w
            pre = self.prefix(lo, hi)
            if pre is None:
                return None
            new = Counter(pre)
            forced = False
            for x, m in new.items():
                if x >= k:
                    if m > cnt.get(x, 0):
                        return None
                elif m > occ[x]:
                    extra = m - occ[x]
                    if extra > rf:
                        return None
                    rf -= extra
                    t += extra * self.w[x]
                    occ[x] = m
                    forced = True
            if not forced:
                return t, rf, occ, len(pre)

    def run(self):
        self.rec(self.kmax, {}, 0, self.d, Counter())
        return self

    def rec(self, k, cnt, t, rf, occ):
        self.nodes[k] += 1
        base = occ[k]
        for e in range(rf + 1):
            c2 = dict(cnt)
            c2[k] = base + e
            r = self.refine(k, c2, t + e * self.w[k], rf - e, occ)
            if r is None:
                continue
            t2, rf2, occ3, plen = r
            self.stats[k].append((sum(c2.values()), rf2, plen))
            if k == 1:
                c3 = dict(c2)
                c3[0] = occ3[0] + rf2
                s = t2 + rf2 * self.w[0]
                if self.lo_b <= s <= self.hi_b and Counter(self.digits(s)) == +Counter(c3):
                    self.found.append(s)
                continue
            self.rec(k - 1, c2, t2, rf2, occ3)


if __name__ == '__main__':
    b, d = int(sys.argv[1]), int(sys.argv[2])
    tr = Tree(b, d).run()
    print(f"base {b}, d={d}: {sum(tr.nodes.values())} nodes, found {tr.found}")
    for k in sorted(tr.stats, reverse=True):
        st = tr.stats[k]
        hd = Counter(h for h, _, _ in st)
        avg_h = sum(h for h, _, _ in st) / len(st)
        avg_p = sum(p for _, _, p in st) / len(st)
        print(f"k={k:2d} children {len(st):7d}  high digits avg {avg_h:5.2f} (values decided {b-k}, "
              f"expected {(b-k)*d/b:4.1f})  prefix avg {avg_p:5.1f}  max high {max(hd)}")
