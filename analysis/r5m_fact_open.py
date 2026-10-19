"""Question 84: open lengths in the factorial number system.

A Python port of the first levels of fast/src/bin/r3t_factorial.rs with
exact integers, so any L works. The search fixes the length L, decides the
counts of the digit values from the largest down, and after each decision
reads off the top factorial digits that all sums F in the remaining range
share (settle). A shared digit must be one of the decided copies, or it
forces one more copy of an undecided smaller value. A value u can only sit
at a position >= u (Hall condition).

For each L the script runs the tree down to `depth` decided values and
reports the number of surviving nodes, and among them the nodes that are
"committed": at least one copy of a value above a threshold is present, so
the top digits of F have to place it.

usage: python3 r5m_fact_open.py m Lmin Lmax depth [offset]
"""
import sys
from math import factorial


class Cfg:
    def __init__(self, L, m, off=0):
        self.L = L
        self.fact = [factorial(i) for i in range(L + 2)]
        top = self.fact[L + 1] - 1
        w = [m]
        kmax = 0
        for v in range(1, L + 1):
            p = v ** v
            if p + off > top:
                break
            w.append(p)
            kmax = v
        self.w = w
        self.kmax = kmax
        nv = kmax + 1
        self.nv = nv
        self.wmin = [None] * (nv + 1)
        self.wmax = [0] * (nv + 1)
        mn = None
        for k in range(1, nv + 1):
            mn = w[k - 1] if mn is None else min(mn, w[k - 1])
            self.wmin[k] = mn
            self.wmax[k] = max(self.wmax[k - 1], w[k - 1])
        self.wl = self.fact[L]
        self.wu = min(top, max(w) * L + off)
        self.off = off

    def digit_at(self, n, j):
        return (n // self.fact[j]) % (j + 1)

    def hall(self, c, k):
        s = 0
        for u in range(self.kmax, max(k, 1) - 1, -1):
            s += c[u]
            if s > self.L + 1 - u:
                return False
        return True


def settle(cfg, n):
    """n = [k, r, t, j, c, h]; mutates n; returns False if the node dies"""
    while True:
        k, r, t = n[0], n[1], n[2]
        if k == 0:
            lo = hi = t
        else:
            lo, hi = t + r * cfg.wmin[k], t + r * cfg.wmax[k]
        lo, hi = max(lo, cfg.wl), min(hi, cfg.wu)
        if lo > hi:
            return False
        forced = False
        while n[3] > 1:
            j = n[3] - 1
            if lo // cfg.fact[j] != hi // cfg.fact[j]:
                break
            x = cfg.digit_at(lo, j)
            n[3] = j
            n[5][x] += 1
            if n[5][x] > n[4][x]:
                if x >= n[0] or n[1] == 0:
                    return False
                n[4][x] += 1
                n[2] += cfg.w[x]
                n[1] -= 1
                forced = True
                break
        if not forced:
            return cfg.hall(n[4], n[0])


def children(cfg, n):
    x = n[0] - 1
    r = n[1]
    rng = [r] if x == 0 else range(0, r + 1)
    out = []
    for e in rng:
        t2 = n[2] + e * cfg.w[x]
        rr = r - e
        if x > 0:
            if t2 + rr * cfg.wmin[x] > cfg.wu:
                break
            if t2 + rr * cfg.wmax[x] < cfg.wl:
                continue
        ch = [x, rr, t2, n[3], list(n[4]), list(n[5])]
        ch[4][x] += e
        if settle(cfg, ch):
            out.append(ch)
    return out


def explore(L, m, depth, off=0):
    cfg = Cfg(L, m, off)
    if cfg.wl > cfg.wu:
        return cfg, []
    root = [cfg.nv, L, off, L + 1, [0] * (L + 2), [0] * (L + 2)]
    if not settle(cfg, root):
        return cfg, []
    level = [root]
    for _ in range(depth):
        nxt = []
        for nd in level:
            if nd[0] == 0:
                continue
            nxt.extend(children(cfg, nd))
        level = nxt
    return cfg, level


def main():
    m, lmin, lmax, depth = map(int, sys.argv[1:5])
    off = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    print(f"# factorial system, 0^0 = {m}, offset {off}, tree to depth {depth} (values kmax..kmax-{depth - 1} decided)")
    print("# L kmax survivors with_top (some decided value present) fixed_positions_max")
    for L in range(lmin, lmax + 1):
        cfg, lev = explore(L, m, depth, off)
        withtop = [nd for nd in lev if any(nd[4][u] for u in range(nd[0], cfg.nv))]
        fixed = max((L + 1 - nd[3] for nd in lev), default=0)
        print(f"L {L} kmax {cfg.kmax} survivors {len(lev)} with_top {len(withtop)} fixed {fixed}", flush=True)


if __name__ == '__main__':
    main()
