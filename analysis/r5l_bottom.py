"""Question 79: bottom-up information in bases b = 2^k.

Usage: python r5l_bottom.py table
       python r5l_bottom.py trees B [--probes N] [--seed S] [--exact]

table: for b = 32, 64, 128 and each number L of bottom digits, the even
values x whose weight x^x is not 0 mod b^L (x v2(x) < k L). The bottom L
digits of S(c) depend only on the counts of the odd values, of 0 and of
these even values.

trees: node counts (exact, or Knuth's random-probe estimate) of toy count
trees for d = b-1 under 0^0 = 1. Each tree reveals one count per level in a
fixed order. A node is tested by
  - the interval test of r5l_cert.py for any revealed set (the leading
    digits of the interval must fit the revealed counts and the free slots);
  - with bottom checks on: once every value outside V0_L (the even values
    with x v2(x) >= k L) is revealed, the bottom L digits of S are known
    exactly; the leading and the bottom digits together must fit.
Orders:
  plain      top-down, no bottom check
  plain+bot  top-down, with bottom checks
  odd-first  odd values top-down, then 0, then the even values in the order
             in which they unlock bottom digits, with bottom checks
  hybrid     top-down down to value b/2, then the odd values below b/2,
             0 and the unlocking evens, then the rest; with bottom checks
"""
import argparse
import math
import random
import sys


def v2(x):
    n = 0
    while x % 2 == 0:
        x //= 2
        n += 1
    return n


def table():
    print('| b | L | even values with x^x != 0 mod b^L | values that fix the bottom L digits | share of all values |')
    print('|---:|---:|---|---:|---:|')
    for k in (5, 6, 7):
        b = 2 ** k
        for L in range(1, 9):
            E = [x for x in range(2, b, 2) if x * v2(x) < k * L]
            n = b // 2 + 1 + len(E)
            es = ','.join(map(str, E)) if len(E) <= 12 else ','.join(map(str, E[:10])) + f',... ({len(E)} values)'
            print(f'| {b} | {L} | {es} | {n} | {n / b:.2f} |')
            if n >= b:
                break


class Toy:
    def __init__(self, b, d, mode=1, bottom=True):
        self.b, self.d = b, d
        self.k = b.bit_length() - 1
        assert 2 ** self.k == b
        self.W = [mode] + [v ** v for v in range(1, b)]
        self.B0, self.B1 = b ** (d - 1), b ** d - 1
        self.vals = [v for v in range(b) if self.W[v] <= self.B1]
        self.pw = [b ** i for i in range(d + 1)]
        self.bottom = bottom
        # needL[L] = the values that must be revealed to know the bottom L digits
        self.need = {}
        for L in range(1, d + 1):
            self.need[L] = {v for v in self.vals if not (v > 0 and v % 2 == 0 and v * v2(v) >= self.k * L)}

    def ok(self, cr, rf):
        """cr: dict of revealed counts. True if the node survives."""
        b, d, W = self.b, self.d, self.W
        if rf < 0:
            return False
        U = [v for v in self.vals if v not in cr]
        t = sum(W[v] * e for v, e in cr.items())
        if rf == 0 or len(U) <= 1:
            c = dict(cr)
            if rf > 0:
                if not U:
                    return False
                c[U[0]] = rf
            S = t + (rf * W[U[0]] if rf > 0 else 0)
            if not (self.B0 <= S <= self.B1):
                return False
            h = {}
            for i in range(d):
                x = S // self.pw[i] % b
                h[x] = h.get(x, 0) + 1
            return all(h.get(v, 0) == c.get(v, 0) for v in set(h) | set(c))
        lo = max(t + rf * min(W[v] for v in U), self.B0)
        hi = min(t + rf * max(W[v] for v in U), self.B1)
        if lo > hi:
            return False
        known = {}
        for i in range(d - 1, -1, -1):
            a = lo // self.pw[i] % b
            if a != hi // self.pw[i] % b:
                break
            known[i] = a
        if self.bottom:
            rv = set(cr)
            L = 0
            while L < d and self.need[L + 1] <= rv:
                L += 1
            if L:
                low = t % self.pw[L]
                for i in range(L):
                    x = low // self.pw[i] % b
                    if i in known and known[i] != x:
                        return False
                    known[i] = x
        h = {}
        for x in known.values():
            h[x] = h.get(x, 0) + 1
        out = 0
        for x, e in h.items():
            if x in cr:
                if e > cr[x]:
                    return False
            else:
                out += e
        return out <= rf


def make_order(toy, name):
    b, vals = toy.b, toy.vals
    top = sorted(vals, reverse=True)
    if name in ('plain', 'plain+bot'):
        return top
    unlock = sorted([v for v in vals if v > 0 and v % 2 == 0], key=lambda v: (v * v2(v), -v))
    if name == 'odd-first':
        return [v for v in top if v % 2] + ([0] if 0 in vals else []) + unlock
    if name == 'hybrid':
        upper = [v for v in top if v >= b // 2]
        lower_odd = [v for v in top if v < b // 2 and v % 2]
        rest = [v for v in unlock if v < b // 2]
        return upper + lower_odd + ([0] if 0 in vals else []) + rest
    raise ValueError(name)


def children(toy, order, i, cr, rf):
    v = order[i]
    out = []
    for e in range(rf + 1):
        c2 = dict(cr)
        c2[v] = e
        if toy.ok(c2, rf - e):
            out.append((c2, rf - e))
    return out


def exact_count(toy, order):
    n = 0
    stack = [(0, {}, toy.d)]
    while stack:
        i, cr, rf = stack.pop()
        n += 1
        if i == len(order):
            continue
        for c2, r2 in children(toy, order, i, cr, rf):
            if i + 1 < len(order):
                stack.append((i + 1, c2, r2))
            else:
                n += 1
    return n


def knuth(toy, order, probes, rnd):
    ests = []
    for _ in range(probes):
        est, w = 1.0, 1.0
        i, cr, rf = 0, {}, toy.d
        while i < len(order):
            ch = children(toy, order, i, cr, rf)
            if not ch:
                break
            w *= len(ch)
            est += w
            cr, rf = rnd.choice(ch)
            i += 1
        ests.append(est)
    m = sum(ests) / len(ests)
    sd = math.sqrt(sum((x - m) ** 2 for x in ests) / (len(ests) - 1)) / math.sqrt(len(ests))
    return m, sd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('what')
    ap.add_argument('b', type=int, nargs='?')
    ap.add_argument('--probes', type=int, default=2000)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--exact', action='store_true')
    ap.add_argument('--orders', default='plain,plain+bot,hybrid,odd-first')
    a = ap.parse_args()
    if a.what == 'table':
        table()
        return
    b, d = a.b, a.b - 1
    print(f'# base {b}, d = {d}, 0^0 = 1, ' + ('exact counts' if a.exact else f'Knuth estimates, {a.probes} probes, seed {a.seed}'))
    for name in a.orders.split(','):
        toy = Toy(b, d, bottom=(name != 'plain'))
        order = make_order(toy, name)
        if a.exact:
            print(f'{name}: {exact_count(toy, order)} nodes', flush=True)
        else:
            m, sd = knuth(toy, order, a.probes, random.Random(a.seed))
            print(f'{name}: {m:.4g} +/- {sd:.2g} nodes', flush=True)


if __name__ == '__main__':
    main()
