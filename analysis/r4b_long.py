"""Round 4, blocks: exact blocks inside the long solutions of bases 2 to 41.

For every solution with at least 4 digits in output/b2-41-<mode>.txt and
output/b43-<mode>.txt:

- split m (tail of m digits, m = 1, 2, 3): the split is exact when the tail
  u pays for itself, P_u(b) = F(u) with leading zeros of u weighing 0^0.
  Then the top part is an exact block at shift m;
- every contiguous substring t of length L >= 2, not the whole string and
  with t_1 >= 1, that pays for itself at its position p >= 1:
  b^p P_t(b) = F(t).

The model of chapter 5 treats the digits of a solution as random, so a tail
of m digits pays for itself with probability T_m(b) / b^m, where T_m(b) is
the number of strings u of m digits (leading zeros allowed) with
P_u(b) = F(u). The script compares the observed counts with this.

    python3 r4b_long.py > data/r4b_long.txt
"""
import itertools
import os
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..')


def load(mode):
    out = []
    for name in ('b2-41', 'b43'):
        path = os.path.join(ROOT, 'output', f'{name}-{mode}.txt')
        for line in open(path):
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            b, m, n, ns = line.split(':', 3)
            for t in (eval('(' + ns + ',)') if ns.strip() else ()):
                if len(t) >= 2:
                    out.append((int(b), tuple(t)))
    return out


def P(t, b):
    v = 0
    for d in t:
        v = v * b + d
    return v


def F(t, mode):
    return sum(mode if d == 0 else d ** d for d in t)


def tails(b, m, mode):
    """strings u of m digits (leading zeros allowed) with P_u(b) = F(u)"""
    out = []
    for u in itertools.product(range(b), repeat=m):
        if P(u, b) == F(u, mode):
            out.append(u)
    return out


def main():
    for mode in (1, 0):
        sols = [(b, s) for b, s in load(mode) if len(s) >= 4]
        print(f"# 0^0 = {mode}: {len(sols)} solutions with at least 4 digits, bases 2 to 41 and 43")
        T = {}
        for b in sorted({b for b, s in sols}):
            for m in (1, 2, 3):
                T[b, m] = tails(b, m, mode)
        print("# m | observed exact splits | model sum T_m(b)/b^m | self-paying tails of length m in the bases (first few)")
        for m in (1, 2, 3):
            obs = sum(1 for b, s in sols if s[-m:] in T[b, m])
            exp = sum(len(T[b, m]) / b ** m for b, s in sols)
            ex = sorted({(b, u) for (b, mm), us in T.items() if mm == m for u in us})
            print(f"{m} | {obs} | {exp:.2f} | " + ', '.join(f"{u}@{b}" for b, u in ex[:12]) + (' ...' if len(ex) > 12 else ''))
        # last digit 1 under 0^0 = 1, by base parity
        by = defaultdict(lambda: [0, 0.0])
        for b, s in sols:
            key = 'odd' if b % 2 else 'even'
            by[key][0] += s[-1] == 1
            by[key][1] += 1 / b
        print("# solutions ending in 1: " + ', '.join(f"{k} bases: {v[0]} against {v[1]:.2f}" for k, v in sorted(by.items())))
        # exact substrings of length >= 2 at positions >= 1
        found = []
        for b, s in sols:
            k = len(s)
            for i in range(k):
                for j in range(i + 2, k + 1):
                    t = s[i:j]
                    p = k - j
                    if t[0] == 0 or p == 0 or (i == 0 and j == k):
                        continue
                    if b ** p * P(t, b) == F(t, mode):
                        found.append((b, s, t, p))
        print(f"# exact blocks of length >= 2 at positions >= 1 inside these solutions: {len(found)}")
        for b, s, t, p in found[:60]:
            print(f"  base {b}: {t} at position {p} in {s}")
        if len(found) > 60:
            print(f"  ... {len(found) - 60} more")
        print()


if __name__ == '__main__':
    main()
