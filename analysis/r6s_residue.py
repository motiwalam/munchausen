"""Round 6: how much of the residue space a few free digits reach.

Usage:
  python r6s_residue.py [B ...]

A node of the exact search with f free slots, all holding digits below k,
can still satisfy n == F(n) modulo q = b - 1 only if its residue R has
-R in A_f, the set of sums of f values r_m(y) = w(y) - y mod q over the
digits y < k (Proposition 1.5). Under both conventions at once the node
survives if one of them does. This script prints, for k = round(0.57 b),
the level where the tree is widest, the share of residues that pass for
f = 1, 2, 3: under 0^0 = 0, under 0^0 = 1, and under either, for a node
whose two residues differ by z0 = 1 (one known zero).
"""
import sys


def reach(q, k, m, f):
    r = [((pow(y, y, q) - y) % q) if y > 0 else (m % q) for y in range(k)]
    s = {0}
    for _ in range(f):
        s = {(a + x) % q for a in s for x in r}
    return s


def main():
    bases = [int(a) for a in sys.argv[1:]] or list(range(20, 41)) + [50, 64, 100, 127]
    print('| b | q = b-1 | k | f=1: m=0, m=1, either | f=2: m=0, m=1, either | f=3: either |')
    print('|---:|---:|---:|---|---|---:|')
    for b in bases:
        q, k = b - 1, round(0.57 * b)
        row = []
        for f in (1, 2, 3):
            a0, a1 = reach(q, k, 0, f), reach(q, k, 1, f)
            # R0 passes if -R0 in a0; R1 = R0 + 1 passes if -R0 - 1 in a1
            either = sum(1 for r in range(q) if (-r) % q in a0 or (-r - 1) % q in a1) / q
            row.append((len(a0) / q, len(a1) / q, either))
        print(f'| {b} | {q} | {k} | {row[0][0]:.2f}, {row[0][1]:.2f}, {row[0][2]:.2f} | '
              f'{row[1][0]:.2f}, {row[1][1]:.2f}, {row[1][2]:.2f} | {row[2][2]:.2f} |')


if __name__ == '__main__':
    main()
