#!/usr/bin/env python3
"""Round 6, search 2: the exact tests on nodes with two free slots.

Usage: python r6s2_pair.py [data/r6s2_pair_b20_30.txt]

Reads the stderr of an instrumented build of `fast search b -j 4` (the
patch r6s2_pair_probe.py) with PAIR_TEST = 0 to 5, and prints, per base,
the share of the nodes with two free slots (after their forced digits)
that fail each test, and the nodes of the whole search with that test, as
a share of the nodes without it. The tests ask for a pair y1 <= y2 < k
such that, under a reported convention:

  1: the residue mod b - 1 holds and S = t + w(y1) + w(y2) is in the
     clipped interval of the node;
  2: 1, and the digit of S at the first unknown position is a digit the
     unknown positions can hold (a decided digit with copies outside the
     prefix, y1 or y2);
  3: 1, and the last digit of S is such a digit;
  4: 1, 2 and 3;
  5: S is a solution (its digits are the multiset).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'data', 'r6s2_pair_b20_30.txt')
    rows = {}
    b = v = None
    for line in open(path):
        m = re.match(r'== base (\d+) v (\d+)', line)
        if m:
            b, v = int(m.group(1)), int(m.group(2))
            continue
        m = re.search(r'base \d+: (\d+) nodes', line)
        if m:
            rows.setdefault(b, {})[v] = {'nodes': int(m.group(1))}
            continue
        m = re.search(r'pair: tested (\d+) failed (\d+)', line)
        if m:
            rows[b][v].update(tested=int(m.group(1)), failed=int(m.group(2)))
    print('| b | nodes | two-slot nodes | fail 1 | fail 2 | fail 3 | fail 4 | nodes 1 | nodes 2 | nodes 3 | nodes 4 | nodes 5 |')
    print('|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for b in sorted(rows):
        r = rows[b]
        n0 = r[0]['nodes']
        fails = [r[v]['failed'] / r[v]['tested'] for v in (1, 2, 3, 4)]
        ratios = [r[v]['nodes'] / n0 for v in (1, 2, 3, 4, 5)]
        print(f"| {b} | {n0:,} | {r[1]['tested']:,} | " + ' | '.join(f'{x:.3f}' for x in fails) + ' | ' + ' | '.join(f'{x:.3f}' for x in ratios) + ' |')


if __name__ == '__main__':
    main()
