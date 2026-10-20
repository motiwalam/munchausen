#!/usr/bin/env python3
"""Round 6, search 2: the cycle tables of the draft.

Usage: python r6s2_tables.py [data/r6s2_cycles.json]

The data come from r6s2_bench.py: user-mode cycles of `fast search b -j 1`
pinned to one P-core, medians of 3 alternating runs of each build and
flag set. `base` is the engine with the residue rule only (commit 9756e6b),
`off` the new engine with both last-digit tests off, `L3P1` the test with
one free slot on three digits and the test with two free slots on one
digit, `L2P2` and `L3P2` the same with two and three digits and pairs on
two digits (`L3P2` is the default).
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def nodes(x):
    return int(re.search(r'(\d+) nodes', x['nodes']).group(1))


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'data', 'r6s2_cycles.json')
    data = json.load(open(path))
    for mode, title in (('both', 'both conventions'), ('m0', '-m 0'), ('m1', '-m 1')):
        print(f'\n{title}: cycles (G), ratio of cycles and of nodes to base')
        print('| b | base | off | L3P1 | L2P2 | L3P2 | nodes, L3P2 |')
        print('|---:|---:|---:|---:|---:|---:|---:|')
        for b in sorted(data[mode], key=int):
            d = data[mode][b]
            c0, n0 = d['base']['cycles'], nodes(d['base'])
            cells = [f"{c0:.3f} G"]
            for label in ('off', 'L3P1', 'L2P2', 'L3P2'):
                cells.append(f"{d[label]['cycles'] / c0:.3f}")
            cells.append(f"{nodes(d['L3P2']) / n0:.3f}")
            print(f'| {b} | ' + ' | '.join(cells) + ' |')
        print('instructions, ratio of L3P2 to base:', ' '.join(f"{b}: {data[mode][b]['L3P2']['instr'] / data[mode][b]['base']['instr']:.3f}" for b in sorted(data[mode], key=int)))
        print('largest spread of a median (max - min) / median:', f"{max((max(r[0] for r in x['runs']) - min(r[0] for r in x['runs'])) / x['cycles'] for d in data[mode].values() for x in d.values()):.3f}")


if __name__ == '__main__':
    main()
