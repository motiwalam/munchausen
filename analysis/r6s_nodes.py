#!/usr/bin/env python3
"""Round 6: tables of the node counts of `fast search` runs.

Usage:
  python r6s_nodes.py a.err b.err ...   per base, the node counts in the stderr
                                        of each run and their ratio to the first
  python r6s_nodes.py --rf file         Table 1.1 of the round 6 search draft:
                                        nodes by free slots from data/r6s_rf_*.txt

The files data/r6s_rf_b28_*.txt are --tree-stats tables of a test build
that keys the table by the free slots rf instead of the unknown positions.
"""
import collections
import re
import sys


def rf_table(path):
    n, s, nk = collections.Counter(), collections.Counter(), collections.defaultdict(collections.Counter)
    for line in open(path):
        if line.startswith('#'):
            continue
        d, k, rf, c, sz = map(int, line.split())
        n[rf] += c
        s[rf] += sz
        nk[rf][k] += c
    tot = sum(n.values())
    print(f'total {tot} nodes in subtrees that ran in one task')
    print('| rf | nodes | share | mean subtree | mean level |')
    for rf in sorted(n):
        if n[rf] / tot > 1e-4:
            lev = sum(k * c for k, c in nk[rf].items()) / n[rf]
            print(f'| {rf} | {n[rf]:,} | {n[rf] / tot:.3f} | {s[rf] / n[rf]:.2f} | {lev:.1f} |')


def node_table(paths):
    tabs = []
    for f in paths:
        t = {}
        for line in open(f):
            m = re.match(r'\s*base (\d+): (\d+) nodes, (\d+) interval', line)
            if m:
                t[int(m[1])] = int(m[2])
        tabs.append(t)
    print('base ' + ' '.join(paths))
    for b in sorted(set().union(*tabs)):
        row = [t.get(b) for t in tabs]
        r0 = row[0]
        print(b, ' '.join(f'{v} ({v / r0:.3f})' if v and r0 else str(v) for v in row))


if __name__ == '__main__':
    if sys.argv[1] == '--rf':
        rf_table(sys.argv[2])
    else:
        node_table(sys.argv[1:])
