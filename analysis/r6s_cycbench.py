#!/usr/bin/env python3
"""Round 6: compare builds of `fast` in user-mode cycles on one core.

Usage:
  python r6s_cycbench.py <reps> <core> "<args>" build1 build2 ...

Runs the builds alternately, pinned to one core with taskset, under
r6s_cyc (build it with `gcc -O2 -o r6s_cyc r6s_cyc.c` in this directory).
Prints cycles, instructions and branch misses of each run, then the
medians and the ratio of each build's cycles to the first build's. Cycle
counts of the process itself depend little on other jobs on the machine,
which wall times do not.
"""
import os
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    reps, core = int(sys.argv[1]), sys.argv[2]
    args = sys.argv[3].split()
    builds = sys.argv[4:]
    res = {b: [] for b in builds}
    print('load', os.getloadavg(), flush=True)
    for _ in range(reps):
        for b in builds:
            p = subprocess.run(['taskset', '-c', core, os.path.join(HERE, 'r6s_cyc'), b] + args,
                               stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
            lines = p.stderr.splitlines()
            c = [x for x in lines if x.startswith('cycles')][-1].split()
            nodes = [x for x in lines if 'nodes' in x]
            res[b].append((float(c[1]), float(c[4]), float(c[7])))
            print(b, ' '.join(c), nodes[-1].strip() if nodes else '', flush=True)
    first = None
    for b in builds:
        c, i, m = (statistics.median(x[j] for x in res[b]) for j in range(3))
        first = first or c
        print(f'{b}: median cycles {c:.4f} G ({c / first:.3f}), instructions {i:.4f} G, branch misses {m:.4f} G')


if __name__ == '__main__':
    main()
