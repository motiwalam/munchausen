#!/usr/bin/env python3
"""Round 6, search 2: alternating user-mode cycle counts of several runs.

Usage: python r6s2_bench.py <reps> <core> <config.json> [out.json]

Like r6s_cycbench.py, but each run is a (label, binary, args) triple, so
one build can run with several flag sets.
config: list of [label, binary, "args"]. Each run is pinned to <core> with
taskset and counted with r6s_cyc. Prints medians and the ratio to the first.
"""
import json
import os
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    reps, core = int(sys.argv[1]), sys.argv[2]
    cfg = json.load(open(sys.argv[3]))
    out = sys.argv[4] if len(sys.argv) > 4 else None
    res = {c[0]: [] for c in cfg}
    nodes = {}
    print('load', os.getloadavg(), flush=True)
    for _ in range(reps):
        for label, binary, args in cfg:
            p = subprocess.run(['taskset', '-c', core, os.path.join(HERE, 'r6s_cyc'), binary] + args.split(),
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            lines = p.stderr.splitlines()
            c = [x for x in lines if x.startswith('cycles')][-1].split()
            nl = [x for x in lines if 'nodes' in x]
            res[label].append((float(c[1]), float(c[4]), float(c[7])))
            nodes[label] = (nl[-1].strip() if nl else '', hash(p.stdout))
            print(label, ' '.join(c), nodes[label][0], flush=True)
    first = None
    summary = {}
    for label, _, _ in cfg:
        c, i, m = (statistics.median(x[j] for x in res[label]) for j in range(3))
        first = first or c
        summary[label] = dict(cycles=c, instr=i, bmiss=m, runs=res[label], nodes=nodes[label][0])
        print(f'{label}: median cycles {c:.4f} G ({c / first:.3f}), instructions {i:.4f} G, branch misses {m:.4f} G, {nodes[label][0]}')
    outs = {nodes[l][1] for l in nodes}
    print('outputs identical' if len(outs) == 1 else 'OUTPUTS DIFFER', flush=True)
    print('load', os.getloadavg(), flush=True)
    if out:
        json.dump(summary, open(out, 'w'), indent=1)


if __name__ == '__main__':
    main()
