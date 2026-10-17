"""Measure the inexact search: node counts, growth rate, and missed solutions.

Runs `fast search` with pruning options for a range of bases and compares the
solutions with the exhaustive results in output/.
"""
import math
import re
import subprocess
import sys

from catalog import exhaustive_bases

FAST = '../fast/target/release/fast'
EXACT = exhaustive_bases()


def run(b, opts):
    p = subprocess.run([FAST, 'search', str(b)] + opts, capture_output=True, text=True)
    nodes = int(re.search(r'(\d+) nodes', p.stderr).group(1))
    sk = re.search(r'skipped subtrees ([0-9.e+-]+)', p.stderr)
    run.skipped = float(sk.group(1)) if sk else 0.0
    found = set()
    for line in p.stdout.splitlines():
        bb, m, n, ns = line.split(':', 3)
        for t in (eval('(' + ns + ',)') if ns.strip() else ()):
            if t not in ((0,), (1,)):
                found.add((int(m), tuple(t)))
    return nodes, found


def sweep(opts, bases, miss_bases):
    nodes = {b: run(b, opts)[0] for b in bases}
    xs = list(bases)
    ys = [math.log(nodes[b]) for b in xs]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs)
    missed = total = 0
    reported = 0.0
    for b in miss_bases:
        _, found = run(b, opts)
        reported += run.skipped
        want = {(m, t) for m in (0, 1) for t in EXACT[(m, b)]}
        total += len(want)
        missed += len(want - found)
    return math.exp(slope), nodes[xs[-1]], missed, total, reported


if __name__ == '__main__':
    configs = [[], ['--ratio', '1e-3'], ['--ratio', '3e-3'], ['--ratio', '1e-2'], ['--ratio', '3e-2'],
               ['--ratio', '1e-2', '--deficit', '2'], ['--ratio', '3e-3', '--deficit', '2', '--band', '2.5']]
    bases = range(int(sys.argv[1]), int(sys.argv[2]) + 1)
    miss_bases = range(10, int(sys.argv[3]) + 1)
    for opts in configs:
        g, last, missed, total, reported = sweep(opts, bases, miss_bases)
        print(f"{' '.join(opts) or 'exact':40s} growth {g:.3f}  nodes at {bases[-1]}: {last:.3g}  "
              f"missed {missed}/{total} in bases 10-{miss_bases[-1]} (model estimate {reported:.2f})", flush=True)
