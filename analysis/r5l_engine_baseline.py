"""Question 77: the engine's cost for d = b-1 on one thread, as a baseline.

Usage: python r5l_engine_baseline.py B0 B1 [--reps R]
Prints b, d, nodes, interval evaluations, and the median CPU seconds of R runs
of `fast search b --min-digits b-1 --max-digits b-1 -j 1`.
"""
import os
import re
import resource
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FAST = os.path.join(HERE, '..', 'fast', 'target', 'release', 'fast')


def run(b, d):
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run([FAST, 'search', str(b), '--min-digits', str(d), '--max-digits', str(d), '-j', '1'],
                       capture_output=True, text=True, check=True)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    m = re.search(r'(\d+) nodes, (\d+) interval evaluations', p.stderr)
    return int(m.group(1)), int(m.group(2)), r1.ru_utime - r0.ru_utime + r1.ru_stime - r0.ru_stime


def main():
    b0, b1 = int(sys.argv[1]), int(sys.argv[2])
    reps = int(sys.argv[sys.argv.index('--reps') + 1]) if '--reps' in sys.argv else 5
    print('# b d nodes evals cpu_s(median)')
    for b in range(b0, b1 + 1):
        d = b - 1
        runs = [run(b, d) for _ in range(reps)]
        print(f'{b} {d} {runs[0][0]} {runs[0][1]} {statistics.median(r[2] for r in runs):.4f}', flush=True)


if __name__ == '__main__':
    main()
