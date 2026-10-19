"""Wall times of fast search configurations, in alternating rounds.

    python3 r5p_timing.py <rounds> <base> '<opts>' ['<opts>' ...] >> data/r5p_timing.txt

Each round runs every configuration once, in the given order, so slow
phases of the shared machine hit all of them. Prints one line per run:
base, options, wall seconds, CPU seconds (user + system), nodes, 1-minute
load average before the run, and a checksum of the solutions; then the
medians per configuration. Under load from other jobs the CPU seconds are
the steadier measure for CPU-only runs.
"""
import hashlib
import os
import re
import resource
import statistics
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
FAST = os.environ.get('FAST', os.path.join(HERE, '..', 'fast', 'target-gpu', 'release', 'fast'))


def cpu():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


def run(b, opts):
    load = os.getloadavg()[0]
    t, c = time.time(), cpu()
    p = subprocess.run([FAST, 'search', str(b)] + opts.split(), capture_output=True, text=True)
    dt, dc = time.time() - t, cpu() - c
    nodes = int(re.search(r'base \d+: (\d+) nodes', p.stderr).group(1))
    return dt, dc, nodes, load, hashlib.md5(p.stdout.encode()).hexdigest()[:8]


def main():
    rounds, b = int(sys.argv[1]), int(sys.argv[2])
    cfgs = sys.argv[3:]
    times = {c: [] for c in cfgs}
    for r in range(rounds):
        for c in cfgs:
            dt, dc, nodes, load, md5 = run(b, c)
            times[c].append((dt, dc))
            print(f"run base {b} [{c}] {dt:.2f} s wall, {dc:.2f} s CPU, {nodes} nodes, load {load:.1f}, output {md5}", flush=True)
    for c in cfgs:
        print(f"median base {b} [{c}] {statistics.median(t for t, _ in times[c]):.2f} s wall, "
              f"{statistics.median(u for _, u in times[c]):.2f} s CPU over {rounds} runs", flush=True)


if __name__ == '__main__':
    main()
