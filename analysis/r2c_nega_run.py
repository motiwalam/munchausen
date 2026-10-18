"""Question 42: resumable census of one negative base with worlds lanes.

    python3 r2c_nega_run.py BASE WEIGHTS OUT [threads] [shards]

BASE is negative (for example -37), WEIGHTS is pow0 or pow1. The run is cut
into units, one per odd length d, and the long lengths (d >= b - 7) into
SHARDS parts with `worlds lanes --shard i/n` (default 48). Every finished
unit appends its output to OUT, between the lines "unit d i n" and
"end d i n". A rerun skips the finished units, so the census survives an
interruption. At the end the script prints the solutions and the time.
"""
import os
import subprocess
import sys

WORLDS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../fast/target/release/worlds')


def main():
    base, wt, out = int(sys.argv[1]), sys.argv[2], sys.argv[3]
    threads = sys.argv[4] if len(sys.argv) > 4 else '3'
    nsh = int(sys.argv[5]) if len(sys.argv) > 5 else 48
    b = -base
    done = set()
    if os.path.exists(out):
        for line in open(out):
            p = line.split()
            if p and p[0] == 'end':
                done.add(tuple(map(int, p[1:4])))
    env = dict(os.environ, RAYON_NUM_THREADS=threads)
    with open(out, 'a') as f:
        for d in range(3, b + 2, 2):
            n = nsh if d >= b - 7 else 1
            for i in range(n):
                if (d, i, n) in done:
                    continue
                cmd = ['nice', '-n', '10', WORLDS, 'lanes', str(base), wt, '--dmin', str(d), '--dmax', str(d)]
                if n > 1:
                    cmd += ['--shard', f'{i}/{n}']
                p = subprocess.run(cmd, capture_output=True, text=True, check=True, env=env)
                body = [ln for ln in p.stdout.splitlines() if ln.startswith(('sol ', 'len '))]
                f.write(f"unit {d} {i} {n}\n" + ''.join(ln + '\n' for ln in body) + f"end {d} {i} {n}\n")
                f.flush()
    sols, secs, nodes = [], 0.0, 0
    for line in open(out):
        p = line.split()
        if p and p[0] == 'sol':
            sols.append(line.strip())
        elif p and p[0] == 'len':
            secs += float(p[p.index('secs') + 1])
            nodes += int(p[p.index('nodes') + 1])
    for s in sorted(set(sols)):
        print(s)
    print(f"total base {base} w {wt} sols {len(set(sols))} nodes {nodes} secs {secs:.1f}")


if __name__ == '__main__':
    main()
