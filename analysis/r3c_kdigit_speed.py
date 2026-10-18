"""Question 47: wall-clock time of the old and the new kdigit.

    python3 r3c_kdigit_speed.py OLD NEW THREADS reps "k M" ... > data/r3c_kdigit_speed.txt

OLD is kdigit built from commit 4e0da21 (18 primes, eager masks), NEW a
copy of the current fast/target/release/kdigit. The runs alternate between the
two binaries, and the script prints the best wall and user time of each and
checks that the outputs are equal.
"""
import os
import re
import resource
import subprocess
import sys
import time


def run(binary, k, M, threads):
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.time()
    p = subprocess.run([binary, str(k), str(M)], capture_output=True, text=True,
                       env=dict(os.environ, RAYON_NUM_THREADS=str(threads)), check=True)
    wall = time.time() - t0
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    surv = int(re.search(r'(\d+) passed', p.stderr).group(1))
    return wall, r1.ru_utime - r0.ru_utime, surv, p.stdout


def main():
    old, new, threads, reps = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    print(f"# {threads} threads, best of {reps} alternating runs; load average at start {os.getloadavg()[0]:.1f}")
    print("# k M | survivors old | new | wall old s | new s | speedup | user old s | new s | speedup | outputs equal")
    for kM in sys.argv[5:]:
        k, M = map(int, kM.split())
        best = {}
        for _ in range(reps):
            for name, b in (('old', old), ('new', new)):
                w, u, s, out = run(b, k, M, threads)
                pw, pu = best.get(name, (1e9, 1e9, 0, ''))[:2]
                best[name] = (min(pw, w), min(pu, u), s, out)
        o, n = best['old'], best['new']
        print(f"{k} {M} | {o[2]} | {n[2]} | {o[0]:.2f} | {n[0]:.2f} | {o[0] / n[0]:.2f} | "
              f"{o[1]:.2f} | {n[1]:.2f} | {o[1] / n[1]:.2f} | {o[3] == n[3]}", flush=True)
    print(f"# load average at end {os.getloadavg()[0]:.1f}")


if __name__ == '__main__':
    main()
