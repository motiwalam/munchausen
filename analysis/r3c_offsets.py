"""Question 49: the defect spectrum of short strings.

For each offset D, runs `kdigit k M --offset D` and prints every pair (s, b)
with b > max(s) and P_s(b) - F(s) = D, one per line:

    D mode base digits

    python3 r3c_offsets.py k M D-list [threads] > data/r3c_offsets_k<k>_<name>.txt

D-list is a comma-separated list of offsets, with ranges a:b or a:b:c.
"""
import os
import subprocess
import sys

from r3c_root_spectrum import parse

KDIGIT = os.path.join(os.path.dirname(__file__), '..', 'fast', 'target', 'release', 'kdigit')


def main():
    k, M = int(sys.argv[1]), int(sys.argv[2])
    Ds = parse(sys.argv[3])
    threads = sys.argv[4] if len(sys.argv) > 4 else '4'
    print(f"# kdigit {k} {M} --offset D for D in {sys.argv[3]}; columns: D mode base digits", flush=True)
    for D in Ds:
        p = subprocess.run([KDIGIT, str(k), str(M), '--offset', str(D)], capture_output=True, text=True,
                           env=dict(os.environ, RAYON_NUM_THREADS=threads), check=True)
        print(p.stderr.strip())
        for line in p.stdout.splitlines():
            kk, mode, b, ds = line.split()
            print(f"{D} {mode} {b} {ds}")
        sys.stdout.flush()


if __name__ == '__main__':
    main()
