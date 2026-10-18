"""Defect spectrum with offsets D = j * 2b(b-1), which also match D = 0 mod b.

Usage: defects_modb.py first_base last_base jmax > data/defects_modb.txt
"""
import subprocess
import sys

FAST = '../fast/target/release/fast'
b0, b1, jmax = map(int, sys.argv[1:4])
print("# base mode j count   (D = j * 2b(b-1))")
for b in range(b0, b1 + 1):
    for j in range(jmax + 1):
        out = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', '2', '--offset', str(j * 2 * b * (b - 1)),
                              '--min-digits', '2'], capture_output=True, text=True).stdout
        for line in out.splitlines():
            bb, m, n, _ = line.split(':', 3)
            print(b, m, 2 * j, n, flush=True)
