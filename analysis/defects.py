"""Defect spectrum: how many n have n - F(n) = D, for D = j (b-1).

A solution is the case D = 0. If solutions are coincidences, D = 0 is one
draw among many: the counts for other D in the same residue class mod
2(b-1) (j even) estimate how many solutions to expect in that very base,
with the arithmetic of the true weights x^x included. Runs `fast search
--offset D`, both conventions at once, lengths 2 and up.

Usage: defects.py first_base last_base jmax > data/defects.txt
"""
import subprocess
import sys

FAST = '../fast/target/release/fast'
b0, b1, jmax = map(int, sys.argv[1:4])
print("# base mode j count   (D = j (b-1), n - F(n) = D, n >= b)")
for b in range(b0, b1 + 1):
    for j in range(jmax + 1):
        out = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', '3', '--offset', str(j * (b - 1)), '--min-digits', '2'],
                             capture_output=True, text=True).stdout
        for line in out.splitlines():
            bb, m, n, _ = line.split(':', 3)
            print(b, m, j, n, flush=True)
