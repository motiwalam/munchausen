"""Defect spectrum restricted to long numbers (at least b-6 digits).

Offsets D shift n by at most about 10^6, which is negligible against
b^(b-7), so every offset sees the same set of lengths. (Short numbers need
n > D, which biases large offsets against them.) Two families of offsets:
- 'b1': D = j (b-1), j = 0..jmax (j even matches D = 0 mod 2(b-1));
- 'bb': D = 2 j b (b-1), j = 0..jmax/2, which also matches D = 0 mod b.

Usage: defects_bulk.py b1|bb first_base last_base jmax
"""
import subprocess
import sys

FAST = '../fast/target/release/fast'
kind, b0, b1, jmax = sys.argv[1], *map(int, sys.argv[2:5])
print(f"# base mode j count   kind {kind}, lengths >= b-6")
for b in range(b0, b1 + 1):
    js = range(jmax + 1) if kind == 'b1' else range(0, jmax + 1, 2)
    for j in js:
        D = j * (b - 1) if kind == 'b1' else j * b * (b - 1)
        out = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', '4', '--offset', str(D),
                              '--min-digits', str(b - 6)], capture_output=True, text=True).stdout
        for line in out.splitlines():
            bb, m, n, _ = line.split(':', 3)
            print(b, m, j, n, flush=True)
