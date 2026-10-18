"""Near-solutions with exactly b digits (question 17).

For offsets D = j (b-1), j even (same residue class as D = 0 mod 2(b-1)),
count the b-digit n with n - F(n) = D under each convention. Their mean per
offset estimates the expected number of b-digit solutions in that base with
the true weights.

Usage: bdigit_spectrum.py first_base last_base jmax > data/bdigit_spectrum.txt
"""
import subprocess
import sys

FAST = '../fast/target/release/fast'
b0, b1, jmax = map(int, sys.argv[1:4])
print("# base mode j count   (b-digit n with n - F(n) = j (b-1))")
for b in range(b0, b1 + 1):
    for j in range(0, jmax + 1, 2):
        out = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', '2', '--offset', str(j * (b - 1)),
                              '--min-digits', str(b), '--max-digits', str(b)], capture_output=True, text=True).stdout
        for line in out.splitlines():
            bb, m, n, _ = line.split(':', 3)
            print(b, m, j, n, flush=True)
