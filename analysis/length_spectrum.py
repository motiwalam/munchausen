"""Question 21: the law of J = b - k from near-solutions.

For offsets D = j (b-1), j even, record the length of every n with
n - F(n) = D and at least b - 12 digits, and compare the shares of J with the
sampled model of analysis/length_law.py.
"""
import subprocess
import sys
from collections import Counter
from length_window import short_e

FAST = '../fast/target/release/fast'
jmax = int(sys.argv[1])
for b in map(int, sys.argv[2:]):
    for mode in (1, 0):
        js = Counter()
        offs = 0
        for j in range(2, jmax + 1, 2):
            out = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', '3', '-m', str(mode),
                                  '--offset', str(j * (b - 1)), '--min-digits', str(b - 12)],
                                 capture_output=True, text=True).stdout
            offs += 1
            for line in out.splitlines():
                ns = line.split(':', 3)[3]
                for t in (eval('(' + ns + ',)') if ns.strip() else ()):
                    js[b - len(t)] += 1
        n = sum(js.values())
        model = {J: short_e(b, b - J, mode, samples=40000) * offs for J in range(0, 13)}
        print(f"base {b}, 0^0={mode}, {offs} offsets, {n} near-solutions")
        print("   J:        " + " ".join(f"{J:6d}" for J in range(13)))
        print("   observed: " + " ".join(f"{js.get(J, 0):6d}" for J in range(13)))
        print("   model:    " + " ".join(f"{model[J]:6.1f}" for J in range(13)), flush=True)
