"""Near-solutions for other weights: N_D(b) = #{n : n = F(n) + D}.

Section 11.1 uses the offsets D = j (b-1) as fresh draws of the same
coincidence. Here the same test runs for any weight family. For each base
and j = 1..J the script counts the solutions with d >= ref-5 digits.

    python3 wgt_offsets.py b0 b1 J [engine flags] > data/wgt_offsets_<name>.txt

Lines: off b j mode count
"""
import math
import sys
from wgt_model import run_fast

b0, b1, J = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
flags = sys.argv[4:]


def ref_len(b):
    if '--factorial' in flags:
        n, k = math.factorial(b - 1), 0
        while n:
            n //= b
            k += 1
        return k
    if '--shift' in flags:
        return b + int(flags[flags.index('--shift') + 1])
    return b


print(f"# flags {' '.join(flags) or '(none)'}, bases {b0}-{b1}, offsets j (b-1) for j = 1..{J}, bulk d >= ref-5")
for b in range(b0, b1 + 1):
    r = ref_len(b)
    for j in range(1, J + 1):
        res, _ = run_fast(b, b, flags + ['--offset', str(j * (b - 1)), '--min-digits', str(max(2, r - 5))])
        for mode in (0, 1):
            print(f"off {b} {j} {mode} {len(res[b, mode])}", flush=True)
