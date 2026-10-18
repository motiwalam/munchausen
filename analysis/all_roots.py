"""All integer roots of the Munchausen polynomial Q_s(r) = P_s(r) - F(s).

For the strings that pass the local test (kdigit --survivors), find every
integer root r and sort it into:
- base: r > max(s), an ordinary solution in base r;
- negabase: r < -max(s), a solution in the negative base r, where every
  integer has a unique representation with digits 0..|r|-1;
- improper: |r| <= max(s), a representation with digits too large for r.
Strings that fail the local test have no integer root at all.
"""
import subprocess
import sys
from collections import defaultdict
import numpy as np

FAST = '../fast/target/release/kdigit'


def integer_roots(s, F):
    k = len(s)
    coef = [float(c) for c in s]
    coef[-1] -= float(F)
    out = set()
    for z in np.roots(coef):
        if abs(z.imag) > 1e-6 * max(1.0, abs(z.real)):
            continue
        for r in (int(round(z.real)) + d for d in (-1, 0, 1)):
            v = 0
            for c in s:
                v = v * r + c
            if v == F:
                out.add(r)
    return out


if __name__ == '__main__':
    runs = [tuple(map(int, a.split(':'))) for a in sys.argv[1:]] or [(3, 80), (4, 44), (5, 28), (6, 20)]
    for k, M in runs:
        lines = subprocess.run([FAST, str(k), str(M), '--survivors'], capture_output=True, text=True).stdout.split('\n')
        found = defaultdict(list)
        for line in lines:
            if not line.strip():
                continue
            _, mode, ds = line.split()
            mode = int(mode)
            s = tuple(map(int, ds.split(',')))
            F = sum((mode if x == 0 else x ** x) for x in s)
            for r in integer_roots(s, F):
                kind = 'base' if r > max(s) else ('negabase' if r < -max(s) else 'improper')
                found[(kind, mode)].append((r, s))
        for kind in ('base', 'negabase', 'improper'):
            for mode in (1, 0):
                v = sorted(found[(kind, mode)])
                show = v if (kind == 'negabase' or len(v) <= 12) else v[:12] + ['...']
                print(f"k={k} M={M} 0^0={mode} {kind:8s}: {len(v)}  {show}", flush=True)
