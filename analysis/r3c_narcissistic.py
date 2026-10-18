"""Question 58: narcissistic numbers against the refined model.

A d-digit narcissistic number in base b equals the sum of its digits, each
raised to the power d. The weights x^d change with d, and so do their
residues modulo b-1, which set the factor of the refined model.

    python3 r3c_narcissistic.py search b0 b1 [maxd]  > data/r3c_narcissistic_search.txt
        exact counts per base and length, with `fast search --power d`
    python3 r3c_narcissistic.py brute b0 b1          (small bases only)
        the same counts by brute force over digit multisets, as a check
    python3 r3c_narcissistic.py model b0 b1 [samples] > data/r3c_narcissistic_model.txt
        the basic and refined model per base and length
    python3 r3c_narcissistic.py compare SEARCH MODEL
        the tables of the draft

Search lines: nar b d count digits...; model lines: mod b d basic refined se
factor, where factor = refined / basic.
"""
import math
import os
import subprocess
import sys
from itertools import combinations_with_replacement

import numpy as np

from wgt_model import expected

FAST = os.path.join(os.path.dirname(__file__), '..', 'fast', 'target', 'release', 'fast')


def max_len(b):
    """largest d with d (b-1)^d >= b^(d-1)"""
    d = 1
    while (d + 1) * (b - 1) ** (d + 1) >= b ** d:
        d += 1
    return d


def search(b, d, threads='3'):
    p = subprocess.run([FAST, 'search', str(b), '--power', str(d), '--zero', '0', '--min-digits', str(d),
                        '--max-digits', str(d), '-m', '1', '-j', threads], capture_output=True, text=True, check=True)
    out = []
    for line in p.stdout.splitlines():
        bb, mode, _, sols = line.split(':', 3)
        for s in sols.replace('(', ' ').replace(')', ' ').split():
            digits = tuple(int(x) for x in s.split(',') if x != '')
            if len(digits) == d:
                out.append(digits)
    return sorted(set(out))


def brute(b, d):
    out = []
    pw = [x ** d for x in range(b)]
    lo, hi = b ** (d - 1), b ** d
    for ms in combinations_with_replacement(range(b), d):
        n = sum(pw[x] for x in ms)
        if lo <= n < hi:
            ds = []
            m = n
            while m:
                ds.append(m % b)
                m //= b
            if sorted(ds) == list(ms):
                out.append(tuple(reversed(ds)))
    return sorted(out)


def residue_factor(b, d):
    """the exact factor of the digit-sum identity when the residues of
    x^d - x mod b-1 are all 0 (then every multiset passes)"""
    m = b - 1
    return all((x ** d - x) % m == 0 for x in range(b))


def main():
    cmd = sys.argv[1]
    if cmd in ('search', 'brute'):
        b0, b1 = int(sys.argv[2]), int(sys.argv[3])
        maxd = int(sys.argv[4]) if len(sys.argv) > 4 else 10 ** 9
        print(f"# narcissistic numbers with at least 2 digits, bases {b0}-{b1}, by {cmd}; lines: nar b d count digits")
        for b in range(b0, b1 + 1):
            for d in range(2, min(max_len(b), maxd) + 1):
                sols = search(b, d) if cmd == 'search' else brute(b, d)
                print(f"nar {b} {d} {len(sols)} " + ' '.join(','.join(map(str, s)) for s in sols), flush=True)
    elif cmd == 'model':
        b0, b1 = int(sys.argv[2]), int(sys.argv[3])
        samples = int(sys.argv[4]) if len(sys.argv) > 4 else 400_000
        print(f"# refined model for narcissistic numbers, {samples} samples per length; lines: mod b d basic refined se factor all_residues_zero")
        for b in range(b0, b1 + 1):
            for d in range(2, max_len(b) + 1):
                w = [0] + [x ** d for x in range(1, b)]
                basic, ref, se = expected(b, d, w, 0, samples=samples, rng=np.random.default_rng(1000 * b + d))
                fac = ref / basic if basic > 0 else float('nan')
                print(f"mod {b} {d} {basic:.5f} {ref:.5f} {se:.5f} {fac:.3f} {int(residue_factor(b, d))}", flush=True)
    elif cmd == 'compare':
        compare(sys.argv[2], sys.argv[3])


def compare(fs, fm):
    obs = {}
    for line in open(fs):
        if line.startswith('nar'):
            p = line.split()
            obs[int(p[1]), int(p[2])] = int(p[3])
    mod = {}
    for line in open(fm):
        if line.startswith('mod'):
            p = line.split()
            mod[int(p[1]), int(p[2])] = (float(p[3]), float(p[4]), float(p[5]), int(p[7]))
    bases = sorted({b for b, _ in obs})
    print("| base | lengths | observed | basic model | refined model | chi2 refined |")
    print("|---:|---:|---:|---:|---:|---:|")
    tot = [0, 0.0, 0.0]
    for b in bases:
        ds = [d for (bb, d) in obs if bb == b and (bb, d) in mod]
        if not ds:
            continue
        o = sum(obs[b, d] for d in ds)
        e0 = sum(mod[b, d][0] for d in ds)
        e1 = sum(mod[b, d][1] for d in ds)
        chi = sum((obs[b, d] - mod[b, d][1]) ** 2 / mod[b, d][1] for d in ds if mod[b, d][1] > 0)
        tot[0] += o
        tot[1] += e0
        tot[2] += e1
        print(f"| {b} | {min(ds)}-{max(ds)} | {o} | {e0:.2f} | {e1:.2f} | {chi:.1f} on {len(ds)} |")
    print(f"| all | | {tot[0]} | {tot[1]:.2f} | {tot[2]:.2f} | |")
    # by the residue class of the factor
    print()
    print("| class of (b, d) | cells | observed | basic | refined |")
    print("|---|---:|---:|---:|---:|")
    groups = {}
    for (b, d), o in obs.items():
        if (b, d) not in mod:
            continue
        basic, ref, se, allzero = mod[b, d]
        f = ref / basic if basic > 0 else 0
        key = 'x^d == x mod b-1 for all x' if allzero else ('factor >= 1.5' if f >= 1.5 else ('factor <= 0.67' if f <= 0.67 else 'factor 0.67-1.5'))
        g = groups.setdefault(key, [0, 0, 0.0, 0.0])
        g[0] += 1
        g[1] += o
        g[2] += basic
        g[3] += ref
    for key, g in sorted(groups.items()):
        print(f"| {key} | {g[0]} | {g[1]} | {g[2]:.2f} | {g[3]:.2f} |")
    # short and long lengths, base parity, and the dispersion of the long cells
    print()
    print("| cells | count | observed | basic | refined | sum (N - E)^2 / E, cells with E >= 0.05 |")
    print("|---|---:|---:|---:|---:|---:|")
    sel = {
        'd <= 5': lambda b, d: d <= 5,
        'd >= 6': lambda b, d: d >= 6,
        'd >= 6, odd b': lambda b, d: d >= 6 and b % 2 == 1,
        'd >= 6, even b': lambda b, d: d >= 6 and b % 2 == 0,
        'd >= 6, x^d == x mod b-1 for all x': lambda b, d: d >= 6 and mod[b, d][3],
        'd >= 6, other cells': lambda b, d: d >= 6 and not mod[b, d][3],
    }
    for name, f in sel.items():
        cells = [(b, d) for (b, d) in obs if (b, d) in mod and f(b, d)]
        o = sum(obs[c] for c in cells)
        e0 = sum(mod[c][0] for c in cells)
        e1 = sum(mod[c][1] for c in cells)
        big = [c for c in cells if mod[c][1] >= 0.05]
        chi = sum((obs[c] - mod[c][1]) ** 2 / mod[c][1] for c in big)
        print(f"| {name} | {len(cells)} | {o} | {e0:.2f} | {e1:.2f} | {chi:.1f} on {len(big)} |")


if __name__ == '__main__':
    main()
