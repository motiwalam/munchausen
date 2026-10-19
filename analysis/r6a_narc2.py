"""Round 6, section 4: two-digit narcissistic numbers and tau(b^2 + 1).

A 2-digit number (s1, s0) in base b equals s1^2 + s0^2 exactly when
(2 s1 - b)^2 + (2 s0 - 1)^2 = b^2 + 1. Theorem 4.1 of the draft says the
number of them is tau(b^2 + 1) - 2. This script checks the formula by brute
force, compares the averages by parity with (2/pi) ln b and (4/pi) ln b
(Hooley's (3/pi) X ln X split by the 2-adic factor), and lists the share of
even bases with b^2 + 1 prime (bases with none).

    python3 r6a_narc2.py BRUTE BMAX   -> data/r6a_narc2.txt
"""
import math
import os
import sys

import numpy as np
from sympy import divisor_count, sqrt_mod

from r6a_lib import primes_upto

HERE = os.path.dirname(os.path.abspath(__file__))


def brute(b):
    n = 0
    for s1 in range(1, b):
        for s0 in range(b):
            if s1 * b + s0 == s1 * s1 + s0 * s0:
                n += 1
    return n


def tau_table(bmax):
    """tau(b^2 + 1) for b = 0..bmax by sieving with the roots of x^2 = -1."""
    v = np.arange(bmax + 1, dtype=np.int64) ** 2 + 1
    t = np.ones(bmax + 1, dtype=np.int64)
    for l in primes_upto(bmax):
        l = int(l)
        if l != 2 and l % 4 != 1:
            continue
        roots = [1] if l == 2 else sqrt_mod(-1, l, all_roots=True)
        for r in roots:
            idx = np.arange(r, bmax + 1, l)
            e = np.zeros(len(idx), dtype=np.int64)
            sub = v[idx]
            while True:
                m = sub % l == 0
                if not m.any():
                    break
                sub = np.where(m, sub // l, sub)
                e += m
            v[idx] = sub
            t[idx] *= e + 1
    t[v > 1] *= 2          # one prime factor above bmax remains
    return t


def main():
    bb, bmax = int(sys.argv[1]), int(sys.argv[2])
    out = open(os.path.join(HERE, 'data', 'r6a_narc2.txt'), 'w')
    bad = [b for b in range(2, bb + 1) if brute(b) != divisor_count(b * b + 1) - 2]
    out.write('# brute force check b = 2..%d: mismatches %s\n' % (bb, bad))
    out.write('# X  mean_even  (2/pi)ln X + c  mean_odd  ratio odd/even  even bases with none  share\n')
    se = so = ne = no = 0
    none_even = 0
    marks = set(int(10 ** (k / 2)) for k in range(4, 2 * int(math.log10(bmax)) + 1))
    tt = tau_table(bmax)
    spot = [b for b in range(2, min(bmax, 3000) + 1) if tt[b] != divisor_count(b * b + 1)]
    out.write('# sieve against sympy for b <= 3000: mismatches %s\n' % spot)
    for b in range(2, bmax + 1):
        v = int(tt[b]) - 2
        if b % 2 == 0:
            se += v
            ne += 1
            if v == 0:
                none_even += 1
        else:
            so += v
            no += 1
        if b in marks:
            out.write('%d %.4f %.4f %.4f %.4f %d %.4f\n' % (
                b, se / ne, 2 / math.pi * math.log(b), so / no, (so / no + 2) / (se / ne + 2),
                none_even, none_even / ne))
    out.close()
    print(open(os.path.join(HERE, 'data', 'r6a_narc2.txt')).read())


if __name__ == '__main__':
    main()
