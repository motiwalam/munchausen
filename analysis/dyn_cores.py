"""Cores of the known solutions under 0^0 = 0 (question 16).

Proposition 2.3 splits a solution under 0^0 = 0 into a core, a set of
self-paying digits and an optional final 1. This script reads every known
solution under 0^0 = 0 (output/ and the k-digit lists of analysis/data/),
splits it, and lists the solutions that have both a nonzero core and at
least one self-paying digit.

usage: python3 analysis/dyn_cores.py
"""
import glob
import os
import re

import gmpy2

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def power_decomp(n):
    n = gmpy2.mpz(n)
    r, t = n, 1
    while gmpy2.is_power(r):
        for p in range(2, int(gmpy2.bit_length(r)) + 1):
            if gmpy2.is_prime(p):
                root, exact = gmpy2.iroot(r, p)
                if exact:
                    r, t = root, t * p
                    break
    return int(r), t


def self_paying_positions(b):
    """Map position -> self-paying digit of base b."""
    r, t = power_decomp(b)
    out = {}
    for s in range(1, t):
        if (s * (r ** s - 1)) % t == 0:
            out[s * (r ** s - 1) // t] = r ** s
    return out


def solutions():
    seen = set()
    for f in glob.glob(os.path.join(ROOT, 'output', '*-0.txt')):
        for line in open(f):
            m = re.match(r'(\d+):0:\d+: (.*)', line)
            if not m:
                continue
            b = int(m.group(1))
            for tup in re.findall(r'\(([\d,]+)\)', m.group(2)):
                d = tuple(int(x) for x in tup.split(',') if x)
                if len(d) >= 2:
                    seen.add((b, d))
    for f in glob.glob(os.path.join(ROOT, 'analysis', 'data', 'k[0-9].txt')):
        for line in open(f):
            p = line.split()
            if len(p) == 4 and p[1] == '0':
                seen.add((int(p[2]), tuple(int(x) for x in p[3].split(','))))
    return sorted(seen)


def main():
    sols = solutions()
    composite = []
    cache = {}
    for b, d in sols:
        if b not in cache:
            cache[b] = self_paying_positions(b) if gmpy2.is_power(b) else {}
        sp = cache[b]
        k = len(d)
        core = list(d)
        removed = []
        for i in range(k):
            pos = k - 1 - i
            if pos in sp and d[i] == sp[pos]:
                core[i] = 0
                removed.append((sp[pos], pos))
        if core[-1] == 1 and k >= 2:
            core[-1] = 0
        while core and core[0] == 0:
            core.pop(0)
        if removed and core:
            composite.append((b, d, tuple(core), removed))
    print(f'{len(sols)} known solutions under 0^0 = 0 with at least 2 digits')
    print(f'{len(composite)} have a nonzero core and a self-paying digit:')
    for b, d, core, removed in composite:
        print(f'  base {b}: {d}  core {core}  self-paying {removed}')


if __name__ == '__main__':
    main()
