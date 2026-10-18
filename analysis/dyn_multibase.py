"""Integers that are Munchausen numbers in several bases (question 30).

bases_of(N, m) returns every base b >= 2 in which N is a solution. It is
complete. Every digit d of a solution has d^d <= F(N) = N, so d <= X with
X^X <= N. Bases up to B0 are checked directly. For b > B0 and k digits, let
p be the leading digit. The second digit is at most X, so
N / b^(k-1) < p + (X + 1) / b, and b lies within (X + 1) / (p (k - 1)) of
(N / p)^(1/(k-1)). The script tests those few bases for every k and p.

Candidates: every known solution (output/, analysis/data/) and the sums
a^a + c^c with a, c up to a bound, which are the integers with two 2-digit
representations (Proposition 30.2).

usage: python3 analysis/dyn_multibase.py [pair bound]
"""
import glob
import os
import re
import sys
from collections import defaultdict

import gmpy2

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
B0 = 1000


def digits(n, b):
    out = []
    while n:
        n, r = divmod(n, b)
        out.append(r)
    return out[::-1]


def F(ds, m):
    return sum(d ** d if d else m for d in ds)


def xmax(N):
    x = 1
    while (x + 1) ** (x + 1) <= N:
        x += 1
    return x


def bases_of(N, m):
    found = {}
    X = xmax(N)
    for b in range(2, min(B0, N) + 1):
        ds = digits(N, b)
        if len(ds) >= 2 and max(ds) <= X and F(ds, m) == N:
            found[b] = tuple(ds)
    k = 2
    while B0 ** (k - 1) <= N:
        for p in range(1, X + 1):
            top = int(gmpy2.iroot(gmpy2.mpz(N // p), k - 1)[0])
            span = (X + 1) // (p * (k - 1)) + 2
            for b in range(max(B0 + 1, top - span), top + 2):
                ds = digits(N, b)
                if len(ds) == k and ds[0] == p and max(ds) <= X and F(ds, m) == N:
                    found[b] = tuple(ds)
        k += 1
    return found


def known(m):
    out = set()
    for f in glob.glob(os.path.join(ROOT, 'output', f'*-{m}.txt')):
        for line in open(f):
            mm = re.match(r'(\d+):\d+:\d+: (.*)', line)
            if not mm:
                continue
            b = int(mm.group(1))
            for tup in re.findall(r'\(([\d,]+)\)', mm.group(2)):
                ds = [int(x) for x in tup.split(',') if x]
                if len(ds) >= 2:
                    out.add(sum(d * b ** (len(ds) - 1 - i) for i, d in enumerate(ds)))
    for f in glob.glob(os.path.join(ROOT, 'analysis', 'data', 'k[0-9].txt')):
        for line in open(f):
            p = line.split()
            if len(p) == 4 and p[1] == str(m):
                b = int(p[2])
                ds = [int(x) for x in p[3].split(',')]
                out.add(sum(d * b ** (len(ds) - 1 - i) for i, d in enumerate(ds)))
    return out


def main():
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    for m in (1, 0):
        cands = set(known(m))
        for a in range(1, bound + 1):
            for c in range(0, bound + 1):
                cands.add(a ** a + (c ** c if c else m))
        hist = defaultdict(int)
        multi = []
        for N in sorted(cands):
            if N < 3:
                continue
            fb = bases_of(N, m)
            hist[len(fb)] += 1
            if len(fb) >= 2:
                multi.append((N, fb))
        long_multi = [(N, fb) for N, fb in multi if any(len(d) >= 3 for d in fb.values())]
        print(f'0^0 = {m}: {len(cands)} candidates; number of bases: {dict(sorted(hist.items()))}')
        print(f'  integers with 2 or more bases: {len(multi)}; with a representation of 3 or more digits: {len(long_multi)}')
        for N, fb in long_multi[:30]:
            print(f'  N = {N}: ' + '; '.join(f'base {b}: {d}' for b, d in sorted(fb.items())))
        top = sorted(multi, key=lambda x: -len(x[1]))[:5]
        for N, fb in top:
            print(f'  most: N = {N} in {len(fb)} bases ' + ', '.join(str(b) for b in sorted(fb)))


if __name__ == '__main__':
    main()
