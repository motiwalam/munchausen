"""Integers that are solutions in three bases under 0^0 = 1 (question 39).

Uses bases_of() of analysis/dyn_multibase.py, which is complete for one N.
Part 1: every N = a^a + w(c) that is a 2-digit solution, a, c <= L1.
Part 2: every N = a^a + c^c with two 2-digit bases ((a, c) and (c, a),
        a | c^c - c and c | a^a - a), a, c <= L2.
Prints every N with 3 or more bases, and every N with a representation of
3 or more digits besides a 2-digit one.

usage: python3 analysis/r2nt_multibase.py L1 L2
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dyn_multibase import bases_of

M = 1


def w(d):
    return M if d == 0 else d ** d


def valid(a, c):
    num = a ** a + w(c) - c
    return num % a == 0 and num // a > max(a, c)


def main():
    L1, L2 = int(sys.argv[1]), int(sys.argv[2])
    seen = set()
    hist = {}
    special = []
    for a in range(1, L1 + 1):
        for c in range(0, L1 + 1):
            if not valid(a, c):
                continue
            N = a ** a + w(c)
            if N in seen:
                continue
            seen.add(N)
            fb = bases_of(N, M)
            hist[len(fb)] = hist.get(len(fb), 0) + 1
            if len(fb) >= 3 or any(len(d) >= 3 for d in fb.values()):
                special.append((N, fb))
    print(f'part 1: {len(seen)} integers with a 2-digit representation, digits <= {L1}')
    print('  number of bases:', dict(sorted(hist.items())))
    doubles = 0
    for a in range(2, L2 + 1):
        for c in range(2, a):
            if valid(a, c) and valid(c, a):
                N = a ** a + c ** c
                doubles += 1
                if N in seen:
                    continue
                seen.add(N)
                fb = bases_of(N, M)
                if len(fb) >= 3 or any(len(d) >= 3 for d in fb.values()):
                    special.append((N, fb))
    print(f'part 2: {doubles} integers a^a + c^c with two 2-digit bases, a, c <= {L2}')
    print('integers with 3 or more bases, or with a representation of 3 or more digits:')
    for N, fb in special:
        print('  ', N if N < 10 ** 30 else f'~10^{len(str(N)) - 1}', fb)
    if not special:
        print('   none')


if __name__ == '__main__':
    main()
