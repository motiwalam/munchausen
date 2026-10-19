"""Zero digits of the integer near-solutions of analysis/data/r5e_int_std.txt.

Leads for questions 93 and 94 of docs/library/questions-round6.md.
Run from the repository root:

    python3 analysis/r6p_zeros.py conv   # with and without zeros, per convention
    python3 analysis/r6p_zeros.py pos    # zero rate times b, by position
    python3 analysis/r6p_zeros.py peak   # near-solutions per offset, by band of j
"""
import sys
from collections import defaultdict

DATA = 'analysis/data/r5e_int_std.txt'


def hits():
    for line in open(DATA):
        p = line.split()
        if p[0] != 'hit':
            continue
        b, m, j = int(p[1]), int(p[2]), int(p[3])
        yield b, m, j, list(map(int, p[4].split(',')))


def conv():
    strings = defaultdict(int)
    msets = defaultdict(set)
    byz = defaultdict(int)
    for b, m, j, s in hits():
        if j == 0:
            continue
        z = s.count(0)
        par = 'odd' if b % 2 else 'even'
        key = (par, m, z > 0)
        strings[key] += 1
        msets[key].add((b, tuple(sorted(s))))
        byz[(par, m, min(z, 3))] += 1
    for par in ('even', 'odd'):
        for m in (0, 1):
            print('%s bases, 0^0 = %d: with zeros %d strings, %d multisets; '
                  'zero-free %d strings, %d multisets; strings by zeros 0,1,2,3+: %s'
                  % (par, m, strings[(par, m, True)], len(msets[(par, m, True)]),
                     strings[(par, m, False)], len(msets[(par, m, False)]),
                     [byz[(par, m, k)] for k in range(4)]))


def pos():
    top = defaultdict(lambda: [0, 0])
    bot = defaultdict(lambda: [0, 0])
    mid = defaultdict(lambda: [0, 0])
    for b, m, j, s in hits():
        if j == 0:
            continue
        par = 'odd' if b % 2 else 'even'
        d = len(s)
        for i in range(1, 6):
            top[(m, par, i)][0] += b * (s[i] == 0)
            top[(m, par, i)][1] += 1
        for i in range(6):
            bot[(m, par, i)][0] += b * (s[d - 1 - i] == 0)
            bot[(m, par, i)][1] += 1
        for i in range(6, d - 6):
            mid[(m, par)][0] += b * (s[i] == 0)
            mid[(m, par)][1] += 1
    for m in (0, 1):
        for par in ('even', 'odd'):
            t = ' '.join('%.2f' % (top[(m, par, i)][0] / top[(m, par, i)][1]) for i in range(1, 6))
            bt = ' '.join('%.2f' % (bot[(m, par, i)][0] / bot[(m, par, i)][1]) for i in range(6))
            n0, n1 = mid[(m, par)]
            print('0^0 = %d, %s bases: top positions 1-5: %s | middle %.2f (%d digits) | '
                  'bottom positions 0-5: %s' % (m, par, t, n0 / n1, n1, bt))


def peak():
    count = defaultdict(int)
    for b, m, j, s in hits():
        count[(m, j)] += 1
    for m in (0, 1):
        out = []
        for lo in range(2, 121, 20):
            hi = lo + 18
            n = sum(count[(m, j)] for j in range(lo, hi + 1, 2))
            out.append('j %d-%d: %.2f' % (lo, hi, n / ((hi - lo) // 2 + 1)))
        print('0^0 = %d: D = 0 has %d;' % (m, count[(m, 0)]), ', '.join(out))


if __name__ == '__main__':
    {'conv': conv, 'pos': pos, 'peak': peak}[sys.argv[1]]()
