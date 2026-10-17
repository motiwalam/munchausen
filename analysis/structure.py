"""Classify solutions by their balance structure.

A digit x at position i has balance x * b^i - w(x). A number is a solution
exactly when its balances add up to zero. Placements with balance zero are:

- a zero, under 0^0 = 0;
- a 1 in the last position;
- a self-paying digit a at position k, with a^(a-1) = b^k.

The kernel of a solution is the list of its placements with nonzero balance.
"""
import sys
from collections import Counter

from catalog import everything


def w(x, mode):
    return mode if x == 0 else x ** x


def placements(b, digits):
    d = len(digits)
    return [(x, d - 1 - i) for i, x in enumerate(digits)]


def balance(b, x, i, mode):
    return x * b ** i - w(x, mode)


def kernel(b, digits, mode):
    return [(x, i) for x, i in placements(b, digits) if balance(b, x, i, mode) != 0]


def self_paying(b, digits):
    return [(x, i) for x, i in placements(b, digits) if x >= 2 and i >= 1 and x * b ** i == x ** x]


def classify(mode, b, digits):
    ker = kernel(b, digits, mode)
    comp = self_paying(b, digits)
    if not ker:
        return 'pure'
    if len(digits) == 2 and not comp:
        return 'two-digit'
    if comp:
        return 'self-paying digits + kernel of %d' % len(ker)
    if len(ker) <= 3:
        return 'small kernel of %d' % len(ker)
    return 'unstructured'


if __name__ == '__main__':
    stats = Counter()
    examples = {}
    for mode, b, digits in everything():
        c = classify(mode, b, digits)
        key = (mode, c.split(' of ')[0] if 'kernel of' in c else c)
        stats[key] += 1
        examples.setdefault((mode, c), (b, digits))
    for key in sorted(stats):
        print(f"0^0={key[0]}  {key[1]:35s} {stats[key]}")
    print()
    for (mode, c), (b, digits) in sorted(examples.items()):
        if c != 'unstructured' and c != 'two-digit':
            s = ','.join(map(str, digits))
            print(f"0^0={mode} {c:35s} base {b if b < 10**12 else '~10^%d' % (len(str(b)) - 1)}: ({s[:80]})")
    if len(sys.argv) > 1:
        # list the kernel of the small-kernel solutions
        for mode, b, digits in everything():
            if classify(mode, b, digits).startswith('small kernel'):
                print(mode, b, digits, kernel(b, digits, mode))
