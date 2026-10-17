"""Bases with self-paying digits: a^(a-1) = b^k with 2 <= a < b, k >= 1.

Writing b = r^t with r not a perfect power, the self-paying digits are
a = r^s for 1 <= s < t with t | s (r^s - 1), at position k = s (r^s - 1) / t.
"""
import math
import sys


def perfect_power(b):
    """(r, t) with b = r^t and t as large as possible."""
    best = (b, 1)
    for t in range(2, b.bit_length() + 1):
        r = round(b ** (1 / t))
        for c in (r - 1, r, r + 1):
            if c > 1 and c ** t == b:
                best = (c, t)
    return best


def self_paying(b):
    r, t = perfect_power(b)
    return [(r ** s, s * (r ** s - 1) // t) for s in range(1, t) if (s * (r ** s - 1)) % t == 0]


if __name__ == '__main__':
    limit = int(sys.argv[1])
    found = [(b, self_paying(b)) for b in range(2, limit + 1)]
    found = [(b, sp) for b, sp in found if sp]
    print(f"{len(found)} bases <= {limit} have self-paying digits:")
    for b, sp in found:
        print(f"  {b}: " + ", ".join(f"digit {a} at position {k}" for a, k in sp))
    pp = [b for b in range(2, limit + 1) if perfect_power(b)[1] > 1]
    print("perfect powers without self-paying digits:", [b for b in pp if not self_paying(b)][:40])
