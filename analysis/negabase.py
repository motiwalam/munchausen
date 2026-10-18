"""All Munchausen numbers in the negative base -b, for small b, by brute force
over digit multisets.

n = F(n) with n written in base -b (digits 0..b-1). F depends only on the
multiset, so for each multiset c compute F(c), write it in base -b, and
compare the digit counts. Lengths are bounded: a d-digit number in base -b
is at least about b^(d-2), and F(c) <= d (b-1)^(b-1).
"""
import sys
from itertools import combinations_with_replacement


def negadigits(n, b):
    out = []
    while n:
        n, r = divmod(n, -b)
        if r < 0:
            n, r = n + 1, r + b
        out.append(r)
    return out[::-1] or [0]


def search(b, mode):
    w = [mode] + [x ** x for x in range(1, b)]
    sols = []
    top = (b + 3) * (b - 1) ** (b - 1) + b
    for d in range(1, b + 4):
        if b ** (d - 2) > top * b:
            break
        for c in combinations_with_replacement(range(b), d):
            f = sum(w[x] for x in c)
            ds = negadigits(f, b)
            if len(ds) == d and sorted(ds) == list(c):
                sols.append(tuple(ds))
    return sorted(set(sols), key=lambda t: (len(t), t))


if __name__ == '__main__':
    lo = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    for b in range(lo, int(sys.argv[1]) + 1):
        for mode in (1, 0):
            s = [t for t in search(b, mode) if t not in ((0,), (1,))]
            print(f"base -{b}, 0^0={mode}: {len(s)} nontrivial: {s}", flush=True)
