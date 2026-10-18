"""Bases with a 2-digit and a 3-digit solution (question 36).

Part 1. For every base in analysis/data/k3.txt (all 3-digit solutions in
bases up to 10^51) list the 2-digit solutions of that base.
Part 2. For every 2-digit solution (a, c) with a, c <= L, find every
3-digit solution in its base b = (a^a + g(c)) / a, g(c) = w(c) - c.

Method of part 2, for one base b. A 3-digit solution (p, q, r) has
F = p b^2 + q b + r in [p b^2, (p+1) b^2) and w(M) <= F < 3 w(M) for its
largest digit M. So for each p only the M with p b^2 / 3 < w(M) <= (p+1) b^2
occur, at most two. M sits at position 1 (then p = M), 2 or 3:
  M = q:  w(r) - r = p b^2 + M b - w(p) - w(M), and w(r) - r is increasing;
  M = r:  w(q) - q b = p b^2 + M - w(p) - w(M), convex in q, so at most
          two roots, found by bisection on each monotone piece;
  M = p:  q and r both free: w(q) + w(r) - q b - r = M b^2 - w(M); the
          larger of q, r is fixed up to two values by size, the other by
          inversion.
Every candidate is checked exactly.

usage: python3 analysis/r2nt_two_three.py L m
"""
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def wfun(m):
    return lambda d: m if d == 0 else d ** d


def two_digit_in_base(b, m):
    w = wfun(m)
    out = []
    a = 1
    while a < b and a ** a <= a * b + b:
        T = a * b - a ** a  # = w(c) - c
        for c in range(0, b):
            v = w(c) - c
            if v == T:
                out.append((a, c))
            if v > T and c >= 2:
                break
        a += 1
    return out


def inv_increasing(f, target, lo, hi):
    """smallest x in [lo, hi] with f(x) >= target, f increasing"""
    while lo < hi:
        mid = (lo + hi) // 2
        if f(mid) < target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def three_digit_in_base(b, m, X):
    w = wfun(m)
    sols = set()

    def check(p, q, r):
        if 0 < p < b and 0 <= q < b and 0 <= r < b and p * b * b + q * b + r == w(p) + w(q) + w(r):
            sols.add((p, q, r))

    Ms = list(range(0, X + 1))
    for p in range(1, X + 1):
        lo, hi = p * b * b // 3, (p + 1) * b * b
        cand = [M for M in Ms if lo < w(M) <= hi and M >= p]
        for M in cand:
            # M = q
            T = p * b * b + M * b - w(p) - w(M)
            r = inv_increasing(lambda x: w(x) - x if x >= 1 else -10 ** 9, T, 1, X)
            for rr in (r, 0):
                check(p, M, rr)
            # M = r
            T = p * b * b + M - w(p) - w(M)
            f = lambda x: w(x) - x * b
            # minimum of f near x with w'(x) = b
            k = 1
            while k < X and f(k + 1) <= f(k):
                k += 1
            q1 = inv_increasing(lambda x: -f(x), -T, 0, k)  # decreasing piece
            q2 = inv_increasing(f, T, k, X)
            for qq in (q1, q2, q1 - 1, q2 - 1):
                if qq >= 0:
                    check(p, qq, M)
            # M = p (leading digit is the largest)
            if M == p:
                T = M * b * b - w(M)  # = q b + r - w(q) - w(r)
                for q in range(0, M + 1):
                    T2 = w(q) - q * b - T  # need w(r) - r = -T2 ... rearranged
                    # p b^2 + q b + r = w(p) + w(q) + w(r)  =>  w(r) - r = p b^2 + q b - w(p) - w(q)
                    T3 = p * b * b + q * b - w(p) - w(q)
                    r = inv_increasing(lambda x: w(x) - x if x >= 1 else -10 ** 9, T3, 1, M)
                    for rr in (r, 0):
                        check(p, q, rr)
    return sorted(sols)


def main():
    L = int(sys.argv[1])
    m = int(sys.argv[2])
    w = wfun(m)
    print(f'0^0 = {m}')
    print('part 1: bases of analysis/data/k3.txt (complete up to 10^51)')
    bases = sorted({int(line.split()[2]) for line in open(os.path.join(ROOT, 'analysis/data/k3.txt'))
                    if line.split()[1] == str(m)})
    for b in bases:
        if b > 10 ** 12:
            # 2-digit solutions in huge self-paying bases: only (x, 0), (x, 1)
            pass
        t = two_digit_in_base(b, m) if b < 10 ** 40 else 'skipped'
        three = [line.split()[3] for line in open(os.path.join(ROOT, 'analysis/data/k3.txt'))
                 if line.split()[1] == str(m) and int(line.split()[2]) == b]
        print(f'  base {b}: 3-digit {three}; 2-digit {t}')
    print(f'part 2: 3-digit solutions in the bases of all 2-digit solutions with a, c <= {L}')
    count = 0
    found = []
    for a in range(1, L + 1):
        for c in range(0, L + 1):
            num = a ** a + w(c) - c
            if num % a:
                continue
            b = num // a
            if b <= max(a, c):
                continue
            count += 1
            X = 2
            while (X + 1) ** (X + 1) <= 3 * (X + 2) * b * b:
                X += 1
            s3 = three_digit_in_base(b, m, X + 1)
            if s3:
                found.append((a, c, b if b < 10 ** 30 else f'~10^{len(str(b)) - 1}', s3))
    print(f'  {count} bases checked; bases with a 3-digit solution:')
    for f in found:
        print('   ', f)


if __name__ == '__main__':
    main()
