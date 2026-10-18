"""Question 45: count digit multisets instead of digit strings.

Part 1 checks the window of Proposition 15.17 (Lemma 1.1 of the round 3
draft) on every known solution, with exact integer arithmetic.
Part 2 runs the multiset search of Lemma 1.1 for short lengths and compares
it with the complete lists analysis/data/k3.txt to k7.txt.
Part 3 checks the divisor lemma (Lemma 1.4) on random data and records how
many window bases pass the test b - 1 | F(c) - S(c).
Part 4 evaluates the bound of Proposition 1.2 at B = 10^96 and the
threshold of Theorem 1.3 for larger B.

usage: python3 analysis/r3nt_multiset.py
"""
import glob
import math
import os
import random
from fractions import Fraction
from itertools import combinations_with_replacement

from mpmath import mp, mpf

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')


def w(d, m):
    return m if d == 0 else d ** d


def digits(n, b):
    out = []
    while n:
        out.append(n % b)
        n //= b
    return out[::-1]


def largest_x(N):
    """Largest X >= 1 with X^X <= N."""
    t = N.bit_length() * math.log(2)
    X = 1
    lo, hi = 1, 2
    while hi * math.log(hi) < t + 10:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid * math.log(mid) <= t:
            lo = mid
        else:
            hi = mid
    X = max(1, lo - 2)
    while X > 1 and X ** X > N:
        X -= 1
    while (X + 1) ** (X + 1) <= N:
        X += 1
    return X


def load_solutions():
    sols = set()
    for f in glob.glob(os.path.join(ROOT, 'output', 'b*.txt')):
        for line in open(f):
            line = line.strip()
            if not line:
                continue
            b, m, _, rest = line.split(':', 3)
            for t in rest.split('), ('):
                t = t.strip(' ()')
                ds = tuple(int(v) for v in t.split(',') if v.strip())
                if len(ds) >= 2:
                    sols.add((int(b), int(m), ds))
    for f in glob.glob(os.path.join(ROOT, 'analysis', 'data', 'k[2-7].txt')):
        for line in open(f):
            if line.startswith('#') or not line.strip():
                continue
            k, m, b, ds = line.split()
            sols.add((int(b), int(m), tuple(int(v) for v in ds.split(','))))
    return sorted(sols)


def iroot(n, e):
    """Floor of the e-th root of n >= 0."""
    if n < 2 or e == 1:
        return n
    x = 1 << ((n.bit_length() + e - 1) // e)
    while True:
        y = ((e - 1) * x + n // x ** (e - 1)) // e
        if y >= x:
            break
        x = y
    while x ** e > n:
        x -= 1
    while (x + 1) ** e <= n:
        x += 1
    return x


def window_ok(b, k, p, N, X):
    """b <= (N/p)^(1/(k-1)) < b + (X+1)/(p(k-1)), checked exactly."""
    left = p * b ** (k - 1) <= N
    h = Fraction(X + 1, p * (k - 1))
    right = N < p * (b + h) ** (k - 1)
    return left and right


def part1():
    sols = load_solutions()
    bad = 0
    notlargest = 0
    tight = 0.0
    for b, m, ds in sols:
        k = len(ds)
        N = sum(w(d, m) for d in ds)
        assert N == sum(d * b ** (k - 1 - i) for i, d in enumerate(ds)), (b, m, ds)
        p = ds[0]
        X = largest_x(N)
        assert max(ds) <= X
        if not window_ok(b, k, p, N, X):
            bad += 1
            print('  window fails:', b, m, ds)
        if max(ds) > p:
            notlargest += 1
        # the stronger form with the actual largest digit M
        M = max(ds)
        if not N < p * b ** (k - 1) + (M + 1) * b ** (k - 2):
            bad += 1
            print('  strong window fails:', b, m, ds)
        # position t in [0, 1) of (N/p)^(1/(k-1)) = b + t (X+1)/(p(k-1))
        mp.dps = len(str(N)) + 30
        r = (mpf(N) / p) ** (mpf(1) / (k - 1))
        tight = max(tight, float((r - b) / (mpf(X + 1) / (p * (k - 1)))))
    print(f'part 1: {len(sols)} known solutions with 2 or more digits, '
          f'{notlargest} with a leading digit below the largest digit; '
          f'window failures: {bad}; largest relative position in the window: {float(tight):.4f}')


def multiset_search(k, M, m):
    """All k-digit solutions with digits <= M, by multisets and windows."""
    found = set()
    ncand = 0
    maxcand = 0
    npass = 0
    for c in combinations_with_replacement(range(M + 1), k):
        N = sum(w(d, m) for d in c)
        S = sum(c)
        sc = sorted(c)
        for p in set(c):
            if p == 0:
                continue
            # integer part of Y = (N/p)^(1/(k-1)), then the window (Y - h, Y]
            Y = iroot(N // p, k - 1)
            h = Fraction(M + 1, p * (k - 1))
            lo = max(max(c) + 1, 2, math.floor(Y - h))
            cnt = 0
            for b in range(lo, Y + 1):
                if p * b ** (k - 1) > N or not N < p * b ** (k - 1) + (M + 1) * b ** (k - 2):
                    continue
                cnt += 1
                if (N - S) % (b - 1) == 0:
                    npass += 1
                ds = digits(N, b)
                if len(ds) == k and sorted(ds) == sc:
                    found.add((b, tuple(ds)))
            ncand += cnt
            maxcand = max(maxcand, cnt)
    return found, ncand, maxcand, npass


def part2():
    lists = {}
    for k in range(3, 8):
        for line in open(os.path.join(ROOT, 'analysis', 'data', f'k{k}.txt')):
            if line.startswith('#') or not line.strip():
                continue
            kk, m, b, ds = line.split()
            lists.setdefault((k, int(m)), set()).add((int(b), tuple(int(v) for v in ds.split(','))))
    for k, M in ((3, 40), (4, 22), (5, 12), (6, 9), (7, 7)):
        for m in (0, 1):
            found, ncand, maxcand, npass = multiset_search(k, M, m)
            ref = {s for s in lists.get((k, m), set()) if max(s[1]) <= M}
            status = 'same' if found == ref else f'DIFFERENT: {sorted(found ^ ref)}'
            nms = math.comb(M + k, k)
            print(f'part 2: k={k} M={M} 0^0={m}: {nms} multisets, {ncand} window bases '
                  f'(at most {maxcand} per multiset and leading digit), {npass} with b-1 | F-S, '
                  f'{len(found)} solutions; list: {status}')


def lcm_bound_ok(trials=20000):
    """Lemma 1.4: r divisors of m in (Y-h, Y] force m >= (Y-h)^r / h^(r(r-1)/2)."""
    rnd = random.Random(1)
    worst = 0.0
    for _ in range(trials):
        Y = rnd.randrange(50, 10 ** 6)
        h = rnd.randrange(1, 60)
        r = rnd.randrange(2, 5)
        ds = sorted(rnd.sample(range(max(1, Y - h + 1), Y + 1), min(r, h)))
        if len(ds) < 2:
            continue
        L = 1
        for d in ds:
            L = L * d // math.gcd(L, d)
        rr = len(ds)
        bound = (Y - h) ** rr / h ** (rr * (rr - 1) / 2)
        if L < bound:
            return False, (Y, h, ds)
        worst = max(worst, bound / L)
    return True, worst


def part3():
    ok, info = lcm_bound_ok()
    print(f'part 3: lcm inequality of Lemma 1.4 holds on random tests: {ok} (largest bound / lcm = {info})')


def lnbinom(n, k):
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def xk(L, k):
    """Largest X with X ln X < k L (L = ln B), the digit bound of Proposition 10.4."""
    t = k * L
    lo, hi = 1.0, max(3.0, t)
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid * math.log(mid) < t:
            lo = mid
        else:
            hi = mid
    return math.floor(lo)


def lnterm(L, k):
    X = xk(L, k)
    Hk = math.log(k) + 1 if k > 50 else sum(1.0 / j for j in range(1, k + 1))
    return lnbinom(X + k, k) + math.log((X + 1) * Hk / (k - 1) + k)


def lnbound(L, K):
    """ln of the bound of Proposition 1.2 summed over 2 <= k <= K (one convention).

    For K > 200 the sum is replaced by K times its last term, an upper bound
    because the terms increase with k.
    """
    if K > 200:
        return math.log(K) + lnterm(L, K)
    tot = None
    for k in range(2, K + 1):
        t = lnterm(L, k)
        tot = t if tot is None else max(tot, t) + math.log1p(math.exp(-abs(tot - t)))
    return tot


def lnstrings(L, K):
    tot = None
    for k in range(2, K + 1):
        X = xk(L, k)
        t = math.log(X) + (k - 1) * math.log(X + 1)
        tot = t if tot is None else max(tot, t) + math.log1p(math.exp(-abs(tot - t)))
    return tot


def part4():
    L = 96 * math.log(10)
    print('part 4: B = 10^96, ln B / ln ln B = %.2f' % (L / math.log(L)))
    print('   K   alpha   strings: log_B   multisets: log_B')
    for K in (4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52):
        print(f'  {K:3d}  {K * math.log(L) / L:5.3f}   {lnstrings(L, K) / L:8.3f}   {lnbound(L, K) / L:8.3f}')
    K = 2
    while lnbound(L, K + 1) < L:
        K += 1
    print(f'  largest K with multiset bound below B: {K} (alpha = {K * math.log(L) / L:.3f})')
    K2 = 2
    while lnstrings(L, K2 + 1) < L:
        K2 += 1
    print(f'  largest K with string bound below B: {K2} (alpha = {K2 * math.log(L) / L:.3f})')
    print('threshold: largest K with bound < B, against L/ln L and the formula of Theorem 1.3')
    for e in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 6, 10 ** 8, 10 ** 10):
        L = e * math.log(10)
        lo, hi = 2, 2
        while lnbound(L, hi) < L:
            hi *= 2
        lo = hi // 2
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if lnbound(L, mid) < L:
                lo = mid
            else:
                hi = mid
        lL = math.log(L)
        pred = L / lL * (1 + (math.log(lL) + math.log(2) - 1) / lL)
        print(f'  B = 10^{e}: K = {lo}, L/lnL = {L / lL:.1f}, formula = {pred:.1f}, '
              f'K lnL / L = {lo * lL / L:.4f}')


if __name__ == '__main__':
    part1()
    part3()
    part4()
    part2()
