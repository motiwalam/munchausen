"""Check the reduction from SUBSET-SUM to the generalized Munchausen problem.

The generalized problem: given a base b and weights w(0), ..., w(b-1), is
there an n >= b with sum of w(digit) over the digits of n equal to n?

The reduction (docs/library/drafts/complexity-and-poisson.md, Theorem 1.3)
maps an instance (a_1, ..., a_k; T) to a base b and a weight table. This
script builds the table for many tiny instances, finds every solution with
an exact search that does not use the reduction's proof, and checks that the
solutions correspond one to one to the subsets with sum T.

Usage:
    python thy_reduction.py selftest    # exact search against plain brute force
    python thy_reduction.py sweep K AMAX # all instances with k <= K, a_i <= AMAX
    python thy_reduction.py broken      # what goes wrong without the gadgets
"""
import itertools
import random
import sys
import time


def is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def largest_prime_factor(n):
    best, i = 1, 2
    while i * i <= n:
        while n % i == 0:
            best, n = i, n // i
        i += 1
    return max(best, n) if n > 1 else best


def parameters(k, big):
    """Smallest base b that meets the conditions of Theorem 1.3.

    Returns (b, p, L): p is a prime dividing b - 1 and L is the size of the
    low block. D = L + 2k + 4 bounds the length of every solution.
    """
    b = 3
    while True:
        p = largest_prime_factor(b - 1)
        for L in range(0, 200):
            D = L + 2 * k + 4
            if b ** (L + 1) > D * p * big:
                break
        if 2 * D <= b and p > D:
            return b, p, L
        b += 1


def build(a, T, increasing=False):
    """Weight table for the instance (a; T). Returns (b, w, info)."""
    k = len(a)
    big = max([T, 1] + list(a))
    b, p, L = parameters(k, big)
    pos = [L + 2 * i for i in range(1, k + 1)]
    pz = L + 2 * k + 2
    if increasing:
        items = [b - 3 - k + i for i in range(1, k + 1)]
        z = b - 2
    else:
        items = [b - 1 - i for i in range(1, k + 1)]
        z = b - 2 - k
    w = [y + 1 for y in range(b)]          # prohibited: w(y) = y + 1
    w[0] = 0
    for x, P, ai in zip(items, pos, a):
        w[x] = x * b ** P + p * ai
    w[z] = z * b ** pz - p * T
    if increasing:
        w[b - 1] = (b - 1) * b ** pz + 1
        assert all(w[i] < w[i + 1] for i in range(b - 1)), w
    info = dict(b=b, p=p, L=L, items=items, pos=pos, z=z, pz=pz, D=L + 2 * k + 4)
    return b, w, info


def length_bound(b, w):
    """Largest D with b^(D-1) <= D * max(w): no solution is longer."""
    wmax = max(w)
    D = 1
    while b ** D <= (D + 1) * wmax:
        D += 1
    return D


def digits(n, b):
    out = []
    while n:
        n, r = divmod(n, b)
        out.append(r)
    return out


def solutions(b, w, light=None):
    """Every n >= b with F(n) = n, for an arbitrary weight table.

    Exact for every table with w(0) = 0. The values with weight at most
    `light` are light, the others heavy. The search fixes the counts of the
    heavy values (at most D in total, D from length_bound), then tries every
    possible total s of the light weights. For each pair it computes
    n = heavy sum + s and checks that the digits of n have the assumed heavy
    counts and light total. Every solution arises this way for exactly one
    pair, because its nonzero digit multiset determines both.
    """
    assert w[0] == 0
    D = length_bound(b, w)
    if light is None:
        light = b * b
    heavy = [x for x in range(1, b) if w[x] > light]
    lmax = max([w[x] for x in range(1, b) if w[x] <= light] + [0])
    found = set()
    top = b ** D
    smax = D * lmax
    # n = hi * R + (lo + s): only the r low digits depend on s, up to one carry
    r = 1
    while b ** r <= smax:
        r += 1
    R = b ** r
    isheavy = [x in heavy for x in range(b)]
    wl = [0 if isheavy[x] else w[x] for x in range(b)]   # light weight, 0 for heavy

    def profile(m):
        """Counts of the heavy values and light weight total of the digits of m."""
        hc = [0] * b
        lw = 0
        for x in digits(m, b):
            if isheavy[x]:
                hc[x] += 1
            lw += wl[x]
        return hc, lw

    def rec(i, left, total, counts):
        if total >= top:
            return
        if i == len(heavy):
            want = [0] * b
            for x, c in zip(heavy, counts):
                want[x] = c
            hi, lo = divmod(total, R)
            highs = [profile(hi), profile(hi + 1)]
            # zeros are free (w(0) = 0), so padding the low part with zeros is harmless
            if all(any(hc[x] > want[x] or want[x] > hc[x] + r for x in heavy) for hc, _ in highs):
                return
            for s in range(0, smax + 1):
                v = lo + s
                carry, v = divmod(v, R)
                n = (hi + carry) * R + v
                if n < b:
                    continue
                hc, lw = highs[carry]
                hc = list(hc)
                for _ in range(r):
                    v, x = divmod(v, b)
                    if isheavy[x]:
                        hc[x] += 1
                    lw += wl[x]
                if lw == s and all(hc[x] == want[x] for x in heavy):
                    found.add(n)
            return
        x = heavy[i]
        c = 0
        while c <= left and total + c * w[x] < top:
            counts.append(c)
            rec(i + 1, left - c, total + c * w[x], counts)
            counts.pop()
            c += 1

    rec(0, D, 0, [])
    return sorted(found)


def naive(b, w):
    D = length_bound(b, w)
    out = []
    for n in range(b, b ** D):
        if sum(w[x] for x in digits(n, b)) == n:
            out.append(n)
    return out


def selftest(trials=300, seed=7):
    """The exact search agrees with brute force on random weight tables."""
    rng = random.Random(seed)
    done = withsol = 0
    for t in range(trials):
        b = rng.randint(3, 7)
        cap = rng.choice([10, 50, 300, 2000])
        w = [0] + [rng.randint(0, cap) for _ in range(b - 1)]
        if rng.random() < 0.5:
            # plant a self-paying digit so that solutions exist
            x = rng.randint(1, b - 1)
            w[x] = x * b ** rng.randint(0, 3)
        if b ** length_bound(b, w) > 3_000_000:
            continue
        light = rng.choice([0, b, b * b, 10 ** 9])
        a, c = solutions(b, w, light), naive(b, w)
        assert a == c, (b, w, a, c)
        done += 1
        withsol += bool(a)
    print(f"selftest: exact search equals brute force on {done} random tables, {withsol} of them with solutions")


def subset_count(a, T):
    return sum(1 for r in range(len(a) + 1) for S in itertools.combinations(range(len(a)), r)
               if sum(a[i] for i in S) == T)


def decode(n, info, b):
    """The subset an honest solution encodes, or None."""
    ds = digits(n, b)
    S = []
    for i, (x, P) in enumerate(zip(info['items'], info['pos'])):
        if P < len(ds) and ds[P] == x:
            S.append(i)
    return tuple(S)


def sweep(K, amax):
    t0 = time.time()
    tested = yes = 0
    for k in range(1, K + 1):
        for a in itertools.product(range(1, amax + 1), repeat=k):
            for T in range(0, sum(a) + 2):
                for inc in (False, True):
                    b, w, info = build(list(a), T, inc)
                    sols = solutions(b, w)
                    want = subset_count(a, T)
                    assert len(sols) == want, (a, T, inc, sols, want)
                    subsets = sorted(decode(n, info, b) for n in sols)
                    assert all(sum(a[i] for i in S) == T for S in subsets)
                    assert len(set(subsets)) == len(subsets)
                    tested += 1
                    yes += want > 0
        print(f"k={k}: all instances with a_i <= {amax} pass "
              f"(base {b}, solutions at most {info['D']} digits), {time.time() - t0:.0f} s", flush=True)
    print(f"{tested} weight tables, {yes} with a solution; "
          "solution count = subset count in every case")


def broken():
    """Remove one gadget at a time and look for spurious solutions."""
    a, T = [2, 3], 4      # no subset sums to 4
    b, w, info = build(a, T)
    print("instance a=(2,3), T=4 has", subset_count(a, T), "subsets; reduction gives",
          len(solutions(b, w)), "solutions in base", b)
    # 1. prohibited values made self-paying at position 0: w(y) = y
    w1 = list(w)
    for y in range(1, b):
        if w1[y] == y + 1:
            w1[y] = y
    s1 = solutions(b, w1)
    print("  with w(y) = y for the prohibited values:", len(s1), "solutions, e.g.",
          [digits(n, b)[::-1] for n in s1[:3]])
    # 2. prohibited values made free: w(y) = 0
    w2 = list(w)
    for y in range(1, b):
        if w2[y] == y + 1:
            w2[y] = 0
    s2 = solutions(b, w2)
    print("  with w(y) = 0 for the prohibited values:", len(s2), "solutions, e.g.",
          [digits(n, b)[::-1] for n in s2[:3]])
    # 3. errors not multiples of p: the residue argument fails
    w3 = list(w)
    for x, ai in zip(info['items'], a):
        w3[x] -= info['p'] * ai - ai
    w3[info['z']] += info['p'] * T - T
    s3 = solutions(b, w3)
    print("  with errors a_i, -T instead of p a_i, -p T:", len(s3), "solutions",
          [digits(n, b)[::-1] for n in s3[:3]])


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'sweep'
    if what == 'selftest':
        selftest()
    elif what == 'sweep':
        sweep(int(sys.argv[2]) if len(sys.argv) > 2 else 3, int(sys.argv[3]) if len(sys.argv) > 3 else 3)
    elif what == 'broken':
        broken()
    elif what == 'show':
        b, w, info = build([1, 2, 3], 3)
        print(info)
        for x in range(b):
            print(x, w[x])
        for n in solutions(b, w):
            print(n, digits(n, b)[::-1])
