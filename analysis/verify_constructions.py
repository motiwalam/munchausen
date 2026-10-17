"""Check the explicit constructions in docs/library with exact integers.

Numbers are given sparsely as {position: digit}; every other digit is 0.
"""
import itertools


def is_sparse_solution(items, b, mode=0, length=None):
    """Exact check. length is needed under 0^0 = 1, where zeros weigh 1."""
    v = sum(x * b ** p for p, x in items.items())
    f = sum(x ** x for x in items.values() if x)
    if mode == 1:
        f += length - sum(1 for x in items.values() if x)
    return all(0 <= x < b for x in items.values()) and v == f


print("swap (4, 0^185, 256) in base 2048:", is_sparse_solution({186: 4, 0: 256}, 2048))
for a in (3, 5, 7):
    b = a ** ((a ** (a + 1) - 1) // 2)
    print(f"swap (a, 0, a^a), a={a}, base a^((a^(a+1)-1)/2):", is_sparse_solution({2: a, 0: a ** a}, b))

ok = True
for k in range(2, 30):
    for t in (2, 3, 4):
        r = t * (k - 1) + 1
        b = r ** t
        ok &= is_sparse_solution({k - 1: r}, b) and is_sparse_solution({k - 1: r, 0: 1}, b)
print("(r, 0, ..., 0) and (r, 0, ..., 1) with k digits, r = t(k-1)+1, base r^t, k = 2..29, t = 2..4:", ok)

for L in (2, 3, 4, 5):
    N = L * (2 ** L - 1)
    blocks = {}
    for j in range(1, 2 ** L - 1):
        s = j * L
        assert (s * (2 ** s - 1)) % N == 0
        blocks[s * (2 ** s - 1) // N] = s  # position -> exponent s of the digit 2^s
    if L <= 3:
        b = 2 ** N
        good = True
        count = 0
        for r in range(len(blocks) + 1):
            for sub in itertools.combinations(sorted(blocks), r):
                for e in (0, 1):
                    items = {p: 2 ** blocks[p] for p in sub}
                    if e:
                        items[0] = 1
                    if sub:
                        good &= is_sparse_solution(items, b)
                        count += 1
        print(f"base 2^{N}: {len(blocks)} self-paying digits, {count} nontrivial solutions checked exactly: {good}")
    else:
        # too large to write out: digit 2^s at position p is self-paying iff
        # s + N*p == s * 2^s (compare the exponents of 2)
        good = all(s + N * p == s * 2 ** s and s < N for p, s in blocks.items())
        print(f"base 2^{N}: {len(blocks)} self-paying digits (exponent check: {good}), "
              f"so at least {2 ** (len(blocks) + 1) - 2} nontrivial solutions")
