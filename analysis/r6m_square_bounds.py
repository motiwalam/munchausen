"""Bounds of Theorem 38.2 and Table 38.2.3.1 (chapter 38, square families).

For a middle family (p, x, q) with p*A = k^2 a perfect square and an odd
prime power x prime to 2k, a solution forces the integer k^a * Tr(w) to be
k^a * 2 sinh(t) (e odd) or k^a * 2 cosh(t) (e even), with
2ke - e (2 k^3 / x^2 + Lam0) <= t < 2ke.
So x^2 <= 2 e k^3 / (g- - e Lam0), where g- = 2ke - f^{-1}(floor f(2ke)),
provided e Lam0 < g+ = f^{-1}(floor f(2ke) + 1) - 2ke.

Prints, for every family with p, q <= 20 and p*A a square, the numbers
k, e, a, f(2ke), the gap g and the bound X_sq.

Usage: python r6m_square_bounds.py [B]
"""
import sys
from math import gcd
import mpmath as mp


def w(d, m):
    return m if d == 0 else d ** d


def isqrt_exact(n):
    import math
    r = math.isqrt(n)
    return r if r * r == n else None


def vals(n):
    out = {}
    l = 2
    while l * l <= n:
        while n % l == 0:
            out[l] = out.get(l, 0) + 1
            n //= l
        l += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def ea(p, k):
    """Least e >= 1, a >= 0 with e v_l(p) = a v_l(k) for all l | k."""
    vk = vals(k)
    vp = vals(p)
    if p == 1:
        return 1, 0
    for l in vp:
        if l not in vk:
            return None
    for e in range(1, 200):
        for a in range(0, 400):
            if all(e * vp.get(l, 0) == a * vk[l] for l in vk):
                return e, a
    return None


def bound(k, e, a):
    T = 2 * k * e
    mp.mp.dps = int(T / 2.3) + 60
    if e % 2:
        f = lambda t: k ** a * 2 * mp.sinh(t)
        finv = lambda v: mp.asinh(v / (2 * k ** a))
    else:
        f = lambda t: k ** a * 2 * mp.cosh(t)
        finv = lambda v: mp.acosh(v / (2 * k ** a))
    fT = f(T)
    N0 = mp.floor(fT)
    g = T - finv(N0)
    gplus = finv(N0 + 1) - T
    X = mp.sqrt(2 * e * mp.mpf(k) ** 3 / g)
    return fT, N0, g, gplus, X


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seen = {}
    for m in (1, 0):
        for p in range(1, B + 1):
            for q in range(0, B + 1):
                if q > 0 and m == 0:
                    continue
                A = w(p, m) + w(q, m) - q
                k = isqrt_exact(p * A)
                if k is None:
                    continue
                conv = "both" if q > 0 else f"0^0={m}"
                seen.setdefault((p, A, k), []).append(f"({p},x,{q}) {conv}")
    print("# middle families with p, q <= %d and p*A = k^2" % B)
    print("# columns: p A k e a | families | f(2ke) | gaps g-, g+ | X_sq = sqrt(2 e k^3 / g-)")
    for (p, A, k), fams in sorted(seen.items()):
        r = ea(p, k)
        if r is None:
            print(p, A, k, "e,a: none (not proportional)", fams)
            continue
        e, a = r
        print(f"p={p} A={A} k={k} e={e} a={a} | {'; '.join(fams)}")
        if 2 * k * e > 4000:
            print(f"   2ke = {2 * k * e}: X_sq is about exp(ke), not computed")
            continue
        fT, N0, g, gplus, X = bound(k, e, a)
        print(f"   f(2ke) = {mp.nstr(fT, 25)}   frac = {mp.nstr(fT - N0, 6)}")
        print(f"   g- = {mp.nstr(g, 6)}   g+ = {mp.nstr(gplus, 6)}   X_sq = {mp.nstr(X, 8)}")


if __name__ == "__main__":
    main()
