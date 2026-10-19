"""Question 101: averaging over bases with the small digits compressed.

Section 20.1.3 bounds the number of bases b <= B with a solution of 2..K
digits by the sum over k of C(X_k + k, k) k ((X_k + 1) H_k / (k-1) + k)
(Proposition 20.2). Question 101 averages over the bases: split the digits
into large ones and small ones (z^z * k < sqrt(B) - 1, so for b > sqrt(B)
the small part of m(c) = F(c) - S(c) is below b - 1). For fixed large part
and base, b - 1 | m(c) leaves at most 2 values of the small part, and the
number of small multisets with a given value is at most r_j, bounded by
dissociation (Lemma 30.2): digits from z0 = max(2, ceil((j-1)/2)) up are
fixed by the value once the digits below z0 are fixed, so
r_j <= C(z0 + j, j).

The averaged bound is

    sqrt(B) + sum_k sum_j C(X_k - z + k - j - 1, k - j) min(C(z + j, j), 2 r_j)
                       * ((X_k + 1) H_k / (k - 1) + 2 k),

the window of the large part being one base wider for each leading digit.

Prints, for B = 10^E, both bounds as powers of B and the largest K below B,
and the share of multisets of K digits with no digit <= z (Proposition 35.9).

    python3 r6h_average.py > data/r6h_average.txt
"""
import math
import sys


def lc(n, k):
    """log of C(n, k)"""
    if k < 0 or k > n:
        return float('-inf')
    return math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)


def xk(LB, k):
    """largest X with X ln X < k ln B (as r3nt_multiset.xk)"""
    t = k * LB
    lo, hi = 1.0, max(3.0, t)
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid * math.log(mid) < t:
            lo = mid
        else:
            hi = mid
    return math.floor(lo)


def lse(vals):
    vals = [v for v in vals if v > float('-inf')]
    if not vals:
        return float('-inf')
    m = max(vals)
    return m + math.log(sum(math.exp(v - m) for v in vals))


def bounds(LB, K, z):
    plain, avg = [], []
    for k in range(2, K + 1):
        X = xk(LB, k)
        H = sum(1.0 / i for i in range(1, k + 1))
        win = math.log((X + 1) * H / (k - 1) + k)
        win1 = math.log((X + 1) * H / (k - 1) + 2 * k)
        plain.append(lc(X + k, k) + win)
        terms = []
        for j in range(0, k + 1):
            large = lc(X - z + k - j - 1, k - j) if k - j > 0 else 0.0
            small_all = lc(z + j, j)
            z0 = max(2, math.ceil((j - 1) / 2))
            small = min(small_all, math.log(2) + lc(min(z0, z + 1) + j, j))
            terms.append(large + small)
        avg.append(lse(terms) + win1)
    return lse(plain), lse([0.5 * LB] + avg)


def main():
    print("# E K z: log_B of the bound of Proposition 20.2 (plain) and of the averaged bound; "
          "share of K-digit multisets with no digit <= z")
    for E in (96, 1000):
        LB = E * math.log(10)
        z = 1
        while (z + 1) * math.log(z + 1) + math.log(60) < 0.5 * LB:
            z += 1
        lastp = lasta = None
        for K in (range(10, 70) if E == 96 else range(300, 380, 2)):
            p, a = bounds(LB, K, z)
            X = xk(LB, K)
            share = math.exp(lc(X - z - 1 + K, K) - lc(X + K, K))
            if p < LB:
                lastp = K
            if a < LB:
                lasta = K
            if E == 96 or K % 10 == 0:
                print(f"{E} {K} {z} plain B^{p / LB:.4f} averaged B^{a / LB:.4f} share {share:.3f} "
                      f"(K z / X = {K * z / X:.2f})", flush=True)
        print(f"# E={E}: largest K below B: plain {lastp}, averaged {lasta}")


if __name__ == '__main__':
    main()
