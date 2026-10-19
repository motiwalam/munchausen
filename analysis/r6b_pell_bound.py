"""Round 6, basics: an explicit bound for 3-digit strings with an even digit.

Let p = n f^2 with n > 1 squarefree, and let x be even. A string (p, q, x)
or (p, x, q) is a solution in base b exactly when

    U^2 - n V^2 = R,   V = 2 f x^(x/2),

with U = 2 p b + q (last) or U = 2 p b + x (middle) and
R = q^2 + 4p (w(p) + w(q) - x)   (last),
R = x^2 + 4p (w(p) + w(q) - q)   (middle).
The field Q(sqrt n) does not depend on x. 2^(x/2) divides V, so the element
U - V sqrt(n) of norm R is 2-adically close to its conjugate, and the bound
of Bugeaud and Laurent for two 2-adic logarithms (Theorem 2.1 of Bennett and
Bugeaud, Acta Arith. 155 (2012)) gives

    x/2 + 2 - log2|R| <= C g D^4 max(log b' + log log 2 + 0.4, 10)^2
                         * log A1 * log A2,

with C = 24 * 2 / (log 2)^4, D = 2, g <= 3, log A1 = log(|R| eta),
log A2 = log eta, b' = 1/(2 log A2) + |m|/(2 log A1) and
|m| <= (log(4 f sqrt n) + (x/2) log x) / log eta + 1/2.
Here eta is the fundamental unit of the ring of integers of Q(sqrt n).
This script finds the largest even x that satisfies the inequality, for every
non-square p <= P and q <= Q, both positions and both conventions.

usage: r6b_pell_bound.py P Q [sq]   prints "p q pos m n eta_log X0"
With "sq" it prints instead the bound T0 on t for odd square x = t^2
(t0_square below).
"""
import math
import sys


def squarefree_part(p):
    n, f, d = p, 1, 2
    while d * d <= n:
        while n % (d * d) == 0:
            n //= d * d
            f *= d
        d += 1
    return n, f


def unit(n):
    """The fundamental unit (a + b sqrt n) / k of the integers of Q(sqrt n)."""
    # smallest unit > 1, with k = 2 for n == 1 (mod 4)
    k = 2 if n % 4 == 1 else 1
    b = 1
    while True:
        for s in (-1, 1):
            a2 = n * b * b + s * k * k
            a = math.isqrt(a2)
            if a * a == a2 and a > 0:
                return a, b, k
        b += 1


def unit_log(n):
    a, b, k = unit(n)
    return math.log((a + b * math.sqrt(n)) / k)


def nu2_eta12(n):
    """An upper bound for v(eta^12 - 1) at a prime above 2: v_2 of its norm."""
    a, b, k = unit(n)
    # (a + b sqrt n)^12 = A + B sqrt n, exactly; eta^12 = (A + B sqrt n) / k^12
    A, B = 1, 0
    for _ in range(12):
        A, B = A * a + B * b * n, A * b + B * a
    K = k ** 12
    N = ((A - K) ** 2 - n * B * B) // (K * K)  # norm of eta^12 - 1, an integer
    v = 0
    while N % 2 == 0:
        N //= 2
        v += 1
    return v


def w(d, m):
    return m if d == 0 else d ** d


def x0(p, q, pos, m, lam):
    n, f = squarefree_part(p)
    C = 24 * 2 / math.log(2) ** 4 * 3 * 2 ** 4
    la2 = max(lam, math.log(2) / 2)

    def rup(x):
        if pos == 'last':
            return q * q + 4 * p * (w(p, m) + w(q, m) + x)
        return x * x + 4 * p * (w(p, m) + w(q, m) + q)

    def ok(x):
        # True if x is not excluded by the bound. R is replaced by an upper
        # bound for |R| that grows with x: log A1 may be any upper bound for
        # the height, and log2|R| enters the left side with a minus sign
        R = rup(x)
        la1 = max(math.log(R) + lam, math.log(2) / 2)
        # |m| log eta <= log(2 V sqrt(n) + 1) + (log eta)/2, V = 2 f x^(x/2)
        mm = (math.log(4 * f * math.sqrt(n)) + x / 2 * math.log(x) + 1e-6) / lam + 0.5
        bp = 1 / (2 * la2) + mm / (2 * la1)
        rhs = C * max(math.log(bp) + math.log(math.log(2)) + 0.4, 10) ** 2 * la1 * la2
        lhs = x / 2 + 2 - math.log2(R)
        return lhs <= rhs

    # ok(x) is true for small x and false beyond a threshold; bisect on a
    # doubling bracket, then confirm that the inequality fails past it
    hi = 4
    while ok(hi):
        hi *= 2
    lo = hi // 2
    while hi - lo > 2:
        mid = (lo + hi) // 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    for t in range(hi, 4 * hi, max(1, hi // 1000)):
        assert not ok(t), (p, q, pos, m, t)
    X0 = lo + (lo % 2)

    # The two side cases of the proof give much smaller bounds; check that
    # X0 covers them. (a) delta-bar/delta = +-1: then v(eta^(4m) - 1) is at
    # least x/2 + 2 - log2|R| and at most v(eta^12 - 1) + log2|m|.
    # (b) m = 0: then V sqrt(n) < (|R| eta)^(1/2).
    c12 = nu2_eta12(n)

    def side(x):
        R = rup(x)
        mm = (math.log(4 * f * math.sqrt(n)) + x / 2 * math.log(x) + 1e-6) / lam + 0.5
        a = x / 2 + 2 - math.log2(R) <= c12 + math.log2(mm)
        b = math.log(2 * f * math.sqrt(n)) + x / 2 * math.log(x) < (math.log(R) + lam) / 2
        return a or b

    for x in range(X0, 4 * X0, max(1, X0 // 1000)):
        assert not side(x), (p, q, pos, m, x)
    return X0


def main():
    P, Q = int(sys.argv[1]), int(sys.argv[2])
    bound = t0_square if sys.argv[3:] == ['sq'] else x0
    for p in range(2, P + 1):
        n, f = squarefree_part(p)
        if n == 1:
            continue
        lam = unit_log(n)
        for q in range(0, Q + 1):
            for pos in ('last', 'mid'):
                for m in (0, 1):
                    if q > 0 and m == 1:
                        continue  # the conventions differ only when q = 0
                    print(p, q, pos, m if q == 0 else '-', n, f'{lam:.4f}',
                          bound(p, q, pos, m, lam))



def t0_square(p, q, pos, m, lam):
    """The bound for odd square x = t^2, from Matveev's theorem.

    Then x^x = (t^x)^2 and V = 2 f t^x. With beta' = U + V sqrt n = delta' eta'^m,
    Lambda = log(4 f sqrt n) + x log t - log|delta'| + m' log eta
    equals log|1 - beta/beta'|, so |Lambda| <= 2 |R| / (n V^2). Matveev
    (Izv. Math. 64 (2000), Corollary 2.3) for four logarithms in a real
    field of degree D = 2 gives
    log|Lambda| > -1.4 30^7 4^4.5 D^2 (1 + log D) (1 + log B) A1 A2 A3 A4,
    with A1 = log(16 f^2 n), A2 = 2 log t, A3 = log(|R| eta), A4 = log eta
    and B = max(x, |m|). Returns the largest odd t not excluded.
    """
    n, f = squarefree_part(p)
    C = 1.4 * 30 ** 7 * 4 ** 4.5 * 4 * (1 + math.log(2))

    def ok(t):
        x = t * t
        if pos == 'last':
            R = q * q + 4 * p * (w(p, m) + w(q, m) + x)
        else:
            R = x * x + 4 * p * (w(p, m) + w(q, m) + q)
        lt = math.log(t)
        mm = (math.log(4 * f * math.sqrt(n)) + x * lt + 1e-6) / lam + 0.5
        B = max(x, mm)
        A = (math.log(16 * f * f * n), 2 * lt, math.log(R) + lam, max(lam, 0.16))
        A = [max(a, 0.16) for a in A]
        rhs = C * (1 + math.log(B)) * A[0] * A[1] * A[2] * A[3]
        lhs = 2 * x * lt - math.log(2 * R) + math.log(4 * f * f * n)
        return lhs <= rhs

    hi = 3
    while ok(hi):
        hi *= 2
    lo = hi // 2
    while hi - lo > 2:
        mid = (lo + hi) // 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    for t in range(hi, 4 * hi, max(1, hi // 1000)):
        assert not ok(t), (p, q, pos, m, t)
    return lo + 1 - (lo % 2)


if __name__ == '__main__':
    main()
