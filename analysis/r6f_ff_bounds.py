"""Round 6, field families: bounds for a large odd last digit.

For the string (p, q, x) with x odd and x > W + q^2/(4p), W = w(p) + w(q),

    U^2 + D = 4 p x^x,   U = 2 p b + q,   D = 4p (x - W) - q^2 > 0,

and mu = (U + sqrt(-D))/2 lies in the imaginary quadratic field
K = Q(sqrt(-D)). Write (mu) = J A^x with N(A) = x. Two bounds on x:

Bound A (J ambiguous, primitive divisors). Theorem 36.5. Let t, n be as in its proof,
x = t n, n odd, t <= h(K).
  n >= 7: x <= (14/13) (sqrt(D)/pi) (log 4D + 2)
  n <= 5: x <= 5 (2 sqrt(D)/pi) (log 4D + 2)
with D < 4 p x. X_A(p) is the largest x allowed by either.

Bound B (any J, Matveev with three logarithms).
  (x/2) log x - (1/2) log(8x)
     <= 2^38 * 4 * (1 + log 2) * (1 + log Bc) * pi * (4/sqrt 3) * e * ws * log x
with e <= (2 sqrt(D)/pi)(log 4D + 2), ws = max(log p + log D, pi),
Bc = 5 x log x + 5 ws + 6, D = 4 p x.
X_B(p) is the largest x allowed. Neither bound depends on q.

Proposition (leading position, x even, square part). Write x = n f^2 with
n > 1 squarefree. The 2-adic inequality of Theorem 32.2 holds for
(x, q, r) with eta the fundamental unit of Q(sqrt n) and
R = q^2 + 4x (w(q) + w(r) - r). With log eta <= sqrt(n) (log 4n + 2) it
bounds f^2 = x/n; lead_square_part(B, x) is the largest f^2 it allows.

usage: r6f_ff_bounds.py [P]   prints p, X_A(p), X_B(p) for p <= P (default 20)
       r6f_ff_bounds.py lead B   prints the square-part bound for q, r <= B
"""
import math
import sys


def hbound(D):
    """Upper bound for the class number of Q(sqrt(-D)): |Delta| <= 4D."""
    d = 4 * D
    return math.sqrt(d) / math.pi * (math.log(d) + 2)


def allowed_A(x, p):
    D = 4 * p * x
    big_n = (14 / 13) * math.sqrt(D) / math.pi * (math.log(4 * D) + 2)
    small_n = 5 * hbound(D)
    return x <= max(big_n, small_n)


def allowed_B(x, p):
    D = 4 * p * x
    lx = math.log(x)
    ws = max(math.log(p) + math.log(D), math.pi)
    Bc = 5 * x * lx + 5 * ws + 6
    lhs = x / 2 * lx - 0.5 * math.log(8 * x)
    rhs = (2.0 ** 38 * 4 * (1 + math.log(2)) * (1 + math.log(Bc)) * math.pi
           * (4 / math.sqrt(3)) * hbound(D) * ws * lx)
    return lhs <= rhs


def largest(allowed, p, lo=25.0):
    """Largest x allowed, by stepping a factor 1.01 and then bisection.

    The allowed set is an initial interval: beyond the crossing the left
    side grows like x log x and the right side like sqrt(x) times logs.
    The script checks this by stepping on to 1000 times the crossing.
    """
    x = lo
    while allowed(x * 1.01, p):
        x *= 1.01
    a, b = x, x * 1.01
    for _ in range(200):
        m = (a + b) / 2
        if allowed(m, p):
            a = m
        else:
            b = m
    y = b
    while y < 1000 * b:
        assert not allowed(y, p), (p, y)
        y *= 1.05
    return math.floor(a)


def lead_rhs_ok(x, n, f, R, lam):
    """Theorem 32.2's inequality at x, with log eta = lam; True if allowed."""
    C = 24 * 2 / math.log(2) ** 4 * 3 * 2 ** 4
    la2 = max(lam, math.log(2) / 2)
    la1 = max(math.log(R) + lam, math.log(2) / 2)
    mm = (math.log(4 * f * math.sqrt(n)) + x / 2 * math.log(x) + 1e-6) / lam + 0.5
    bp = 1 / (2 * la2) + mm / (2 * la1)
    rhs = C * max(math.log(bp) + math.log(math.log(2)) + 0.4, 10) ** 2 * la1 * la2
    main = x / 2 + 2 - math.log2(R) <= rhs
    # the side cases of the proof of Theorem 32.2: (a) a_1 = +-1, with
    # v(eta^12 - 1) <= log2 |N(eta^12 - 1)| <= 12 lam / log 2 + 2;
    # (b) m = 0, so V sqrt(n) < (|R| eta)^(1/2)
    side_a = x / 2 + 2 - math.log2(R) <= 12 * lam / math.log(2) + 2 + math.log2(mm)
    side_b = math.log(2 * f * math.sqrt(n)) + x / 2 * math.log(x) < (math.log(R) + lam) / 2
    return main or side_a or side_b


def lead_square_part(B, x):
    """Largest F = f^2 (a power of 1.01) such that some n = x/F and some
    log eta in [0.48, sqrt(n)(log 4n + 2)] satisfy the inequality."""
    R = B * B + 4 * x * (2 * B ** B + B)

    def allowed(F):
        n = x / F
        if n < 2:
            return True
        top = math.sqrt(n) * (math.log(4 * n) + 2)
        lam = 0.48
        while lam < top * 1.01:
            if lead_rhs_ok(x, n, math.sqrt(F), R, min(lam, top)):
                return True
            lam *= 1.05
        return False

    F = 1.0
    while F < x / 2 and allowed(F * 1.01):
        F *= 1.01
    # the allowed set is an initial segment: check a stretch beyond F
    G = F * 1.02
    while G < min(x / 2, 100 * F):
        assert not allowed(G), (x, G)
        G *= 1.1
    return F


def main():
    if sys.argv[1:2] == ["lead"]:
        B = int(sys.argv[2])
        print("x F_max F_max/(log x)^4")
        for k in (6, 9, 12, 20, 30, 50, 100):
            x = 10.0 ** k
            F = lead_square_part(B, x)
            print("1e%d %.4g %.1f" % (k, F, F / math.log(x) ** 4))
        return
    P = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    print("p X_A X_B")
    for p in range(1, P + 1):
        print(p, largest(allowed_A, p), "%.3e" % largest(allowed_B, p))


if __name__ == "__main__":
    main()
