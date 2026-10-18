"""Pure solutions of b (b + x) = x^n + 1 for odd x (question 32).

Notation of docs/library/drafts/round2-number-theory.md, section 1.
eps = (x + sqrt(x^2+4))/2, eta0 = eps^(1/r) the fundamental unit,
mu0 = log eta0, z = (eps+1)/(eps-1). A pure solution with n odd satisfies
    Lam = |n log z - s mu0| < tau_n,   s odd,
    tau_n = sqrt(x^2+4) / (x^(n/2) - x/2 - 1).
Laurent's two-log bound (Corollary 2, m = 10, C = 25.2, d = 2) gives n <= n_hi(x).

For every odd non-square x <= X the script
  1. checks n = 5, 7, ..., 15 exactly (4x^n + x^2 + 4 a square),
  2. checks n * tau_n < mu0 / 2 for n >= 17, so that s/n reduced is a
     convergent of beta = log z / mu0 (Legendre),
  3. runs through the convergents p/q of beta with q <= n_hi(x) and tests
     |q log z - p mu0| < tau_q (the test for multiples g q is implied),
  4. checks exactly every candidate.
It prints every x where a candidate appears and the largest n_hi.

usage: python3 analysis/r2nt_pure.py X
"""
import sys
import gmpy2
from mpmath import mp, mpf, sqrt, log, sinh, nint

mp.dps = 60
C2 = 403.2  # 25.2 * d^4 with d = 2


def lucas_V(r, y):
    # trace of ((y + sqrt(y^2+4))/2)^r: V_0 = 2, V_1 = y, V_k = y V_(k-1) + V_(k-2)
    a, b = 2, y
    for _ in range(r - 1):
        a, b = b, y * b + a
    return b if r >= 1 else a


def unit_root(x, mu):
    """largest odd r with x = V_r(y) for an integer y >= 1"""
    best = 1
    r = 3
    while r * 0.48 <= mu + 1:
        y = int(nint(2 * sinh(mu / r)))
        if y >= 1 and lucas_V(r, y) == x:
            best = r
        r += 2
    return best


def log_tau(x, n):
    D = x * x + 4
    return log(sqrt(D)) - log(mpf(x) ** (mpf(n) / 2) - mpf(x) / 2 - 1)


def n_high(x, mu0, lz):
    lA1 = max(mu0 / 2, mpf(1) / 2)
    lA2 = max(log(x * ((mpf(1) + 1 / ((x + sqrt(x * x + 4)) / 2)) / (1 - 1 / ((x + sqrt(x * x + 4)) / 2)))) / 2, mpf(1) / 2)

    def ok(n):  # True if Laurent does not exclude n
        lt = log_tau(x, n)
        s = (n * lz + mp.e ** lt) / mu0
        bp = s / (2 * lA2) + n / (2 * lA1)
        M = max(log(bp) + mpf('0.38'), 5)
        return lt >= -C2 * M * M * lA1 * lA2

    lo = 17
    if not ok(lo):
        return lo - 2
    hi = lo
    while ok(hi):
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    # monotonicity: past lo the left side drops by (log x)/2 per step, the right
    # side by at most 2 C2 M lA1 lA2 / b' per step; checked below
    return lo


def convergents(beta, qmax):
    p0, q0, p1, q1 = 0, 1, 1, 0
    a = beta
    out = []
    for _ in range(200):
        ai = int(mp.floor(a))
        p0, q0, p1, q1 = p1, q1, ai * p1 + p0, ai * q1 + q0
        if q1 > qmax:
            break
        out.append((p1, q1))
        frac = a - ai
        if frac == 0:
            break
        a = 1 / frac
    return out


def main():
    X = int(sys.argv[1])
    worst = (0, 0)
    found = []
    for x in range(3, X + 1, 2):
        if gmpy2.is_square(x):
            continue
        for n in range(5, 16, 2):
            if gmpy2.is_square(4 * gmpy2.mpz(x) ** n + x * x + 4):
                found.append((x, n, 'direct'))
        D = x * x + 4
        eps = (x + sqrt(D)) / 2
        mu = log(eps)
        r = unit_root(x, mu)
        mu0 = mu / r
        lz = log((eps + 1) / (eps - 1))
        assert 17 * mp.e ** log_tau(x, 17) < mu0 / 2
        nh = n_high(x, mu0, lz)
        if nh > worst[0]:
            worst = (nh, x)
        beta = lz / mu0
        t5 = mp.e ** log_tau(x, 5)
        for p, q in convergents(beta, nh):
            # n = g q with g >= 1; the gap grows like g and tau_n falls, so
            # g = 1 decides unless q is below 17 (then compare with tau_5)
            gap = abs(q * lz - p * mu0)
            bound = mp.e ** log_tau(x, q) if q >= 5 else t5
            if gap < bound + mpf(10) ** -40:
                for g in range(1, nh // q + 1):
                    n = g * q
                    if n < 17 or n % 2 == 0 or (g * p) % 2 == 0:
                        continue
                    if g * gap >= mp.e ** log_tau(x, n):
                        break
                    ok = gmpy2.is_square(4 * gmpy2.mpz(x) ** n + x * x + 4)
                    found.append((x, n, 'candidate', g * p, ok))
        if x % 20001 == 0:
            print('progress', x, 'max n_hi', worst, flush=True)
    print('X =', X, 'largest n_hi =', worst)
    print('hits:', found)


if __name__ == '__main__':
    main()
