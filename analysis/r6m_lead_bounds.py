"""Bounds for the leading position with x even (round 6, middle draft).

The string (x, q, r) with x even and q >= 1 is a solution exactly when
U^2 = 4 x^(x+1) + R, U = 2xb + q, R = q^2 + 4xA, A = w(q) + w(r) - r.
With theta = (q + sqrt R)/2 (norm -xA) the number nu = mu / theta^(x+1),
mu = (U + sqrt R)/2, is an S-unit for the primes above A*q
(Lemma M.5 of the draft). Two bounds follow.

  laurent   the family b(xb + 1) = x^x + 1 ((x,1,1), and (x,1,0) under
            0^0 = 0): S is empty and Laurent's bound for two logarithms
            gives an explicit X_L.
  matveev B every family with 1 <= q <= B, 0 <= r <= B: Matveev's bound
            with a reduced basis of the S-unit lattice (Theorem M.6).

Usage: python r6m_lead_bounds.py laurent
       python r6m_lead_bounds.py matveev B
"""
import sys
from math import log, sqrt, pi, gamma, exp
from sympy import factorint
import mpmath as mp


def w(d, m):
    return m if d == 0 else d ** d


def laurent_ok(x):
    """True if the inequality of Theorem M.7 allows this even x."""
    R = 4 * x + 1
    lx = log(x)
    alpha_log = 2.0001 / sqrt(R)          # log alpha, alpha = |theta/theta'|
    logA2 = 0.5 * (lx + alpha_log)        # h(alpha) = (1/2) log(x alpha)
    reg_max = sqrt(R) / 2 * (log(R) + 2)  # h Reg <= sqrt(Delta)/2 (log Delta + 2)
    lhs = (x + 1) / 2 * lx - log(2 * sqrt(R)) - 1e-9
    # the right side increases with Reg (checked on a grid below)
    best = 0.0
    for t in range(0, 201):
        reg = 0.4812 + (reg_max - 0.4812) * t / 200
        logA1 = max(reg, 1) / 2
        bprime = (x + 1) * alpha_log / (reg * 2 * logA2) + (x + 1) / (2 * logA1)
        M = max(log(bprime) + 0.38, 5)
        rhs = 25.2 * 16 * M * M * logA1 * logA2
        best = max(best, rhs)
    return lhs <= best


def laurent():
    lo, hi = 10.0, 1e20
    # find the largest x allowed by bisection on a log scale
    assert laurent_ok(1e6)
    assert not laurent_ok(1e18)
    for _ in range(200):
        mid = sqrt(lo * hi)
        if laurent_ok(mid):
            lo = mid
        else:
            hi = mid
    print("# Theorem M.7: b(xb + 1) = x^x + 1, x even")
    print(f"X_L = {hi:.6e}  (no even x above this passes the inequality)")
    for x in (1e9, 1e10, 1e11, 1e12, 1e13):
        print(f"  x = {x:.0e}: allowed by the inequality: {laurent_ok(x)}")


def matveev_x(A, q):
    """Largest x allowed by the Matveev inequality for a family."""
    fac = factorint(A * q)
    nS = 2 * len(fac)
    prodlog = 1.0
    for l in fac:
        prodlog *= max(log(l) ** 2, 2 * log(l))
    r = 1 + nS
    s = r + 1
    Vr = pi ** (r / 2) / gamma(r / 2 + 1)
    # Minkowski II: independent v_i with |v_i| = lambda_i, prod lambda_i
    # <= Kr covol; they span a sublattice of index N <= Kr.
    Kr = 2 ** r / Vr
    C = 1.4 * 30 ** (s + 3) * s ** 4.5 * 4 * (1 + log(2))

    def ok(lx):
        # everything in logarithms; x = e^lx
        x = mp.e ** lx
        R = q * q + 4 * x * A
        lR = mp.log(R)
        log_reg_h = lR / 2 + mp.log(mp.log(4 * R) + 2)   # sqrt(Delta)/2 (log Delta + 2)
        log_prodA = (r * mp.log(mp.sqrt(r + 1) / 2) + mp.log(Kr)
                     + mp.log(mp.sqrt(2 + nS)) + log_reg_h + mp.log(prodlog))
        Ath = lx + mp.log(A) + 1
        # B' = max(N (x + 1), |m_i|), N <= Kr, |m_i| <= N |phi| Kr / lambda_1
        logBp = mp.log(Kr * max(x + 1, Kr * mp.sqrt(r + 1) / 0.96 * 4 * (x + 1)
                                * (2 * lx + mp.log(A))))
        lhs = (x + 1) / 2 * lx - mp.log(3) - lR / 2
        log_rhs = mp.log(C) + mp.log(1 + logBp) + log_prodA + mp.log(Ath)
        return lhs <= 0 or mp.log(lhs) <= log_rhs

    lo, hi = 5.0, 5000.0
    if not ok(lo):
        return 0.0, nS
    for _ in range(100):
        mid = (lo + hi) / 2
        if ok(mid):
            lo = mid
        else:
            hi = mid
    return hi / log(10), nS


def matveev(B):
    print("# Theorem M.6: log10 of the bound X_M for (x, q, r), x even, q >= 1")
    print("# q r m  A  |S|max  log10(X_M)")
    worst = 0
    for q in range(1, B + 1):
        for r in range(0, B + 1):
            for m in ((0, 1) if r == 0 else (1,)):
                A = w(q, m) + w(r, m) - r
                lx, nS = matveev_x(A, q)
                worst = max(worst, lx)
                print(q, r, m, A, nS, f"{lx:.2f}")
    print(f"# largest log10(X_M): {worst:.2f}")


if __name__ == "__main__":
    if sys.argv[1] == "laurent":
        laurent()
    else:
        matveev(int(sys.argv[2]))
