"""Bounds for b (b + x) = x^n + 1 when the ideal B is principal or of order d.

Section 1.5 of docs/library/drafts/round2-number-theory.md. For odd x and
n odd, (b + eps) = B^n. If B^d = (eta) then
    Lam = |b1 log eta0 - (n/d) log w| < tau_n,   w = |eta/eta'| > 1,
with log A1 = max(mu0, 1)/2, log A2 = (d log x + mu0)/2 (an upper bound for
the height of w), b1 <= n/d + 1. Laurent (m = 10, C = 25.2, D = 2) then
bounds n. The worst case is mu0 = log eps.

usage: python3 analysis/r2nt_principal.py
prints (1) the largest x with a principal solution of n = x (question 12),
(2) n_max(x) for principal B on a grid, (3) n_max(x, d).
"""
from mpmath import mp, mpf, log, sqrt

mp.dps = 40
C2 = 403.2


def log_tau(x, n):
    return log(sqrt(mpf(x) ** 2 + 4)) - log(mpf(x) ** (mpf(n) / 2) - mpf(x) / 2 - 1)


def allowed(x, n, d=1):
    """True if Laurent does not exclude exponent n (B^d principal)."""
    eps = (x + sqrt(mpf(x) ** 2 + 4)) / 2
    mu0 = log(eps)
    lA1 = max(mu0, 1) / 2
    lA2 = (d * log(x) + mu0) / 2
    m = mpf(n) / d
    bp = (m + 1) / (2 * lA2) + m / (2 * lA1)
    M = max(log(bp) + mpf('0.38'), 5)
    return log_tau(x, n) >= -C2 * M * M * lA1 * lA2


def nmax(x, d=1):
    lo = max(5, d)
    if not allowed(x, lo, d):
        return None
    hi = lo
    while allowed(x, hi, d):
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if allowed(x, mid, d):
            lo = mid
        else:
            hi = mid
    return lo


def main():
    # (1) n = x
    lo, hi = 9, 10 ** 9
    assert allowed(lo, lo) and not allowed(hi, hi)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if allowed(mid, mid):
            lo = mid
        else:
            hi = mid
    print('n = x, B principal: Laurent allows x only up to', lo)
    for x in (10 ** 7, 10 ** 8, 4 * 10 ** 9):
        print('  check: x =', x, 'allowed:', allowed(x, x))
    # (2) principal: n_max(x)
    print('principal B: n_max(x), and n_max / (log x (log log x)^2)')
    for e in range(1, 31, 3):
        x = 10 ** e + 1
        nm = nmax(x)
        print(f'  x = 1e{e}: n_max = {nm}, ratio {float(nm / (log(x) * log(log(x)) ** 2)):.1f}')
    # (3) class of order d
    print('B of order d: n_max(x, d) / d')
    for x in (10 ** 3 + 1, 10 ** 6 + 1, 10 ** 12 + 1):
        print('  x =', x, [(d, nmax(x, d)) for d in (1, 3, 5, 15, 101, 1001)])


if __name__ == '__main__':
    main()
