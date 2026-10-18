"""Positive against negative roots of 3-digit Q_s (question 34), 0^0 = 1.

For s = (p, q, r), Q_s(t) = p t^2 + q t + r - F with discriminant
Delta = q^2 + 4 p (F - r). The roots t+ > 0 > t- have the same |Q_s'| =
sqrt(Delta) and the same residues mod every prime, so the root heuristic
of section 11.4 gives them equal weight. The script measures, over all
strings with digits <= D:
  - the local-factor heuristic E+ and E- for roots beyond the digits,
    split by square class (4 p w(d*) a perfect square, d* the digit of
    largest weight) and by s_1 | s_2;
  - the near-integer counts #{||t+|| < eta} and #{||t-|| < eta};
  - for the square class the offset delta = (sqrt(Delta) - Y) / (2p),
    which decides the two roots: t+ is an integer when
    delta == q/(2p) mod 1, t- when delta == -q/(2p) mod 1.

usage: python3 analysis/r2nt_negroots.py D
"""
import sys
from collections import Counter
import gmpy2
from gmpy2 import mpz

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
BITS = 64


def w(d):
    return 1 if d == 0 else d ** d


def rho(p_, q_, c_, m):
    return sum(1 for t in range(m) if (p_ * t * t + q_ * t + c_) % m == 0)


def frac_roots(p, q, Delta):
    """t+ and t- as exact floats with BITS fractional bits (as Fractions)."""
    sq = gmpy2.isqrt(Delta << (2 * BITS))  # sqrt(Delta) * 2^BITS, floor
    one = mpz(1) << BITS
    tp = (sq - q * one) / mpz(2 * p)      # mpq-free: use floats of big ints
    tm = (-sq - q * one) / mpz(2 * p)
    return tp / one, tm / one, sq


def dist(t):
    f = t - gmpy2.floor(t)
    return min(f, 1 - f)


def main():
    D = int(sys.argv[1])
    gmpy2.get_context().precision = 2000
    W = [mpz(w(d)) for d in range(D + 1)]
    E = Counter()
    near = Counter()
    hits = []
    offs = Counter()
    R = Counter()
    for p in range(1, D + 1):
        for q in range(D + 1):
            for r in range(D + 1):
                F = W[p] + W[q] + W[r]
                M = max(p, q, r)
                Delta = q * q + 4 * p * (F - r)
                c = r - F
                dstar = max((p, q, r), key=lambda d: W[d])
                Y2 = 4 * p * W[dstar]
                sqc = gmpy2.is_square(Y2)
                cls = 'square' if sqc else 'other'
                part = 'partner' if q % p == 0 else 'nonpartner'
                S = 1
                for m in PRIMES:
                    S *= rho(p, q, c, m)
                    if S == 0:
                        break
                sd = gmpy2.sqrt(gmpy2.mpfr(Delta))
                tp = (-q + sd) / (2 * p)
                tm = (-q - sd) / (2 * p)
                for sign, t in (('+', tp), ('-', tm)):
                    if abs(t) <= M:
                        continue
                    if M >= 6:
                        E[(cls, part, sign)] += min(1.0, float(S / sd)) if S else 0.0
                    dd = dist(t)
                    for eta in (1e-2, 1e-3):
                        if dd < eta:
                            near[(cls, part, sign, eta)] += 1
                    if gmpy2.is_square(Delta):
                        num = (-q + gmpy2.isqrt(Delta)) if sign == '+' else (-q - gmpy2.isqrt(Delta))
                        if num % (2 * p) == 0:
                            hits.append((p, q, r, sign, int(num // (2 * p))))
                if sqc and part == 'nonpartner' and abs(tp) > M:
                    # refined heuristic: Delta is a square with probability
                    # 1/(2 sqrt(Delta)), and then sqrt(Delta) = Y + t* with
                    # t* the nearest integer, which fixes the sign of the
                    # integer root
                    Y = gmpy2.isqrt(Y2)
                    ts = int(gmpy2.rint(sd - Y))
                    wgt = float(1 / (2 * sd))
                    pos = 'lead' if dstar == p else 'inner'
                    if ts >= 1:
                        if (Y + ts - q) % (2 * p) == 0:
                            R[(pos, '+')] += wgt
                        if (Y + ts + q) % (2 * p) == 0:
                            R[(pos, '-')] += wgt
                    R[(pos, 'symmetric, per sign')] += wgt / (2 * p)
                    delta = (sd - Y) / (2 * p)
                    # which residue class mod 1 is delta closest to:
                    # q/(2p) gives t+, -q/(2p) gives t-
                    fp = dist(delta - gmpy2.mpfr(q) / (2 * p))
                    fm = dist(delta + gmpy2.mpfr(q) / (2 * p))
                    offs[('lead' if dstar == p else 'inner', 'delta<1' if delta < 1 else 'delta>=1', 'closer to +' if fp < fm else 'closer to -')] += 1
    print(f'digits <= {D}, 0^0 = 1')
    print('heuristic expectation (local factors, primes <= 31), roots beyond the digits:')
    for k in sorted(E):
        print('  ', k, f'{E[k]:.3e}')
    print('near-integer roots:')
    for k in sorted(near):
        print('  ', k, near[k])
    print('square class, position of delta = (sqrt(Delta) - Y)/(2p):')
    for k in sorted(offs):
        print('  ', k, offs[k])
    print('refined heuristic, square class, non-partner, roots beyond the digits:')
    print('  expected solutions with t+ (Y + t* == q mod 2p), with t- (== -q), and the symmetric value')
    for k in sorted(R):
        print('  ', k, f'{R[k]:.3e}')
    print('integer roots beyond the digits:', hits)


if __name__ == '__main__':
    main()
