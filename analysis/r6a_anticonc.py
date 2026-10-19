"""Round 6, section 1: the dissociation bound of Theorem 1.3 made numeric.

Small digits z have exact integer weights g(z) = z^z - z. If n copies of
digits from Z = [z0, y] are drawn and n g(y) < Q, their sum modulo Q fixes
the counts (Lemma 1.2), so a residue has probability at most n!/J^n,
J = |Z|. This script

  1. checks g(z) >= 2 z g(z-1) for 3 <= z <= ZMAX (Lemma 1.1);
  2. for a modulus Q = 10^E and a digit share lambda = k/(M+1), picks
     y, z0 = ceil((y+1)/2), J = y - z0 + 1, and evaluates

        bound = P(N < n1) + P(N > 2 z0 + 1) + max_{n1 <= n <= 2 z0 + 1} n!/J^n,

     with Chernoff bounds for the binomial tails, N ~ Bin(k, J/(M+1)) of
     mean mu = lambda J, optimized over n1.

    python3 r6a_anticonc.py      -> data/r6a_anticonc.txt
"""
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def h(t):
    return t * math.log(t) - t + 1 if t > 0 else 1.0


def log_fact_over_pow(n, J):
    return math.lgamma(n + 1) - n * math.log(J)


def bound(logQ, lam):
    """logQ natural log of the modulus."""
    # largest y with (y + 3) y^y < Q
    y = 2
    while math.log(y + 4) + (y + 1) * math.log(y + 1) < logQ:
        y += 1
    z0 = math.ceil((y + 1) / 2)
    J = y - z0 + 1
    nmax = 2 * z0 + 1
    mu = lam * J
    up = math.exp(-mu * h(nmax / mu)) if nmax > mu else 1.0
    best = None
    step = max(1, int(mu) // 2000)
    for n1 in range(1, int(mu) + 1, step):
        lo = math.exp(-mu * h((n1 - 1) / mu)) if n1 - 1 < mu else 1.0
        # n!/J^n is log-convex in n, so its maximum on an interval is at an end
        mid = math.exp(max(log_fact_over_pow(n1, J), log_fact_over_pow(nmax, J)))
        tot = lo + up + mid
        if best is None or tot < best[0]:
            best = (tot, n1)
    if best is None:
        best = (1.0, 0)
    return y, z0, J, best[0], best[1]


def main():
    out = open(os.path.join(HERE, 'data', 'r6a_anticonc.txt'), 'w')
    # Lemma 1.1 check with exact integers
    worst = min(((z ** z - z) / (2 * z * ((z - 1) ** (z - 1) - (z - 1))), z)
                for z in range(3, 400))
    out.write('# Lemma 1.1: min over 3 <= z < 400 of g(z) / (2 z g(z-1)) = %.4f at z = %d\n'
              % worst)
    out.write('# log10 Q  lambda  y  z0  J  bound  n1\n')
    for E in [6, 10, 30, 100, 300, 1000, 3000, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 8]:
        for lam in [0.5, 1.0]:
            y, z0, J, bnd, n1 = bound(E * math.log(10), lam)
            out.write('%d %.1f %d %d %d %.3e %d\n' % (E, lam, y, z0, J, min(bnd, 1.0), n1))
    out.close()
    print(open(os.path.join(HERE, 'data', 'r6a_anticonc.txt')).read())


if __name__ == '__main__':
    main()
