"""Round 6, section 2.4: two-digit solutions and fixed points of x -> x^x.

By Proposition 2.6, (a, c) is a 2-digit solution exactly when a divides
w(c) - c (and the base is large enough). So the last digits that go with a
leading digit a are the fixed points of x -> x^x modulo a, the object of
Kurlberg, Luca and Shparlinski for prime a. This script computes

  f(a) = density of c >= 1 with c^c == c (mod a), over a full period,
  f(p) against the formula (1 + sum_{d | p-1} phi(d)/d) / p for primes,
  the census share of pairs (a, c), 1 <= a, c <= Y, that are solutions
  (under 0^0 = 1, with the size condition), against (1/Y) sum_{a <= Y} f(a),
  the primes p <= PMAX with no c in [2, p-1] with c^c == c (mod p).

    python3 r6a_twodigit.py Y PMAX   -> data/r6a_twodigit.txt
"""
import math
import os
import sys

from r6a_lib import factor, divisors, phi, primes_upto

HERE = os.path.dirname(os.path.abspath(__file__))


def carmichael(n):
    l = 1
    for p, a in factor(n).items():
        if p == 2 and a >= 3:
            t = 2 ** (a - 2)
        else:
            t = (p - 1) * p ** (a - 1)
        l = l * t // math.gcd(l, t)
    return l


def fdens(a):
    """density of c with c^c == c (mod a); c ranges over a period starting
    above the largest exponent in a, so that c mod a and c mod lambda(a) decide."""
    if a == 1:
        return 1.0
    L = a * carmichael(a) // math.gcd(a, carmichael(a))
    start = 64 * L            # beyond every exponent of a
    hit = 0
    for c in range(start, start + L):
        if pow(c, c, a) == c % a:
            hit += 1
    return hit / L


def main():
    Y, pmax = int(sys.argv[1]), int(sys.argv[2])
    out = open(os.path.join(HERE, 'data', 'r6a_twodigit.txt'), 'w')
    # prime formula check
    worst = 0.0
    for p in primes_upto(200):
        p = int(p)
        form = (1 + sum(phi(d) / d for d in divisors(p - 1))) / p
        worst = max(worst, abs(form - fdens(p)))
    out.write('# primes p <= 200: max |f(p) - (1 + sum phi(d)/d)/p| = %.2e\n' % worst)
    # census share against the mean of f
    F = [0.0] + [fdens(a) for a in range(1, Y + 1)]
    out.write('# Y  census share (0^0 = 1)  (1/Y) sum f(a)\n')
    for y in sorted(set([20, 40, 60, 100, 200, 300, 400, 600, Y])):
        if y > Y:
            continue
        sol = 0
        for a in range(1, y + 1):
            for c in range(0, y + 1):
                wc = 1 if c == 0 else c ** c
                if (wc - c) % a == 0:
                    b = (a ** a + wc - c) // a
                    if b > max(a, c):
                        sol += 1
        share = sol / (y * (y + 1))
        out.write('%d %.4f %.4f\n' % (y, share, sum(F[1:y + 1]) / y))
    # primes without a nontrivial partner below p
    none = [int(p) for p in primes_upto(pmax) if p > 2 and
            not any(pow(c, c, int(p)) == c for c in range(2, int(p)))]
    out.write('# primes p <= %d with no c in [2, p-1], c^c == c (mod p): %d of %d\n'
              % (pmax, len(none), len(primes_upto(pmax)) - 1))
    out.write('# first ones: %s\n' % none[:30])
    sg = [p for p in none if p % 8 == 3 and all((p - 1) // 2 % r for r in range(2, int(((p - 1) // 2) ** 0.5) + 1))]
    out.write('# of these, p == 3 (mod 8) with (p-1)/2 prime: %d\n' % len(sg))
    out.close()
    print(open(os.path.join(HERE, 'data', 'r6a_twodigit.txt')).read())


if __name__ == '__main__':
    main()
