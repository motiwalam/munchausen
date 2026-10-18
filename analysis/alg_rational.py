"""Rational non-integer roots of Q_s (question 11).

For every string of length k with digits up to M, both conventions, find the
rational roots p/q of Q_s with q > 1 (PARI factor; by the rational root
theorem q divides the leading digit). Sort them into r > max(s), 0 < r <= max(s)
and r < 0, and print every root above the largest digit.
usage: python3 alg_rational.py k M
"""
import sys
import itertools
from collections import Counter
import cypari2

pari = cypari2.Pari()

if __name__ == '__main__':
    k, M = int(sys.argv[1]), int(sys.argv[2])
    count = Counter()
    for m in (1, 0):
        W = [m] + [x**x for x in range(1, M + 1)]
        for s in itertools.product(range(M + 1), repeat=k):
            if s[0] < 2:                  # q > 1 must divide the leading digit
                continue
            F = sum(W[x] for x in s)
            coeffs = list(s)
            coeffs[-1] -= F
            for f in pari.factor(pari('Pol(' + str(coeffs) + ', r)'))[0]:
                if int(pari.poldegree(f)) != 1:
                    continue
                root = -pari.polcoef(f, 0) / pari.polcoef(f, 1)
                if int(pari.denominator(root)) == 1:
                    continue
                kind = 'above' if root > max(s) else ('small' if root > 0 else 'negative')
                count[(m, kind)] += 1
                if kind != 'small':
                    print(f"0^0={m} {s} F={F} root {root} ({float(root):.4f}) {kind}", flush=True)
    for key in sorted(count):
        print('total', key, count[key])
