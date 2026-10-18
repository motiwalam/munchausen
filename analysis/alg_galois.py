"""Galois groups of irreducible Q_s for k = 4, 5, 6 (question 4).

For every string of length k with digits up to M and both conventions, compute
the Galois group of Q_s with PARI's polgalois when Q_s is irreducible. Count
the groups, and list the strings whose group is not the full symmetric group,
with the largest digit and whether P_s is decomposable (alg_reducible.decompose).
Theorem 5 of the draft says: for k = 4 a smaller group needs largest digit <= 5;
for k = 5 it needs largest digit <= 6 unless P_s is decomposable.
usage: python3 alg_galois.py k M
"""
import sys
import itertools
import math
from collections import Counter
import cypari2
from alg_reducible import decompose

pari = cypari2.Pari()

if __name__ == '__main__':
    k, M = int(sys.argv[1]), int(sys.argv[2])
    count = Counter()
    for m in (1, 0):
        W = [m] + [x**x for x in range(1, M + 1)]
        for s in itertools.product(range(M + 1), repeat=k):
            if s[0] == 0:
                continue
            coeffs = list(s)
            coeffs[-1] -= sum(W[x] for x in s)
            pol = pari('Pol(' + str(coeffs) + ', r)')
            if not pari.polisirreducible(pol):
                continue
            g = pari.polgalois(pol)
            name = str(g[3]).strip('"')
            count[(m, name)] += 1
            if int(g[0]) < math.factorial(k - 1):
                dec = decompose(s)
                print(f"0^0={m} {s} max digit {max(s)} group {name}"
                      f" {'decomposable h=' + str(dec[1].as_expr()) if dec else 'indecomposable'}",
                      flush=True)
    for key in sorted(count):
        print('total', key, count[key])
