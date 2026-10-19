"""Which lengths do positive integers have in the Eisenstein base -n + omega?

Exact lengths of the integers 1..X, plus 3000 random integers in each decade
from 10^4 to 10^30, as analysis/wld_gauss_lengths.py does for -n + i.
The digit of a + b omega is (a + n b) mod Q, Q = n^2 + n + 1, and
(x + b omega) / beta = ((b - (n+1) x) + (-x - n b) omega) / Q.
usage: python3 r3t_eisen_lengths.py
"""
import random
from math import atan2, sqrt, pi


def length(N, n):
    Q = n * n + n + 1
    a, b, k = N, 0, 0
    while a or b:
        r = (a + n * b) % Q
        x = a - r
        a, b = (b - (n + 1) * x) // Q, (-x - n * b) // Q
        k += 1
    return k


random.seed(5)
for n in (1, 2, 3, 4):
    X = 10 ** 5 if n == 1 else 10 ** 6
    seen = {length(N, n) for N in range(1, X)}
    for e in range(4, 30):
        for _ in range(3000):
            seen.add(length(random.randint(10 ** e, 10 ** (e + 1)), n))
    seen = sorted(D for D in seen if D <= 40)
    missing = [D for D in range(1, 41) if D not in seen]
    # beta = -n + omega = (-n - 1/2) + i sqrt(3)/2
    arg = atan2(sqrt(3) / 2, -n - 0.5)
    print(f"n={n}: arg(beta) = pi - {pi - arg:.4f}, half-period pi/(pi - arg) = {pi / (pi - arg):.2f}")
    print(f"      lengths seen <= 40: {seen}")
    print(f"      never seen: {missing}")
    if n == 1:
        # beta^12 = 729, so the set of lengths is closed under adding 12
        print(f"      closed under +12 up to 40: {all(D + 12 not in missing for D in seen if D + 12 <= 40)}")
