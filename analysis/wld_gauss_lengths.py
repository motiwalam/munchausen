"""Which lengths do positive integers have in base -n+i?

Exact lengths of the integers 1..X, plus 300 random integers in each decade
from 10^7 to 10^30. In base -1+i, beta^8 = 16, so ell(16 N) = ell(N) + 8.
"""
import random


def length(N, n):
    q = n * n + 1
    a, b, k = N, 0, 0
    while a or b:
        r = (a + n * b) % q
        x = a - r
        a, b = (-n * x + b) // q, (-x - n * b) // q
        k += 1
    return k


random.seed(5)
for n in (1, 2, 3, 4):
    X = 10 ** 4 if n == 1 else 10 ** 6
    seen = {length(N, n) for N in range(1, X)}
    for e in range(7, 30):
        for _ in range(300):
            seen.add(length(random.randint(10 ** e, 10 ** (e + 1)), n))
    seen = sorted(D for D in seen if D <= 40)
    missing = [D for D in range(1, 41) if D not in seen]
    print(f"n={n}: lengths seen <= 40: {seen}")
    print(f"      never seen: {missing}")
