"""Exact local densities for b(b+x) = x^x + 1 (question 12).

f(x) = 4 x^x + x^2 + 4 must be a square. Modulo an odd prime p, f(x) depends
on x mod p and x mod (p-1). For odd x, print the share of residue classes
mod p(p-1) in which f(x) is a nonresidue mod p, so that p excludes x.
Then the exact share of odd x that survive all primes in a set, computed by
CRT over the lcm of the p(p-1).
usage: python3 alg_local171.py [pmax]
"""
import sys
from math import lcm
from sympy import primerange


def killed_classes(p):
    sq = {(y * y) % p for y in range(p)}
    bad = set()
    for a in range(p):
        for e in range(1, p - 1, 2):          # x odd, so x mod (p-1) is odd
            f = (4 * pow(a, e, p) + a * a + 4) % p if a else 4 % p
            if f not in sq:
                bad.add((a, e))
    return bad


if __name__ == '__main__':
    pmax = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    print("p  share of odd x excluded by p")
    tables = {}
    for p in primerange(3, pmax):
        bad = killed_classes(p)
        tables[p] = bad
        print(p, f"{len(bad) / (p * (p - 1) // 2):.4f}")
    # joint survival over the first primes, exactly, by enumerating odd x mod M
    ps = []
    for p in primerange(3, pmax):
        M = lcm(2, *[q * (q - 1) for q in ps + [p]])
        if M > 3 * 10**7:
            break
        ps.append(p)
        alive = 0
        for x in range(1, M, 2):
            if all((x % q, x % (q - 1)) not in tables[q] for q in ps):
                alive += 1
        print(f"primes 3..{p}: modulus {M}, share of odd x surviving = {alive / (M // 2):.4f}", flush=True)
