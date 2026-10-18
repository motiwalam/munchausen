"""abc quality forced by a solution of b(b+x) = x^x + 1 (question 12).

A solution with odd x gives the abc triple (x^2+4) + 4x^x = (2b+x)^2, with
coprime terms. Its radical is at most 2x (x^2+4)(2b+x), and 2b+x < 2x^(x/2)+1.
So its quality log c / log rad is at least the lower bound printed here.
Also prints the x-adic check for prime x: the root beta = 1 (mod x) of
t^2 + x t - 1 = 0, reduced mod x^x, is below x^(x/2) only for a solution.
"""
import math
import gmpy2
from sympy import primerange

REYSSAT = 1.629911684                     # 2 + 3^10 * 109 = 23^5, best known

if __name__ == '__main__':
    first = None
    for x in range(3, 200, 2):
        U = 2 * gmpy2.isqrt(gmpy2.mpz(x) ** x) + 2   # upper bound for 2b + x
        c = 4 * gmpy2.mpz(x) ** x + x * x + 4
        q = math.log(int(c)) / math.log(int(2 * x * (x * x + 4) * U))
        if x in (9, 15, 21, 25, 27, 29, 31, 51, 101, 199) or (first is None and q > REYSSAT):
            print(f"x={x}: quality > {q:.4f}")
        if first is None and q > REYSSAT:
            first = x
    print(f"every odd x >= {first} would give quality above Reyssat's 1.6299")
    # x-adic form for prime x
    for x in primerange(3, 60):
        mod = gmpy2.mpz(x) ** x
        b = gmpy2.mpz(1)                 # Hensel lift of the root = 1 (mod x)
        for _ in range(8):
            b = (b - (b * b + x * b - 1) * gmpy2.invert(2 * b + x, mod)) % mod
        assert (b * b + x * b - 1) % mod == 0 and b % x == 1
        top = math.log(int(b)) / math.log(x)
        print(f"x={x}: residue of the root mod x^x is about x^{top:.3f}"
              f"{'  (below x^(x/2): solution b=' + str(b) + ')' if b * b < mod else ''}")
