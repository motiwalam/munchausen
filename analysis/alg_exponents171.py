"""Solutions of b(b+x) = x^n + 1 off the diagonal n = x (question 12).

The (1,x,1) equation is the case n = x of U^2 = 4 x^n + x^2 + 4, U = 2b + x.
n = 1 always works (b = 1). For n >= 3 odd and x odd, list every solution with
x up to XMAX and n up to NMAX. Even n >= 4 is excluded by the square class.
usage: python3 alg_exponents171.py XMAX NMAX
"""
import sys
import gmpy2

if __name__ == '__main__':
    XMAX, NMAX = int(sys.argv[1]), int(sys.argv[2])
    for x in range(2, XMAX + 1):
        c = x * x + 4
        xn = gmpy2.mpz(x)
        for n in range(2, NMAX + 1):
            xn *= x
            f = 4 * xn + c
            if gmpy2.is_square(f):
                U = gmpy2.isqrt(f)
                if (U - x) % 2 == 0:
                    print(f"x={x} n={n} b={(U - x) // 2}")
