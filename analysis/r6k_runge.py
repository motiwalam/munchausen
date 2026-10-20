"""Round 6, k-length: the threshold of the Runge gap (Theorem K.1).

A k-digit string s with one large digit x (at the power b^j) and small
digits is a solution in base b when P(b) - W = x^x, W the weight of the
small digits. Let l be the leading digit (l = x when x leads), d = k - 1,
g a prime divisor of d, e = d / g, and suppose x^x / l = Z^g with Z
rational. Put T = (P - W) / l (monic of degree d), A the polynomial part
of T^(1/g) (monic of degree e), Rm = T - A^g (degree <= d - e - 1). Then

  (i)  if Z != A(b): g * min(Z, A(b))^(g-1) <= Delta * |Rm(b)|, where
       Delta = l * (common denominator of A); since |Rm(b)| <= Rb :=
       sum |c_i| bmax^i with bmax = ((W + x^x) / l)^(1/d), and
       min(Z, A(b)) >= (x^x / l - Rb)^(1/g), this is impossible once
       g (x^x/l - Rb)^((g-1)/g) > Delta Rb;
  (ii) if Z = A(b): Rm(b) = 0, impossible for Rm != 0 once
       bmin = ((W + x^x) / S)^(1/d) > 1 + DeltaR * max |c_i|, with S the
       digit sum and DeltaR the common denominator of Rm.

So beyond the threshold, a solution in the Runge class makes P - W = l A^g
an identity. The script finds, for every family with small digits <= B and
every prime g | d, the largest x <= XMAX at which (i) or (ii) fails (so the
gap argument does not yet apply), and checks the margin on a grid up to
10^7 beyond. It does not use the condition x^x / l = Z^g: the threshold is
a property of the family.

usage: r6k_runge.py K B XMAX
"""
import itertools
import math
import sys
from fractions import Fraction


def w(d, m):
    return m if d == 0 else d ** d


def primes_dividing(n):
    return [p for p in range(2, n + 1) if n % p == 0 and all(p % q for q in range(2, p))]


def poly_mul(a, b):
    r = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            r[i + j] += u * v
    return r


def poly_pow(a, n):
    r = [Fraction(1)]
    for _ in range(n):
        r = poly_mul(r, a)
    return r


def root_part(T, g):
    """T monic, coefficients highest first, degree d = g e. Returns A, Rm."""
    d = len(T) - 1
    e = d // g
    A = [Fraction(1)]
    for i in range(1, e + 1):
        # choose the coefficient a_i so that A^g matches T in degree d - i
        trial = A + [Fraction(0)] * (e + 1 - len(A))
        Ag = poly_pow(trial, g)
        # coefficient of r^(d - i) of (A + a r^(e - i))^g is Ag[i] + g a
        a = (T[i] - Ag[i]) / g
        A = A + [a]
    A = A + [Fraction(0)] * (e + 1 - len(A))
    Ag = poly_pow(A, g)
    Rm = [T[i] - Ag[i] for i in range(d + 1)]
    assert all(c == 0 for c in Rm[: e + 1]), Rm
    return A, Rm[e + 1:]


def lcm_den(cs):
    L = 1
    for c in cs:
        L = L * c.denominator // math.gcd(L, c.denominator)
    return L


def fails(s, ix, m, g, x):
    """True if (i) or (ii) fails at x for the string s with x at index ix."""
    k = len(s)
    d = k - 1
    s = list(s)
    s[ix] = x
    W = sum(w(s[i], m) for i in range(k) if i != ix)
    l = s[0]
    T = [Fraction(c, l) for c in s]
    T[-1] -= Fraction(W, l)
    A, Rm = root_part(T, g)
    if all(c == 0 for c in Rm):
        return False  # an identity: nothing to prove
    Delta = l * lcm_den(A)
    lx = x * math.log(x)                      # log x^x
    lWx = lx + math.log1p(W / math.exp(min(lx, 700))) if lx < 700 else lx
    lbmax = (lWx - math.log(l)) / d
    lbmin = (lWx - math.log(sum(s))) / d
    degR = len(Rm) - 1
    # log Rb, with Rb = sum |c_i| bmax^(degR - i)
    terms = [math.log(abs(c)) + (degR - i) * lbmax for i, c in enumerate(Rm) if c != 0]
    mx = max(terms)
    lRb = mx + math.log(sum(math.exp(t - mx) for t in terms))
    lZg = lx - math.log(l)
    if lZg <= lRb + 1e-9:
        return True
    diff = lZg + math.log1p(-math.exp(lRb - lZg))
    ok1 = math.log(g) + (g - 1) / g * diff > math.log(Delta) + lRb
    DR = lcm_den(Rm)
    mc = max(abs(c) for c in Rm)
    ok2 = lbmin > math.log1p(float(DR * mc))
    return not (ok1 and ok2)


def main():
    K, B, XMAX = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    d = K - 1
    worst = (0, None)
    grid = sorted(set([int(10 ** (u / 20)) for u in range(20 * len(str(XMAX)), 141)]))
    nfam = 0
    for g in primes_dividing(d):
        for ix in range(K):
            for ds in itertools.product(range(B + 1), repeat=K - 1):
                if ix != 0 and ds[0] == 0:
                    continue
                for m in ((0, 1) if 0 in ds else (1,)):
                    s = list(ds)
                    s.insert(ix, 0)
                    nfam += 1
                    last = 0
                    for x in range(2, XMAX + 1):
                        if fails(s, ix, m, g, x):
                            last = x
                    for x in grid:
                        if fails(s, ix, m, g, x):
                            print("fails on the grid", s, ix, m, g, x)
                    if last > worst[0]:
                        worst = (last, (tuple(ds), K - 1 - ix, m, g))
    print("K %d B %d: %d families; the gap applies for every x > %d (worst %s)"
          % (K, B, nfam, worst[0], worst[1]))


if __name__ == "__main__":
    main()
