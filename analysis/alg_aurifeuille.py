"""Aurifeuillian factors L < M and the M/L law (question 1, Theorem 1).

For squarefree x == 3 (mod 4), Phi_2x(x t^2) splits in Z[t]; for squarefree
x == 1 (mod 4), Phi_x(x t^2) does (the factor of x^x - 1). Evaluating the two
factors at t = 1 gives L < M. For each x print:
- log(M/L) - 2 and x times it;
- the difference between log(M/L) and the series of Theorem 1,
  2 * sum over odd j coprime to x of psi(j) / (j x^((j-1)/2)), psi = (D/j),
  D = 4x or x the discriminant of Q(sqrt x);
- for x == 3 (mod 4): l = (L-1)/x and m = (M-1)/x mod x (Proposition 3 says
  m - l == 2), and the largest j with x^j | E, E = M - (x+1)L - x, which is 0
  exactly when ((x+1)L, M) is a (1,x,1) solution (Proposition 3: j >= 2).
usage: python3 alg_aurifeuille.py [xmax]
"""
import sys
import math
import cypari2
from mpmath import mp, mpf, log
from sympy import factorint

pari = cypari2.Pari()
pari.allocatemem(10**9)
mp.dps = 60


def aurifeuille(x):
    n = 2 * x if x % 4 == 3 else x
    v = pari(f"my(f=factor(subst(polcyclo({n},x),x,{x}*t^2))[,1]);"
             f"vector(#f,i,subst(f[i],t,1))")
    L, M = sorted(abs(int(a)) for a in v)
    assert L * M == int(pari(f"polcyclo({n},{x})"))
    return L, M


def kronecker(D, j):
    return int(pari.kronecker(D, j))


def series(x, terms=60):
    D = 4 * x if x % 4 == 3 else x
    return 2 * sum(mpf(kronecker(D, j)) / (j * mpf(x) ** ((j - 1) // 2))
                   for j in range(1, 2 * terms, 2) if math.gcd(j, x) == 1)


def vx(E, x):
    if E == 0:
        return math.inf
    j = 0
    while E % x == 0:
        E //= x
        j += 1
    return j


if __name__ == '__main__':
    xmax = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    print("x  x%4  M/L  log(M/L)-2  x*(log-2)  (x|3)  |log(M/L)-series|  m-l  v_x(E)")
    for x in range(3, xmax + 1, 2):
        if any(e > 1 for e in factorint(x).values()):
            continue
        L, M = aurifeuille(x)
        lr = log(mpf(M)) - log(mpf(L))
        err = abs(lr - series(x))
        chi = kronecker(x, 3) if x % 3 else 0
        extra = ''
        if x % 4 == 3:
            assert (L - 1) % x == 0 and (M - 1) % x == 0
            dm = (((M - 1) // x) - ((L - 1) // x)) % x
            extra = f"{dm} {vx(M - (x + 1) * L - x, x)}"
        print(f"{x} {x % 4} {float(M / L):.4f} {float(lr - 2):+.6f} {float(x * (lr - 2)):+.4f} "
              f"{chi:+d} {float(err):.1e} {extra}", flush=True)
