"""Census against the refined model, split by the factorization type of B - 1.

Type: the sorted list of (degree, multiplicity) of the irreducible factors.
kappa: the dimension of the kernel of sigma'^(e-1) - 1 on F_q[T]/(B - 1),
sigma' the Frobenius. On x with D_j = 0 for j < e - 1 the identity reads
sigma'^(e-1) D = D, so q^kappa such x satisfy it, against q^k(B) in the model.
usage: python3 r4f_bytype.py file...
"""
import re
import sys
from collections import defaultdict
from sympy import Poly, symbols, Matrix
from r4f_byk import load
from r4f_lib import decode, pdivmod, padd, trim

T = symbols('T')


def ftype(code, q, e):
    b = decode(code, q, e + 1)
    b = b + [0] * (e + 1 - len(b))
    b[0] = (b[0] - 1) % q
    f = Poly(list(reversed(b)), T, modulus=q)
    return tuple(sorted((g.degree(), k) for g, k in f.factor_list()[1]))


def kappa(code, q, e):
    b = trim(decode(code, q, e + 1))
    bm1 = padd(b, [q - 1], q)
    rows = []
    for t in range(e):
        v = [0] * (t * q ** (e - 1) + 1)
        v[-1] = 1
        r = pdivmod(trim(v), bm1, q)[1]
        r = r + [0] * (e - len(r))
        r[t] = (r[t] - 1) % q
        rows.append(r)
    M = Matrix(rows)
    rank = M.rank(iszerofunc=lambda x: x % q == 0)
    # rank over F_q: use row reduction mod q
    A = [row[:] for row in rows]
    rk = 0
    for col in range(e):
        piv = next((i for i in range(rk, e) if A[i][col] % q), None)
        if piv is None:
            continue
        A[rk], A[piv] = A[piv], A[rk]
        inv = pow(A[rk][col], q - 2, q)
        for i in range(e):
            if i != rk and A[i][col] % q:
                c = A[i][col] * inv % q
                A[i] = [(x - c * y) % q for x, y in zip(A[i], A[rk])]
        rk += 1
    return e - rk


def main():
    for path in sys.argv[1:]:
        q, e, m = map(int, re.search(r'q(\d+)e(\d+)m(\d+)', path).groups())
        agg = defaultdict(lambda: [0, 0.0, 0.0, set(), set()])
        for r in load(path):
            t = ftype(r['code'], q, e)
            a = agg[t]
            a[0] += r['size']
            a[1] += r['sols'] * r['size']
            a[2] += r['refined'] * r['size']
            a[3].add(r['k'])
            a[4].add(kappa(r['code'], q, e))
        print(f"# q {q} e {e} m {m}")
        for t, a in sorted(agg.items()):
            print(f"type {t} bases {a[0]} k {sorted(a[3])} kappa {sorted(a[4])} "
                  f"census/base {a[1] / a[0]:.2f} refined/base {a[2] / a[0]:.2f} ratio {a[1] / a[2]:.2f}")


if __name__ == '__main__':
    main()
