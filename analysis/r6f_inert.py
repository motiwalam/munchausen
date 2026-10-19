"""Least inert primes of quadratic fields, for the bounds of round 6 (factorials).

For a squarefree D != 0, 1 let Delta be the discriminant of Q(sqrt D)
(D if D == 1 mod 4, else 4D) and chi the Kronecker symbol (Delta / .).
l(Delta) is the least prime l with chi(l) = -1 (l inert). For odd l,
chi(l) = (D / l); for l = 2, chi(2) = -1 exactly when D == 5 (mod 8).

The script prints the record holders: the Delta (by |Delta|, separately for
Delta > 0 and Delta < 0) at which max over |Delta'| <= |Delta| of l(Delta')
increases. The envelope Lam(q) = max over 1 < |Delta| <= q of l(Delta) is
then read off this list. Used by r6f_factorion3.py.

    python3 analysis/r6f_inert.py 4000000 > analysis/data/r6f_inert.txt
"""
import sys

import numpy as np
import sympy


def squarefree_mask(n):
    """mask[k] for 0 <= k <= n: k squarefree"""
    m = np.ones(n + 1, dtype=bool)
    m[0] = False
    for p in sympy.primerange(2, int(n ** 0.5) + 2):
        m[p * p::p * p] = False
    return m


def least_inert(D):
    """least inert prime for each D in the int64 array D (squarefree, != 0, 1)"""
    out = np.zeros(len(D), dtype=np.int64)
    out[(D % 8) == 5] = 2
    for l in sympy.primerange(3, 10 ** 5):
        todo = out == 0
        if not todo.any():
            break
        leg = np.zeros(l, dtype=np.int8)
        sq = set((i * i) % l for i in range(1, l))
        for r in range(1, l):
            leg[r] = 1 if r in sq else -1
        r = D[todo] % l
        idx = np.nonzero(todo)[0]
        out[idx[leg[r] == -1]] = l
    return out


def main():
    Q = int(sys.argv[1]) if len(sys.argv) > 1 else 4 * 10 ** 6
    sf = squarefree_mask(Q)
    print(f"# least inert prime l(Delta), fundamental discriminants with 1 < |Delta| <= {Q}")
    print("# record holders: sign Delta l(Delta) (envelope max over |Delta'| <= |Delta|)")
    for sign in (1, -1):
        n = np.arange(1, Q + 1, dtype=np.int64)
        good = sf[1:]
        D = sign * n[good]
        D = D[D != 1]
        Delta = np.where(D % 4 == 1, D, 4 * D)
        keep = np.abs(Delta) <= Q
        D, Delta = D[keep], Delta[keep]
        li = least_inert(D)
        order = np.argsort(np.abs(Delta), kind='stable')
        best = 0
        count = 0
        for i in order:
            if li[i] > best:
                best = int(li[i])
                print(f"{'+' if sign > 0 else '-'} {int(Delta[i])} {best}")
            count += 1
        print(f"# sign {'+' if sign > 0 else '-'}: {count} discriminants, max l(Delta) = {best}")
        sys.stdout.flush()


if __name__ == '__main__':
    main()
