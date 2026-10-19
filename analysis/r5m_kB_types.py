"""k(B) against omega(B - 1) for the factor types that Theorem 2.3 of
docs/library/drafts/round5-model.md leaves open (question 82).

k(B) = omega(B - 1) is proved unless every irreducible factor P of B - 1 has
gcd(deg P, e - 1) > 1. This script builds every M = B - 1 of such a type
from monic irreducibles, M = prod P_i^(a_i), and compares
k = corank of D -> sum_j (Frob^j - 1) D_j mod M with omega = number of P_i.
Only monic M are built: scaling M by a unit changes neither number.

usage: python3 r5m_kB_types.py Q E [max_count]
"""
import itertools
import sys
from collections import Counter

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])


def polymulmod(a, b, M, q):
    """a * b mod M, arrays low first, M monic"""
    r = np.convolve(a, b) % q
    e = len(M) - 1
    for k in range(len(r) - 1, e - 1, -1):
        c = r[k]
        if c:
            r[k - e:k + 1] = (r[k - e:k + 1] - c * M) % q
    out = np.zeros(e, dtype=np.int64)
    n = min(e, len(r))
    out[:n] = r[:n]
    return out


def frob_matrix(M, q):
    """columns: t^(i q) mod M for i < e"""
    e = len(M) - 1
    t = np.zeros(e, dtype=np.int64)
    t[1 % e] = 1 if e > 1 else 0
    # t^q
    res = np.zeros(e, dtype=np.int64)
    res[0] = 1
    base, k = t.copy(), q
    while k:
        if k & 1:
            res = polymulmod(res, base, M, q)
        base = polymulmod(base, base, M, q)
        k >>= 1
    cols = [np.eye(e, dtype=np.int64)[0]]
    cur = cols[0]
    for i in range(1, e):
        cur = polymulmod(cur, res, M, q)
        cols.append(cur)
    return np.stack(cols, axis=1) % q


def rank_mod(A, q):
    A = A.copy() % q
    nr, nc = A.shape
    r = 0
    for c in range(nc):
        piv = np.nonzero(A[r:, c])[0]
        if len(piv) == 0:
            continue
        p = r + piv[0]
        A[[r, p]] = A[[p, r]]
        A[r] = A[r] * pow(int(A[r, c]), q - 2, q) % q
        nzr = np.nonzero(A[:, c])[0]
        for i in nzr:
            if i != r:
                A[i] = (A[i] - A[i, c] * A[r]) % q
        r += 1
        if r == nr:
            break
    return r


def k_omega(M, q):
    e = len(M) - 1
    Phi = frob_matrix(M, q)
    I = np.eye(e, dtype=np.int64)
    omega = e - rank_mod((Phi - I) % q, q)
    cols = []
    P = I.copy()
    for j in range(1, e):
        P = Phi @ P % q
        cols.append(((P - I) % q)[:, :j + 1])
    k = e - rank_mod(np.concatenate(cols, axis=1).T, q)
    return k, omega


def deg_D(M, q):
    """degree of D = M'^(1-q) mod M (M squarefree), the element d_1 of
    Proposition 2.5 of round5-model.md; k(B) = omega + 1 needs deg D <= 1"""
    from r4f_lib import pdivmod, pmul, padd, trim
    Ml = trim([int(c) for c in M])
    dM = trim([(i * c) % q for i, c in enumerate(Ml)][1:])
    E = [1]
    for _ in range(q - 1):
        E = pdivmod(pmul(E, dM, q), Ml, q)[1]
    # inverse of E mod M by the extended Euclidean algorithm
    r0, r1, s0, s1 = Ml, E, [], [1]
    while r1:
        quo, rem = pdivmod(r0, r1, q)
        r0, r1 = r1, rem
        s0, s1 = s1, padd(s0, [(-c) % q for c in pmul(quo, s1, q)], q)
    inv = pow(r0[0], q - 2, q)
    D = pdivmod([c * inv % q for c in s0], Ml, q)[1]
    return len(D) - 1


def irreducibles(q, f):
    """monic irreducible polynomials of degree f over F_q, as arrays low first"""
    out = []
    for c in range(q ** f):
        P = np.array([(c // q ** i) % q for i in range(f)] + [1], dtype=np.int64)
        if f > 1 and P[0] == 0:
            continue
        # irreducible iff squarefree with one irreducible factor:
        # x^(q^f) == x mod P and gcd(x^(q^(f/r)) - x, P) = 1 for primes r | f (Rabin)
        if rabin(P, q, f):
            out.append(P)
    return out


def xpow_mod(P, q, n):
    """x^(q^n) mod P"""
    e = len(P) - 1
    x = np.zeros(e, dtype=np.int64)
    if e == 1:
        x[0] = (-P[0]) % q
    else:
        x[1] = 1
    for _ in range(n):
        res = np.zeros(e, dtype=np.int64)
        res[0] = 1
        base, k = x.copy(), q
        while k:
            if k & 1:
                res = polymulmod(res, base, P, q)
            base = polymulmod(base, base, P, q)
            k >>= 1
        x = res
    return x


def pgcd(a, b, q):
    a = np.trim_zeros(a % q, 'b')
    b = np.trim_zeros(b % q, 'b')
    while len(b):
        inv = pow(int(b[-1]), q - 2, q)
        while len(a) >= len(b):
            c = a[-1] * inv % q
            sh = len(a) - len(b)
            a[sh:] = (a[sh:] - c * b) % q
            a = np.trim_zeros(a, 'b')
            if not len(a):
                break
        a, b = b, a
    return len(a) - 1


def rabin(P, q, f):
    if f == 1:
        return True
    x = np.zeros(f, dtype=np.int64)
    x[1] = 1
    if not np.array_equal(xpow_mod(P, q, f) % q, x):
        return False
    for r in {p for p in range(2, f + 1) if f % p == 0 and all(p % s for s in range(2, p))}:
        d = (xpow_mod(P, q, f // r) - x) % q
        if pgcd(P.copy(), d, q) != 0:
            return False
    return True


def bad_types(e):
    """multisets of (f, a) with sum a f = e, every gcd(f, e - 1) > 1"""
    from math import gcd
    parts = [(f, a) for f in range(2, e + 1) for a in range(1, e // f + 1) if gcd(f, e - 1) > 1]
    out = []

    def rec(start, left, cur):
        if left == 0:
            out.append(list(cur))
            return
        for i in range(start, len(parts)):
            f, a = parts[i]
            if a * f <= left:
                cur.append((f, a))
                rec(i, left - a * f, cur)
                cur.pop()
    rec(0, e, [])
    return out


def main():
    q, e = int(sys.argv[1]), int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
    types = bad_types(e)
    print(f"# q {q} e {e}: {len(types)} all-bad factor types")
    irr = {}
    total = Counter()
    for ty in types:
        for f, _ in ty:
            if f not in irr:
                irr[f] = irreducibles(q, f)
        # distinct irreducibles for the parts of the type
        pools = [irr[f] for f, _ in ty]
        stats = Counter()
        dstats = Counter()
        n = 0
        for combo in itertools.product(*[range(len(p)) for p in pools]):
            keys = [(ty[i][0], combo[i]) for i in range(len(ty))]
            if len(set(keys)) < len(keys):
                continue
            # skip permutations of equal parts
            if any(ty[i] == ty[i + 1] and combo[i] > combo[i + 1] for i in range(len(ty) - 1)):
                continue
            M = np.array([1], dtype=np.int64)
            for i, (f, a) in enumerate(ty):
                for _ in range(a):
                    M = np.convolve(M, pools[i][combo[i]]) % q
            k, om = k_omega(M, q)
            stats[k - om] += 1
            if all(a == 1 for _, a in ty):
                dstats[deg_D(M, q)] += 1
            if k != om and stats[k - om] <= 3:
                print(f"  COUNTEREXAMPLE type {ty} M = {M.tolist()} (low first) k {k} omega {om}")
            n += 1
            if n >= cap:
                break
        total.update(stats)
        print(f"  type {ty}: {n} polynomials, k - omega counts {dict(stats)}, deg D counts {dict(sorted(dstats.items()))}")
    print(f"# total k - omega counts {dict(total)}")


if __name__ == '__main__':
    main()
