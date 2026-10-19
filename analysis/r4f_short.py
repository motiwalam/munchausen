"""Check Theorem 4.1 (short solutions) against a direct count.

Short solutions are those with D_j constant for every j >= 2, so that
F = C + b T^q. The theorem says they exist only when B - 1 has e distinct
roots in F_q, and then there are exactly q(q-1) or none, by a test on the
digits of Q = (T^q - T)/(B - 1). This script applies the test to every base
of degree e and compares with a direct count of the short solutions
(class sums enumerated with D_j constant for j >= 2, m = 0).
With "census" it compares the test instead with the solutions of length
floor(q/e) + 1 in r4f_census_q{q}e{e}m0.txt (one base per orbit).
usage: python3 r4f_short.py q e [census]
"""
import sys
import itertools
from r4f_lib import all_bases, digits, padd, pdivmod, trim


def predicted(B, q, e):
    bm1 = padd(B, [q - 1], q)
    roots = [a for a in range(q) if sum(c * pow(a, i, q) for i, c in enumerate(bm1)) % q == 0]
    tq = [0] * (q + 1)
    tq[q] = 1
    tq[1] = q - 1
    Q, r = pdivmod(trim(tq), bm1, q)
    if r:
        return 0, len(roots)
    qd = digits(Q, B, q, e) or [[0] * e]
    qd = [trim(d) for d in qd] + [[]]
    E = {j: [0] * e for j in range(e)}
    for i in range(1, len(qd)):
        delta = padd(qd[i - 1], [(q - c) % q for c in qd[i]], q)
        if delta:
            j = len(delta) - 1
            for t, c in enumerate(delta):
                E[j][t] = (E[j][t] + c) % q
    tm = padd([0, 1], [(q - c) % q for c in qd[0]], q)
    j0 = max(len(tm) - 1, 0)
    ok = all(not any(E[j][1:]) for j in range(2, e) if j != j0)
    if j0 >= 2:
        ok = ok and E[1][1] == 1
    return (q * (q - 1) if ok else 0), len(roots)


def direct(B, q, e):
    """count solutions with D_j constant for j >= 2 by brute force over the class sums"""
    count = 0
    consts = range(q)
    for d0, a1, b1 in itertools.product(range(q), range(q), range(1, q)):
        for hi in itertools.product(consts, repeat=e - 2):
            C = (d0 + a1 + sum(hi)) % q
            f = [0] * (q + 1)
            f[0] = C
            f[q] = b1
            ds = [trim(d) for d in digits(trim(f), B, q, e)]
            if len(ds) < 2:
                continue
            cls = {j: [0] * (j + 1) for j in range(e)}
            for d in ds:
                if d:
                    j = len(d) - 1
                    for t, c in enumerate(d):
                        cls[j][t] = (cls[j][t] + c) % q
            want = {0: [d0], 1: [a1, b1]}
            for j, h in zip(range(2, e), hi):
                want[j] = [h] + [0] * j
            if all(cls[j] == want[j] for j in range(e)):
                count += 1
    return count


def census(q, e):
    from r4f_byk import load
    from r4f_lib import decode
    L = q // e + 1
    agree = bad = tot = 0
    for r in load(f'data/r4f_census_q{q}e{e}m0.txt'):
        p, _ = predicted(trim(decode(r['code'], q, e + 1)), q, e)
        c = r['lens'].get(L, 0)
        agree += r['size'] * (p == c)
        bad += r['size'] * (p != c)
        tot += r['size'] * c
    print(f"q {q} e {e}: bases {agree + bad}, test agrees with the census in {agree}, short solutions per base {tot / (agree + bad):.3f}")


def main():
    q, e = map(int, sys.argv[1:3])
    if len(sys.argv) > 3:
        return census(q, e)
    agree = bad = nz = 0
    for B in all_bases(q, e):
        p, nr = predicted(B, q, e)
        d = direct(B, q, e)
        if p == d:
            agree += 1
        else:
            bad += 1
            print('mismatch', B, p, d)
        nz += d > 0
    print(f"q {q} e {e}: bases {agree + bad}, agree {agree}, mismatch {bad}, bases with short solutions {nz}")


if __name__ == '__main__':
    main()
