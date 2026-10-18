"""3-digit solutions with two large digits (questions 1 and 8).

Every 3-digit string (p, q, r) in which two digits are at most D and the third
is at most S, both conventions. A solution in base b means
p b^2 + q b + r = F(s), so the discriminant q^2 + 4p(F - r) must be a square
and b = (sqrt - q) / (2p) must exceed every digit. The complete 3-digit lists
of chapter 3 cover digits up to 80; this covers two digits up to D.
The same discriminant gives the negative bases: s is a solution in base -c
when c = (sqrt + q) / (2p) is an integer above every digit (section 12.3).
Each line says whether the other root of Q_s is an integer base (a partner).
usage: python3 alg_twolarge.py D S
"""
import sys
from fractions import Fraction
import gmpy2

if __name__ == '__main__':
    D, S = int(sys.argv[1]), int(sys.argv[2])
    W = [gmpy2.mpz(x) ** x for x in range(D + 1)]
    found = set()
    checked = 0
    for m in (0, 1):
        W[0] = gmpy2.mpz(m)
        for z in range(S + 1):
            for u in range(D + 1):
                for v in range(D + 1):
                    for s in ((z, u, v), (u, z, v), (u, v, z)):
                        p, q, r = s
                        if p == 0:
                            continue
                        checked += 1
                        F = W[p] + W[q] + W[r]
                        disc = q * q + 4 * p * (F - r)
                        if disc >= 0 and gmpy2.is_square(disc):
                            sq = gmpy2.isqrt(disc)
                            for t, sign in ((sq - q, 1), (sq + q, -1)):
                                if t % (2 * p) == 0 and t // (2 * p) > max(s):
                                    found.add((m, sign * int(t // (2 * p)), s))
    for m, b, s in sorted(found):
        bs = str(b) if abs(b) < 10**30 else f"{'-' if b < 0 else ''}~10^{len(str(abs(b))) - 1}"
        other = Fraction(-s[1], s[0]) - b          # the other root of Q_s
        partner = other.denominator == 1 and (m, int(other), s) in found
        print(f"0^0={m} base {bs}: {s}{'  partner of base ' + str(int(other)) if partner else ''}")
    print(f"strings checked (with repeats): {checked}")
