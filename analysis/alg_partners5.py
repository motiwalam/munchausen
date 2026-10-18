"""5-digit strings that are solutions in a base b and in the base -(b + delta).

Theorem 7 of the draft: for digits above a small bound this needs
P_s(r) = P_s(-r - delta), that is s2 = 2 delta s1 and s4 = delta (s3 - delta^2 s1).
Then P_s = G(u) with u = r^2 + delta r and G(u) = s1 u^2 + (s3 - delta^2 s1) u + s5.
This script runs through all such strings with digits up to M, solves
G(u) = F(s) for an integer u and then u = b (b + delta) for an integer b above
every digit. Both conventions.
usage: python3 alg_partners5.py M
"""
import sys
import gmpy2

if __name__ == '__main__':
    M = int(sys.argv[1])
    W = [gmpy2.mpz(x) ** x for x in range(M + 1)]
    n = 0
    for m in (0, 1):
        W[0] = gmpy2.mpz(m)
        for s1 in range(1, M + 1):
            for delta in range(0, M // (2 * s1) + 1):
                s2 = 2 * delta * s1
                for s3 in range(delta * delta * s1, M + 1):
                    A = s3 - delta * delta * s1
                    s4 = delta * A
                    if s4 > M:
                        break
                    base_F = W[s1] + W[s2] + W[s3] + W[s4]
                    for s5 in range(M + 1):
                        n += 1
                        F = base_F + W[s5]
                        disc = A * A + 4 * s1 * (F - s5)
                        if not gmpy2.is_square(disc):
                            continue
                        t = gmpy2.isqrt(disc) - A
                        if t % (2 * s1):
                            continue
                        u = t // (2 * s1)
                        d2 = delta * delta + 4 * u
                        if not gmpy2.is_square(d2):
                            continue
                        t2 = gmpy2.isqrt(d2) - delta
                        if t2 % 2:
                            continue
                        b = t2 // 2
                        s = (s1, s2, s3, s4, s5)
                        if b > max(s):
                            bs = str(b) if b < 10**20 else f"~10^{len(str(b)) - 1}"
                            print(f"0^0={m} {s} bases {bs} and -(b+{delta})", flush=True)
    print(f"strings checked: {n}")
