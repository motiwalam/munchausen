"""Round 4, blocks: binomial families of short solutions under both conventions.

Let j >= 2, c >= 1, e >= 1, and t_i = c^(j-i) C(j,i) e^i for i = 0..j-1, the
coefficients of (c r + e)^j without the constant term. Put
x = e^j + sum t_i^(t_i). If x^x = y^j for an integer y, c | y - e, and
b = (y - e)/c exceeds every digit, then (t_0, ..., t_(j-1), x) is a
(j+1)-digit Munchausen number in base b:

    P(b) = (c b + e)^j - e^j + x = x^x + sum t_i^(t_i) = F.

All digits are positive, so this holds under both conventions. The script

1. checks the identity exactly for the members it can write down, and
   modulo 20 large primes for the others;
2. lists the members with small c and e for k = j + 1 = 3 to 9 digits;
3. lists all 3-digit solutions (p, q, x) of the form of Corollary 8.4 with
   R = 0, that is x = p^p + q^q + q^2/(4p) and p x^x a square, for p, q up
   to 60.

    python3 r4b_families.py > data/r4b_families.txt
"""
import math
import sys

sys.set_int_max_str_digits(0)

PRIMES = [1000000007, 998244353, 2305843009213693951, 1000003, 999999937, 4294967291, 2147483647, 1099511627791,
          67280421310721, 274177, 6700417, 3203431780337, 59649589127497217, 5704689200685129054721, 1000000009,
          1000000021, 1000000033, 1000000087, 1000000093, 1000000097]


def binom_prefix(j, c, e):
    return [c ** (j - i) * math.comb(j, i) * e ** i for i in range(j)]


def lam(n):
    """Carmichael function"""
    out = 1
    m = n
    p = 2
    while p * p <= m:
        if m % p == 0:
            k = 0
            while m % p == 0:
                m //= p
                k += 1
            l = (p - 1) * p ** (k - 1)
            if p == 2 and k >= 3:
                l //= 2
            out = out * l // math.gcd(out, l)
        p += 1
    if m > 1:
        out = out * (m - 1) // math.gcd(out, m - 1)
    return out


def x_mod(t, e, j, mod):
    """x mod `mod` without computing x"""
    return (pow(e, j, mod) + sum(pow(ti, ti, mod) for ti in t)) % mod


def log10_x(t, e, j):
    """log10 of x = e^j + sum t^t, from the largest term"""
    big = max(ti * math.log10(ti) for ti in t)
    return max(big, j * math.log10(e))


def member(j, c, e):
    """Return a dict for the family member (j, c, e) if j | x and c | y - e,
    where y = x^(x/j); None otherwise. Works without x when x is huge."""
    t = binom_prefix(j, c, e)
    if max(t) <= 4000:
        x = e ** j + sum(ti ** ti for ti in t)
        if x % j:
            return None
        # y = x^(x/j) mod c
        ymod = pow(x % c, x // j, c) if c > 1 else 0
        if (ymod - e) % c:
            return None
        lx = math.log10(x)
        lb = (x / j) * lx - math.log10(c) if lx < 300 else None
        return dict(j=j, c=c, e=e, t=t, x=x, log10_x=lx, log10_b=lb, log10_log10_b=lx + math.log10(lx) - math.log10(j))
    # x too large to write: decide j | x and c | y - e by residues
    L = lam(c) if c > 1 else 1
    mod = j * c * L * 64
    xm = x_mod(t, e, j, mod)
    if xm % j:
        return None
    if c > 1:
        # x/j mod L, and x mod c; x/j is huge, so the exponent is large enough
        ex = (xm // j) % L + 64 * L
        if (pow(xm % c, ex, c) - e) % c:
            return None
    lx = log10_x(t, e, j)
    return dict(j=j, c=c, e=e, t=t, x=None, log10_x=lx, log10_b=None, log10_log10_b=lx + math.log10(lx) - math.log10(j))


def check_mod(j, c, e, x):
    """check P(b) = F(s) modulo PRIMES, with b = (x^(x/j) - e)/c"""
    t = binom_prefix(j, c, e)
    for p in PRIMES:
        if c % p == 0:
            continue
        y = pow(x, x // j, p)
        b = (y - e) * pow(c, -1, p) % p
        P = 0
        for d in t + [x]:
            P = (P * b + d) % p
        F = (sum(pow(d, d, p) for d in t) + pow(x, x, p)) % p
        if P != F:
            return False
    return True


def check_exact(j, c, e, x):
    t = binom_prefix(j, c, e)
    y = x ** (x // j)
    assert (y - e) % c == 0
    b = (y - e) // c
    assert b > max(t + [x])
    P = 0
    for d in t + [x]:
        P = P * b + d
    return P == sum(d ** d for d in t) + x ** x


def three_digit(Pmax=60, Qmax=60):
    """(p, q, x) with R = 0: x = p^p + q^q + q^2/(4p) and p x^x a square,
    b = (2 sqrt(p x^x) - q) / (2p) an integer above the digits; 0^0 = 1 for q = 0"""
    out = []
    for p in range(1, Pmax + 1):
        for q in range(0, Qmax + 1):
            if (q * q) % (4 * p):
                continue
            wq = 1 if q == 0 else q ** q
            x = p ** p + wq + q * q // (4 * p)
            # p x^x a square
            if x % 2 == 0:
                c = math.isqrt(p)
                if c * c != p:
                    continue
                # sqrt(p x^x) = c x^(x/2)
                rt_mod = c * pow(x, x // 2, 2 * p) % (2 * p)
                sq_desc = f"{c} * x^(x/2)"
                log_rt = math.log10(c) + x / 2 * math.log10(x)
            else:
                s = math.isqrt(p * x)
                if s * s != p * x:
                    continue
                rt_mod = s * pow(x, (x - 1) // 2, 2 * p) % (2 * p)
                sq_desc = f"{s} * x^((x-1)/2)"
                log_rt = math.log10(s) + (x - 1) / 2 * math.log10(x)
            if (2 * rt_mod - q) % (2 * p):
                continue
            log_b = log_rt + math.log10(2) - math.log10(2 * p)
            ok = None
            if x < 10 ** 6:
                rt = math.isqrt(p * x ** x)
                assert rt * rt == p * x ** x
                b = (2 * rt - q) // (2 * p)
                ok = b > max(p, q, x) and p * b * b + q * b + x == p ** p + wq + x ** x
            out.append((p, q, x, sq_desc, log_b, ok))
    return out


def main():
    print("# binomial families: (t_0..t_(j-1), x), t_i = c^(j-i) C(j,i) e^i, x = e^j + sum t_i^t_i, base (x^(x/j) - e)/c")
    print("# only members with j | x are listed (x^x = (x^(x/j))^j); x a perfect power without j | x is not searched")
    print()
    print("## exact and modular checks")
    for (j, c, e) in [(2, 1, 1), (2, 1, 3)]:
        m = member(j, c, e)
        print(f"j={j} c={c} e={e}: digits {m['t'] + [m['x']]}, exact check: {check_exact(j, c, e, m['x'])}")
    for (j, c, e) in [(3, 1, 2), (2, 1, 5), (2, 2, 2), (3, 3, 3), (4, 2, 2)]:
        m = member(j, c, e)
        if m and m['x'] is not None:
            print(f"j={j} c={c} e={e}: digits {m['t'] + [m['x']]}, check modulo {len(PRIMES)} primes: {check_mod(j, c, e, m['x'])}")
    print()
    print("## members with c <= 6 and e <= 12, by length k = j + 1")
    print("# k j c e prefix log10(x) log10(log10(b)) check modulo 20 primes")
    for j in range(2, 9):
        found = []
        for c in range(1, 7):
            for e in range(1, 13):
                m = member(j, c, e)
                if m is None:
                    continue
                llb = math.log10(m['log10_b']) if m['log10_b'] else m['log10_log10_b']
                found.append((llb, c, e, m))
        found.sort()
        for llb, c, e, m in found:
            pre = m['t'] if max(m['t']) < 10 ** 6 else '...'
            chk = check_mod(j, c, e, m['x']) if m['x'] is not None else 'x not written'
            print(f"{j + 1} {j} {c} {e} {pre} {m['log10_x']:.2f} {llb:.3f} mod-check={chk}"
                  + (f"  x = {m['x']}" if m['x'] is not None and m['x'] < 10 ** 30 else ''))
        print(f"# k = {j + 1}: {len(found)} members with c <= 6, e <= 12")
    print()
    print("## the corollary: c = e = j gives a member for every j (proof in the draft)")
    for j in range(2, 9):
        m = member(j, j, j)
        print(f"k={j + 1}: c = e = {j}: member: {m is not None}")
    print()
    print("## 3-digit solutions (p, q, x) with R = 0 (the case left out of Corollary 8.4), p, q <= 60")
    print("# p q x sqrt(p x^x) log10(b) exact-check(if x < 10^6)")
    for p, q, x, sq, lb, ok in three_digit():
        xs = str(x) if x < 10 ** 40 else f"~10^{math.log10(x):.1f}"
        print(f"{p} {q} {xs} {sq} {lb:.6g} {ok}")


if __name__ == '__main__':
    main()
