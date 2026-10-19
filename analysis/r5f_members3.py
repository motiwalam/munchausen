"""Round 5, families: every 3-digit power-identity member under 0^0 = 1.

A 3-digit string (p, q, x) has Q_s(r) = lam (c r + e)^2 - x^x exactly when
p = lam c^2, q = 2 lam c e (lam squarefree, c >= 1, e >= 0) and
x = w(p) + w(q) + lam e^2, with w(d) = d^d and w(0) = 1. It is then a
solution in base b exactly when x^x = lam (c b + e)^2 with b > x.

  x even: x^x is a square, so lam = 1, y = x^(x/2), and c | y - e.
  x odd:  x^x = x * (x^((x-1)/2))^2, so x / lam must be a square m^2,
          y = m x^((x-1)/2), and c | y - e.

Part 1 lists every member with p, q <= QMAX in increasing order of base.
Since x >= w(p) and x >= w(q), the list holds every member with
x < (QMAX+1)^(QMAX+1). The base increases with x (draft, Proposition 2.1).
Part 2 checks P(b) = F exactly for x < 10^6, and modulo 24 primes above
10^9 for all members.
Part 3 (question 50): in the base of a member, any other 3-digit solution
is (p, x, r) with w(r) - r = (x - q) b - w(p) - lam e^2 (E1), or (p, q', x)
with q' != q and q' b - w(q') = q b - w(q) (E2). The script locates the only
candidate r and q' with high-precision logarithms and tests the equation
modulo the primes. A failure modulo one prime excludes the candidate.

    python3 analysis/r5f_members3.py QMAX XCHECK > analysis/data/r5f_members3.txt
"""
import math
import sys

import gmpy2
import mpmath

sys.set_int_max_str_digits(0)

PRIMES = [p for p in range(10 ** 9, 10 ** 9 + 2000) if gmpy2.is_prime(p)][:24]
W = {}


def w(d):
    if d not in W:
        W[d] = 1 if d == 0 else d ** d
    return W[d]


def squarefree(n):
    return all(n % (k * k) for k in range(2, math.isqrt(n) + 1))


STATS = dict(odd=0, odd_exp=0.0, even_lam=0, even_lam1=0)


def members(qmax):
    out = []
    for lam in range(1, qmax + 1):
        if not squarefree(lam):
            continue
        c = 1
        while lam * c * c <= qmax:
            p = lam * c * c
            e = 0
            while 2 * lam * c * e <= qmax:
                q = 2 * lam * c * e
                x = w(p) + w(q) + lam * e * e
                m = None
                if x % 2 == 0:
                    ok = lam == 1
                    if ok:
                        ymod = pow(x % c, x // 2, c) if c > 1 else 0
                    STATS['even_lam' if lam > 1 else 'even_lam1'] += 1
                else:
                    STATS['odd'] += 1
                    STATS['odd_exp'] += math.exp(-0.5 * math.log(x // lam)) if x < 10 ** 300 else 0.0
                    ok = x % lam == 0 and gmpy2.is_square(x // lam)
                    if ok:
                        m = int(gmpy2.isqrt(x // lam))
                        ymod = (m * pow(x % c, (x - 1) // 2, c)) % c if c > 1 else 0
                if ok and (ymod - e) % c == 0 and x > 2:
                    out.append(dict(lam=lam, c=c, e=e, p=p, q=q, x=x, m=m))
                e += 1
            c += 1
    out.sort(key=lambda d: d['x'])
    return out


def ymod(d, mod):
    x = d['x']
    if d['m'] is None:
        return pow(x % mod, x // 2, mod)
    return d['m'] * pow(x % mod, (x - 1) // 2, mod) % mod


def bmod(d, mod):
    return (ymod(d, mod) - d['e']) * pow(d['c'], -1, mod) % mod


def check_mod(d):
    for ell in PRIMES:
        b = bmod(d, ell)
        P = (d['p'] * b * b + d['q'] * b + d['x']) % ell
        F = (pow(d['p'], d['p'], ell) + (1 if d['q'] == 0 else pow(d['q'], d['q'], ell)) + pow(d['x'], d['x'], ell)) % ell
        if P != F:
            return False
    return True


def check_exact(d):
    x = d['x']
    y = x ** (x // 2) if d['m'] is None else d['m'] * x ** ((x - 1) // 2)
    assert (y - d['e']) % d['c'] == 0
    b = (y - d['e']) // d['c']
    ok = b > x and d['p'] * b * b + d['q'] * b + x == w(d['p']) + w(d['q']) + x ** x
    return ok, b


def log_b(d):
    """natural log of the base, as an mpf at the current precision"""
    x = mpmath.mpf(d['x'])
    if d['m'] is None:
        ly = x / 2 * mpmath.log(x)
    else:
        ly = mpmath.log(d['m']) + (x - 1) / 2 * mpmath.log(x)
    # y - e = y (1 - e/y); e/y is far below the working precision
    return ly - mpmath.log(d['c'])


def inv_rlogr(L):
    """real t with t ln t = L"""
    t = L / mpmath.log(L)
    for _ in range(200):
        t2 = t - (t * mpmath.log(t) - L) / (mpmath.log(t) + 1)
        if abs(t2 - t) < mpmath.mpf(10) ** (-5):
            return t2
        t = t2
    return t


def other_solutions(d):
    """candidates for E1 and E2 and whether a prime excludes each"""
    x, p, q, lam, e = d['x'], d['p'], d['q'], d['lam'], d['e']
    digits = len(str(x))
    mpmath.mp.prec = int(3.4 * digits) + 200
    Lb = log_b(d)
    res = {}
    # E1: w(r) - r = (x - q) b - w(p) - lam e^2; w(r) - r = r^r (1 - r^(1-r)), so ln(w(r) - r) = r ln r to the precision used
    LT = mpmath.log(x - q) + Lb
    r0 = int(mpmath.floor(inv_rlogr(LT)))
    cands = [r for r in (r0 - 1, r0, r0 + 1, r0 + 2) if 1 <= r < x]
    res['E1'] = [(r, excluded_E1(d, r)) for r in cands]
    # E2: w(q') - w(q) = (q' - q) b with q' > q on the decreasing branch: q' ln q' = ln(q' - q) + ln b + ln(1 + w(q)/((q'-q) b))
    # first approximation without the small terms, then two fixed-point steps
    t = inv_rlogr(Lb)
    for _ in range(3):
        t = inv_rlogr(Lb + mpmath.log(t - q))
    q0 = int(mpmath.floor(t))
    cands = [s for s in (q0 - 1, q0, q0 + 1, q0 + 2) if q < s < x]
    res['E2'] = [(s, excluded_E2(d, s)) for s in cands]
    return res


def excluded_E1(d, r):
    for ell in PRIMES:
        b = bmod(d, ell)
        lhs = (pow(r, r, ell) - r) % ell
        rhs = ((d['x'] - d['q']) * b - pow(d['p'], d['p'], ell) - d['lam'] * d['e'] ** 2) % ell
        if lhs != rhs:
            return ell
    return None


def excluded_E2(d, s):
    for ell in PRIMES:
        b = bmod(d, ell)
        wq = 1 if d['q'] == 0 else pow(d['q'], d['q'], ell)
        lhs = (pow(s, s, ell) - wq) % ell
        rhs = (s - d['q']) * b % ell
        if lhs != rhs:
            return ell
    return None


def lg10(n):
    return math.log10(n) if n < 10 ** 300 else (len(str(n)) - 1) + math.log10(int(str(n)[:15]) / 10 ** 14)


def main():
    qmax = int(sys.argv[1])
    xcheck = int(sys.argv[2])  # E1/E2 checks for members with log10 x below this
    ms = members(qmax)
    xs = [d['x'] for d in ms]
    print(f"# 3-digit power-identity members (lam c^2, 2 lam c e, x) under 0^0 = 1, p, q <= {qmax}")
    print(f"# complete for x < {qmax + 1}^{qmax + 1} = 10^{(qmax + 1) * math.log10(qmax + 1):.1f}")
    print(f"# shapes tested: x even with lam = 1: {STATS['even_lam1']}; x even with lam > 1 (excluded): {STATS['even_lam']}; "
          f"x odd: {STATS['odd']}, expected number of squares x/lam, sum of (x/lam)^(-1/2): {STATS['odd_exp']:.3g}")
    print(f"# members: {len(ms)}; distinct x: {len(set(xs))}; odd x: {sum(1 for d in ms if d['x'] % 2)}; lam > 1: {sum(1 for d in ms if d['lam'] > 1)}")
    print("# rank lam c e p q log10(x) log10(log10(b)) check E1 E2   (x written out below 10^40)")
    allmod = True
    for i, d in enumerate(ms, 1):
        lx = lg10(d['x'])
        llb = lx + math.log10(math.log10(d['x']) if lx < 300 else lx) - math.log10(2)
        ok = check_mod(d)
        allmod &= ok
        chk = 'mod24'
        if d['x'] < 10 ** 6:
            ok2, b = check_exact(d)
            chk = f"exact={ok2}" + (f" b={b}" if b < 10 ** 30 else '')
            allmod &= ok2
        else:
            chk = f"mod24={ok}"
        oth = ''
        if lx < xcheck:
            res = other_solutions(d)
            e1 = all(ex is not None for _, ex in res['E1']) and res['E1']
            e2 = all(ex is not None for _, ex in res['E2']) and res['E2']
            oth = f" E1:{'excluded' if e1 else res['E1']} E2:{'excluded' if e2 else res['E2']}"
            if d['x'] < 10 ** 40:
                oth += f" [r cands {[r for r, _ in res['E1']]}, q' cands {[s for s, _ in res['E2']]}]"
        xs_ = str(d['x']) if d['x'] < 10 ** 40 else f"~10^{lx:.2f}"
        print(f"{i} {d['lam']} {d['c']} {d['e']} {d['p']} {d['q']} x={xs_} {lx:.3f} {llb:.3f} {chk}{oth}")
    print(f"# all checks passed: {allmod}")


if __name__ == '__main__':
    main()
