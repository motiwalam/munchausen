"""3-digit factorions with one large digit: bounds and a complete check.

Round 6, question 97 (docs/library/drafts/round6-factorials.md, section 1).

A 3-digit string (d2, d1, d0) is a factorion in base b > max digit when
d2 b^2 + d1 b + d0 = w(d2) + w(d1) + w(d0), w(x) = x! and w(0) = m (m = 1 is
0! = 1, m = 0 the other convention). Multiply by 4 d2 and complete the
square: U^2 = M + K with U = 2 d2 b + d1 and, for one large digit x,

    last     (p, q, x):  M = 4p x!,  K = q^2 + 4p (w(p) + w(q) - x)
    middle   (p, x, r):  M = 4p x!,  K = x^2 + 4p (w(p) + w(r) - r)
    leading  (x, q, r):  M = 4x x!,  K = q^2 + 4x (w(q) + w(r) - r)

Lemma 1.2: if K is not a square in Q_l and v_l(M) > v_l(K) + 2 v_l(2), there
is no solution. Lemma 1.3 bounds the least inert prime l0 of Q(sqrt K):

    Delta > 0: table (r6f_inert.txt) up to 4e6, then Delta^0.45 (Trevino 2012)
    Delta < 0: table up to 4e6, then Polya-Vinogradov (Pomerance 2011 constants)
    under GRH: table, then (1.17 log q + 15.2)^2, and (1.17 log q - 6.36)^2
               for q >= 1e8 (Bach 1990, as stated by McGown)

Part 1 prints X0, the bound beyond which K non-square excludes x, for each
position and digit pair up to BD, both conventions, unconditionally and
under GRH, and the bounds uniform in B. Part 2 checks every x up to X0 for
all digit pairs up to BD: exactly for x <= 400, by local obstructions above.
The x with K a perfect square in the leading position (Brocard type) are
listed and left to r6f_brocard.c.

    python3 analysis/r6f_factorion3.py 10 all analysis/data/r6f_brocard_cand.txt \
        > analysis/data/r6f_factorion3.txt
"""
import math
import sys
from math import factorial, isqrt

import numpy as np
import sympy

TABLE_Q = 4 * 10 ** 6
EULER_GAMMA = 0.5772156649015329


def load_table(path='analysis/data/r6f_inert.txt'):
    rec = {1: [], -1: []}
    for line in open(path):
        if line.startswith('#'):
            continue
        sg, D, l = line.split()
        rec[1 if sg == '+' else -1].append((math.log(abs(int(D))), int(l)))
    return rec


REC = load_table()


def lam_table(logq, sign):
    """max least inert prime over 1 < |Delta| <= q (sign 0: both signs)"""
    if sign == 0:
        return max(lam_table(logq, 1), lam_table(logq, -1))
    best = 0
    for lD, l in REC[sign]:
        if lD <= logq + 1e-12:
            best = l
    return best


def lam_pv(logq):
    """least prime with chi = -1 for an odd primitive real chi mod q (q > 4e6)"""
    llq = math.log(logq)
    S = math.exp(logq / 2) * (logq / (2 * math.pi) + llq / math.pi + 1)
    phi_low = 1 / (math.exp(EULER_GAMMA) * llq + 2.50637 / llq)
    two_omega = math.exp(math.log(2) * 1.3841 * logq / llq)
    return (S + two_omega) / phi_low + 1


def lam_unc(logq, sign):
    if logq <= math.log(TABLE_Q):
        return lam_table(logq, sign)
    pos = math.exp(0.45 * logq)
    if sign > 0:
        return pos
    neg = lam_pv(logq)
    return neg if sign < 0 else max(pos, neg)


def lam_grh(logq, sign):
    if logq <= math.log(TABLE_Q):
        return lam_table(logq, sign)
    if logq < math.log(1e8):
        return (1.17 * logq + 15.2) ** 2
    return (1.17 * logq - 6.36) ** 2


def excluded(lx, logK, sign, grh):
    """True if Lemmas 1.2 and 1.3 exclude x = e^lx when |K| <= e^logK, K not a square"""
    x = math.exp(lx)
    log2K = logK / math.log(2)
    if grh:
        L = max(lam_grh(logK + math.log(4), sign), 2)
        need = max(2 * (log2K + 3), L * (logK / math.log(L) + 3))
        return x >= need
    # (A) l0 does not divide f: l0 <= x suffices (x >= 4 for l0 = 2)
    if x < 4 or lam_unc(logK + math.log(4), sign) > x:
        return False
    # (B) l0 divides f: then l0 <= Lam(4|K| / l0^2). l - Lam(4|K|/l^2) is
    # increasing in l: bisect for the largest real l with l <= Lam(4|K|/l^2)
    lo, hi = 2.0, max(2.0, x)
    if lo <= lam_unc(logK + math.log(4) - 2 * math.log(lo), sign):
        while hi - lo > 1e-6 * hi:
            mid = (lo + hi) / 2
            if mid <= lam_unc(logK + math.log(4) - 2 * math.log(mid), sign):
                lo = mid
            else:
                hi = mid
    need = max(2 * (log2K + 3), lo * (logK / math.log(lo) + 3))
    return x >= need


def threshold(logKmax, sign, grh, xstart, lxmax=math.log(1e30), step=math.log(1.1)):
    """X0 >= xstart such that every x in [X0, e^lxmax] is excluded. logKmax(lx)
    must be increasing in lx. The interval [x_i, x_(i+1)] is safe when x_i is
    excluded with |K| bounded by Kmax(x_(i+1))."""
    lx0 = math.log(xstart)
    X0 = lx0
    lx = lx0
    while lx < lxmax:
        nlx = lx + step
        if not excluded(lx, logKmax(nlx), sign, grh):
            X0 = nlx
        lx = nlx
    return math.ceil(math.exp(X0))


def logadd(a, b):
    hi, lo = max(a, b), min(a, b)
    return hi + math.log1p(math.exp(lo - hi))


def w_of(m):
    return lambda d: m if d == 0 else factorial(d)


def cases(BD, m):
    w = w_of(m)
    out = []
    for p in range(1, BD + 1):
        for q in range(BD + 1):
            out.append(('last', p, q))
    for p in range(1, BD + 1):
        for r in range(BD + 1):
            out.append(('middle', p, r))
    for q in range(BD + 1):
        for r in range(BD + 1):
            out.append(('leading', q, r))
    return out


def case_data(kind, a, c, m, xlim):
    """(sign of K, logKmax(log x), K(x), sorted x with K(x) a square, x <= xlim for
    the leading position). sign 0 means either sign."""
    w = w_of(m)
    if kind == 'last':
        p, q = a, c
        c0 = q * q + 4 * p * (w(p) + w(q))
        sq = sorted({(c0 - t * t) // (4 * p) for t in range(isqrt(c0) + 1) if (c0 - t * t) % (4 * p) == 0})
        return 0, (lambda lx: logadd(math.log(c0), math.log(4 * p) + lx)), (lambda x: c0 - 4 * p * x), sq
    if kind == 'middle':
        p, r = a, c
        A = w(p) + w(r) - r
        N = 4 * p * A
        sq = sorted({(N // d - d) // 2 for d in sympy.divisors(N) if d * d < N and (N // d - d) % 2 == 0})
        return 1, (lambda lx: logadd(2 * lx, math.log(N))), (lambda x: x * x + N), sq
    q, r = a, c
    A = w(q) + w(r) - r
    if A == 0:
        return None
    mod = 4 * A
    roots = sympy.sqrt_mod(q * q % mod, mod, all_roots=True) if mod > 1 else [0]
    sq = set()
    for r0 in roots:
        t = r0
        while t * t <= q * q + 4 * A * xlim:
            if t * t >= q * q and (t * t - q * q) % mod == 0:
                sq.add((t * t - q * q) // mod)
            t += mod
    lq = 2 * math.log(q) if q else -1e9
    return 1, (lambda lx: logadd(lq, math.log(4 * A) + lx)), (lambda x: q * q + 4 * x * A), sorted(sq)


def x_abc(logR, xmax=10 ** 9):
    """largest x with log(4x) + log x! < 7 log 2 + 14 (1.01624 x + logR(x)): the
    consequence c < rad(abc)^(7/4) of Baker's explicit abc conjecture allows no
    leading-position solution U^2 = 4x x! + s^2 beyond it"""
    best = 0
    x = 2
    while x < xmax:
        if math.log(4 * x) + math.lgamma(x + 1) < 7 * math.log(2) + 14 * (1.01624 * x + logR(x)):
            best = x
        x = x + 1 if x < 1000 else int(x * 1.0001) + 1
    return best


def string_of(kind, a, c, x):
    if kind == 'last':
        return (a, c, x)
    if kind == 'middle':
        return (a, x, c)
    return (x, a, c)


def exact_solution(s, m):
    w = w_of(m)
    d2, d1, d0 = s
    if d2 == 0:
        return None
    F = w(d2) + w(d1) + w(d0)
    D = d1 * d1 + 4 * d2 * (F - d0)
    if D < 0:
        return None
    U = isqrt(D)
    if U * U != D or (U - d1) % (2 * d2):
        return None
    b = (U - d1) // (2 * d2)
    return b if b > max(s) else None


def vl_fact(x, l):
    v, t = 0, x
    while t:
        t //= l
        v += t
    return v


def local_obstruction(K, Mcoef, x, lmax):
    """a prime l <= lmax with K not a square in Q_l and v_l(Mcoef x!) > v_l(K) + 2 v_l(2)"""
    for l in sympy.primerange(2, lmax + 1):
        vK, Kp = 0, K
        while Kp % l == 0:
            Kp //= l
            vK += 1
        vM = vl_fact(x, l) + (0 if Mcoef % l else sympy.multiplicity(l, Mcoef))
        if vM <= vK + (2 if l == 2 else 0):
            continue
        if vK % 2:
            return l
        if l == 2:
            if Kp % 8 != 1:
                return l
        elif pow(Kp % l, (l - 1) // 2, l) == l - 1:
            return l
    return None


SMALL = list(sympy.primerange(3, 300))
LEG = {l: np.array([0] + [1 if pow(r, (l - 1) // 2, l) == 1 else -1 for r in range(1, l)], dtype=np.int8)
       for l in SMALL}


def check_case(kind, a, c, m, X, sq):
    """all x <= X with K(x) not a square: solutions, undecided x"""
    w = w_of(m)
    sols, undecided = [], []
    _, _, Kf, _ = case_data(kind, a, c, m, 0) if kind != 'leading' else (None, None, None, None)
    if kind == 'leading':
        Kf = lambda x: a * a + 4 * x * (w(a) + w(c) - c)
    sqset = set(sq)
    for x in range(0, min(X, 400) + 1):
        if x in sqset:
            continue
        s = string_of(kind, a, c, x)
        if s[0] == 0:
            continue
        b = exact_solution(s, m)
        if b is not None:
            sols.append((s, b))
    if X <= 400:
        return sols, undecided
    xs = np.arange(401, X + 1, dtype=np.int64)
    alive = np.ones(len(xs), dtype=bool)
    for l in SMALL:
        if kind == 'last':
            p, q = a, c
            Kl = ((q * q + 4 * p * (w(p) + w(q))) % l - (4 * p % l) * (xs % l)) % l
        elif kind == 'middle':
            p, r = a, c
            Kl = ((xs % l) * (xs % l) + (4 * p * (w(p) + w(r) - r)) % l) % l
        else:
            q, r = a, c
            Kl = ((q * q) % l + 4 * (xs % l) * ((w(q) + w(r) - r) % l)) % l
        # K a nonzero nonresidue mod l and l <= x: v_l(K) = 0 < v_l(M)
        alive &= ~((LEG[l][Kl] == -1) & (xs >= l))
    for x in xs[alive]:
        x = int(x)
        if x in sqset:
            continue
        K = Kf(x)
        Mcoef = 4 * (a if kind != 'leading' else x)
        if local_obstruction(K, Mcoef, x, min(x, 10 ** 5)) is None:
            s = string_of(kind, a, c, x)
            if x <= 3000:
                b = exact_solution(s, m)
                if b is not None:
                    sols.append((s, b))
            else:
                undecided.append(x)
    return sols, undecided


def main():
    BD = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    part = sys.argv[2] if len(sys.argv) > 2 else 'all'
    cand_path = sys.argv[3] if len(sys.argv) > 3 else '/dev/null'
    if part in ('all', 'uniform'):
        print("## part 1a: bounds uniform in B (the two other digits at most B, both conventions)")
        print("# beyond X0, an x with K(x) not a square is excluded; X0 unconditional, and under GRH")
        print("# B | last: X0, X0 GRH | middle: X0, X0 GRH | leading: X0, X0 GRH")
        for B in (2, 5, 10, 20, 50, 100):
            lBf = math.lgamma(B + 1)
            c0 = math.log(4 * B * (2 * math.exp(lBf) + B) + B * B)
            last = lambda lx: logadd(c0, math.log(4 * B) + lx)
            mid = lambda lx: logadd(2 * lx, math.log(8 * B) + lBf)
            lead = lambda lx: logadd(2 * math.log(B), math.log(8) + lBf + lx)
            row = []
            for f, sign in ((last, 0), (mid, 1), (lead, 1)):
                u = threshold(f, sign, False, 4, lxmax=math.log(1e250))
                g = threshold(f, sign, True, 4, lxmax=math.log(1e250))
                row.append(f"{u:.4g}, {min(u, g):.4g}")
            print(f"{B} | " + " | ".join(row))
            sys.stdout.flush()
    if part in ('all', 'check'):
        logR10 = lambda x: math.log(100 + 8 * x * factorial(10))
        XL = x_abc(logR10)
        print(f"## part 1b and 2: each digit pair up to {BD}, both conventions")
        print(f"# x_abc for the leading position with digits <= 10: {XL} (square-K x listed up to it)")
        print("# m kind a c X0unc X0grh Xcheck | solutions | square-K x (count, largest) | undecided")
        tot = dict(cases=0, sols=0, squares=0, undecided=0, maxX=0)
        cand = open(cand_path, 'w')
        allsols = set()
        for m in (1, 0):
            for kind, a, c in cases(BD, m):
                cd = case_data(kind, a, c, m, XL)
                if cd is None:
                    print(f"{m} {kind} {a} {c} K = 0: 4x x! must be a square, impossible for x >= 4 (Bertrand)")
                    for x in range(0, 4):
                        b = exact_solution(string_of(kind, a, c, x), m)
                        if b is not None:
                            allsols.add((m, string_of(kind, a, c, x), b))
                    continue
                sign, logK, Kf, sq = cd
                X0u = threshold(logK, sign, False, 4)
                X0g = min(X0u, threshold(logK, sign, True, 4))
                X = max(X0u, 150)
                sols, und = check_case(kind, a, c, m, X, sq)
                # square-K x: exact up to 3000, the rest to the sieve r6f_brocard.c
                for x in sq:
                    if x <= 3000:
                        s_ = string_of(kind, a, c, x)
                        if s_[0] == 0:
                            continue
                        b = exact_solution(s_, m)
                        if b is not None:
                            sols.append((s_, b))
                    else:
                        coef = 4 * (a if kind != 'leading' else x)
                        cand.write(f"{x} {coef} {isqrt(Kf(x))} {m} {kind} {a} {c}\n")
                for s_, b in sols:
                    allsols.add((m, s_, b))
                tot['cases'] += 1
                tot['sols'] += len(sols)
                tot['squares'] += len(sq)
                tot['undecided'] += len(und)
                tot['maxX'] = max(tot['maxX'], X)
                big = [x for x in sq if x > 3000]
                print(f"{m} {kind} {a} {c} {X0u} {X0g} {X} | {sols} | {len(sq)}, {len(big)} above 3000, "
                      f"max {max(sq) if sq else None} | {und}")
                sys.stdout.flush()
        cand.close()
        print(f"# total: {tot}")
        print("# distinct solutions (m, string, base):")
        for t in sorted(allsols, key=lambda t: (t[0], t[2])):
            print(f"#   {t}")


if __name__ == '__main__':
    main()
