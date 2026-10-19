"""Round 5, question 86: a mixing statistic for every world.

For random digit strings c of the dominant length whose sum F(c) has the
same length and meets the identity of the world, compare the digits of
F(c) below its top 3 positions with what c still needs there, r = c minus
the top 3 digits of F(c). For each digit value v, a(v) is the chance that
the low histogram of F(c) has exactly r_v copies of v. The comparator U
keeps the top 3 digits of F(c) and the class of the identity, and draws
the low digits at random. The statistic is

    R = prod over v of a_F(v) / a_U(v),

the factor by which the low digits of F match c more often than random
digits do, if the values were independent, and the ratio of the mean
agreement rates. The model assumes both are 1. A second factor compares
the chance that the top 3 digits of F(c) lie inside c with the same chance
for the top 3 digits of an independent string of the world (the forced top
digits of section 11.2).
Output: data/r5e_mixing.txt.

    python3 r5e_mixing.py [samples]
"""
import math
import os
import random
import sys
from decimal import Decimal, getcontext

import numpy as np

import r4f_lib as R4

HERE = os.path.dirname(os.path.abspath(__file__))
TOP = 3


class Acc:
    def __init__(self, nv):
        self.F = np.zeros(nv)
        self.U = np.zeros(nv)
        self.n = 0
        self.topok = 0
        self.topv = 0
        self.prev = None

    def add(self, chist, fdig, udig, nv, cdig=None):
        """fdig, udig: digit lists, top first (values 0..nv-1)."""
        top = np.bincount(fdig[:TOP], minlength=nv)
        if np.all(top <= chist):
            self.topok += 1
        # the top digits of an independent string of the world (the previous c)
        if self.prev is not None and np.all(np.bincount(self.prev, minlength=nv) <= chist):
            self.topv += 1
        self.prev = np.array(cdig[:TOP]) if cdig is not None else None
        r = np.maximum(chist - top, 0)
        lf = np.bincount(fdig[TOP:], minlength=nv)
        lu = np.bincount(udig[TOP:], minlength=nv)
        self.F += (lf == r)
        self.U += (lu == r)
        self.n += 1

    def result(self):
        ok = (self.U > 0) & (self.F > 0)
        logr = float(np.sum(np.log(self.F[ok] / self.U[ok])))
        # standard error by the delta method, values taken independent
        se = math.sqrt(float(np.sum((1 - self.F[ok] / self.n) / self.F[ok] + (1 - self.U[ok] / self.n) / self.U[ok])))
        return math.exp(logr), se, self.F.sum() / self.U.sum(), self.topok / max(self.n, 1), \
            self.topok / max(self.topv, 1)


# ---------- integer-like worlds: base b > 0, base -b, factorions ----------

def to_digits(n, base):
    """digits top first; base may be negative"""
    out = []
    if base > 0:
        while n:
            n, r = divmod(n, base)
            out.append(r)
    else:
        b = -base
        while n:
            r = n % b
            out.append(r)
            n = (n - r) // base
    return out[::-1]


def low_with_residue(rng, nlow, nv, need, M):
    """nlow uniform digits 0..nv-1 whose sum is == need (mod M)."""
    while True:
        d = rng.integers(0, nv, size=nlow)
        if (int(d.sum()) - need) % M == 0:
            return d


def world_int(base, L, weights, M, samples, rng):
    b = abs(base)
    acc = Acc(b)
    tries = 0
    while acc.n < samples:
        tries += 1
        c = rng.integers(0, b, size=L)
        c[0] = rng.integers(1, b)
        F = sum(weights[int(x)] for x in c)
        if (F - int(c.sum())) % M:
            continue
        fd = to_digits(F, base)
        if len(fd) != L:
            continue
        need = (sum(fd) - sum(fd[:TOP]))
        low = low_with_residue(rng, L - TOP, b, need, M)
        acc.add(np.bincount(c, minlength=b), np.array(fd), np.concatenate([fd[:TOP], low]).astype(int), b, list(c))
    return acc


# ---------- the factorial number system ----------

def fact_digits(n):
    """digits d_L..d_1 of n = sum d_i i!, top first"""
    out = []
    i = 2
    while n:
        out.append(n % i)
        n //= i
        i += 1
    return out[::-1]


def world_factorial(L, m, samples, rng):
    lo, hi = math.factorial(L), math.factorial(L + 1)
    nv = L + 1
    acc = Acc(nv)
    w = [m] + [x ** x for x in range(1, nv)]
    while acc.n < samples:
        n = int(rng.integers(lo, hi))
        c = fact_digits(n)
        F = sum(w[x] for x in c)
        fd = fact_digits(F)
        if len(fd) != L:
            continue
        # positions L..1 top first; position p allows digits 0..p
        low = [int(rng.integers(0, p + 1)) for p in range(L - TOP, 0, -1)]
        acc.add(np.bincount(c, minlength=nv), np.array(fd), np.array(fd[:TOP] + low), nv, c)
    return acc


# ---------- F_q[T] ----------

def world_ffield(q, e, L, m, B, samples, rng):
    nv = q ** e
    acc = Acc(nv)
    # weight of each digit code: d(T^(q^deg d)), as a polynomial
    wts = []
    for code in range(nv):
        d = R4.decode(code, q, e)
        if not d:
            wts.append([m] if m else [])
            continue
        j = len(d) - 1
        p = [0] * ((len(d) - 1) * q ** j + 1)
        for t, a in enumerate(d):
            p[t * q ** j] = a
        wts.append(R4.trim(p))
    Bm1 = R4.padd(B, [q - 1], q)
    while acc.n < samples:
        c = rng.integers(0, nv, size=L)
        c[0] = rng.integers(1, nv)
        F = []
        for x in c:
            F = R4.padd(F, wts[int(x)], q)
        # identity: F == sum of digits (mod B - 1)
        s = []
        for x in c:
            s = R4.padd(s, R4.decode(int(x), q, e), q)
        if R4.pdivmod(R4.padd(F, [(-a) % q for a in s], q), Bm1, q)[1]:
            continue
        fd = [R4.encode(R4.trim(dd), q) for dd in R4.digits(F, B, q, e)][::-1]
        if len(fd) != L:
            continue
        # comparator: low digits uniform with the same digit sum (a vector of F_q^e)
        target = [0] * e
        for code in fd[TOP:]:
            for t, a in enumerate(R4.decode(code, q, e) + [0] * e):
                if t < e:
                    target[t] = (target[t] + a) % q
        low = [int(rng.integers(0, nv)) for _ in range(L - TOP - 1)]
        acc_s = [0] * e
        for code in low:
            for t, a in enumerate(R4.decode(code, q, e) + [0] * e):
                if t < e:
                    acc_s[t] = (acc_s[t] + a) % q
        last = [(target[t] - acc_s[t]) % q for t in range(e)]
        low.append(R4.encode(R4.trim(last), q))
        acc.add(np.bincount(c, minlength=nv), np.array(fd), np.array(fd[:TOP] + low), nv, list(c))
    return acc


# ---------- the Pisot base eps_x ----------

class Pisot:
    def __init__(self, x):
        getcontext().prec = 80
        self.x = x
        self.eps = (Decimal(x) + (Decimal(x * x + 4)).sqrt()) / 2
        self.F = {0: 0, 1: 1}
        for i in range(2, 200):
            self.F[i] = x * self.F[i - 1] + self.F[i - 2]
        for i in range(1, 200):
            self.F[-i] = (-1) ** (i + 1) * self.F[i]

    def pw(self, i):
        """eps^i = F_(i-1) + F_i eps"""
        return self.F[i - 1], self.F[i]

    def val(self, a, b):
        return Decimal(a) + Decimal(b) * self.eps

    def expand(self, n):
        k = 0
        while self.val(*self.pw(k + 1)) <= n:
            k += 1
        ra, rb = n, 0
        out = []
        i = k
        while True:
            a, b = self.pw(i)
            v = self.val(a, b)
            d = int(self.val(ra, rb) / v)
            d = max(0, min(d, self.x))
            while d > 0 and self.val(ra - d * a, rb - d * b) < 0:
                d -= 1
            while d < self.x and self.val(ra - (d + 1) * a, rb - (d + 1) * b) >= 0:
                d += 1
            ra -= d * a
            rb -= d * b
            out.append(d)
            i -= 1
            if i < 0 and ra == 0 and rb == 0:
                break
            if len(out) > 300:
                raise RuntimeError("no termination")
        return k, out


def world_pisot(x, T, m, samples, rng, nlo, nhi):
    P = Pisot(x)
    nv = x + 1
    w = [m] + [d ** d for d in range(1, nv)]
    acc = Acc(nv)
    while acc.n < samples:
        n = int(rng.integers(nlo, nhi))
        k, c = P.expand(n)
        if len(c) != T:
            continue
        F = sum(w[d] for d in c)
        if (F - sum(c)) % x:
            continue
        kf, fd = P.expand(F)
        if len(fd) != T:
            continue
        # comparator: a random integer with the same top 3 digits, length and residue mod x
        pa = pb = 0
        for t in range(TOP):
            a, b = P.pw(kf - t)
            pa += fd[t] * a
            pb += fd[t] * b
        lo = P.val(pa, pb)
        hi = lo + P.val(*P.pw(kf - TOP + 1))
        ilo, ihi = int(lo.to_integral_value(rounding='ROUND_CEILING')), int(hi)
        u = None
        for _ in range(200):
            nn = int(rng.integers(ilo, ihi + 1))
            if (nn - F) % x:
                continue
            ku, ud = P.expand(nn)
            if ku == kf and len(ud) == T and ud[:TOP] == fd[:TOP]:
                u = ud
                break
        if u is None:
            continue
        acc.add(np.bincount(c, minlength=nv), np.array(fd), np.array(u), nv, c)
    return acc


def main():
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    rng = np.random.default_rng(86)
    rows = []
    for m in (0, 1):
        w = [m] + [x ** x for x in range(1, 20)]
        rows.append((f"integers b=20, 19 digits, 0^0={m}", world_int(20, 19, w, 19, samples, rng)))
        rows.append((f"base -20, 19 digits, 0^0={m}", world_int(-20, 19, w, 21, samples, rng)))
        wf = [m] + [math.factorial(x) for x in range(1, 20)]
        rows.append((f"factorions b=20, 14 digits, w(0)={m}", world_int(20, 14, wf, 19, samples, rng)))
        rows.append((f"factorial system L=12, 0^0={m}", world_factorial(12, m, samples, rng)))
        for bcode in (130, 260, 400):
            B = R4.decode(bcode, 5, 4)
            rows.append((f"F_5[T] e=3 B={bcode}, 17 digits, 0^0={m}",
                         world_ffield(5, 3, 17, m, B, max(samples // 10, 500), rng)))
        rows.append((f"Pisot x=6, T=12, 0^0={m}", world_pisot(6, 12, m, max(samples // 5, 500), rng, 2000, 200000)))
    out = ["# r5e_mixing.py: R = prod a_F(v)/a_U(v) over digit values, low digits below the top 3",
           "# world | samples | R | se of log R | ratio of the mean agreement rates F / U | "
           "top 3 of F inside c | top factor: that share over the share for the top 3 of an independent string"]
    for name, acc in rows:
        Rv, se, ar, top, tf = acc.result()
        out.append(f"{name} | {acc.n} | {Rv:.3f} | {se:.3f} | {ar:.4f} | {top:.3f} | {tf:.3f}")
        print(out[-1], flush=True)
    with open(os.path.join(HERE, 'data', 'r5e_mixing.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")


if __name__ == '__main__':
    main()
