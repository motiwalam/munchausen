"""Round 6, section 2: collisions of the self-power map and of its shift.

For primes p this computes
  I(p)  = #{1 <= x, y <= p-1 : x^x == y^y (mod p)},
  Ng(p) = #{1 <= x, y <= p-1 : x^x - x == y^y - y (mod p)},
  Nd(p) = the same for g over the digits 0..p of base b = p + 1, with
          w(0) = 0 (Nd0) and w(0) = 1 (Nd1),
  F(p)  = #{1 <= x <= p-1 : x^x == x}, the fixed points of Kurlberg, Luca
          and Shparlinski (the fibre of g over 0),
and compares I(p) with Conjecture 6.4(a) of Holden and Moree (Math. Comp.
75 (2006)). For small p it also evaluates the shifted analogue of their
heuristic: u = x mod p and v = x mod (p-1) independent and uniform.

    python3 r6a_selfpower.py collide PMAX       -> data/r6a_selfpower_collide.txt
    python3 r6a_selfpower.py model PMAX         -> data/r6a_selfpower_model.txt
    python3 r6a_selfpower.py digits BMAX        -> data/r6a_selfpower_digits.txt

The mode digits computes, for every base b, q = b - 1 and w(0) = 0, the
collision count N_M = #{x, y <= M : g(x) == g(y) (mod q)} and the constant
kappa_CS(b) = max over b/2 <= M <= b-1 of q N_M / (M+1)^2 of Proposition 2.1.
"""
import os
import sys

import numpy as np

from r6a_lib import selfpow, gvals, primes_upto, divisors, phi

HERE = os.path.dirname(os.path.abspath(__file__))


def coll(v, q):
    c = np.bincount(v, minlength=q)
    return int((c.astype(np.int64) ** 2).sum()), int(c.max())


def hm_pred(p):
    n = p - 1
    tot = 0.0
    for m in divisors(n):
        s = sum(phi(d * m) / d for d in divisors(n // m))
        tot += phi(m) / m ** 2 * s * s
    return n + tot


def collide(pmax):
    out = open(os.path.join(HERE, 'data', 'r6a_selfpower_collide.txt'), 'w')
    out.write('# p  I(p)  HM(p)  I/HM  Ng(p)  (Ng-(p-1))/(p-1)  Nd0  Nd1  maxfib_g  F(p)\n')
    rows = []
    for p in primes_upto(pmax):
        p = int(p)
        if p < 11:
            continue
        s = selfpow(p - 1, p)[1:]           # x = 1..p-1
        I, _ = coll(s, p)
        x = np.arange(1, p, dtype=np.int64)
        g = (s - x) % p
        Ng, mf = coll(g, p)
        F = int((g == 0).sum())
        Nd0, _ = coll(gvals(p, p, 0), p)
        Nd1, _ = coll(gvals(p, p, 1), p)
        hm = hm_pred(p)
        rows.append((p, I, hm, Ng, Nd0, Nd1, mf, F))
        out.flush() if p % 1000 < 20 else None
        out.write("%d %d %.1f %.4f %d %.4f %d %d %d %d\n" % (
            p, I, hm, I / hm, Ng, (Ng - (p - 1)) / (p - 1), Nd0, Nd1, mf, F))
    out.close()
    a = np.array([[r[0], r[1] / r[2], (r[3] - (r[0] - 1)) / (r[0] - 1),
                   r[4] / (r[0] + 1), r[5] / (r[0] + 1), r[6], r[7],
                   r[1] / (r[0] - 1)] for r in rows])
    for lo, hi in [(11, 1000), (1000, 10000), (10000, 50000), (50000, 10 ** 9)]:
        sel = (a[:, 0] >= lo) & (a[:, 0] < hi)
        if not sel.any():
            continue
        b = a[sel]
        print('p in [%d, %d): %d primes' % (lo, hi, len(b)))
        print('  I/HM  mean %.4f  min %.4f  max %.4f' % (b[:, 1].mean(), b[:, 1].min(), b[:, 1].max()))
        print('  offdiag Ng/(p-1) mean %.4f  min %.4f  max %.4f' % (b[:, 2].mean(), b[:, 2].min(), b[:, 2].max()))
        print('  Nd0/(p+1) mean %.4f max %.4f;  Nd1/(p+1) mean %.4f max %.4f' % (
            b[:, 3].mean(), b[:, 3].max(), b[:, 4].mean(), b[:, 4].max()))
        print('  max fibre of g: max %d;  fixed points F(p): mean %.2f max %d;'
              ' share of p with max fibre = F(p): %.3f' % (
            b[:, 5].max(), b[:, 6].mean(), b[:, 6].max(), (b[:, 5] == b[:, 6]).mean()))
        print('  I/(p-1) mean %.4f' % b[:, 7].mean())


def model(pmax):
    """Shifted heuristic: P(c) = P(u^v - u = c), u in F_p^*, v mod p-1 uniform.
    Returns the predicted off-diagonal collisions (p-1)(p-2) sum_c P(c)^2,
    over p - 1."""
    out = open(os.path.join(HERE, 'data', 'r6a_selfpower_model.txt'), 'w')
    out.write('# p  model_offdiag/(p-1)  actual_offdiag/(p-1)\n')
    for p in primes_upto(pmax):
        p = int(p)
        if p < 11:
            continue
        n = p - 1
        # discrete log table
        from sympy import primitive_root
        gr = primitive_root(p)
        ind = np.zeros(p, dtype=np.int64)
        y = 1
        for i in range(n):
            ind[y] = i
            y = y * gr % p
        P = np.zeros(p)
        c = np.arange(p, dtype=np.int64)
        for i in range(n):
            u = pow(gr, i, p)
            gd = np.gcd(i, n)
            gd = n if i == 0 else gd
            orde = n // gd
            a = (u + c) % p
            ok = (a != 0) & (ind[a] % gd == 0)
            P[ok] += 1.0 / orde        # (p-1)/ord(u) values of v, over (p-1)^2
        P /= n                          # now P(c) = sum_u (1/ord u) 1[...] / (p-1)
        pred = (n - 1) * n * (P ** 2).sum() / n
        s = selfpow(p - 1, p)[1:]
        g = (s - np.arange(1, p)) % p
        Ng, _ = coll(g, p)
        act = (Ng - n) / n
        out.write('%d %.4f %.4f\n' % (p, pred, act))
        print(p, round(pred, 4), round(act, 4))
    out.close()


def digits(bmax):
    out = open(os.path.join(HERE, 'data', 'r6a_selfpower_digits.txt'), 'w')
    out.write('# b  N_(b-1)/b  kappa_CS\n')
    worst = {0: (0, 0), 1: (0, 0)}
    for b in range(12, bmax + 1):
        q = b - 1
        g = gvals(b - 1, q, 0)
        cnt = np.zeros(q, dtype=np.int64)
        N = 0
        kap = 0.0
        for M in range(b):
            v = g[M]
            N += 2 * cnt[v] + 1
            cnt[v] += 1
            if 2 * M + 2 >= b:
                kap = max(kap, q * N / (M + 1) ** 2)
        out.write('%d %.4f %.4f\n' % (b, N / b, kap))
        par = b % 2
        if kap > worst[par][0]:
            worst[par] = (kap, b)
    out.close()
    print('even bases: max kappa_CS %.3f at b = %d; odd bases: max %.3f at b = %d' % (
        worst[0][0], worst[0][1], worst[1][0], worst[1][1]))


if __name__ == '__main__':
    mode = sys.argv[1]
    pmax = int(sys.argv[2])
    {'collide': collide, 'model': model, 'digits': digits}[mode](pmax)
