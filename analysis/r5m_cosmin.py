"""Question 80: spread of x^x - x modulo the odd prime powers q | b - 1.

For each base b <= BMAX and each odd prime power q dividing b - 1, with
f(x) = x^x - x over the digits x = 0..b-1 (0^0 = 0, so f(0) = 0):

  phi(h) = (1/b) sum_x e(h f(x) / q)                 (one FFT of the histogram)
  c_pois = min over h != 0 of 1 - Re phi(h)          (Poisson rate: |E e(hS/q)| = exp(-lambda b (1 - Re phi)))
  c_mult = min over h != 0 of 1 - |phi(h)|           (rate for a fixed number of uniform digits)

Writes one line per (b, q): b q p c_pois h_pois c_mult h_mult.

usage: python3 r5m_cosmin.py BMAX OUT [workers]
"""
import sys
from multiprocessing import Pool

import numpy as np


def factor(n):
    out = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def selfpow_mod(x, q):
    """x^x mod q for an int64 array x (q < 3e9 / q keeps products in int64)"""
    res = np.ones_like(x)
    base = x % q
    e = x.copy()
    while e.any():
        odd = (e & 1).astype(bool)
        res = np.where(odd, res * base % q, res)
        base = base * base % q
        e >>= 1
    res[x == 0] = 0  # 0^0 = 0
    return res


def one_base(b):
    out = []
    x = np.arange(b, dtype=np.int64)
    for p, a in factor(b - 1).items():
        if p == 2:
            continue
        for k in range(1, a + 1):
            q = p ** k
            f = (selfpow_mod(x, q) - x) % q
            hist = np.bincount(f, minlength=q).astype(float)
            # phi(h) = (1/b) sum_r hist[r] e(h r / q); np.fft.fft uses e(-h r/q), same modulus, conj phase
            phi = np.fft.fft(hist) / b
            re = phi.real[1:]
            ab = np.abs(phi[1:])
            hp = int(np.argmax(re)) + 1
            hm = int(np.argmax(ab)) + 1
            out.append((b, q, p, 1 - re[hp - 1], hp, 1 - ab[hm - 1], hm))
    return out


def main():
    bmax = int(sys.argv[1])
    path = sys.argv[2]
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    with Pool(workers) as pool, open(path, 'w') as fh:
        fh.write("# b q p c_pois h_pois c_mult h_mult   (0^0 = 0, digits 0..b-1)\n")
        for rows in pool.imap(one_base, range(3, bmax + 1), chunksize=50):
            for r in rows:
                fh.write("%d %d %d %.6f %d %.6f %d\n" % r)


if __name__ == '__main__':
    main()
