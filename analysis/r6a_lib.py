"""Shared helpers for the round 6 applications scripts (r6a_*).

Vectorized modular powers, the shifted self-power map g(x) = w(x) - x,
and small number-theory helpers.
"""
import numpy as np


def modpow_vec(base, exp, q):
    """base^exp mod q elementwise; base, exp int64 arrays, q < 3e9."""
    base = np.asarray(base, dtype=np.int64) % q
    exp = np.asarray(exp, dtype=np.int64).copy()
    res = np.ones_like(base) % q
    while np.any(exp > 0):
        odd = (exp & 1) == 1
        res = np.where(odd, (res * base) % q, res)
        base = (base * base) % q
        exp >>= 1
    return res


def selfpow(xmax, q):
    """x^x mod q for x = 0..xmax, with 0^0 = 1."""
    x = np.arange(xmax + 1, dtype=np.int64)
    v = modpow_vec(x, x, q)
    v[0] = 1 % q
    return v


def gvals(xmax, q, m):
    """g(x) = w(x) - x mod q for x = 0..xmax, w(0) = m, w(x) = x^x."""
    v = selfpow(xmax, q)
    v[0] = m % q
    x = np.arange(xmax + 1, dtype=np.int64)
    return (v - x) % q


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def divisors(n):
    ds = [1]
    for p, a in factor(n).items():
        ds = [d * p ** i for d in ds for i in range(a + 1)]
    return sorted(ds)


def phi(n):
    r = n
    for p in factor(n):
        r = r // p * (p - 1)
    return r


def tau(n):
    r = 1
    for a in factor(n).values():
        r *= a + 1
    return r
