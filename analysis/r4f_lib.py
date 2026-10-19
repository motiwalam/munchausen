"""Shared tools for the round 4 study of F_q[T] (q prime), weight d^(q^deg d).

Polynomials are lists of ints mod q, lowest coefficient first, no trailing
zeros. The group G of class sums has coordinates (j, t), the coefficient of
T^t in D_j (t <= j < e), and with m = 1 one more coordinate z mod q.
F(x) = sum x_jt T^(t q^j) + m z. Its base-B digits are linear in x, so one
matrix per base gives the digit vectors of all F(x) at once.
"""
import itertools
import numpy as np


def trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def padd(a, b, q):
    n = max(len(a), len(b))
    return trim([((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % q for i in range(n)])


def pmul(a, b, q):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return trim([c % q for c in r])


def pdivmod(a, b, q):
    a = list(a)
    inv = pow(b[-1], q - 2, q)
    quo = [0] * max(len(a) - len(b) + 1, 0)
    while len(a) >= len(b):
        c = a[-1] * inv % q
        sh = len(a) - len(b)
        quo[sh] = c
        for i, y in enumerate(b):
            a[sh + i] = (a[sh + i] - c * y) % q
        a = trim(a)
    return trim(quo), a


def digits(n, B, q, e):
    """base-B digits of n, least significant first, each a length-e list"""
    out = []
    while n:
        n, r = pdivmod(n, B, q)
        out.append(r + [0] * (e - len(r)))
    return out


def decode(c, q, k):
    v = []
    for _ in range(k):
        v.append(c % q)
        c //= q
    return trim(v)


def encode(p, q):
    return sum(c * q ** i for i, c in enumerate(p))


def all_bases(q, e):
    """all B of degree e, any nonzero leading coefficient"""
    lo = q ** e
    return [decode(c, q, e + 1) for c in range(lo, lo * q)]


class World:
    def __init__(self, q, e, m):
        self.q, self.e, self.m = q, e, m
        self.coords = [(j, t) for j in range(e) for t in range(j + 1)]
        if m == 1:
            self.coords.append((e, 0))
        self.nc = len(self.coords)
        self.n = q ** self.nc
        self.maxdeg = (e - 1) * q ** (e - 1)
        self.lmax = self.maxdeg // e + 1
        # all x in G as an (n, nc) array; coordinate k is digit k of the index in base q
        idx = np.arange(self.n)
        self.X = np.stack([(idx // q ** k) % q for k in range(self.nc)], axis=1).astype(np.int64)
        # the monomial degree of each coordinate
        self.cdeg = [t * q ** j if j < e else 0 for (j, t) in self.coords]

    def F(self, xrow):
        f = [0] * (self.maxdeg + 1)
        for k, (j, t) in enumerate(self.coords):
            f[self.cdeg[k]] = (f[self.cdeg[k]] + xrow[k] * (self.m if j == self.e else 1)) % self.q
        return trim(f)

    def digit_matrix(self, B):
        """(nc, lmax*e) matrix: row k = digit vector of the monomial of coordinate k"""
        q, e = self.q, self.e
        M = np.zeros((self.nc, self.lmax * e), dtype=np.int64)
        for k, (j, t) in enumerate(self.coords):
            mono = [1] if j == e else [0] * self.cdeg[k] + [1]
            if j == e and self.m == 0:
                continue
            for i, d in enumerate(digits(mono, B, q, e)):
                M[k, i * e:(i + 1) * e] = d
        return M

    def digit_vectors(self, B, X=None):
        """(N, lmax, e) digits of F(x) for every row x of X"""
        X = self.X if X is None else X
        M = self.digit_matrix(B)
        return ((X @ M) % self.q).reshape(len(X), self.lmax, self.e)

    def class_sums(self, dv):
        """class sums (as an (N, nc) array in coordinate order) and lengths"""
        q, e = self.q, self.e
        N = dv.shape[0]
        nz = dv != 0
        # degree of each digit, -1 for zero
        dg = np.where(nz.any(axis=2), e - 1 - np.argmax(nz[:, :, ::-1], axis=2), -1)
        pos_nz = dg >= 0
        length = np.where(pos_nz.any(axis=1), self.lmax - np.argmax(pos_nz[:, ::-1], axis=1), 0)
        inside = np.arange(self.lmax)[None, :] < length[:, None]
        z = ((dg == -1) & inside).sum(axis=1)
        out = np.zeros((N, self.nc), dtype=np.int64)
        for k, (j, t) in enumerate(self.coords):
            if j == e:
                out[:, k] = z % q
            else:
                out[:, k] = (dv[:, :, t] * (dg == j)).sum(axis=1) % q
        return out, length, dg, z

    def index(self, Xarr):
        return (Xarr * (self.q ** np.arange(self.nc))[None, :]).sum(axis=1)

    def lengths_of_F(self):
        """length of F(x) for every x (independent of B)"""
        q = self.q
        coef = np.zeros((self.n, self.maxdeg + 1), dtype=np.int64)
        for k, (j, t) in enumerate(self.coords):
            w = self.m if j == self.e else 1
            coef[:, self.cdeg[k]] += self.X[:, k] * w
        coef %= q
        nz = coef != 0
        dg = np.where(nz.any(axis=1), self.maxdeg - np.argmax(nz[:, ::-1], axis=1), -1)
        return np.where(dg >= 0, dg // self.e + 1, 0), dg

    def identity_mask(self, B):
        """x with F(x) == digit sum (mod B - 1)"""
        q, e = self.q, self.e
        bm1 = padd(B, [q - 1], q)
        R = np.zeros((self.nc, e), dtype=np.int64)
        for k, (j, t) in enumerate(self.coords):
            if j == e:
                v = [self.m]
            else:
                v = padd([0] * self.cdeg[k] + [1], [0] * t + [q - 1], q)
            r = pdivmod(trim(v), bm1, q)[1]
            R[k, :len(r)] = r
        return ((self.X @ R) % q == 0).all(axis=1)

    def digit_elems(self):
        """group element of each digit value 0..q^e-1"""
        q, e = self.q, self.e
        out = np.zeros((q ** e, self.nc), dtype=np.int64)
        for c in range(q ** e):
            d = decode(c, q, e)
            if not d:
                if self.m == 1:
                    out[c, self.nc - 1] = 1
                continue
            j = len(d) - 1
            for t in range(j + 1):
                out[c, self.coords.index((j, t))] = d[t]
        return out

    def shift_table(self, elems):
        """table[g, idx] = index of x_idx + elems[g]"""
        q = self.q
        return np.stack([self.index((self.X + g[None, :]) % q) for g in elems])

    def string_laws(self, lmax=None, top_digits=None):
        """P_L for L = 1..lmax: law on G of the class sums of L digits,
        the top digit uniform on top_digits (default all nonzero), the rest uniform"""
        q, e = self.q, self.e
        lmax = lmax or self.lmax
        elems = self.digit_elems()
        tab = self.shift_table(elems)
        nd = q ** e
        top = list(range(1, nd)) if top_digits is None else top_digits
        p = np.zeros(self.n)
        for c in top:
            p[tab[c, 0]] += 1.0 / len(top)
        laws = {1: p.copy()}
        for L in range(2, lmax + 1):
            np_ = np.zeros(self.n)
            for c in range(nd):
                np.add.at(np_, tab[c], p)
            p = np_ / nd
            laws[L] = p.copy()
        return laws


def compose(B, a, b, q):
    """B(aT + b)"""
    r = []
    for c in reversed(B):
        r = padd(pmul(r, trim([b, a]), q), trim([c]), q)
    return r


def base_orbits(q, e):
    """orbits of the bases of degree e under T -> aT + b, as (representative, size)"""
    seen = set()
    out = []
    for B in all_bases(q, e):
        c = encode(B, q)
        if c in seen:
            continue
        orb = {encode(compose(B, a, s, q), q) for a in range(1, q) for s in range(q)}
        seen |= orb
        out.append((B, len(orb)))
    return out


def type_index(W, X):
    """model type of each x: per class j, 0 if D_j = 0, 1 if D_j != 0 with zero T^j
    coefficient, 2 if the T^j coefficient is nonzero; base 3 digit j; then z"""
    q, e = W.q, W.e
    ty = np.zeros(len(X), dtype=np.int64)
    for j in range(e):
        ks = [k for k, (jj, t) in enumerate(W.coords) if jj == j]
        top = X[:, W.coords.index((j, j))] != 0
        nz = (X[:, ks] != 0).any(axis=1)
        tau = np.where(top, 2, np.where(nz, 1, 0))
        ty += tau * 3 ** j
    if W.m == 1:
        ty += X[:, -1] * 3 ** e
    return ty


def class_factor(W, counts, ntype):
    """F[c, type]: probability that digits with class counts c (zero class first,
    then degrees 0..e-1) have class sums equal to one fixed x of the type, with
    digit values uniform within their class"""
    q, e = W.q, W.e
    r = -1.0 / (q - 1)
    out = np.ones((len(counts), ntype))
    for ty in range(ntype):
        taus = [(ty // 3 ** j) % 3 for j in range(e)]
        zt = ty // 3 ** e
        f = np.ones(len(counts))
        for j in range(e):
            k = counts[:, 1 + j]
            s0 = (1 + (q - 1) * r ** k) / q
            s1 = (1 - r ** k) / q
            val = np.where(k == 0, 1.0 if taus[j] == 0 else 0.0, q ** (-j) * (s0 if taus[j] < 2 else s1))
            f = f * val
        if W.m == 1:
            f = f * (counts[:, 0] % q == zt)
        out[:, ty] = f
    return out
