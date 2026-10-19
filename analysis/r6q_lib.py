"""Round 6, workload 1: shared tools.

weights(b, m, perturb)  the digit weights, including fast's --perturb
refined_by_zeros(...)   the refined model of section 5.3 for one length,
                        split by the number of zero digits, computed exactly
                        by the walk of r6q_trace.py
load_hits(path)         the near-solution strings of r5e_int_offsets.py
"""
import bisect
import math
from collections import defaultdict

import numpy as np

EPS = 1e-15
MASK = (1 << 64) - 1


def _splitmix_limbs(seed, b, j, count):
    state = (seed ^ (b << 32) ^ ((j * 0x9e3779b97f4a7c15) & MASK)) & MASK
    out = []
    for _ in range(count):
        state = (state + 0x9e3779b97f4a7c15) & MASK
        z = state
        z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK
        z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK
        out.append((z ^ (z >> 31)) & 0xffffffff)
    return out


def weights(b, m=1, perturb=0):
    """w[0..b-1] as in fast/src/search.rs::weights (w[0] = m)."""
    w = [m] + [x ** x for x in range(1, b)]
    if perturb:
        for j in range(2, b):
            room = w[j] // 4 + 1
            limbs = _splitmix_limbs(perturb, b, j, room.bit_length() // 32 + 2)
            big = sum(v << (32 * i) for i, v in enumerate(limbs))
            w[j] += big % room
    return w


def leaves(b, d, w):
    """The walk of r6q_trace.py for arbitrary increasing weights w[1..b-1]
    (w[0] <= w[1]). Yields (length of F, x, r, lead, U, p) with U the sum of
    w(x) - x over the placed digits modulo b - 1."""
    qm = b - 1
    g = [(w[x] - x) % qm for x in range(b)]
    pw = [b ** k for k in range(b + 2)]
    out = []

    def length(v):
        return bisect.bisect_right(pw, v)

    def walk(x, r, lead, s, U, p):
        if x < 0 or (r == 0 and not lead):
            out.append((length(s), -1, 0, 0, U, p))
            return
        if x == 0:
            out.append((length(s + r * w[0]), 0, r, 0, U, p))
            return
        top = s + (r + lead) * w[x]
        if s > 0 and length(s) == length(top):
            out.append((length(s), x, r, lead, U, p))
            return
        q = 1.0 / (x + 1)
        opts = [(1.0 / x, 1), (1.0 - 1.0 / x, 0)] if lead else [(1.0, 0)]
        for pl, isl in opts:
            if pl == 0.0:
                continue
            nl = lead and not isl
            pk = (1.0 - q) ** r if r else 1.0
            for k in range(0, r + 1):
                if k > 0:
                    pk *= (r - k + 1) / k * q / (1.0 - q)
                pp = p * pl * pk
                if pp < EPS:
                    if k > r * q + 2:
                        break
                    continue
                walk(x - 1, r - k, nl, s + (k + isl) * w[x], (U + (k + isl) * g[x]) % qm, pp)

    walk(b - 1, d - 1, 1, 0, 0, 1.0)
    return out


def refined_by_zeros(b, d, w, zmax=3, shift=0):
    """Expected number of d-digit solutions in the refined model (identity
    modulo b - 1 only), split by the number z of zero digits, z = 0..zmax-1
    and z >= zmax. Exact up to EPS. With shift = c the residue condition is
    that of the offsets D == c (mod b - 1): sum of w(x) - x == -c."""
    qm = b - 1
    g = np.array([(w[x] - x) % qm for x in range(b)])
    t = np.arange(qm)
    E = np.exp(2j * np.pi * np.outer(t, g) / qm)
    cum = np.cumsum(E, axis=1)
    nz = np.zeros_like(cum)
    nz[:, 1:] = cum[:, 1:] - E[:, :1]  # sum over 1..x
    acc = defaultdict(float)
    for L, x, r, lead, U, p in leaves(b, d, w):
        if L == d:
            acc[(x, r, lead, U)] += p
    res = np.zeros(zmax + 1)
    for (x, r, lead, U), p in acc.items():
        base = np.exp(2j * np.pi * t * (U + shift) / qm) * p
        if x < 0:
            res[0] += base.sum().real
            continue
        if lead:
            base = base * nz[:, x] / x
        A = nz[:, x] / (x + 1)
        B = E[:, 0] / (x + 1)
        tot = base * (A + B) ** r
        part = np.zeros(qm, dtype=complex)
        for z in range(min(zmax, r + 1)):
            cz = math.comb(r, z) * B ** z * A ** (r - z)
            v = (base * cz).sum().real
            res[z] += v
            part += base * cz
        res[zmax] += (tot - part).sum().real
    return res


def load_hits(path):
    """events (b, m, k, digits) with D = k (b - 1), and the offsets done per base"""
    ev, done = [], defaultdict(set)
    for line in open(path):
        p = line.split()
        if not p:
            continue
        if p[0] == 'hit':
            ev.append((int(p[1]), int(p[2]), int(p[3]), tuple(map(int, p[4].split(',')))))
        elif p[0] == 'done':
            done[int(p[1])].add(int(p[2]))
    return ev, done
