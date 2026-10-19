"""Round 5, question 73: clusters in the base-by-base window of section 22.4.

Recomputes the class counts of r4b_spectrum.c for k-digit strings (k = 4,
5), 0^0 = 1, bases 13 to 99: every string s with leading digit >= 1 and
V = P_s(b) - F(s) in the class of 0 modulo 2(b-1), b <= |V| <= W,
W = floor(0.05 b^(k-1)). The mean count per offset estimates N_0 for the
base. Here the hits keep their strings, so they can be grouped by multiset
(the swap lemma) and by a common prefix of k-2 digits (blocks, section
19.2.3). Output: data/r5e_short_spectrum.txt.

    python3 r5e_short_spectrum.py
"""
import itertools
import math
import os
import sys

import numpy as np

from r5e_cluster import UF
from r5e_lib import cluster_stats, p_high, poisson_high

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'data', 'r5e_short_spectrum.txt')
WFRAC = 0.05


def wt(x, mode):
    return mode if x == 0 else x ** x


def base_hits(b, k, mode):
    W = math.floor(WFRAC * b ** (k - 1))
    E = b
    X = max(x for x in range(b) if x == 0 or x ** x <= b ** k + W)
    M2 = 2 * (b - 1)
    digs = np.arange(X + 1, dtype=np.int64)
    w = np.array([wt(x, mode) for x in range(X + 1)], dtype=np.int64)
    grids = np.meshgrid(*([digs] * k), indexing='ij')
    V = np.zeros(grids[0].shape, dtype=np.int64)
    for i, g in enumerate(grids):
        V += g * b ** (k - 1 - i) - w[g]
    lead = grids[0] >= 1
    a = np.abs(V)
    sel = lead & (a >= E) & (a <= W) & (V % M2 == 0)
    zero = lead & (V == 0)
    idx = np.argwhere(sel)
    hits = [(tuple(int(t) for t in row), int(V[tuple(row)])) for row in idx]
    sols = [tuple(int(t) for t in row) for row in np.argwhere(zero)]
    noff = 2 * (W // M2 - (E - 1) // M2)
    return hits, sols, noff


def cluster_ids(hits, k, prefix):
    uf = UF(len(hits))
    seen = {}
    for i, (s, _) in enumerate(hits):
        keys = [('ms', tuple(sorted(s)))]
        if prefix:
            keys.append(('pre', s[:k - 2]))
        for key in keys:
            if key in seen:
                uf.union(i, seen[key])
            else:
                seen[key] = i
    return [uf.find(i) for i in range(len(hits))]


def main():
    lines = []
    for k in (4, 5):
        mode = 1
        lam = var_naive = 0.0
        var_ms = var_pre = 0.0
        n_all = 0
        obs = 0
        ms_shared = 0
        per_base = []
        for b in range(13, 100):
            hits, sols, noff = base_hits(b, k, mode)
            obs += len(sols)
            if noff == 0:
                continue
            n = len(hits)
            n_all += n
            lam += n / noff
            var_naive += n / noff ** 2
            for prefix in (False, True):
                cid = cluster_ids(hits, k, prefix)
                st = cluster_stats([(c, v) for c, (_, v) in zip(cid, hits)])
                v = st['phi'] * n / noff ** 2 if n else 0.0
                if prefix:
                    var_pre += v
                else:
                    var_ms += v
                    ms_shared += st['shared'] * n
            per_base.append((b, n, noff, len(sols)))
        phi_ms = var_ms / var_naive
        phi_pre = var_pre / var_naive
        T_eq = lam ** 2 / var_naive  # equivalent Poisson total for one offset
        lines.append(f"k={k} mode={mode} bases 13-99: hits {n_all}, observed N_0 {obs}, "
                     f"estimate {lam:.4f}, naive se {math.sqrt(var_naive):.4f}, "
                     f"se by multiset clusters {math.sqrt(var_ms):.4f} (phi {phi_ms:.2f}), "
                     f"se by multiset+prefix clusters {math.sqrt(var_pre):.4f} (phi {phi_pre:.2f}), "
                     f"share of hits whose multiset recurs {ms_shared / n_all:.3f}")
        # P(N_0 >= obs): fixed lambda, then lambda with its error (equivalent
        # total T_eq over J_eq = T_eq / lam offsets), naive and clustered
        J_eq = T_eq / lam
        lines.append(f"  P(N_0 >= {obs}): fixed {poisson_high(obs, lam):.4f}; with calibration error, "
                     f"independent {p_high(obs, T_eq, J_eq):.4f}, "
                     f"multiset clusters {p_high(obs, T_eq, J_eq, phi=phi_ms):.4f}, "
                     f"multiset+prefix clusters {p_high(obs, T_eq, J_eq, phi=phi_pre):.4f}")
    with open(OUT, 'w') as f:
        f.write("# r5e_short_spectrum.py: window b <= |D| <= 0.05 b^(k-1), class 0 mod 2(b-1), 0^0 = 1\n")
        for line in lines:
            f.write(line + "\n")
    print("\n".join(lines))


if __name__ == '__main__':
    main()
