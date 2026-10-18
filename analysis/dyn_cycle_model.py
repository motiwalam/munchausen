"""Cycle counts of n -> F(n) against the random-mapping model.

Input: the census analysis/data/dyn_cycles.txt and the transition matrices
that `fast/target/release/dyn_cycles <b> <m> --matrix FILE --model-only`
writes (default directory fast/target/dyn, file mat_<b>_<m>.txt).

The model. A class K = (d, r) is the set of d-digit multisets whose digit
sum is r mod (b-1). A multiset c in class K maps to the class K' of its
image S(c), which is determined. Inside K' the image is a random multiset,
drawn with the weight of the number of d'-digit strings that have it. For
such a map the expected number of cycles of length L is

    E_L = (1/L) * (sum over tuples of distinct nodes of the product of the
           transition probabilities)  ~  (1/L) tr(M^L) * exp(-L^2 / (2 N)),

where M is the class transition matrix and N the effective number of nodes
(one over the collision probability). The trivial fixed point 1 is its own
class (1, 1) and is removed from M and from the counts.

Lumpings: "flat" uses one class per length (no residue), "par" keeps the
residue mod 2 (odd bases only), "full" keeps the residue mod b-1.

usage: python3 analysis/dyn_cycle_model.py [matrix_dir]
"""
import math
import os
import re
import sys
from collections import defaultdict

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MATDIR = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'fast', 'target', 'dyn')
BASES = range(3, 18)
LMAX_SHOW = 6


def load_census():
    cyc = defaultdict(list)
    for line in open(os.path.join(ROOT, 'analysis', 'data', 'dyn_cycles.txt')):
        if line.startswith('cycle'):
            m = int(re.search(r' m=(\d+)', line).group(1))
            b = int(re.search(r' b=(\d+)', line).group(1))
            L = int(re.search(r' L=(\d+)', line).group(1))
            mn = int(re.search(r' min=(\d+)', line).group(1))
            if L == 1 and mn == 1:
                continue
            cyc[(b, m)].append(L)
    return cyc


def load_matrix(b, m):
    q = b - 1
    S = b * q
    W = np.zeros((S, S))
    coll = np.zeros(S)
    for line in open(os.path.join(MATDIR, f'mat_{b}_{m}.txt')):
        if line.startswith('#'):
            continue
        p = line.split()
        if p[0] == 'coll':
            coll[int(p[1])] = float(p[2])
        else:
            W[int(p[0]), int(p[1])] += float(p[2])
    return W, coll


def lump(W, coll, b, mod):
    """Merge residues mod (b-1) into residues mod `mod` (mod | b-1; mod 1 = flat)."""
    q = b - 1
    # one-digit classes keep the full residue: each is a single digit
    S2 = q + (b - 1) * mod
    idx = [i if i < q else q + (i // q - 1) * mod + (i % q) % mod for i in range(b * q)]
    W2 = np.zeros((S2, S2))
    c2 = np.zeros(S2)
    for i in range(b * q):
        c2[idx[i]] += coll[i]
        for j in np.nonzero(W[i])[0]:
            W2[idx[i], idx[j]] += W[i, j]
    triv = 1 % q  # the class of the digit 1 alone (length 1, residue 1)
    return W2, c2, triv


def model(W, coll, triv):
    T = W.sum(axis=1)
    keep = [i for i in range(len(T)) if T[i] > 0 and i != triv]
    M = W[np.ix_(keep, keep)] / T[keep][:, None]
    qK = coll[keep] / T[keep] ** 2
    ev = np.linalg.eigvals(M)
    # closed classes: stationary laws of the eigenvalue-1 eigenspace
    vals, vecs = np.linalg.eig(M.T)
    neffs = []
    for k in range(len(vals)):
        if abs(vals[k] - 1) < 0.1:
            mu = np.real(vecs[:, k])
            mu = mu / mu.sum()
            neffs.append(1 / float(np.sum(mu ** 2 * qK)))
    return M, ev, neffs


def predicted(M, ev, neffs, L):
    tr = float(np.real(np.sum(ev ** L)))
    # finite-size factor, applied to the eigenvalue-1 part, one per closed class
    ones = sum(float(np.real(v)) ** L for v in ev if abs(v - 1) < 0.1)
    fs = sum(float(np.real(v)) ** L * math.exp(-L * L / (2 * n)) for v, n in zip([v for v in ev if abs(v - 1) < 0.1], neffs))
    return (tr - ones + fs) / L


def poisson_cdf(k, lam):
    return sum(math.exp(-lam) * lam ** i / math.factorial(i) for i in range(k + 1))


def main():
    cyc = load_census()
    out = []
    agg = defaultdict(lambda: [0.0, 0])
    tot = defaultdict(lambda: [0.0, 0])
    out.append('base m | observed L=1..6 | full-model E_L, L=1..6 | flat-model E_2 | N_eff | cycles obs/pred')
    for b in BASES:
        for m in (0, 1):
            W, coll = load_matrix(b, m)
            Wf, cf, tf = lump(W, coll, b, b - 1)
            M, ev, neffs = model(Wf, cf, tf)
            W1, c1, t1 = lump(W, coll, b, 1)
            M1, ev1, n1 = model(W1, c1, t1)
            flat2 = predicted(M1, ev1, n1, 2)
            obs = defaultdict(int)
            for L in cyc[(b, m)]:
                obs[L] += 1
            Lcap = 4 * int(max(math.sqrt(n) for n in neffs)) + 10
            E = [predicted(M, ev, neffs, L) for L in range(1, Lcap)]
            par = 'odd' if b % 2 else 'even'
            for L in range(1, LMAX_SHOW + 1):
                agg[(par, m, L)][0] += E[L - 1]
                agg[(par, m, L)][1] += obs[L]
            tot[(par, m)][0] += sum(E)
            tot[(par, m)][1] += len(cyc[(b, m)])
            out.append(f'{b:2d} {m} | ' + ' '.join(f'{obs[L]:d}' for L in range(1, LMAX_SHOW + 1))
                       + ' | ' + ' '.join(f'{E[L - 1]:.2f}' for L in range(1, LMAX_SHOW + 1))
                       + f' | {flat2:.2f} | ' + ','.join(f'{n:.3g}' for n in neffs)
                       + f' | {len(cyc[(b, m)])}/{sum(E):.1f}')
    out.append('')
    out.append('aggregate over bases 3-17 (observed / full model, P(X <= obs), P(X >= obs))')
    for par in ('odd', 'even'):
        for m in (0, 1):
            row = []
            for L in range(1, LMAX_SHOW + 1):
                e, o = agg[(par, m, L)]
                lo = poisson_cdf(o, e)
                hi = 1 - poisson_cdf(o - 1, e) if o > 0 else 1.0
                row.append(f'L={L}: {o}/{e:.2f} ({lo:.2f},{hi:.2f})')
            e, o = tot[(par, m)]
            out.append(f'{par:4s} m={m}: ' + '; '.join(row) + f'; all lengths {o}/{e:.1f}')
    text = '\n'.join(out)
    print(text)
    with open(os.path.join(ROOT, 'analysis', 'data', 'dyn_cycle_model.txt'), 'w') as f:
        f.write(text + '\n')


if __name__ == '__main__':
    main()
