"""Question 83: a model that keeps the Frobenius blocks (0^0 = 0).

By Corollary 24.3, F(x) is assembled from e digits p_0, ..., p_(e-1):
p_(e-1) = D_(e-1), p_j = sigma(p_(j+1)) + D_j, p_0 = sigma(p_1) + D_0, and
the digits of F(x) are p_0 at position 0 and the digits of Phi^j(p_j) at the
positions [q^(j-1), q^j). The class sums of F(x) are
class(p_0) + sum_j K_j(p_j) with one table K_j per base.

Block model: keep the block maps, replace each p_j by a uniform digit of the
same degree (zero stays zero). The map x -> (p_0, ..., p_(e-1)) is a
bijection, so the expected count is

    E_block = sum over degree tuples delta of
              #{x : delta(x) = delta, delta(X(x)) = delta, len F(x) >= 2} / #{x : delta(x) = delta},

with X(x) the class sums of F(x). The refined block model also keeps
F mod (B - 1) exact: p~ is uniform among the tuples of the same degrees whose
F has the same residue mod B - 1, so

    E_ref = sum over x of [delta(X) = delta(x), r(X) = r(x), len >= 2] / C(delta(x), r(x)),

with r(x) = F(x) mod (B - 1) and C the number of x with that degree tuple and residue.

The script also counts the exact solutions (X(x) = x, length >= 2) and checks
them against the census file.

usage: python3 r5m_block.py Q E [max_orbits [workers]]   (reads data/r4f_census_qQeEm0.txt)
"""
import re
import subprocess
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r4f_lib import decode, digits, padd, pdivmod, trim
from r4f_byk import load


def ftypes(codes, q, e):
    """factorization type of B - 1 for each code, via PARI/GP"""
    lines = []
    for c in codes:
        b = decode(c, q, e + 1)
        b = b + [0] * (e + 1 - len(b))
        b[0] = (b[0] - 1) % q
        pol = '+'.join(f'{x}*x^{i}' for i, x in enumerate(b) if x)
        lines.append(f'f=factormod({pol},{q});print(vecsort(vector(#f~,i,[poldegree(f[i,1]),f[i,2]])))')
    out = subprocess.run(['gp', '-q', '-f'], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.split('\n')
    return [o.strip() for o in out if o.strip()]


def tables(B, q, e):
    coords = [(j, t) for j in range(e) for t in range(j + 1)]
    cidx = {c: k for k, c in enumerate(coords)}
    nc = len(coords)
    nd = q ** e
    P = np.array([[(c // q ** t) % q for t in range(e)] for c in range(nd)], dtype=np.int64)
    # sigma: digit -> T^(t q) mod B
    S = np.zeros((e, e), dtype=np.int64)
    for t in range(e):
        r = pdivmod([0] * (t * q) + [1], B, q)[1]
        S[:len(r), t] = r
    K = {}
    NZ = {}
    for j in range(1, e):
        lo, hi = q ** (j - 1), q ** j
        mono = []
        npos = 0
        for t in range(e):
            dv = digits([0] * (t * q ** j) + [1], B, q, e)
            mono.append(dv)
            npos = max(npos, len(dv))
        Mono = np.zeros((e, npos, e), dtype=np.int64)
        for t in range(e):
            for i, d in enumerate(mono[t]):
                Mono[t, i] = d
        dv = np.einsum('pt,tie->pie', P, Mono) % q  # (nd, npos, e)
        win = dv[:, lo:min(hi, npos), :]
        nz = win != 0
        dg = np.where(nz.any(axis=2), e - 1 - np.argmax(nz[:, :, ::-1], axis=2), -1)
        Kj = np.zeros((nd, nc), dtype=np.int64)
        for (jj, t), k in cidx.items():
            Kj[:, k] = (win[:, :, t] * (dg == jj)).sum(axis=1) % q
        K[j] = Kj
        NZ[j] = nz.any(axis=(1, 2))
    # residue of F(x) mod B - 1: coordinate (j, t) -> T^(t q^j) mod (B - 1)
    bm1 = padd(B, [q - 1], q)
    Rm = np.zeros((nc, e), dtype=np.int64)
    for (j, t), k in cidx.items():
        r = pdivmod([0] * (t * q ** j) + [1], bm1, q)[1]
        Rm[k, :len(r)] = r
    return coords, cidx, S, K, NZ, Rm


def pdegs(X, coords, cidx, S, q, e):
    """digits p_j (as (N, e) arrays) and their degrees for class sum rows X"""
    N = len(X)
    D = []
    for j in range(e):
        Dj = np.zeros((N, e), dtype=np.int64)
        for t in range(j + 1):
            Dj[:, t] = X[:, cidx[(j, t)]]
        D.append(Dj)
    p = [None] * e
    p[e - 1] = D[e - 1]
    for j in range(e - 2, -1, -1):
        p[j] = (p[j + 1] @ S.T + D[j]) % q
    degs = []
    for j in range(e):
        nz = p[j] != 0
        degs.append(np.where(nz.any(axis=1), e - 1 - np.argmax(nz[:, ::-1], axis=1), -1))
    return p, degs


def run_base(B, q, e, chunk=1 << 20):
    coords, cidx, S, K, NZ, Rm = tables(B, q, e)
    nc = len(coords)
    n = q ** nc
    pw = q ** np.arange(e)
    nkey = (e + 1) ** e
    cnt = np.zeros(nkey)
    match = np.zeros(nkey)
    sols = 0
    # pass 1: counts per degree tuple and residue; pass 2 needs C first
    keyfull = []
    for start in range(0, n, chunk):
        idx = np.arange(start, min(n, start + chunk))
        X = np.stack([(idx // q ** k) % q for k in range(nc)], axis=1).astype(np.int64)
        p, dg = pdegs(X, coords, cidx, S, q, e)
        key = np.zeros(len(idx), dtype=np.int64)
        for j in range(e):
            key = key * (e + 1) + (dg[j] + 1)
        # class sums of F(x)
        Y = np.zeros_like(X)
        d0 = dg[0]
        for t in range(e):
            for jj in range(t, e):
                sel = d0 == jj
                Y[sel, cidx[(jj, t)]] += p[0][sel, t]
        longf = np.zeros(len(idx), dtype=bool)
        for j in range(1, e):
            pi = p[j] @ pw
            Y += K[j][pi]
            longf |= NZ[j][pi]
        Y %= q
        exact = (Y == X).all(axis=1) & longf
        sols += int(exact.sum())
        _, dgY = pdegs(Y, coords, cidx, S, q, e)
        keyY = np.zeros(len(idx), dtype=np.int64)
        for j in range(e):
            keyY = keyY * (e + 1) + (dgY[j] + 1)
        rX = ((X @ Rm) % q) @ pw
        rY = ((Y @ Rm) % q) @ pw
        ok = (keyY == key) & longf
        cnt += np.bincount(key, minlength=nkey)
        match += np.bincount(key[ok], minlength=nkey)
        keyfull.append((key * q ** e + rX, ok & (rY == rX), exact, key))
    C = np.zeros(nkey * q ** e)
    for kf, _, _, _ in keyfull:
        C += np.bincount(kf, minlength=nkey * q ** e)
    eref = eself = eref2 = 0.0
    for kf, okr, ex, key in keyfull:
        eref += (1.0 / C[kf[okr]]).sum()
        eself += (1.0 / C[kf[ex]]).sum()
        eref2 += (q ** e / cnt[key[okr]]).sum()
    with np.errstate(invalid='ignore', divide='ignore'):
        eblock = float(np.nansum(np.where(cnt > 0, match / cnt, 0)))
    return sols, eblock, eref, eself, eref2


COLS = ['census', 'refined', 'block', 'block_x_q^k', 'block_res', 'block_res_self', 'block_id']


def main():
    q, e = int(sys.argv[1]), int(sys.argv[2])
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 10 ** 9
    workers = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rows = load(f'{__file__.rsplit("/", 1)[0]}/data/r4f_census_q{q}e{e}m0.txt')[:cap]
    types = ftypes([r['code'] for r in rows], q, e)
    agg = defaultdict(lambda: np.zeros(len(COLS) + 1))
    print(f"# q {q} e {e} 0^0 = 0, per orbit representative: " + ' '.join(COLS))
    print("# block: degrees kept; block_x_q^k: block times q^k(B); block_res: degrees and F mod (B-1) kept,"
          " block_res_self: the part of block_res from the exact solutions; block_id: block with the identity factor q^e")
    from multiprocessing import Pool
    args = [(trim(decode(r['code'], q, e + 1)), q, e) for r in rows]
    with Pool(workers) as pool:
        results = pool.starmap(run_base, args, chunksize=1)
    for r, ty, res in zip(rows, types, results):
        sols, eb, er, es, er2 = res
        flag = '' if sols == r['sols'] else f' MISMATCH census {r["sols"]}'
        vals = [sols, r['refined'], eb, eb * q ** r['k'], er, es, er2]
        print(f"orbit {r['code']} size {r['size']} k {r['k']} type {ty} " +
              ' '.join(f'{c} {v:.3f}' for c, v in zip(COLS, vals)) + flag, flush=True)
        agg[ty] += r['size'] * np.array([1] + vals)
    print("# per type of B - 1, mean per base")
    tot = np.zeros(len(COLS) + 1)
    for ty, a in sorted(agg.items()):
        tot += a
        print(f"type {ty} bases {int(a[0])} " + ' '.join(f'{c} {v / a[0]:.2f}' for c, v in zip(COLS, a[1:])))
    print(f"all bases {int(tot[0])} " + ' '.join(f'{c} {v / tot[0]:.3f}' for c, v in zip(COLS, tot[1:])))


if __name__ == '__main__':
    main()
