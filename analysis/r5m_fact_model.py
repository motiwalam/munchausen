"""Question 84: a model that keeps the top digits of F in the factorial system.

Window W = [L!, (L+1)!): n = sum_{i=1..L} d_i i!, 0 <= d_i <= i, d_L >= 1.
The plain model (section 21.5.3) treats F(c) as a uniform member of W:

    E_L = E_n [ 1(F in W) ],                        n uniform in W.

The top-K model keeps the top K factorial digits of F(c) exactly (the digits
at positions L-K+1..L, which the large digit counts fix) and treats the
digits at positions 1..L-K as uniform. For a multiset c this gives

    P(digits of F form c) = 1(T in c) A(c - T, L - K) / prod_{i <= L-K} (i + 1),

with T the top K digits of F(c) and A(c, N) the number of ways to place a
multiset of N digits into positions 1..N with value u only at positions
>= u (a Ferrers board: A = prod over u from the top of
C(N - u + 1 - #(digits > u), c_u)). Written as an average over n,

    E_L(K) = E_n [ 1(F in W) P(top K of a random arrangement of c is T) / P_W(top K is T) ].

K = 0 is the plain model. K = L is the exact count of solutions in W.
With an offset D the same holds for n = F + D (near-solutions).

usage: python3 r5m_fact_model.py m Lmin Lmax samples Kmax [D_step D_count] [workers]
"""
import sys
import math
from math import factorial, lgamma, log, exp
from multiprocessing import Pool

import numpy as np


def logA(cnt, N):
    """log of the number of placements of the multiset cnt (cnt[u] copies of u)
    into positions 1..N, value u only at positions >= u; None if zero"""
    used = 0
    tot = 0.0
    for u in range(len(cnt) - 1, -1, -1):
        cu = cnt[u]
        if cu == 0:
            continue
        avail = N - max(u, 1) + 1 - used
        if avail < cu:
            return None
        tot += lgamma(avail + 1) - lgamma(cu + 1) - lgamma(avail - cu + 1)
        used += cu
    return tot


def log_arr_window(cnt, L):
    """log #(n in W with multiset cnt): placements with d_L != 0"""
    a = logA(cnt, L)
    if a is None:
        return None
    if cnt[0] == 0:
        return a
    c2 = list(cnt)
    c2[0] -= 1
    b = logA(c2, L - 1)
    if b is None:
        return a
    v = 1 - exp(b - a)
    return a + log(v) if v > 0 else None


def run_L(args):
    L, m, samples, kmax, offsets, seed = args
    rng = np.random.default_rng(seed)
    fact = [factorial(i) for i in range(L + 2)]
    w = [m] + [d ** d for d in range(1, L + 1)]
    lo, hi = fact[L], fact[L + 1]
    logw = np.array([log(m) if m else -np.inf] + [d * log(d) for d in range(1, L + 1)]) - lgamma(L + 1)
    caps = np.arange(1, L, dtype=np.int64)
    # log P_W(top K digits = T) = -log(L) - sum_{i=L-K+1}^{L-1} log(i + 1)
    lpw = [0.0] + [-log(L) - sum(log(i + 1) for i in range(L - K + 1, L)) for K in range(1, kmax + 1)]
    res = {D: np.zeros(kmax + 2) for D in offsets}
    stat = [0.0, 0, 0.0]  # EA at D = 0: sum of squares, nonzero terms, largest term
    done = 0
    while done < samples:
        k = min(20000, samples - done)
        low = (rng.random((k, L - 1)) * (caps + 1)).astype(np.int64)
        top = 1 + (rng.random(k) * L).astype(np.int64)
        dg = np.concatenate([low, top[:, None]], axis=1)  # positions 1..L
        with np.errstate(over='ignore'):
            lf = np.log(np.exp(logw[dg]).sum(axis=1))
        # keep a margin; the exact test follows
        cand = np.nonzero((lf > -0.01) & (lf < log(L + 1) + 0.01))[0]
        for s in cand:
            row = dg[s]
            F = sum(w[d] for d in row)
            cnt = np.bincount(row, minlength=L + 1)
            la = None
            for D in offsets:
                v = F + D
                if not (lo <= v < hi):
                    continue
                res[D][0] += 1
                if la is None:
                    la = log_arr_window(cnt, L)
                # adaptive K: the positions >= max digit, where the max digit must sit
                ka = L - int(row.max()) + 1
                c2 = cnt.copy()
                ok = True
                for j in range(L, L - ka, -1):
                    t = (v // fact[j]) % (j + 1)
                    c2[t] -= 1
                    if c2[t] < 0:
                        ok = False
                        break
                if ok:
                    lb = logA(c2, L - ka)
                    if lb is not None:
                        lpa = -log(L) - sum(log(i + 1) for i in range(L - ka + 1, L))
                        val = exp(lb - la - lpa)
                        res[D][kmax + 1] += val
                        if D == 0:
                            stat[0] += val * val
                            stat[1] += 1
                            stat[2] = max(stat[2], val)
                T = []
                for K in range(1, kmax + 1):
                    j = L - K + 1
                    T.append((v // fact[j]) % (j + 1))
                    c2 = cnt.copy()
                    ok = True
                    for t in T:
                        c2[t] -= 1
                        if c2[t] < 0:
                            ok = False
                            break
                    if not ok:
                        break  # larger K need T in c as well
                    lb = logA(c2, L - K)
                    if lb is None:
                        continue
                    res[D][K] += exp(lb - la - lpw[K])
        done += k
    mean = res[0][kmax + 1] / samples
    se = math.sqrt(max(stat[0] / samples - mean * mean, 0) / samples)
    return L, {D: r / samples for D, r in res.items()}, (se, stat[1], stat[2] / samples)


def main():
    m, lmin, lmax, samples, kmax = map(int, sys.argv[1:6])
    dstep = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    dcount = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    workers = int(sys.argv[8]) if len(sys.argv) > 8 else 8
    offsets = [0] + [dstep * j for j in range(1, dcount + 1)]
    jobs = [(L, m, samples, min(kmax, L), offsets, 1000 * L + m) for L in range(lmin, lmax + 1)]
    print(f"# factorial system 0^0 = {m}, {samples} samples per L; E_L(K) for K = 0..{kmax}"
          + (f"; near: mean over D = {dstep} j, j = 1..{dcount}" if dcount else ""))
    with Pool(workers) as pool:
        for L, res, st in pool.imap(run_L, jobs):
            r0 = res[0]
            line = f"L {L} " + " ".join(f"E{K} {r0[K]:.4e}" for K in range(len(r0) - 1)) + f" EA {r0[-1]:.4e} EA_se {st[0]:.2e} EA_terms {st[1]} EA_maxshare {st[2]:.2e}"
            if dcount:
                near = np.mean([res[D] for D in offsets[1:]], axis=0)
                line += ' near ' + ' '.join(f"{x:.4e}" for x in near)
            print(line, flush=True)


if __name__ == '__main__':
    main()
