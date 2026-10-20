"""Local solubility of the middle families (p, x, q) with x odd.

The string is a solution when p b^2 + x b + q = w(p) + x^x + w(q). For each
family with p <= 20, q <= 20 (both conventions when q = 0) and each modulus
M in MODS, an odd x passes M when some b mod M solves the equation modulo M.
The script tests the odd x in [X0, X0 + N) and prints, per family, the share
that passes each modulus and the share that passes all of them. A share 0
for all moduli together would be a covering. Lead for question 165 of
docs/library/questions-round7.md. Needs numpy.

    python3 analysis/r7p_middle_local.py
"""
import numpy as np

MODS = [2**10, 3**6, 5**4, 7**3, 11**2, 13**2]
X0, N = 100001, 200000
xs = np.arange(X0, X0 + N, 2, dtype=np.int64)

xx = {M: np.array([pow(int(x), int(x), M) for x in xs], dtype=np.int64)
      for M in MODS}


def w(d, m):
    return m if d == 0 else d**d


attain_cache = {}


def attain(p, M):
    """tab[x mod M, v] says that p b^2 + x b == v (mod M) for some b."""
    if (p, M) not in attain_cache:
        b = np.arange(M, dtype=np.int64)
        tab = np.zeros((M, M), dtype=bool)
        pb2 = (p * b * b) % M
        for xr in range(M):
            tab[xr, (pb2 + xr * b) % M] = True
        attain_cache[(p, M)] = tab
    return attain_cache[(p, M)]


rows = []
for p in range(1, 21):
    for q in range(0, 21):
        for m in ((0, 1) if q == 0 else (1,)):
            W = w(p, 1) + w(q, m)
            ok_all = np.ones(len(xs), dtype=bool)
            shares = []
            for M in MODS:
                target = (xx[M] + (W - q) % M) % M
                ok = attain(p, M)[xs % M, target]
                shares.append(ok.mean())
                ok_all &= ok
            rows.append((p, q, m, shares, ok_all.mean()))

rows.sort(key=lambda r: r[4])
print("families", len(rows), "moduli", MODS)
for p, q, m, shares, allv in rows:
    print(f"({p:2d}, x, {q:2d}) 0^0={m} "
          + " ".join(f"{s:.3f}" for s in shares) + f"  all {allv:.4f}")
allv = np.array([r[4] for r in rows])
print("families with share 0:", int((allv == 0).sum()))
print("others: min %.4f median %.4f max %.4f"
      % (allv[allv > 0].min(), np.median(allv[allv > 0]), allv.max()))
