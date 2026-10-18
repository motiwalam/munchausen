"""The probabilistic model of chapter 5 for the negative base -b, by sampling.

For each odd length d, draw random d-digit strings in base -b (leading digit
nonzero) and record whether F has exactly d base -b digits, that is, whether
(b^(d-1) - 1)/(b+1) < F <= (b^(d+1) - 1)/(b+1). The mean is E_d (basic
model). The refined model multiplies by (b+1) when the digit-sum identity
sum (w(x) - x) == 0 (mod b+1) holds and by 0 otherwise. The part from strings
without a zero is the same in both conventions, so the expected number of
distinct solutions in either convention is E_0 + E_1 - E_zerofree.

usage: python3 wld_negamodel.py BMIN BMAX [N]   (prints one line per base and d)
The exact sums for small bases come from `worlds brute` (fast/src/bin).
"""
import sys
import numpy as np


def model(b, d, n, rng):
    M = b + 1
    wf = np.array([0.0] + [float(x) ** x for x in range(1, b)])
    wres = np.array([0] + [(pow(x, x, M) - x) % M for x in range(1, b)], dtype=np.int64)
    s = rng.integers(0, b, size=(n, d), dtype=np.int64)
    s[:, 0] = rng.integers(1, b, size=n)
    f0 = wf[s].sum(axis=1)
    c0 = (s == 0).sum(axis=1)
    r0 = wres[s].sum(axis=1) % M
    lo = (b ** (d - 1) - 1) // (b + 1)
    hi = (b ** (d + 1) - 1) // (b + 1)
    out = {}
    for m in (0, 1):
        f = f0 + m * c0
        r = (r0 + m * c0) % M
        win = (f > lo) & (f <= hi)
        out[m] = (win.mean(), (win & (r == 0)).mean() * M)
        if m == 0:
            zf = (win & (r == 0) & (c0 == 0)).mean() * M
    return out, zf


def main():
    bmin, bmax = int(sys.argv[1]), int(sys.argv[2])
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 400000
    rng = np.random.default_rng(12345)
    print("# base d basic refined0 refined1 refined_zerofree")
    for b in range(bmin, bmax + 1):
        for d in range(3, b + 2, 2):
            out, zf = model(b, d, n, rng)
            print(f"{b} {d} {out[0][0]:.6e} {out[0][1]:.6e} {out[1][1]:.6e} {zf:.6e}", flush=True)


if __name__ == "__main__":
    main()
