"""The probabilistic model of chapter 5 for factorions: n = sum of x! over the
base-b digits of n (0! = 1).

For each length d, E_d is the chance that a random d-digit string (leading
digit nonzero) has a sum F with exactly d digits. The refined model multiplies
by b-1 when sum (x! - x) == 0 (mod b-1) and by 0 otherwise. F is computed in
log space, so any base works. The exact sums for small bases come from
`worlds brute b fact`.

usage: python3 wld_factmodel.py B1 B2 ... [--n N]
prints: base d basic refined, and the length L(b) = floor(log_b (b-1)!) + 1.
"""
import math
import sys
import numpy as np


def run(b, n, rng):
    M = max(b - 1, 1)
    lw = np.array([math.lgamma(x + 1) for x in range(b)])
    res = np.array([(math.factorial(x) - x) % M for x in range(b)], dtype=np.int64)
    L = math.floor(math.lgamma(b) / math.log(b)) + 1
    rows = []
    for d in range(max(2, L - 10), L + 3):
        s = rng.integers(0, b, size=(n, d), dtype=np.int64)
        s[:, 0] = rng.integers(1, b, size=n)
        a = lw[s]
        top = a.max(axis=1)
        logf = top + np.log(np.exp(a - top[:, None]).sum(axis=1))
        # exact digit counts would need big integers; the log is exact enough
        # except within 1e-12 of a power of b, a set of measure about zero
        ln = np.floor(logf / math.log(b) + 1e-12).astype(np.int64) + 1
        win = ln == d
        r = res[s].sum(axis=1) % M
        rows.append((d, win.mean(), (win & (r == 0)).mean() * M))
    return L, rows


def main():
    args = sys.argv[1:]
    n = 200000
    if "--n" in args:
        i = args.index("--n")
        n = int(args[i + 1])
        args = args[:i] + args[i + 2:]
    rng = np.random.default_rng(2024)
    print("# base L d basic refined")
    for b in map(int, args):
        L, rows = run(b, n, rng)
        for d, e, er in rows:
            print(f"{b} {L} {d} {e:.6e} {er:.6e}", flush=True)


if __name__ == "__main__":
    main()
