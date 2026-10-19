"""Question 104 and 105: model predictions for bases 42 to 46, written before the run.

    python3 r6c_predict.py census [N]        # bases 42, 44, 45, 46, lengths b-14..b
    python3 r6c_predict.py bdigit B0 B1 [N]  # b-digit solutions only, 0^0 = 1 and 0

For every length d, N random d-digit multisets are drawn as in model.py.
A multiset counts for convention m if its sum F has d digits and meets the
identity modulo b-1 (the refined model of section 5.3). The weight of a
counted multiset is 1 for t = 0, and for t >= 1 the ratio of
r2c_top_model.py: the chance that the multiset holds the top t digits of F,
over the uniform chance. So t = 0 is the refined model and t = 3 keeps the
forced top digits (sections 11.2 and 23.5). All t share one sample.

Each line gives, per base, convention and length class, the expected count
under t = 0 and t = 3, the expected count of zero-free solutions (they
count under both conventions), and the mean number of zeros of a solution.
"""
import math
import sys

import numpy as np

TMAX = 3
JMAX = 14


def sample(b, d, N, rng):
    """Per convention: arrays [t] of sums of weights, of zero-free weights,
    of weights times c_0, and of squared weights."""
    q = b - 1
    scale = (d - 1) * math.log(b)
    x = np.arange(b, dtype=float)
    w = np.exp(np.where(x > 0, x * np.log(np.maximum(x, 1)), 0.0) - scale)
    out = {m: np.zeros((4, TMAX + 1)) for m in (0, 1)}
    u = {m: np.array([((pow(v, v, q) if v > 0 else m) - v) % q for v in range(b)], dtype=np.int64)
         for m in (0, 1)}
    done = 0
    while done < N:
        n = min(50_000, N - done)
        done += n
        c = rng.multinomial(d - 1, np.full(b, 1.0 / b), size=n)
        lead = rng.integers(1, b, size=n)
        c[np.arange(n), lead] += 1
        f0 = c @ w
        for m in (0, 1):
            f = f0 + m * c[:, 0] * math.exp(-scale)
            ok = (f >= 1.0) & (f < b) & ((c @ u[m]) % q == 0)
            cc, ff = c[ok], f[ok]
            k = len(ff)
            if k == 0:
                continue
            rows = np.arange(k)
            base = (d - cc[:, 0]) / d
            num = np.ones(k)
            g = ff.copy()
            digs = []
            wt = [np.ones(k)]
            for t in range(1, TMAX + 1):
                v = np.floor(g).astype(np.int64) % b
                g = (g - np.floor(g)) * b
                used = np.zeros(k, dtype=np.int64)
                for prev in digs:
                    used += (prev == v)
                digs.append(v)
                num = num * np.maximum(0, cc[rows, v] - used) / (d - t + 1)
                wt.append((b - 1) * float(b) ** (t - 1) * num / base)
            z = cc[:, 0]
            for t in range(TMAX + 1):
                out[m][0, t] += wt[t].sum()
                out[m][1, t] += wt[t][z == 0].sum()
                out[m][2, t] += (wt[t] * z).sum()
                out[m][3, t] += (wt[t] ** 2).sum()
    for m in (0, 1):
        out[m] *= q / N
        out[m][3] *= q / N
    return out


def classes(b):
    return [('b', [b]), ('b-1', [b - 1]), ('b-2', [b - 2]), ('b-3', [b - 3]),
            ('<=b-4', list(range(b - JMAX, b - 3)))]


def census(N):
    rng = np.random.default_rng(104)
    for b in (42, 44, 45, 46):
        per_d = {d: sample(b, d, N, rng) for d in range(b - JMAX, b + 1)}
        for m in (0, 1):
            tot = np.zeros((4, TMAX + 1))
            for name, ds in classes(b):
                s = sum(per_d[d][m] for d in ds)
                tot += s
                print(f"base {b} m {m} {name:6s} t0 {s[0, 0]:.4f} t3 {s[0, 3]:.4f} "
                      f"zerofree_t3 {s[1, 3]:.4f} se_t3 {math.sqrt(s[3, 3]):.4f}", flush=True)
            mz = tot[2, 3] / tot[0, 3]
            print(f"base {b} m {m} total  t0 {tot[0, 0]:.4f} t1 {tot[0, 1]:.4f} t2 {tot[0, 2]:.4f} "
                  f"t3 {tot[0, 3]:.4f} zerofree_t3 {tot[1, 3]:.4f} meanzeros_t3 {mz:.3f} "
                  f"se_t3 {math.sqrt(tot[3, 3]):.4f}", flush=True)


def bdigit(b0, b1, N):
    rng = np.random.default_rng(105)
    for b in range(b0, b1 + 1):
        s = sample(b, b, N, rng)
        print(f"bdigit {b} m0 t0 {s[0][0, 0]:.4f} t3 {s[0][0, 3]:.4f} "
              f"m1 t0 {s[1][0, 0]:.4f} t3 {s[1][0, 3]:.4f} se_m1_t3 {math.sqrt(s[1][3, 3]):.4f}", flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'census':
        census(int(sys.argv[2]) if len(sys.argv) > 2 else 400_000)
    else:
        bdigit(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 2_000_000)
