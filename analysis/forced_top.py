"""Correction to the model from the forced top digits of F.

The model treats the digits of F(c) as a uniform random d-digit string. But
the top digits of F(c) are fixed by the counts of the largest digits. For a
random multiset c whose F has d digits, take the actual top t digits tau of
F(c) and treat only the other d - t as random. The chance that F(c) has
digit multiset c changes by the factor

    ratio = (b-1) b^(t-1) * prod_x c_x (c_x - 1) ... (c_x - tau_x + 1)
            / (d (d-1) ... (d-t+1)) / ((d - c_0) / d),

which is 0 when tau is not contained in c. The mean ratio C_t is the factor
by which the model's E_d must be multiplied.
"""
import random
import sys


def correction(b, d, mode, t_max=6, N=40000, seed=1):
    rng = random.Random(seed)
    w = [mode] + [x ** x for x in range(1, b)]
    lo, hi = b ** (d - 1), b ** d
    sums = [0.0] * (t_max + 1)
    acc = 0
    for _ in range(N):
        s = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(d - 1)]
        F = sum(w[x] for x in s)
        if not lo <= F < hi:
            continue
        acc += 1
        c = [0] * b
        for x in s:
            c[x] += 1
        digs = []
        n = F
        for _ in range(d):
            n, r = divmod(n, b)
            digs.append(r)
        digs.reverse()
        for t in range(1, t_max + 1):
            used = [0] * b
            num = 1.0
            for v in digs[:t]:
                num *= max(0, c[v] - used[v])
                used[v] += 1
            den = 1.0
            for i in range(t):
                den *= d - i
            sums[t] += (b - 1) * b ** (t - 1) * num / den / ((d - c[0]) / d)
    return acc / N, [sums[t] / max(1, acc) for t in range(1, t_max + 1)]


if __name__ == '__main__':
    for b in map(int, sys.argv[1:]):
        for j in (0, 1, 2):
            p, cs = correction(b, b - j, 1)
            print(f"base {b}, d = b-{j}: P(F has d digits) {p:.3f}; C_t for t = 1..6: " + " ".join(f"{c:.2f}" for c in cs), flush=True)
