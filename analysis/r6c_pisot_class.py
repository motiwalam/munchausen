"""Question 107: the class modulo 2x in even Pisot bases eps_x.

    python3 r6c_pisot_class.py X NMAX > data/r6c_pisot_class_<X>.txt

eps = (x + sqrt(x^2 + 4)) / 2. Every N <= NMAX gets its greedy expansion,
exactly in Z[eps]. Section 26.6.2 proves, for even x,

    (N - sum d_i) / x == A_2 + A_3 (mod 2),

with A_r the digit sum over the positions == r (mod 4). If x divides
F - sum d_i (the identity of Proposition 21.12 for the multiset), then
N - F = j x with

    j == a - g (mod 2),  a = A_2 + A_3,  g = (F - sum d_i) / x.

Per length T and convention the script counts:
- the share of N with a even, over all N of length T;
- over the broad set, the N whose multiset meets the identity and whose F
  lies in [N/2, 2N]: the shares of a even, of g even and of a == g, and
  the share p_a p_g + (1 - p_a)(1 - p_g) that independent a and g give;
- over the near-solutions, the N with 1 <= |j| <= JMAX: the share of
  even j, of a even and of g even; and the counts for j > 0 alone, the
  offsets of section 26.6.2.
A near-solution has even j exactly when a == g, so the broad share of
a == g predicts the class factor if being near does not depend on a or g.
"""
import math
import sys
from collections import defaultdict

JMAX = 30


def main():
    x = int(sys.argv[1])
    nmax = int(sys.argv[2])
    D = x * x + 4
    e = (x + math.sqrt(D)) / 2

    def mul(p, q):
        a, b = p
        c, d = q
        return (a * c + b * d, a * d + b * c + x * b * d)

    def nonneg(p):
        # a + b eps >= 0, with eps = (x + sqrt(D)) / 2: sign of (2a + b x) + b sqrt(D)
        a, b = p
        u = 2 * a + b * x
        if u >= 0 and b >= 0:
            return True
        if u <= 0 and b <= 0:
            return u == 0 and b == 0
        if u > 0:
            return u * u >= b * b * D
        return b * b * D >= u * u

    def floor_val(p):
        a, b = p
        f = math.floor(a + b * e)
        while not nonneg((a - f, b)):
            f -= 1
        while nonneg((a - f - 1, b)):
            f += 1
        return f

    inv = (-x, 1)  # 1/eps = eps - x
    pw = {0: (1, 0)}
    for i in range(1, 80):
        pw[i] = mul(pw[i - 1], (0, 1))
        pw[-i] = mul(pw[-i + 1], inv)

    def expand(n):
        k = int(math.log(n) / math.log(e)) if n > 1 else 0
        while nonneg((n - pw[k + 1][0], -pw[k + 1][1])):
            k += 1
        while not nonneg((n - pw[k][0], -pw[k][1])):
            k -= 1
        r = (n, 0)
        out = []
        i = k
        while r != (0, 0):
            q = mul(r, pw[-i])
            dg = floor_val(q)
            out.append((i, dg))
            r = (r[0] - dg * pw[i][0], r[1] - dg * pw[i][1])
            i -= 1
        return out

    # per (m, T): all N; the broad set (identity holds, N/2 <= F <= 2N);
    # the near-solutions (1 <= |j| <= JMAX)
    out = defaultdict(lambda: [0] * 12)
    for n in range(1, nmax + 1):
        ex = expand(n)
        T = ex[0][0] - ex[-1][0] + 1
        a = sum(dg for i, dg in ex if i % 4 in (2, 3)) & 1
        ds = [dg for _, dg in ex]
        s = sum(ds)
        nz = T - len(ds) + sum(1 for d in ds if d == 0)
        fpos = sum(d ** d for d in ds if d)
        for m in (0, 1):
            f = fpos + m * nz
            c = out[(m, T)]
            c[0] += 1
            c[1] += a == 0
            if (f - s) % x:
                continue
            g = ((f - s) // x) & 1
            j = (n - f) // x
            assert (j - (a - g)) % 2 == 0, (n, j, a, g)
            if n <= 2 * f and f <= 2 * n:
                c[2] += 1
                c[3] += a == 0
                c[4] += g == 0
                c[5] += a == g
            if 1 <= abs(j) <= JMAX:
                c[6] += 1
                c[7] += j % 2 == 0
                c[8] += a == 0
                c[9] += g == 0
                if j > 0:
                    c[10] += 1
                    c[11] += j % 2 == 0
    print(f"# x {x} NMAX {nmax} JMAX {JMAX}")
    print("# x m T n_all pa_all n_broad pa pg p(a=g) pred_indep n_near even_near pa_near pg_near pred_indep_near "
          "n_near_pos even_near_pos")
    tot = defaultdict(lambda: [0] * 12)
    for (m, T), c in sorted(out.items()):
        for i in range(12):
            tot[m][i] += c[i]
    for (m, T), c in sorted(out.items()) + [((m, 'all'), tot[m]) for m in (0, 1)]:
        if not c[2] and not c[6]:
            continue
        pa = c[3] / c[2] if c[2] else float('nan')
        pg = c[4] / c[2] if c[2] else float('nan')
        eq = c[5] / c[2] if c[2] else float('nan')
        pred = pa * pg + (1 - pa) * (1 - pg)
        ne = c[7] / c[6] if c[6] else float('nan')
        pan = c[8] / c[6] if c[6] else float('nan')
        pgn = c[9] / c[6] if c[6] else float('nan')
        predn = pan * pgn + (1 - pan) * (1 - pgn)
        print(f"{x} {m} {T} {c[0]} {c[1] / c[0]:.4f} {c[2]} {pa:.4f} {pg:.4f} {eq:.4f} {pred:.4f} "
              f"{c[6]} {ne:.4f} {pan:.4f} {pgn:.4f} {predn:.4f} {c[10]} {c[11]}")


if __name__ == '__main__':
    main()
