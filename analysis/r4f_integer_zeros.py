"""The integer analog of the F_q[T] failure: are the zero digits of F(c) forced?

In F_q[T] the Frobenius blocks force zero digits in F(x), and under 0^0 = 1
this breaks the model by large factors. In the integers, for random digit
strings c with d digits (the model distribution) whose sum F(c) also has d
digits, this script compares
  - the law of the number of zero digits of F(c) with that of c,
  - P(zeros of F(c) is even), which the parity factor 1 + e^-2 uses,
  - P(zeros of F(c) = zeros of c), the zero part of the coincidence, against
    the model value sum_k P_c(k)^2,
  - the parity factor 2 P(k even | zeros match) with the true law of the
    zeros of F(c), against the same factor in the model,
  - the rate of zero digits at the top 3 and bottom 3 positions of F(c), times b.
usage: python3 r4f_integer_zeros.py m samples base...
"""
import random
import sys
from collections import Counter


def run(b, d, m, samples, rng):
    w = [m] + [x ** x for x in range(1, b)]
    lo, hi = b ** (d - 1), b ** d
    zc, zf, even_f, even_c, same = Counter(), Counter(), 0, 0, 0
    pos = [0] * d
    n = 0
    while n < samples:
        digs = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(d - 1)]
        s = sum(w[x] for x in digs)
        if not lo <= s < hi:
            continue
        n += 1
        z = digs.count(0)
        t, zs, i = s, 0, 0
        while t:
            zs += t % b == 0
            pos[i] += t % b == 0
            t //= b
            i += 1
        zc[z] += 1
        zf[zs] += 1
        even_f += zs % 2 == 0
        even_c += z % 2 == 0
        same += zs == z
    p_same_indep = sum(zc[k] * zf[k] for k in zc) / n / n
    p_model = sum(zc[k] ** 2 for k in zc) / n / n
    par_true = 2 * sum(zc[k] * zf[k] for k in zc if k % 2 == 0) / n / n / p_same_indep
    par_model = 2 * sum(zc[k] ** 2 for k in zc if k % 2 == 0) / n / n / p_model
    rates = [pos[i] * b / n for i in (d - 1, d - 2, d - 3, 2, 1, 0)]
    return n, zc, zf, even_c / n, even_f / n, same / n, p_same_indep, p_model, par_true, par_model, rates


def main():
    m = int(sys.argv[1])
    samples = int(sys.argv[2])
    rng = random.Random(1)
    print("base d  zeros c  zeros F  P(zF=zc)  indep.  model  parity true  parity model  b*rate top3 / bottom3")
    for b in map(int, sys.argv[3:]):
        d = b - 1
        n, zc, zf, ec, ef, same, ind, pm, pt, pmo, rates = run(b, d, m, samples, rng)
        mc = sum(k * v for k, v in zc.items()) / n
        mf = sum(k * v for k, v in zf.items()) / n
        rs = ' '.join(f"{r:.2f}" for r in rates)
        print(f"{b:4d} {d:3d} {mc:8.4f} {mf:8.4f} {same:8.4f} {ind:7.4f} {pm:6.4f} {pt:12.4f} {pmo:13.4f}  {rs}")


if __name__ == '__main__':
    main()
