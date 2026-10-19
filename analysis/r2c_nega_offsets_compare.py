"""Question 42: D = 0 against the two offset families of r2c_nega_offsets.py.

    cd analysis && python3 r2c_nega_offsets_compare.py

Per base -b (10 to 27) and convention: solutions at D = 0, the model E_m,
and the mean count per offset for the offsets j * step (step = b+1, or
2(b+1) for even b) and j * step * b (which also keep n - F(n) mod b, so
mod 3 when 3 | b). Then totals for the multiples of 3 and for the others.
"""
from collections import defaultdict

import r2c_nega_compare as R


def main():
    off = defaultdict(list)
    for line in open("data/r2c_nega_offsets.txt"):
        p = line.split()
        if p and p[0] == "off":
            off[int(p[1]), int(p[2]), p[3]].append(int(p[5]))
    bases, sols = R.load_census()
    model = R.load_model()
    tot = defaultdict(lambda: [0, 0.0, 0.0, 0.0])
    print("base m | D=0 | model | offsets j*step | offsets j*step*b")
    for b in range(10, 28):
        for m in (0, 1):
            e = sum(model[(b, d)][1 + (m == 1)] for d in range(3, b + 2, 2))
            a, c = off[b, m, "step"], off[b, m, "stepb"]
            o = len(sols[(b, m)])
            print(f"-{b} {m} | {o} | {e:.2f} | {sum(a) / len(a):.2f} | {sum(c) / len(c):.2f}")
            t = tot[("multiple of 3" if b % 3 == 0 else "other", m)]
            t[0] += o
            t[1] += e
            t[2] += sum(a) / len(a)
            t[3] += sum(c) / len(c)
    print()
    print("group, m | D=0 | model | offsets j*step | offsets j*step*b  (bases -10 to -27)")
    for k in sorted(tot):
        t = tot[k]
        print(f"{k[0]}, m={k[1]} | {t[0]} | {t[1]:.2f} | {t[2]:.2f} | {t[3]:.2f}")


if __name__ == "__main__":
    main()
