"""Round 4, blocks: the structure of the short solutions under 0^0 = 1.

For every k-digit solution s in base b (k = 3 to 7, lists data/k<k>.txt and
the round 3 lists), and every split into a top part t (k - m digits) and a
tail u (m digits), the remainder of the top part is

    R_m = b^m P_t(b) - F(t) = F(u) - P_u(b).

R_m = 0 means that t is an exact self-paying block at shift m and that the
tail pays for itself. The script also lists every contiguous substring that
pays for itself at its own position (b^i P_t(b) = F(t)), the self-paying
digits, and whether the top part is a binomial prefix
c^(j-i) C(j,i) e^i (section 3 of the draft).

    python3 r4b_solutions.py > data/r4b_solutions.txt
"""
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def w(x, mode):
    return mode if x == 0 else x ** x


def P(digits, b):
    v = 0
    for d in digits:
        v = v * b + d
    return v


def F(digits, mode):
    return sum(w(d, mode) for d in digits)


def load(mode):
    out = set()
    for k in range(3, 8):
        for path in [f'data/k{k}.txt']:
            for line in open(os.path.join(HERE, path)):
                if line.startswith('#') or not line.strip():
                    continue
                kk, m, b, ds = line.split()
                if int(m) == mode:
                    out.add((int(kk), int(b), tuple(map(int, ds.split(',')))))
    return sorted(out, key=lambda r: (r[0], r[1], r[2]))


def binomial_prefix(t):
    """(c, e) if t = (c^j, j c^(j-1) e, ..., j c e^(j-1)) with j = len(t), else None"""
    j = len(t)
    c = round(t[0] ** (1.0 / j))
    for cc in (c - 1, c, c + 1):
        if cc >= 1 and cc ** j == t[0]:
            if j == 1:
                return (cc, None)
            if t[1] % (j * cc ** (j - 1)):
                return None
            e = t[1] // (j * cc ** (j - 1))
            if all(t[i] == cc ** (j - i) * math.comb(j, i) * e ** i for i in range(j)):
                return (cc, e)
    return None


def describe(k, b, s, mode):
    lines = [f"## {k} digits, base {b}, digits {s}, 0^0 = {mode}"]
    n = P(s, b)
    Fs = F(s, mode)
    assert n == Fs
    ws = sorted(((w(d, mode), d) for d in s), reverse=True)
    lines.append(f"n = {n}; weights, largest first: " + ', '.join(f"{d}^{d}={v}" if d else f"0^0={v}" for v, d in ws)
                 + f"; largest weight / n = {ws[0][0] / n:.4f}, two largest / n = {(ws[0][0] + ws[1][0]) / n:.4f}")
    for m in range(1, k):
        t, u = s[:k - m], s[k - m:]
        R = b ** m * P(t, b) - F(t, mode)
        # derivative of r^m P_t(r) at b: the spacing of R between neighbouring bases
        dQ = m * b ** (m - 1) * P(t, b) + b ** m * sum((len(t) - 1 - i) * d * b ** (len(t) - 2 - i) for i, d in enumerate(t) if len(t) - 1 - i > 0)
        lines.append(f"  split m = {m}: top {t}, tail {u}: R = {R}, R / b^m = {R / b ** m:+.4f}, |R| / Q' = {abs(R) / dQ:.2e}"
                     + ("  EXACT BLOCK" if R == 0 else ""))
    blocks = []
    for i in range(k):
        for j in range(i + 1, k + 1):
            t = s[i:j]
            if t[0] == 0 or (i == 0 and j == k):
                continue
            pos = k - j
            if b ** pos * P(t, b) == F(t, mode):
                blocks.append((t, pos))
    lines.append("  exact blocks inside (substring, shift): " + (', '.join(f"{t}@{p}" for t, p in blocks) if blocks else 'none'))
    bp = binomial_prefix(s[:-1])
    lines.append(f"  binomial prefix (c, e): {bp}")
    return lines


def main():
    for mode in (1, 0):
        print(f"# 0^0 = {mode}")
        for k, b, s in load(mode):
            if mode == 0 and b > 10 ** 6:
                continue
            print('\n'.join(describe(k, b, s, mode)))
        print()


if __name__ == '__main__':
    main()
