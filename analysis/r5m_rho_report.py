"""Summary of r5m_rho output (question 80, Theorem 3.3 of round5-model.md).

For each base b: rho(b) = max |psi_L(h)| over L in [ceil(b/2), b] and h outside
H_0, and the bound kappa(b) <= |H_0| + (b - 1) rho^n with n = ceil(b/2) - 2,
the fewest uniform digits besides the leading one in Lemma 13.10.

usage: python3 r5m_rho_report.py FILE
"""
import math
import sys


def main():
    rows = []
    for line in open(sys.argv[1]):
        if line.startswith('#'):
            continue
        b, rho, L, h, cp = line.split()
        rows.append((int(b), float(rho), int(L), int(h), float(cp)))
    print(f"bases {rows[0][0]}..{rows[-1][0]}")
    for lo in (5, 10, 20, 50, 100, 1000, 3000):
        rs = [r for r in rows if r[0] >= lo]
        m = max(rs, key=lambda r: r[1])
        c = min(rs, key=lambda r: r[4])
        print(f"b >= {lo}: max rho {m[1]:.4f} at b {m[0]} (L {m[2]}, h {m[3]});  min (1 - Re psi) {c[4]:.4f} at b {c[0]}")
    print("\nkappa bound |H_0| + (b-1) rho^n, n = ceil(b/2) - 2:")
    worst = {}
    first_ok = None
    for b, rho, L, h, cp in rows:
        n = (b + 1) // 2 - 2
        h0 = 2 if (b - 1) % 2 == 0 else 1
        extra = (b - 1) * rho ** n
        worst[b] = (h0, extra)
    for lo, hi in ((5, 9), (10, 19), (20, 49), (50, 99), (100, 999), (1000, 6000)):
        ex = [worst[b][1] for b in worst if lo <= b <= hi]
        print(f"  b in [{lo}, {hi}]: max extra {max(ex):.3g}")
    bad = [b for b in worst if b >= 10 and worst[b][1] >= 1e-3]
    print(f"  bases >= 10 with extra >= 1e-3: {len(bad)}, largest {max(bad) if bad else None}")
    for b in (10, 20, 30, 50, 100):
        print(f"  b {b}: |H_0| {worst[b][0]} extra {worst[b][1]:.3g}")
    big = [b for b in worst if b >= 12 and worst[b][1] > 5]
    print(f"  bases >= 12 with extra > 5: {big}")


if __name__ == '__main__':
    main()
