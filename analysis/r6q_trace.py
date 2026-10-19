"""Question 90: the length matrix M_b of the basic model, computed exactly.

M[d][d'] = P(F(n) has d' digits) for n a uniform d-digit string (leading
digit uniform on 1..b-1, the others on 0..b-1), w(x) = x^x, w(0) = m.

The row is computed by a walk over the digit values from b-1 down to 0.
Given that no digit above x is present, the free digits that remain are
uniform on 0..x, so the count of x is binomial, and a pending leading digit
equals x with chance 1/x. The walk stops as soon as the partial sum s and
the largest possible final sum have the same number of digits. Branches
below EPS are dropped and their mass is reported. Sums are exact integers.

    python3 r6q_trace.py rows b [m]        one matrix, trace, spectrum
    python3 r6q_trace.py table b1 b2 ...   trace table for several bases
    python3 r6q_trace.py coef [jmax]       C = sum of the c_j of Proposition 29.7
    python3 r6q_trace.py refined b1 b2 ... the refined count as a sum over the
                                           characters of Z/(b-1) (Proposition 3.6
                                           of drafts/round6-model-complete.md)
"""
import bisect
import math
import sys

EPS = 1e-15


def leaves(b, d, m=1):
    """Yield (length of F, x, r, lead, U, p): the walk stopped with the values
    0..x not yet placed, r free digits uniform on 0..x, a leading digit still
    pending (uniform on 1..x) if lead, U = sum of w - x over the placed digits
    modulo b - 1, and probability p. The last item is the dropped mass."""
    qm = b - 1
    w = [m] + [x ** x for x in range(1, b)]
    g = [(w[x] - x) % qm for x in range(b)]
    pw = [b ** k for k in range(b + 2)]
    out = []
    lost = [0.0]

    def length(v):
        return bisect.bisect_right(pw, v)

    def walk(x, r, lead, s, U, p):
        if x < 0 or (r == 0 and not lead):
            out.append((length(s), -1, 0, 0, U, p))
            return
        if x == 0:
            out.append((length(s + r * w[0]), 0, r, 0, U, p))
            return
        top = s + (r + lead) * w[x]
        if s > 0 and length(s) == length(top):
            out.append((length(s), x, r, lead, U, p))
            return
        q = 1.0 / (x + 1)
        opts = [(1.0 / x, 1), (1.0 - 1.0 / x, 0)] if lead else [(1.0, 0)]
        for pl, isl in opts:
            if pl == 0.0:
                continue
            nl = lead and not isl
            pk = (1.0 - q) ** r if r else 1.0
            for k in range(0, r + 1):
                if k > 0:
                    pk *= (r - k + 1) / k * q / (1.0 - q)
                pp = p * pl * pk
                if pp < EPS:
                    if k > r * q + 2:
                        lost[0] += p * pl * max(0.0, 1.0 - sum_binom_upto(r, q, k - 1))
                        break
                    lost[0] += pp
                    continue
                walk(x - 1, r - k, nl, s + (k + isl) * w[x], (U + (k + isl) * g[x]) % qm, pp)

    walk(b - 1, d - 1, 1, 0, 0, 1.0)
    return out, lost[0]


def row(b, d, m=1):
    out = [0.0] * (b + 2)
    lv, lost = leaves(b, d, m)
    for L, _, _, _, _, p in lv:
        out[L] += p
    return out[1:b + 1], lost


def refined(b, m=1):
    """tau[t] = sum over d of E[1{F has d digits} e(t (F - n) / (b-1))], so that
    the refined model's expected count is sum over t of tau[t] and tau[0] is the
    basic trace. Lengths d = 2..b (length 1 is the trivial fixed point)."""
    import numpy as np
    qm = b - 1
    w = [m] + [x ** x for x in range(1, b)]
    g = np.array([(w[x] - x) % qm for x in range(b)])
    t = np.arange(qm)
    E = np.exp(2j * np.pi * np.outer(t, g) / qm)  # E[t, x]
    cum = np.cumsum(E, axis=1)  # sum over y <= x
    phi = cum / np.arange(1, b + 1)  # uniform on 0..x
    psi = np.zeros_like(phi)
    psi[:, 1:] = (cum[:, 1:] - E[:, :1]) / np.arange(1, b)  # uniform on 1..x
    tau = np.zeros(qm, dtype=complex)
    per_d = {}
    for d in range(2, b + 1):
        lv, _ = leaves(b, d, m)
        acc = {}
        for L, x, r, lead, U, p in lv:
            if L == d:
                acc[(x, r, lead, U)] = acc.get((x, r, lead, U), 0.0) + p
        v = np.zeros(qm, dtype=complex)
        for (x, r, lead, U), p in acc.items():
            f = np.exp(2j * np.pi * t * U / qm) * p
            if x >= 0:
                f = f * phi[:, x] ** r
                if lead:
                    f = f * psi[:, x]
            v += f
        per_d[d] = v
        tau += v
    return tau, per_d


def sum_binom_upto(r, q, k):
    tot, pk = 0.0, (1.0 - q) ** r
    for i in range(0, k + 1):
        if i > 0:
            pk *= (r - i + 1) / i * q / (1.0 - q)
        tot += pk
    return tot


def matrix(b, m=1):
    M, lost = [], 0.0
    for d in range(1, b + 1):
        r, l = row(b, d, m)
        M.append(r)
        lost += l
    return M, lost


def n1(b):
    return sum(1 for x in range(1, b) if x ** x < b)


def report_rows(b, m):
    import numpy as np
    M, lost = matrix(b, m)
    A = np.array(M)
    ev = sorted(np.linalg.eigvals(A), key=lambda z: -abs(z))
    tr = float(np.trace(A))
    print(f"b {b} 0^0={m}: trace {tr:.6f}, trace from d=2 {tr - A[0, 0]:.6f}, "
          f"E_1 = {A[0, 0]:.6f} (N_1/(b-1) = {n1(b) / (b - 1):.6f}), dropped mass {lost:.1e}")
    print("  b (trace from d=2 - 1) =", f"{b * (tr - A[0, 0] - 1):.4f}")
    print("  largest |eigenvalues|:", ' '.join(f"{abs(z):.5f}" for z in ev[:6]))
    print("  eigenvalues 2..6:", ' '.join(f"{z.real:+.5f}{z.imag:+.5f}i" for z in ev[1:6]))
    # the trace restricted to lengths >= 2: eigenvalues of the matrix without length 1
    B = A[1:, 1:]
    ev2 = sorted(np.linalg.eigvals(B), key=lambda z: -abs(z))
    print("  without length 1: largest |eigenvalues|:", ' '.join(f"{abs(z):.5f}" for z in ev2[:5]))
    print("  rows d = b-j, j = 0..4, entries at columns b-j', j' = 0..5:")
    for j in range(5):
        print("   ", j, ' '.join(f"{A[b - 1 - j, b - 1 - jp]:.4f}" for jp in range(6)))


def c_coef(jmax=40, kmax=150):
    def delta(j, y, k):
        return (j + 1) * (y - k) + y * k + k - k * (k - 1) / 2 - y * y / 2 - y
    f = [1.0]
    for k in range(1, kmax + 1):
        f.append(f[-1] / k)
    cs = []
    for j in range(jmax + 1):
        tot = 0.0
        for k in range(1, kmax + 1):
            if j >= 1 and k < math.exp(j):
                tot += math.exp(-j) * f[k] * delta(j, j, k)
            if k > math.exp(j + 1):
                tot += math.exp(-(j + 1)) * f[k] * delta(j, j + 1, k)
        cs.append(tot)
    return cs


def main():
    cmd = sys.argv[1]
    if cmd == 'rows':
        b = int(sys.argv[2])
        m = int(sys.argv[3]) if len(sys.argv) > 3 else 1
        report_rows(b, m)
    elif cmd == 'table':
        C = sum(c_coef())
        print(f"# C = sum_j c_j = {C:.5f}; columns: b, m, trace over d=1..b, E_1, b(trace from d=2 - 1), "
              f"b E_1, dropped mass")
        for b in map(int, sys.argv[2:]):
            for m in (0, 1):
                M, lost = matrix(b, m)
                tr = sum(M[i][i] for i in range(b))
                e1 = M[0][0]
                print(f"{b} {m} {tr:.6f} {e1:.6f} {b * (tr - e1 - 1):.4f} {b * e1:.4f} {lost:.1e}", flush=True)
    elif cmd == 'refined':
        for b in map(int, sys.argv[2:]):
            for m in (0, 1):
                tau, per_d = refined(b, m)
                qm = b - 1
                tot = tau.sum().real
                half = tau[qm // 2].real if qm % 2 == 0 else float('nan')
                rest = [k for k in range(1, qm) if 2 * k != qm]
                other = sum(tau[k] for k in rest).real
                big = max(rest, key=lambda k: abs(tau[k]))
                win = sum(per_d[d].sum().real for d in range(b - 6, b + 1))
                print(f"{b} {m}: refined {tot:.4f} = basic {tau[0].real:.4f} + parity {half:+.4f} "
                      f"+ other characters {other:+.4f} (largest |tau_t| {abs(tau[big]):.4f} at t={big}); "
                      f"refined over lengths b-6..b {win:.4f}", flush=True)
    elif cmd == 'coef':
        jmax = int(sys.argv[2]) if len(sys.argv) > 2 else 40
        cs = c_coef(jmax)
        for j, c in enumerate(cs[:12]):
            print(f"c_{j} = {c:+.5f}")
        print(f"sum over j <= {jmax}: {sum(cs):.6f}")


if __name__ == '__main__':
    main()
