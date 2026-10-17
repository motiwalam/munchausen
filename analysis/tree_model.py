"""Model prediction of the exact search's node count.

At level k (counts of the m = b-k largest digits decided), a node with a
known prefix of l digits is consistent for exactly C(L + m, m) count vectors,
L = d - l, whatever the prefix digits are. If each node's prefix behaves like
a random one, the expected number of nodes at level k is about C(L_k + m, m),
with L_k the number of digits spanned by the remaining uncertainty
rf * (k-1)^(k-1), rf ~ d k / b.
"""
import math
import sys


def predicted(b, d):
    total = 0.0
    peak = (0, 0)
    for k in range(2, b):
        if k ** k >= b ** d:
            continue
        m = b - k
        rf = max(1.0, d * k / b)
        span = math.log(rf) + (k - 1) * math.log(k - 1) if k > 2 else math.log(rf)
        L = min(d, max(0.0, span / math.log(b) + 1))
        n = math.comb(int(round(L)) + m, m)
        total += n
        peak = max(peak, (n, k))
    return total, peak[1]


def typical(b, d):
    """Same, but only vectors whose unseen copies total about L*m/b."""
    total = 0.0
    for k in range(2, b):
        if k ** k >= b ** d:
            continue
        m = b - k
        rf = max(1.0, d * k / b)
        span = math.log(rf) + (k - 1) * math.log(k - 1) if k > 2 else math.log(rf)
        L = min(d, max(0.0, span / math.log(b) + 1))
        t = int(round(L * m / b))
        total += math.comb(t + m - 1, m - 1) if m > 0 else 1
    return total


if __name__ == '__main__':
    measured = {20: 1.11e5, 25: 2.66e6, 28: 1.94e7, 30: 7.14e7, 32: 2.31e8, 34: 8.81e8, 35: 1.61e9,
                39: 2.31e10, 40: 4.28e10, 41: 8.16e10, 43: 2.92e11}
    prev = None
    for b in sorted(measured):
        p, peak = predicted(b, b - 1)
        print(f"base {b}: predicted nodes for d=b-1 {p:.3g} (peak at k={peak}, k/b={peak/b:.2f}); measured, all d: {measured[b]:.3g}")
    for b in (40, 60, 100, 200, 400, 1000):
        r = (predicted(b + 1, b)[0] / predicted(b, b - 1)[0])
        rt = typical(b + 1, b) / typical(b, b - 1)
        print(f"base {b}: predicted growth per base, full tree {r:.3f}, typical tree {rt:.3f}")
