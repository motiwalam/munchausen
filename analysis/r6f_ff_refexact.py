"""Chapter 36, referee checks written separately from r6f_ff_bounds.py and
r6f_ff_runs.py.

usage:
  r6f_ff_refexact.py bounds          X_A(p), X_B(p) for p = 1, 2, 10, 20 by
                                     bisection on the inequalities of
                                     Theorems 36.5 and 36.9; the middle
                                     families with pA a square
  r6f_ff_refexact.py exact P Q X     every last-position string (p, q, x),
                                     p <= P, q <= Q, x odd <= X, tested by
                                     an exact integer square root
  r6f_ff_refexact.py inputs last     input of r6f_ff_refcheck for the slice
                                     of Proposition 36.8 (section 36.7)
  r6f_ff_refexact.py inputs midlead  input for the middle and leading
                                     families, small digits <= 20, x <= 2e6
"""
import math
import random
import sys

sys.set_int_max_str_digits(0)


def w(d, m):
    return m if d == 0 else d ** d


def convs(*digits):
    return (0, 1) if 0 in digits else (1,)


def exact(pmax, qmax, xmax):
    """Last position, x odd: 4p x^x + q^2 + 4p (W - x) = (2pb + q)^2."""
    for p in range(1, pmax + 1):
        for q in range(qmax + 1):
            for m in convs(q):
                W = w(p, m) + w(q, m)
                for x in range(1, xmax + 1, 2):
                    V = 4 * p * x ** x + q * q + 4 * p * (W - x)
                    s = math.isqrt(V)
                    if s * s == V and (s - q) % (2 * p) == 0:
                        b = (s - q) // (2 * p)
                        if b > max(p, q, x):
                            print("solution p q x m base", p, q, x, m, b)
    print("exact test done: p <=", pmax, "q <=", qmax, "odd x <=", xmax)


def XA(p):
    """Largest integer x with x <= 10 sqrt(D) (log 4D + 2) / pi, D = 4px."""
    def ok(x):
        D = 4 * p * x
        return x <= 10 * math.sqrt(D) * (math.log(4 * D) + 2) / math.pi
    lo, hi = 25, 10 ** 9
    assert ok(lo) and not ok(hi)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo


def XB(p):
    """Crossing point of the inequality of Theorem 36.9, D = 4px."""
    C = 2 ** 38 * 4 * (1 + math.log(2)) * math.pi * 4 / math.sqrt(3)

    def ok(lx):
        x = math.exp(lx)
        D = 4 * p * x
        e = 2 * math.sqrt(D) * (math.log(4 * D) + 2) / math.pi
        ws = max(math.log(p * D), math.pi)
        Bp = 5 * x * lx + 5 * ws + 6
        lhs = x / 2 * lx - 0.5 * math.log(8 * x)
        return lhs <= C * (1 + math.log(Bp)) * e * ws * lx
    lo, hi = math.log(25), 200.0
    assert ok(lo) and not ok(hi)
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return math.exp(lo)


def bounds():
    for p in (1, 2, 10, 20):
        print("p", p, "X_A", XA(p), "X_B %.4g" % XB(p))
    n, sq = 0, []
    for p in range(1, 21):
        for q in range(21):
            for m in convs(q):
                n += 1
                v = p * (w(p, m) + w(q, m) - q)
                if math.isqrt(v) ** 2 == v:
                    sq.append((p, q, m))
    print("middle families", n, "with pA a square", len(sq), sq)


def inputs(kind):
    if kind == "last":
        random.seed(36)
        for p in range(1, 11):
            for q in range(11):
                for m in convs(q):
                    print(0, p, q, m, 1, 3_000_000, 1)
        for p in range(1, 11):
            for q in range(11):
                for m in convs(q):
                    top = w(p, m) + w(q, m) + q * q // (4 * p) + 1
                    if top <= 3_000_000:
                        continue
                    print(0, p, q, m, max(3_000_001, top - 1_000_000),
                          top + 1_000_000, 1)
                    if top - 1_000_000 > 4_000_001:
                        r = random.randrange(3_000_001, top - 2_000_000)
                        print(0, p, q, m, r, r + 1_000_000, 1)
    else:
        for p in range(1, 21):
            for q in range(21):
                for m in convs(q):
                    print(1, p, q, m, 1, 2_000_000, 1)
        for a in range(21):
            for c in range(21):
                for m in convs(a, c):
                    print(2, a, c, m, 2, 2_000_000, 0)


def main():
    cmd = sys.argv[1]
    if cmd == "bounds":
        bounds()
    elif cmd == "exact":
        exact(*map(int, sys.argv[2:5]))
    elif cmd == "inputs":
        inputs(sys.argv[2])


if __name__ == "__main__":
    main()
