"""Question 100: near-solutions that provably exist in every base.

The construction of Theorem 5.1 of drafts/round6-existence.md, in exact
integers. For a base b and a target T:

  1. L starts as one copy of b - 1. F(L) has b - 1 digits.
  2. For j = 2..T+1 (digit j sits at position b - 1 - j), if digit j of
     F(L) lies in the zone Z_j, add copies of the steering digit x_j (the
     largest x with x^x <= (b - |Z_j| - 1) b^(b-1-j)) until it leaves.
     Z_j = [x*, b-1] for j <= T, Z_(T+1) = {b-1}; x* is the largest x with
     T x^x + b < b^(b-2-T).
  3. a_1..a_T = digits 1..T of F(L). c = L + {a_i} + zeros, b - 1 digits.
  4. n = a_1 ... a_T followed by the other digits of c. Then n and F(n)
     agree in their top T digits, so |n - F(n)| < b^(b-1-T).

    python3 r6h_near.py check BMIN BMAX [STEP]   run the construction
    python3 r6h_near.py bound BMIN BMAX [STEP]   the guaranteed T of Theorem 5.1

check prints, per base: the guaranteed T, the largest T for which the
construction fits in b - 1 digits, the copies used, and a verification of
the resulting n under both conventions.
"""
import math
import sys


def digit(F, b, j):
    return (F // b ** (b - 1 - j)) % b


def xstar(b, T):
    lim = b ** (b - 2 - T)
    x = b - 1
    while x >= 1 and T * x ** x + b >= lim:
        x -= 1
    return x


def steer_digit(b, z, P):
    cap = (b - z - 1) * P
    x = b - 1
    while x > 1 and x ** x > cap:
        x -= 1
    return x


def construct(b, T):
    """Return (L as dict, a list, copies) or None if it does not fit."""
    if T + 3 > b - 1:
        return None
    xs = xstar(b, T)
    if xs < 1:
        return None
    L = {b - 1: 1}
    F = (b - 1) ** (b - 1)
    if digit(F, b, 1) >= xs:
        return None
    copies = 0
    for j in range(2, T + 2):
        lo = xs if j <= T else b - 1
        z = b - lo
        if 2 * z > b:
            return None
        P = b ** (b - 1 - j)
        if lo <= digit(F, b, j):
            x = steer_digit(b, z, P)
            w = x ** x
            while lo <= digit(F, b, j):
                F += w
                L[x] = L.get(x, 0) + 1
                copies += 1
                if sum(L.values()) + T > b - 2:
                    return None
    a = [digit(F, b, j) for j in range(1, T + 1)]
    if max(a) > xs or digit(F, b, T + 1) > b - 2:
        raise AssertionError((b, T, a))
    return L, a, copies


def ilog(v):
    """natural log of a positive integer of any size"""
    s = max(v.bit_length() - 60, 0)
    return math.log(v >> s) + s * math.log(2)


def verify(b, T, L, a):
    """Build n and check it under both conventions. Return the ratio
    log_b(n / |n - F(n)|) for the worse convention."""
    digits = list(a)
    rest = []
    for x, k in sorted(L.items(), reverse=True):
        rest += [x] * k
    zeros = b - 1 - len(digits) - len(rest)
    assert zeros >= 1
    rest += [0] * zeros
    s = digits + rest
    n = 0
    for x in s:
        n = n * b + x
    worst = None
    for m in (0, 1):
        F = sum(x ** x if x else m for x in s)
        D = n - F
        if D == 0:
            # swap the b - 1 and a zero below the top T digits
            i, k = s.index(b - 1, T), len(s) - 1
            s2 = s[:]
            s2[i], s2[k] = s2[k], s2[i]
            n2 = 0
            for x in s2:
                n2 = n2 * b + x
            D = n2 - F
        assert 0 < abs(D) < b ** (b - 1 - T), (b, T, m)
        t = (ilog(n) - ilog(abs(D))) / math.log(b)
        worst = t if worst is None else min(worst, t)
    return worst


def guaranteed(b):
    """Largest T allowed by the cost bound of Theorem 5.1."""
    best = 0
    for T in range(1, b):
        z = T + 4
        if 2 * z > b or b * (1 - math.exp(-1 + 1 / b)) <= T + 5:
            break
        cost = 1 + T * (z * math.e * b / (b - z - 1) + 1) + (math.e * b / (b - 2) + 1) + T
        if cost > b - 2:
            break
        best = T
    return best


def main():
    mode = sys.argv[1]
    bmin, bmax = int(sys.argv[2]), int(sys.argv[3])
    step = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    if mode == 'bound':
        for b in range(bmin, bmax + 1, step):
            g = guaranteed(b)
            print(f"{b} {g} {g - math.log(math.e) / math.log(b):.3f}")
        return
    print("# b T_thm T_max copies_at_T_max t_achieved(T_max) t_at_T_thm")
    for b in range(bmin, bmax + 1, step):
        g = guaranteed(b)
        tg = None
        if g >= 1:
            r = construct(b, g)
            assert r is not None, (b, g)
            tg = verify(b, g, r[0], r[1])
        best = None
        T = max(g, 1)
        while True:
            r = construct(b, T)
            if r is None:
                break
            best = (T, r)
            T += 1
        if best is None:
            print(f"{b} {g} 0 - - -", flush=True)
            continue
        T, (L, a, copies) = best
        t = verify(b, T, L, a)
        tgs = f"{tg:.3f}" if tg is not None else "-"
        print(f"{b} {g} {T} {copies} {t:.3f} {tgs}", flush=True)


if __name__ == '__main__':
    main()
