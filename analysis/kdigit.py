"""Find every k-digit Munchausen number in every base, up to a digit bound.

A digit string s (most significant first) has the value P_s(b) = sum s_i b^i,
which grows with b, while its Munchausen sum F(s) does not depend on b. So s
is a solution in at most one base: the integer root of P_s(b) = F(s) with b
larger than every digit of s.

A k-digit solution in base b only uses digits x with x^x < b^k. Enumerating
all strings with digits up to M therefore finds every k-digit solution in
every base b with b^k <= (M+1)^(M+1).

Usage: kdigit.py k M  -> prints "k mode base digits" lines.
"""
import itertools
import math
import sys


def iroot(n, r):
    """floor(n ** (1/r)) for integers, by Newton's method."""
    if n < 2 or r == 1:
        return n
    x = 1 << ((n.bit_length() + r - 1) // r)  # an upper bound
    while True:
        y = ((r - 1) * x + n // x ** (r - 1)) // r
        if y >= x:
            return x
        x = y


def base_for(s, f):
    """The base b > max(s) with P_s(b) = f, or None."""
    k = len(s)
    top = s[0]
    if k == 1:
        return None
    lo = max(s) + 1
    b = iroot(f // top, k - 1)  # P_s(b) >= top * b^(k-1), so the root is <= this
    if b < lo:
        return None
    # Newton from above: P is convex and increasing for b > 0, so the
    # iterates stay at or above the root
    while True:
        v = 0
        dv = 0
        for c in s:
            dv = dv * b + v
            v = v * b + c
        v -= f
        if v == 0:
            return b if b >= lo else None
        if v < 0:
            return None
        # the tangent meets f at or right of the root, so this never
        # jumps past it; a step below 1 still has to try b-1
        b -= max(1, v // dv)
        if b < lo:
            return None


def search(k, m):
    w = [x ** x for x in range(m + 1)]
    out = []
    for s in itertools.product(range(m + 1), repeat=k):
        if s[0] == 0:
            continue
        f1 = sum(w[x] for x in s)  # w[0] = 0^0 = 1 in Python
        z = s.count(0)
        for mode, f in ((1, f1), (0, f1 - z)):
            if mode == 0 and z == 0:
                continue  # same sum as under 0^0 = 1; reported once below
            b = base_for(s, f)
            if b is not None:
                modes = (mode,) if z else (0, 1)
                for md in modes:
                    out.append((k, md, b, s))
    return out


if __name__ == '__main__':
    k, m = int(sys.argv[1]), int(sys.argv[2])
    sols = search(k, m)
    sols.sort(key=lambda r: (r[1], r[2], r[3]))
    for k_, mode, b, s in sols:
        print(k_, mode, b, ','.join(map(str, s)))
    print(f"# k={k} M={m}: {len(sols)} solutions; complete for bases b with "
          f"b^{k} <= {m+1}^{m+1}, that is b <= about 10^{(m+1)*math.log10(m+1)/k:.1f}", file=sys.stderr)
