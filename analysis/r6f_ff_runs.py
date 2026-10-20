"""Round 6, field families: inputs for r6f_ff_sieve and exact checks.

usage:
  r6f_ff_runs.py evidence B X        families with small digits <= B in the
                                     three open regimes, x <= X
  r6f_ff_runs.py closure B CAP       last position, x odd, small digits
                                     <= B, x up to max(X_A(p), top of the
                                     real range W + q^2/(4p)) when that top
                                     is at most CAP
  r6f_ff_runs.py check FILE          exact test of every survivor in FILE

The open regimes (field changing with x):
  last, x odd   (p, q, x)   imaginary field Q(sqrt(-D)) once x > W + q^2/(4p)
  mid,  x odd   (p, x, q)   real field Q(sqrt(x^2 + 4pA))
  lead, x even  (x, q, r)   real field Q(sqrt(q^2 + 4xA))
"""
import math
import sys

sys.set_int_max_str_digits(0)

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from r6f_ff_bounds import largest, allowed_A  # noqa: E402
from sympy import factorint  # noqa: E402


def w(d, m):
    return m if d == 0 else d ** d


def conventions(*digits):
    return (0, 1) if 0 in digits else (1,)


def evidence(B, X):
    for p in range(1, B + 1):
        for q in range(B + 1):
            for m in conventions(q):
                print(p, q, "last", m, 1, X, 1)
                print(p, q, "mid", m, 1, X, 1)
    for a in range(B + 1):
        for c in range(B + 1):
            for m in conventions(a, c):
                print(a, c, "lead", m, 1, X, 0)


def closure(B, cap):
    for p in range(1, B + 1):
        xa = largest(allowed_A, p)
        for q in range(B + 1):
            for m in conventions(q):
                top = w(p, m) + w(q, m) + q * q // (4 * p) + 1
                if top > cap:
                    continue
                print(p, q, "last", m, 1, max(xa, top), 1)


def solution(a, c, pos, m, x):
    """Exact test; returns the base or None."""
    if pos == "last":
        p, q = a, c
        D = q * q + 4 * p * (w(p, m) + w(q, m) + x ** x - x)
        s = math.isqrt(D)
        if s * s != D or (s - q) % (2 * p):
            return None
        b = (s - q) // (2 * p)
        return b if b > max(p, q, x) else None
    if pos == "mid":
        p, q = a, c
        D = x * x + 4 * p * (w(p, m) + w(q, m) + x ** x - q)
        s = math.isqrt(D)
        if s * s != D or (s - x) % (2 * p):
            return None
        b = (s - x) // (2 * p)
        return b if b > max(p, q, x) else None
    q, r = a, c
    D = q * q + 4 * x * (x ** x + w(q, m) + w(r, m) - r)
    s = math.isqrt(D)
    if s * s != D or (s - q) % (2 * x):
        return None
    b = (s - q) // (2 * x)
    return b if b > max(q, r, x) else None


def check(path):
    for line in open(path):
        if not line.startswith("survivor"):
            continue
        _, a, c, pos, m, x = line.split()
        a, c, m, x = int(a), int(c), int(m), int(x)
        if x > 20000:
            if pos == "last" and c * c + 4 * a * (w(a, m) + w(c, m) - x) == 0:
                # R = 0: a solution exactly when x^x / a is a square
                fa = factorint(x)
                fp = factorint(a)
                ok = all((x * fa.get(l, 0) - fp.get(l, 0)) % 2 == 0
                         for l in set(fa) | set(fp))
                print(line.strip(), "-> R = 0,", "solution, base about 10^%.0f"
                      % (x * math.log10(x) / 2) if ok else "not a solution")
            elif pos == "lead" and w(a, m) + w(c, m) - c == 0:
                # A = 0: D = 4 x^(x+1) + a^2 with a = 0, a square iff x is
                ok = a == 0 and math.isqrt(x) ** 2 == x
                print(line.strip(), "-> A = 0,", "solution (x a square)" if ok
                      else "not a solution")
            else:
                print("too large for the exact test:", line.strip())
            continue
        b = solution(a, c, pos, m, x)
        print(line.strip(), "->", ("solution in base %d" % b if b < 10 ** 30 else "solution in a base of %d digits" % len(str(b))) if b else "not a solution")


def main():
    cmd = sys.argv[1]
    if cmd == "evidence":
        evidence(int(sys.argv[2]), int(float(sys.argv[3])))
    elif cmd == "closure":
        closure(int(sys.argv[2]), int(float(sys.argv[3])))
    elif cmd == "check":
        check(sys.argv[2])


if __name__ == "__main__":
    main()
