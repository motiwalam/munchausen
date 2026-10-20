"""Referee exact test (chapter 38): integer square roots, no sieve.
middle (p, x, q): x^2 + 4p (x^x + A) a square, A = w(p) + w(q) - q, x odd
leading (x, q, r): q^2 + 4x (x^x + A) a square, A = w(q) + w(r) - r, x even
A root b must also be a positive integer with b > max digit."""
import sys
from math import isqrt
from multiprocessing import Pool

X = int(sys.argv[1])


def w(d, m):
    return m if d == 0 else d ** d


FAM = [("mid", 1, 1, 1), ("mid", 1, 0, 0), ("mid", 1, 3, 1), ("mid", 3, 1, 1),
       ("mid", 3, 0, 0), ("lead", 1, 1, 1), ("lead", 1, 0, 0)]


def test(x):
    out = []
    xx = x ** x
    for pos, a, c, m in FAM:
        if pos == "mid":
            if x % 2 == 0:
                continue
            A = w(a, m) + w(c, m) - c
            D = x * x + 4 * a * (xx + A)
            U = isqrt(D)
            if U * U == D and (U - x) % (2 * a) == 0:
                out.append((pos, a, c, m, x, (U - x) // (2 * a)))
        else:
            if x % 2:
                continue
            A = w(a, m) + w(c, m) - c
            D = a * a + 4 * x * (xx + A)
            U = isqrt(D)
            if U * U == D and (U - a) % (2 * x) == 0:
                out.append((pos, a, c, m, x, (U - a) // (2 * x)))
    return out


if __name__ == "__main__":
  with Pool(8) as pool:
      for res in pool.imap(test, range(1, X + 1), chunksize=8):
          for r in res:
              print("root", *r)
  print(f"done: x <= {X}, families {FAM}")
