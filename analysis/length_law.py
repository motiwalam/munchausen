"""Finite-base law of J = b - k for long solutions, from the sampled model."""
import math
from length_window import short_e
from model import limit_terms

LIM = limit_terms(16)
print("expected solutions with exactly J = b - k digits short of b (0^0 = 1)")
print("   J " + "".join(f"{b:>10d}" for b in (50, 100, 200, 400, 800)) + "     limit")
rows = {}
for b in (50, 100, 200, 400, 800):
    n = 20000 if b <= 200 else 6000
    rows[b] = [short_e(b, b - j, samples=n) for j in range(0, 15)]
for j in range(0, 15):
    print(f"{j:4d} " + "".join(f"{rows[b][j]:10.2e}" for b in rows) + f"{LIM.get(j, 0):10.2e}")
for b in rows:
    r = rows[b]
    slope = (math.log(r[10]) - math.log(r[4])) / 6
    print(f"base {b}: ln E falls {-slope:.3f} per unit of J between J = 4 and J = 10; "
          f"sum over J >= 1 {sum(r[1:]):.3f}")
