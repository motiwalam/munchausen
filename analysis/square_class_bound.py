"""Explicit bound on x for the provable ("square") class of 3-digit patterns.

Pattern: digits with one variable digit x and two fixed digits <= B.
Completing the square gives r^2 = Y^2 + R with Y^2 the dominant term. When
Y^2 is a perfect square and R != 0, |R| >= 2Y - 1. This script finds the
largest x for which that inequality can hold, over all patterns.
"""
import math
import sys

B = int(sys.argv[1])
K = 2 * max(1, B) ** max(1, B) + 1  # bound on the weights of the two fixed digits
worst = 0
for x in range(2, 2_000):
    # compare logarithms; 2Y - 1 >= Y for Y >= 1
    # x leading: Y = 2 x^((x+1)/2), |R| <= s1^2 + 4x(K + s0)
    lead = math.log(2) + (x + 1) / 2 * math.log(x) <= math.log(B * B + 4 * x * (K + B))
    # x not leading, leading digit p: Y = 2 sqrt(p) x^(x/2), |R| <= x^2 + B^2 + 4p(K + B + x)
    other = any(math.log(2 * math.sqrt(p)) + x / 2 * math.log(x) <= math.log(x * x + B * B + 4 * p * (K + B + x))
                for p in range(1, B + 1))
    if lead or other:
        worst = x
print(f"fixed digits <= {B}: the square class has no solution with x > {worst}")
