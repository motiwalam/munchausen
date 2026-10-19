"""Do integer solutions have the digit law the model gives them?

In F_q[T] the model fails because the solutions live on a special set of
class sums (forced by the Frobenius blocks). The integer analog is a check of
the digit law of the actual solutions. Under the model, the multiset of a
solution is distributed like the multiset of a random string of its length,
conditioned on the identity. For zero digits that law is Binomial(d - 1, 1/b)
(top digit nonzero), conditioned on an even count in odd bases under 0^0 = 1.
This script compares the observed zero counts of the long solutions (at least
b - 6 digits) in bases 12 to 41 with that law.
usage: python3 r4f_integer_types.py
"""
import ast
from math import comb


def load(path):
    sols = {}
    for line in open(path):
        b, _, _, rest = line.strip().split(':', 3)
        sols[int(b)] = ast.literal_eval('[' + rest + ']')
    return sols


def binom_law(n, p):
    return [comb(n, k) * p ** k * (1 - p) ** (n - k) for k in range(n + 1)]


def main():
    for m in (0, 1):
        sols = load(f'../output/b2-41-{m}.txt')
        for parity in ('even', 'odd'):
            n = obs = exp = var = 0.0
            z0_obs = z0_exp = 0.0
            for b, lst in sols.items():
                if b < 12 or (b % 2 == 0) != (parity == 'even'):
                    continue
                for s in lst:
                    d = len(s)
                    if d < b - 6:
                        continue
                    law = binom_law(d - 1, 1 / b)
                    if m == 1 and b % 2 == 1:
                        law = [p if k % 2 == 0 else 0.0 for k, p in enumerate(law)]
                    tot = sum(law)
                    law = [p / tot for p in law]
                    mean = sum(k * p for k, p in enumerate(law))
                    n += 1
                    obs += s.count(0)
                    exp += mean
                    var += sum(k * k * p for k, p in enumerate(law)) - mean ** 2
                    z0_obs += s.count(0) == 0
                    z0_exp += law[0]
            print(f"0^0 = {m}, {parity} bases 12-41: {int(n)} long solutions, zero digits {int(obs)} "
                  f"against {exp:.1f} +/- {var ** 0.5:.1f}; solutions without zeros {int(z0_obs)} against {z0_exp:.1f}")


if __name__ == '__main__':
    main()
