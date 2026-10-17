"""The window conjecture for lengths under 0^0 = 1, tested against the model.

Write J = b - k for a k-digit solution in base b. The model gives the
expected number of solutions with each J:
- bulk (k large): the large-base limit E_{b-j} = e^-(j-1) P(1 <= Poisson(1)
  < e^j) of model.limit_terms;
- short (k small): E = P(F(n) has k digits) for a random k-digit string,
  estimated by sampling digits below the largest digit X with X^X < b^k.
An "exception" is a solution with k >= 3 and J > ln b + 2. This script
compares observed and expected exceptions where the data are complete, and
estimates how many the model expects outside the searched ranges.
"""
import math
import numpy as np
from catalog import everything, exhaustive_bases
from model import limit_terms

RNG = np.random.default_rng(3)
LIMIT = limit_terms(60)


def short_e(b, k, mode=1, samples=4000):
    """Model expectation of k-digit solutions in base b (any k, sampled)."""
    lnb = math.log(b)
    X = 1
    while X + 1 < b and (X + 1) * math.log(X + 1) < k * lnb:
        X += 1
    xs = np.arange(X + 1, dtype=float)
    with np.errstate(divide='ignore'):
        lw = np.where(xs > 0, xs * np.log(np.maximum(xs, 1)), -np.inf) - (k - 1) * lnb
    w = np.exp(np.minimum(lw, 700.0))
    w[0] = mode * math.exp(-(k - 1) * lnb)
    lead = RNG.integers(1, X + 1, size=samples)
    rest = RNG.integers(0, X + 1, size=(samples, k - 1))
    f = w[lead] + w[rest].sum(axis=1)
    p = np.count_nonzero((f >= 1.0) & (f < b)) / samples
    return p * (X / (b - 1)) * ((X + 1) / b) ** (k - 1)


def threshold(b):
    """Smallest J that counts as an exception in base b."""
    return math.floor(math.log(b) + 2) + 1


def bulk_tail(b, j0):
    return sum(LIMIT.get(j, 0.0) for j in range(j0, min(60, b - 10) + 1))


if __name__ == '__main__':
    # 1. check the bulk law against the sampled model at moderate J
    for b, j in ((40, 6), (40, 9), (100, 7), (100, 10)):
        print(f"base {b}, J = {j}: sampled model {short_e(b, b - j, samples=200000):.2e}, limit law {LIMIT[j]:.2e}")

    # 2. observed exceptions, with the region where the data are complete
    obs = sorted({(b, len(t)) for m, b, t in everything()
                  if m == 1 and len(t) >= 3 and b - len(t) > math.log(b) + 2})
    print("observed exceptions (base, digits):", obs)

    # 3. expected exceptions in the exhaustive range, bases 10-41 and 43
    full = [b for (m, b) in exhaustive_bases() if m == 1 and b >= 10]
    e_bulk = sum(bulk_tail(b, threshold(b)) for b in full)
    e_short = sum(short_e(b, k) for b in full for k in range(3, 11) if b - k >= threshold(b))
    n_obs = sum(1 for b, k in obs if b in full)
    print(f"bases 10-43 searched in full: observed {n_obs}; model: bulk part (k > 10) {e_bulk:.2f}, k = 3..10 {e_short:.2f}")

    # 4. the model outside the data: bases 128..B for each k, and bulk beyond 43
    for B in (10**3, 10**4, 10**6):
        tail = sum(bulk_tail(b, threshold(b)) for b in range(44, min(B, 10**5) + 1))
        if B > 10**5:
            tail += sum(math.exp(1 - threshold(b)) for b in range(10**5 + 1, B + 1, 1)) if B <= 10**6 else 0
        print(f"bulk exceptions expected in bases 44 to {B:.0e}: {tail:.2f}")
    for k in range(7, 11):
        e = sum(short_e(b, k) for b in range(128, 2001, 1))
        print(f"k = {k}: expected solutions in bases 128-2000: {e:.2e}")
