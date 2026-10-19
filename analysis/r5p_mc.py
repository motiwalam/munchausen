"""Check the null laws of ln E against a direct multinomial simulation.

    python3 r5p_mc.py > data/r5p_mc.txt

For base 40 (kmax = 39) and a few cells (k, pp), draws 200,000 suffixes of
pp digits from the kk = 40 usable values and compares the mean and standard
deviation of ln E with the poisson and cond laws of r5p_law.py.
"""
import math

import numpy as np
from scipy.special import gammaln

from r5p_law import poisson_law, cond_law

rng = np.random.default_rng(1)
b, kmax = 40, 39
kk = kmax + 1
print("k pp | simulation mean sd | poisson mean sd | cond mean sd")
for k, pp in [(30, 25), (25, 22), (20, 18), (15, 12), (10, 8), (6, 4)]:
    m = kk - k
    p = np.array([1 / kk] * m + [k / kk])
    n = rng.multinomial(pp, p, size=200_000)
    le = gammaln(pp + 1) + n[:, -1] * math.log(k) - gammaln(n[:, :-1] + 1).sum(1) - gammaln(n[:, -1] + 1) - pp * math.log(b)
    pm, ps = poisson_law(b, kmax, k, pp)
    cm, cs = cond_law(b, kmax, k, pp)
    print(f"{k} {pp} | {le.mean():.3f} {le.std():.3f} | {pm:.3f} {ps:.3f} | {cm:.3f} {cs:.3f}")
