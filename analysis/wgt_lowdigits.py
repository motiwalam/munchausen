"""The refined model with the last K digits of the sum computed exactly.

The model treats every digit of S(c) as random. But S(c) mod b^K is a fixed
function of c, and for x! it depends only on the small digits, because b^K
divides x! for every x above a small bound. This script keeps the top d-K
digits random and the bottom K digits exact. A multiset c then reproduces
itself with probability

    1[hist(low) <= c] * P_{d-K}(c - hist(low)),

against P_d(c) in the model, so each sampled c gets the weight
R(c) = b^K (d-K)! / d! * prod_x c_x! / (c_x - h_x)!. K = 0 is the refined
model itself.

    python3 wgt_lowdigits.py b0 b1 [--factorial | --shift t] > data/wgt_lowdigits_<name>.txt
"""
import sys
import numpy as np
from wgt_model import weights, max_len

b0, b1 = int(sys.argv[1]), int(sys.argv[2])
kw = {}
if '--factorial' in sys.argv:
    kw['factorial'] = True
if '--shift' in sys.argv:
    kw['shift'] = int(sys.argv[sys.argv.index('--shift') + 1])
KS = (0, 1, 2, 3)
SAMPLES = 100_000
rng = np.random.default_rng(5)


def ref_len(b, w):
    if kw.get('factorial'):
        n, k = w[b - 1], 0
        while n:
            n //= b
            k += 1
        return k
    return b + kw.get('shift', 0)


print(f"# weights {kw or 'x^x'}; bulk lengths d >= ref-5; expected solutions with the last K digits exact")
print("# base mode " + " ".join(f"K={k}" for k in KS))
tot = {(m, k): 0.0 for m in (0, 1) for k in KS}
for b in range(b0, b1 + 1):
    w, zw = weights(b, **kw)
    q = b - 1
    r = ref_len(b, w)
    row = {(m, k): 0.0 for m in (0, 1) for k in KS}
    for d in range(max(2, r - 5), max_len(b, w, zw[1]) + 1):
        scale = float(b) ** (d - 1)
        counts = rng.multinomial(d - 1, np.full(b, 1.0 / b), size=SAMPLES)
        lead = rng.integers(1, b, size=SAMPLES)
        counts[np.arange(SAMPLES), lead] += 1
        for m in (0, 1):
            z = zw[m]
            wf = np.array([z / scale] + [w[x] / scale for x in range(1, b)])
            f = counts @ wf
            u = np.array([(z if x == 0 else w[x] - x) % q for x in range(b)], dtype=np.int64)
            ok = (f >= 1.0) & (f < b) & ((counts @ u) % q == 0)
            idx = np.nonzero(ok)[0]
            if len(idx) == 0:
                continue
            c = counts[idx]
            for k in KS:
                if k == 0:
                    row[m, k] += q * len(idx) / SAMPLES
                    continue
                if d - k < 1:
                    continue
                mod = b ** k
                wm = np.array([z % mod] + [w[x] % mod for x in range(1, b)], dtype=np.int64)
                low = (c @ wm) % mod
                h = np.zeros_like(c)
                v = low.copy()
                for _ in range(k):
                    h[np.arange(len(v)), v % b] += 1
                    v //= b
                rem = c - h
                good = (rem >= 0).all(axis=1)
                # R = b^k (d-k)!/d! * prod c_x!/(c_x - h_x)!
                lr = np.zeros(len(c))
                cc = c.astype(float)
                hh = h.astype(float)
                # log of prod c!/(c-h)!, h_x <= k
                for t in range(k):
                    lr += np.where(hh > t, np.log(np.maximum(cc - t, 1.0)), 0.0).sum(axis=1)
                lr += k * np.log(b) - sum(np.log(d - j) for j in range(k))
                row[m, k] += q * float(np.sum(np.where(good, np.exp(lr), 0.0))) / SAMPLES
    for m in (0, 1):
        print(f"{b} {m} " + " ".join(f"{row[m, k]:.4f}" for k in KS), flush=True)
        for k in KS:
            tot[m, k] += row[m, k]
for m in (0, 1):
    print(f"# total mode {m}: " + " ".join(f"K={k} {tot[m, k]:.2f}" for k in KS))
