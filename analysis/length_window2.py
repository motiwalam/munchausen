"""Exceptions to the length window: sampled model against data, by region."""
import math
from collections import Counter
from catalog import everything
from length_window import short_e, threshold

obs = Counter()
for m, b, t in everything():
    if m == 1 and len(t) >= 3 and b - len(t) >= threshold(b):
        obs[(b, len(t))] += 1

def region(bases, kmax_of_b, samples):
    e = Counter()
    for b in bases:
        for k in range(3, min(b - threshold(b), kmax_of_b(b)) + 1):
            e['k=3-5' if k <= 5 else ('k=6-10' if k <= 10 else 'k>10')] += short_e(b, k, samples=samples)
    return e

full = list(range(10, 42)) + [43]
e1 = region(full, lambda b: b, 20000)
o1 = Counter('k=3-5' if k <= 5 else ('k=6-10' if k <= 10 else 'k>10') for (b, k) in obs.elements() if b in full)
print("bases 10-41 and 43, all lengths:")
for key in ('k=3-5', 'k=6-10', 'k>10'):
    print(f"  {key:7s} expected {e1[key]:.2f}  observed {o1[key]}")
e2 = region(range(44, 128), lambda b: 30, 5000)
o2 = Counter('k=3-5' if k <= 5 else ('k=6-10' if k <= 10 else 'k>10') for (b, k) in obs.elements() if 44 <= b <= 127 and k <= 30)
print("bases 44-127, at most 30 digits:")
for key in ('k=3-5', 'k=6-10', 'k>10'):
    print(f"  {key:7s} expected {e2[key]:.2f}  observed {o2[key]}")
e3 = sum(short_e(b, k, samples=4000) for b in range(128, 5001) for k in (3, 4, 5))
o3 = sum(1 for (b, k) in obs.elements() if 128 <= b <= 5000 and k <= 5)
print(f"bases 128-5000, 3 to 5 digits: expected {e3:.3f}  observed {o3}")
