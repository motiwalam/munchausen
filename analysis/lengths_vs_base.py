"""How the length k of a solution relates to its base b.

J = b - k is the number of digits a solution is short of b. The model says J
is small for the random-looking solutions (P(J = j) falls like e^-j), while
the algebraic families have J of the order of b.
"""
import math
from collections import Counter, defaultdict
from catalog import exhaustive_bases, everything

EX = exhaustive_bases()

# 1. distribution of J for solutions in the exhaustive range, by convention
for mode in (0, 1):
    js = Counter()
    for (m, b), ts in EX.items():
        if m != mode or b < 10:
            continue
        for t in ts:
            js[b - len(t)] += 1
    print(f"0^0={mode}, bases 10-41: J = b - k:", dict(sorted(js.items())))

# 2. J against ln b: which solutions exceed ln b + 2 (all data, k >= 3)?
for mode in (0, 1):
    big = [(b, len(t)) for m, b, t in everything() if m == mode and len(t) >= 3 and b - len(t) > math.log(b) + 2]
    print(f"0^0={mode}: solutions with k >= 3 and J > ln b + 2: {len(big)};",
          "examples:", sorted(set(big))[:12])

# 3. smallest base with a k-digit solution, per convention
first = defaultdict(dict)
for m, b, t in everything():
    k = len(t)
    first[m][k] = min(b, first[m].get(k, b))
for mode in (0, 1):
    row = {k: first[mode].get(k) for k in range(2, 41)}
    print(f"0^0={mode}: smallest base with a k-digit solution:", row)
