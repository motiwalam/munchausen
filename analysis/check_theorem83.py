"""Numerical check of Theorem 8.3 for k = 3, 4, 5.

Leading digit x with x^(x-1) a perfect (k-1)-th power (here: (k-1) | (x-1)),
lower digits all at most B. The theorem says that for large x the only
solutions are the self-paying family under 0^0 = 0, and none under 0^0 = 1.
"""
import itertools
import sys

from kdigit import base_for

B, XMAX = int(sys.argv[1]), int(sys.argv[2])
for k in (3, 4, 5):
    found = []
    for x in range(2, XMAX + 1):
        if (x - 1) % (k - 1):
            continue
        for low in itertools.product(range(B + 1), repeat=k - 1):
            s = (x,) + low
            for mode in (0, 1):
                f = sum((mode if d == 0 else d ** d) for d in s)
                b = base_for(s, f)
                if b is not None:
                    found.append((mode, s, b))
    family = [f for f in found if f[0] == 0 and all(d == 0 for d in f[1][1:-1]) and f[1][-1] in (0, 1)]
    other = [(m, s, b if b < 10**12 else '~10^%d' % (len(str(b)) - 1)) for m, s, b in found if (m, s, b) not in family]
    print(f"k={k}, (k-1)|(x-1), x <= {XMAX}, lower digits <= {B}: {len(family)} self-paying family members, others: {other}")
