"""Compare the plain and the refined model with the data, split by base parity."""
import sys
from collections import defaultdict
from model import expected, expected_refined
from solutions import SOL

b0, b1 = int(sys.argv[1]), int(sys.argv[2])
jmax = 6
tot = defaultdict(float)
for b in range(b0, b1 + 1):
    for mode in (0, 1):
        par = 'odd' if b % 2 else 'even'
        for d in range(2, b + 1):
            j = b - d
            key = j if j <= jmax else 'far'
            tot[(mode, par, key, 'plain')] += expected(b, d, mode, 40_000)[0]
            tot[(mode, par, key, 'refined')] += expected_refined(b, d, mode, 200_000)[0]
        for t in SOL[mode][b]:
            j = b - len(t)
            tot[(mode, par, j if j <= jmax else 'far', 'seen')] += 1
    print('done', b, file=sys.stderr, flush=True)
for mode in (0, 1):
    for par in ('even', 'odd'):
        print(f"0^0={mode}, {par} bases {b0}-{b1}:")
        keys = list(range(jmax + 1)) + ['far']
        for key in keys:
            name = f"d=b-{key}" if key != 'far' else f"d<b-{jmax}"
            print(f"  {name:8s} plain {tot[(mode,par,key,'plain')]:6.2f}  refined {tot[(mode,par,key,'refined')]:6.2f}  seen {int(tot[(mode,par,key,'seen')])}")
        print(f"  total    plain {sum(tot[(mode,par,k,'plain')] for k in keys):6.2f}  refined {sum(tot[(mode,par,k,'refined')] for k in keys):6.2f}  seen {int(sum(tot[(mode,par,k,'seen')] for k in keys))}")
