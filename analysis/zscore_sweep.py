"""Speed and misses of the typical-set rule (--zscore) and of combinations.

Usage: zscore_sweep.py first_base last_base last_miss_base 'opts' ['opts' ...]
"""
import sys
from inexact_sweep import sweep

b0, b1, bm = map(int, sys.argv[1:4])
for opts in sys.argv[4:]:
    g, last, missed, total, reported = sweep(opts.split(), range(b0, b1 + 1), range(10, bm + 1))
    print(f"{opts:32s} growth {g:.3f}  nodes at {b1}: {last:.3g}  missed {missed}/{total} in bases 10-{bm}", flush=True)
