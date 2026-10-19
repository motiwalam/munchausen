"""Search paths of the real solutions, in the format of r5p_trace.py.

    python3 r5p_real.py > data/r5p_trace_real.txt

Every nontrivial solution of the exhaustive bases 10 to 41 and 43 (both
conventions, each digit string once). Each line starts with the base.
"""
import os

from catalog import exhaustive_bases, _load_lines, ROOT
from r5p_trace import trace

sols = exhaustive_bases()
for m in (0, 1):
    for mm, b, t in _load_lines(os.path.join(ROOT, 'output', f'b43-{m}.txt')):
        sols.setdefault((mm, b), set()).add(t)
seen = set()
for (m, b), ts in sorted(sols.items()):
    if b < 10:
        continue
    for t in sorted(ts):
        if (b, t) in seen or len(t) < 3:
            continue
        seen.add((b, t))
        kmax, recs = trace(b, list(t))
        print(f"{b} {len(t)} {kmax} 1 " + " ".join(f"{k},{pp},{rf},{ln:.6f}" for k, pp, rf, ln in recs))
