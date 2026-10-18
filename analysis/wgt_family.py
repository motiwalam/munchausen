"""Questions 9 and 10: solutions and model for one weight family.

    python3 wgt_family.py b0 b1 [engine flags] > data/wgt_<name>.txt

The flags are those of `fast search` (--zero m, --shift t, --factorial). For
every base the script prints, per convention, the nontrivial solutions (at
least 2 digits) by length and the model's expectation by length. Lines:

    raw  b mode solutions
    sol  b mode d count
    exp  b mode d basic refined
    time b seconds nodes
"""
import sys
import time
from collections import Counter
from wgt_model import weights, model_counts, run_fast

b0, b1 = int(sys.argv[1]), int(sys.argv[2])
flags = sys.argv[3:]
kw = {}
i = 0
while i < len(flags):
    f = flags[i]
    if f == '--factorial':
        kw['factorial'] = True
    elif f == '--zero':
        i += 1
        kw['zero'] = int(flags[i])
    elif f == '--shift':
        i += 1
        kw['shift'] = int(flags[i])
    else:
        sys.exit(f"unknown flag {f}")
    i += 1

print(f"# flags {' '.join(flags) or '(none)'}, bases {b0}-{b1}")
for b in range(b0, b1 + 1):
    t = time.time()
    res, err = run_fast(b, b, flags)
    secs = time.time() - t
    nodes = [ln.split()[2] for ln in err.splitlines() if 'nodes' in ln][0]
    print(f"time {b} {secs:.2f} {nodes}")
    w, zw = weights(b, **kw)
    mc = model_counts(b, w, zw, samples=60_000)
    for mode in (0, 1):
        print(f"raw {b} {mode} " + " ".join(",".join(map(str, s)) for s in res[b, mode]))
        for d, c in sorted(Counter(len(s) for s in res[b, mode] if len(s) >= 2).items()):
            print(f"sol {b} {mode} {d} {c}")
        for d, v in mc.items():
            if v[0] > 0 or v[1 + mode] > 0:
                print(f"exp {b} {mode} {d} {v[0]:.5f} {v[1 + mode]:.5f}")
    sys.stdout.flush()
