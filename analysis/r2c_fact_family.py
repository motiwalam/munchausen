"""Question 41: factorions of one base from a journaled run, with the model.

    python3 r2c_fact_family.py B RESULT_FILE SECONDS NODES >> data/r2c_fact_47_49.txt

RESULT_FILE is the stdout of `fast search B --factorial --journal ...`
(branch q-weights engine). The script prints the lines of wgt_family.py
(branch q-weights): time, raw, sol and exp, with the refined model sampled
by wgt_model.model_counts (60,000 strings per length, as for bases 10 to 45).
"""
import os
import re
import sys
from collections import Counter

from r2c_wgt_model import weights, model_counts


def main():
    b, path, secs, nodes = int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
    res = {}
    for line in open(path):
        if not re.match(r'^\d+:\d:', line):
            continue
        bb, mode, _, sols = line.split(':', 3)
        if int(bb) == b:
            res[int(mode)] = [tuple(int(x) for x in s.split(',') if x != '') for s in re.findall(r'\(([^)]*)\)', sols)]
    print(f"# flags --factorial, bases {b}-{b}")
    print(f"time {b} {secs} {nodes}")
    w, zw = weights(b, factorial=True)
    mc = model_counts(b, w, zw, samples=60_000)
    for mode in (0, 1):
        print(f"raw {b} {mode} " + " ".join(",".join(map(str, s)) for s in res[mode]))
        for d, c in sorted(Counter(len(s) for s in res[mode] if len(s) >= 2).items()):
            print(f"sol {b} {mode} {d} {c}")
        for d, v in mc.items():
            if v[0] > 0 or v[1 + mode] > 0:
                print(f"exp {b} {mode} {d} {v[0]:.5f} {v[1 + mode]:.5f}")


if __name__ == '__main__':
    main()
