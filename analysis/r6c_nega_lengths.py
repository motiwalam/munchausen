"""Question 110: the two offset families of section 23.2, split by length.

    python3 r6c_nega_lengths.py run OUT     # bases -10 to -27, both families
    python3 r6c_nega_lengths.py report OUT

Reruns the counts of r2c_nega_offsets.py (`worlds lanes -b powm --offset D
--dmin 3`, D = j step and j step b, j = 1..20) and keeps the number of
near-solutions per length d. Lines "len b m family j d count".
"""
import os
import re
import subprocess
import sys
from collections import defaultdict

BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../fast/target/release/worlds")
J = 20


def run(out):
    done = set()
    if os.path.exists(out):
        for line in open(out):
            f = line.split()
            done.add((int(f[1]), int(f[2]), f[3], int(f[4])))
    env = dict(os.environ, RAYON_NUM_THREADS="1")
    with open(out, "a") as fh:
        for b in range(10, 28):
            step = b + 1 if b % 2 else 2 * (b + 1)
            for m in (0, 1):
                for fam, mult in (("step", 1), ("stepb", b)):
                    for j in range(1, J + 1):
                        if (b, m, fam, j) in done:
                            continue
                        off = j * step * mult
                        res = subprocess.run([BIN, "lanes", f"-{b}", f"pow{m}", "--offset", str(off), "--dmin", "3"],
                                             capture_output=True, text=True, check=True, env=env)
                        text = res.stdout + res.stderr
                        rows = re.findall(r"^len base -\d+ w pow\d d (\d+) sols (\d+)", text, re.M)
                        for d, n in rows:
                            fh.write(f"len {b} {m} {fam} {j} {d} {n}\n")
                        if not rows:
                            fh.write(f"len {b} {m} {fam} {j} 0 0\n")
                        fh.flush()


def report(out):
    tot = defaultdict(int)
    for line in open(out):
        _, b, m, fam, j, d, n = line.split()
        b, m, d, n = int(b), int(m), int(d), int(n)
        grp = "mult3" if b % 3 == 0 else "other"
        j_from_top = b + 1 - d
        cls = "d >= b-3" if j_from_top <= 4 else ("b-9 <= d < b-3" if j_from_top <= 10 else "d < b-9")
        tot[(grp, m, cls, fam)] += n
        tot[(grp, m, "all", fam)] += n
    for grp in ("other", "mult3"):
        for m in (0, 1):
            for cls in ("all", "d >= b-3", "b-9 <= d < b-3", "d < b-9"):
                s, sb = tot[(grp, m, cls, "step")], tot[(grp, m, cls, "stepb")]
                r = sb / s if s else float("nan")
                print(f"{grp} m {m} {cls:16s} step {s:4d} stepb {sb:4d} ratio {r:.3f}")


if __name__ == "__main__":
    (run if sys.argv[1] == "run" else report)(sys.argv[2])
