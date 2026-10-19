"""Round 5, question 73: negative-base near-solutions with their strings.

    python3 r5e_nega_offsets.py OUT BMIN BMAX J

The offsets of r2c_nega_offsets.py (section 23.2): for base -b, step = b+1
(2(b+1) for even b), families j step and j step b, j = 1..J, at least 3
digits, `worlds lanes`. Lines "hit b m family j digits" and
"done b m family j count"; a rerun skips the finished offsets.
"""
import os
import subprocess
import sys

BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../fast/target/release/worlds")


def hits(b, m, off):
    env = dict(os.environ, RAYON_NUM_THREADS="1")
    out = subprocess.run(["nice", "-n", "10", BIN, "lanes", f"-{b}", f"pow{m}", "--offset", str(off), "--dmin", "3"],
                         capture_output=True, text=True, check=True, env=env).stdout
    return [line.split()[-1] for line in out.splitlines() if line.startswith("sol ")]


def main():
    out, bmin, bmax, J = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    done = set()
    if os.path.exists(out):
        for line in open(out):
            p = line.split()
            if p and p[0] == "done":
                done.add((int(p[1]), int(p[2]), p[3], int(p[4])))
    with open(out, "a") as f:
        for b in range(bmin, bmax + 1):
            step = (b + 1) * (1 if b % 2 == 1 else 2)
            for m in (0, 1):
                for fam, mult in (("step", step), ("stepb", step * b)):
                    for j in range(1, J + 1):
                        if (b, m, fam, j) in done:
                            continue
                        hs = hits(b, m, j * mult)
                        for s in hs:
                            f.write(f"hit {b} {m} {fam} {j} {s}\n")
                        f.write(f"done {b} {m} {fam} {j} {len(hs)}\n")
                        f.flush()


if __name__ == "__main__":
    main()
