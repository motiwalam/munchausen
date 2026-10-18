"""Question 42: defect spectra of negative bases with offsets that keep n mod b.

    python3 r2c_nega_offsets.py OUT BMIN BMAX J

For base -b the class of 0 is the multiples of step = (b+1), or 2(b+1) for
even b (wld_negadefects.py). Those offsets change n - F(n) mod b, and so the
residue mod 3 of the last digit when 3 | b. Here every base gets two
families, j * step and j * step * b for j = 1..J, and the script counts the
n with n = F(n) + D and at least 3 digits (`worlds lanes`). Lines
"off b m family j count" are appended to OUT; a rerun skips those present.
"""
import os
import subprocess
import sys

BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "../fast/target/release/worlds")


def count(b, m, off):
    env = dict(os.environ, RAYON_NUM_THREADS="1")
    out = subprocess.run(["nice", "-n", "10", BIN, "lanes", f"-{b}", f"pow{m}", "--offset", str(off), "--dmin", "3"],
                         capture_output=True, text=True, check=True, env=env).stdout
    return sum(1 for line in out.splitlines() if line.startswith("sol "))


def main():
    out, bmin, bmax, J = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    done = set()
    if os.path.exists(out):
        for line in open(out):
            p = line.split()
            if p and p[0] == "off":
                done.add((int(p[1]), int(p[2]), p[3], int(p[4])))
    with open(out, "a") as f:
        for b in range(bmin, bmax + 1):
            step = (b + 1) * (1 if b % 2 == 1 else 2)
            for m in (0, 1):
                for fam, mult in (("step", step), ("stepb", step * b)):
                    for j in range(1, J + 1):
                        if (b, m, fam, j) in done:
                            continue
                        f.write(f"off {b} {m} {fam} {j} {count(b, m, j * mult)}\n")
                        f.flush()


if __name__ == "__main__":
    main()
