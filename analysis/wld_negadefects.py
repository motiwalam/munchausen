"""The defect spectrum of section 11.1 for negative bases.

For base -b and an offset D > 0, count the n with n = F(n) + D and at least 3
digits (`worlds tree -b powM --offset D`). By the identity of the draft
(n == digit sum mod b+1), the offsets in the class of 0 are the multiples of
b+1. In an even base the step is 2(b+1), so that D also has the parity of 0:
n == s_0 (mod 2) ties the parity of n - F(n) to the last digit. Each such offset is
another draw of the coincidence that makes a solution, so the mean count over
offsets estimates the base's own expected number of solutions, lambda(b).

usage: python3 wld_negadefects.py BMIN BMAX J   (offsets j * step, j = 1..J)
"""
import subprocess
import sys

BIN = "../fast/target/release/worlds"


def count(b, m, off):
    out = subprocess.run([BIN, "tree", f"-{b}", f"pow{m}", "--offset", str(off), "--dmin", "3"],
                         capture_output=True, text=True, check=True).stdout
    return sum(1 for line in out.splitlines() if line.startswith("sol "))


def main():
    bmin, bmax, J = map(int, sys.argv[1:4])
    print("# base m step offsets mean variance counts")
    for b in range(bmin, bmax + 1):
        step = (b + 1) * (1 if b % 2 == 1 else 2)
        for m in (1, 0):
            cs = [count(b, m, j * step) for j in range(1, J + 1)]
            mean = sum(cs) / J
            var = sum((c - mean) ** 2 for c in cs) / (J - 1)
            print(f"{b} {m} {step} {J} {mean:.3f} {var:.3f} {' '.join(map(str, cs))}", flush=True)


if __name__ == "__main__":
    main()
