"""Question 93: near-solutions at the shifted offsets D = 2j(b-1) + c.

    python3 r6q_offsets.py OUT c b0 b1 J [threads] [extra fast flags...]

Runs `fast search b --offset 2j(b-1)+c --min-digits b-6` for j = 1..J and
appends "hit b m k digits" lines in the format of r5e_int_offsets.py, with
k = 2j (so D = k(b-1) + c), and "done b k" per offset, so a rerun resumes.
A near-solution under 0^0 = 1 at D with c zeros is a near-solution under
0^0 = 0 at D + c with c zeros (F_1 = F_0 + c_0).
"""
import os
import re
import subprocess
import sys

FAST = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../fast/target/release/fast')


def main():
    out, c, b0, b1, J = sys.argv[1], *map(int, sys.argv[2:6])
    threads = sys.argv[6] if len(sys.argv) > 6 else '1'
    extra = sys.argv[7:]
    done = set()
    if os.path.exists(out):
        for line in open(out):
            p = line.split()
            if p and p[0] == 'done':
                done.add((int(p[1]), int(p[2])))
    with open(out, 'a') as f:
        if not done:
            f.write(f"# r6q_offsets c={c} bases {b0}-{b1} J={J} flags {' '.join(extra)}\n")
        for b in range(b0, b1 + 1):
            for j in range(1, J + 1):
                k = 2 * j
                if (b, k) in done:
                    continue
                D = (b - 1) * k + c
                res = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', threads,
                                      '--offset', str(D), '--min-digits', str(b - 6), *extra],
                                     capture_output=True, text=True, check=True).stdout
                for line in res.splitlines():
                    _, m, _, sols = line.split(':', 3)
                    for s in re.findall(r'\(([^)]*)\)', sols):
                        if s.count(',') >= 1:
                            f.write(f"hit {b} {m} {k} {s}\n")
                f.write(f"done {b} {k}\n")
                f.flush()


if __name__ == '__main__':
    main()
