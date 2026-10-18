"""Question 41: near-factorions at offsets that keep more residues of D = 0.

    python3 r2c_fact_offsets.py OUT b0 b1 J MULT [threads]

For each base b in b0..b1 and j = 1..J, count the n with n = F(n) + D,
F = sum of x! over the base-b digits, D = j * MULT(b), and at least L(b) - 5
digits, where L(b) is the length of (b-1)!. MULT is one of
    b1     D = j (b-1)          residue 0 mod b-1 only (as in wgt_offsets.py)
    bb1    D = j b (b-1)        residues 0 mod b-1 and mod b
    b2b1   D = j b^2 (b-1)      residues 0 mod b-1 and mod b^2
The engine is fast search --factorial of branch q-weights (commit 2e67477),
built in fast/target/qweights. Lines "off b j mode count" are appended to
OUT; a rerun skips the (b, j) already in OUT, so the run can resume.
"""
import math
import os
import re
import subprocess
import sys

FAST = os.path.join(os.path.dirname(__file__), '../fast/target/qweights/fast/target/release/fast')


def ref_len(b):
    n, k = math.factorial(b - 1), 0
    while n:
        n //= b
        k += 1
    return k


def mult(kind, b):
    return {'b1': b - 1, 'bb1': b * (b - 1), 'b2b1': b * b * (b - 1)}[kind]


def run(b, D, dmin, threads):
    p = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', str(threads), '--factorial',
                        '--offset', str(D), '--min-digits', str(dmin)],
                       capture_output=True, text=True, check=True)
    res = {}
    for line in p.stdout.splitlines():
        bb, mode, _, sols = line.split(':', 3)
        res[int(mode)] = [s for s in re.findall(r'\(([^)]*)\)', sols) if s.count(',') >= 1]
    return res


def main():
    out, b0, b1, J, kind = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    threads = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    done = set()
    if os.path.exists(out):
        for line in open(out):
            p = line.split()
            if p and p[0] == 'off':
                done.add((int(p[1]), int(p[2])))
    else:
        with open(out, 'w') as f:
            f.write(f"# factorions, offsets D = j * {kind}, j = 1..{J}, bases {b0}-{b1}, d >= L(b)-5\n")
    with open(out, 'a') as f:
        for b in range(b0, b1 + 1):
            for j in range(1, J + 1):
                if (b, j) in done:
                    continue
                res = run(b, j * mult(kind, b), max(2, ref_len(b) - 5), threads)
                for mode in (0, 1):
                    f.write(f"off {b} {j} {mode} {len(res.get(mode, []))} {' '.join(res.get(mode, []))}\n")
                f.flush()


if __name__ == '__main__':
    main()
