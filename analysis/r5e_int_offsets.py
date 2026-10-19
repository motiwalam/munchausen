"""Round 5, question 73: integer near-solutions with their digit strings.

    python3 r5e_int_offsets.py OUT FAMILY b0 b1 J [threads] [extra fast flags...]

For each base b0..b1 and k in the offset family, run
`fast search b --offset (b-1) k --min-digits b-6` (or the factorion bulk
length with --factorial) and append one line per near-solution:

    hit b m k digits

and one line "done b k" per offset, so a rerun resumes. FAMILY is
    std    k = 2 j, j = 0..J               (section 11.1, class 0 mod 2(b-1))
    free   k from r5e_lib.swap_free_ks(b, J) (no two offsets a transposition apart)
    fb1    k = j, j = 0..J                 (factorions, section 17.4)
The flag --odd (not passed to fast) visits every second base from b0.
The value k = 0 is D = 0, the solutions themselves.
"""
import math
import os
import re
import subprocess
import sys

from r5e_lib import swap_free_ks

FAST = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../fast/target/release/fast')


def fact_ref_len(b):
    n, k = math.factorial(b - 1), 0
    while n:
        n //= b
        k += 1
    return k


def ks(family, b, J):
    if family == 'std':
        return [2 * j for j in range(J + 1)]
    if family == 'free':
        return swap_free_ks(b, J + 1, even=True)
    if family == 'fb1':
        return list(range(J + 1))
    raise SystemExit(f"unknown family {family}")


def main():
    out, family, b0, b1, J = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:6])
    threads = sys.argv[6] if len(sys.argv) > 6 else '1'
    extra = sys.argv[7:]
    step = 1
    if '--odd' in extra:
        extra.remove('--odd')
        step = 2
    done = set()
    if os.path.exists(out):
        for line in open(out):
            p = line.split()
            if p and p[0] == 'done':
                done.add((int(p[1]), int(p[2])))
    with open(out, 'a') as f:
        if not done:
            f.write(f"# r5e_int_offsets {family} bases {b0}-{b1} J={J} flags {' '.join(extra)}\n")
        for b in range(b0, b1 + 1, step):
            dmin = fact_ref_len(b) - 5 if '--factorial' in extra else b - 6
            for k in ks(family, b, J):
                if (b, k) in done:
                    continue
                D = (b - 1) * k
                res = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', threads,
                                      '--offset', str(D), '--min-digits', str(dmin), *extra],
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
