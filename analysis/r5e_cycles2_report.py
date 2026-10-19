"""Round 5, question 73: clusters among the near-2-cycles of section 23.3.

Reads data/r5e_cycles2_hits.txt (r5e_cycles2_run.sh: bases 4 to 16, the
lines "two j n > s" of r2c_cycles2 with base and convention), checks the
summaries against data/r2c_cycles2.txt, and groups the near-2-cycle events
(j = 1..30) by the multiset c of n. A multiset counts at several j when
G(c) + j(b-1) and G(c) + j'(b-1) are both rearrangements of c, the swap
lemma again. Then the test of Table 23.3.1 with the clustered variance.
Output: data/r5e_cycles2_report.txt.
"""
import os
import re
from collections import Counter, defaultdict

from r5e_lib import cluster_stats, p_low_c, poisson_low

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'data')


def main():
    old = {}
    for line in open(os.path.join(D, 'r2c_cycles2.txt')):
        if line.startswith('summary'):
            b = int(re.search(r' b=(\d+)', line).group(1))
            m = int(re.search(r' m=(\d+)', line).group(1))
            old[b, m] = re.search(r' A=([\d,]+)', line).group(1)
    new, ev = {}, []
    for line in open(os.path.join(D, 'r5e_cycles2_hits.txt')):
        if line.startswith('summary'):
            b = int(re.search(r' b=(\d+)', line).group(1))
            m = int(re.search(r' m=(\d+)', line).group(1))
            new[b, m] = re.search(r' A=([\d,]+)', line).group(1)
        mm = re.match(r'b=(\d+) m=(\d) two (\d+) (\S+) > (\S+)', line)
        if mm:
            b, m, j = int(mm.group(1)), int(mm.group(2)), int(mm.group(3))
            n = tuple(map(int, mm.group(4).split(',')))
            ev.append((b, m, j, n))
    agree = sum(1 for k in new if old.get(k) == new[k])
    out = ["# r5e_cycles2_report.py: near-2-cycles, bases 4 to 16, j = 1..30",
           f"# summaries equal to r2c_cycles2.txt: {agree} of {len(new)}"]
    for par, pname in ((0, 'even'), (1, 'odd')):
        for m in (0, 1):
            bases = sorted(b for (b, mm) in new if mm == m and b % 2 == par)
            sel = [e for e in ev if e[1] == m and e[0] in bases and e[2] > 0]
            st = cluster_stats([((e[0], tuple(sorted(e[3]))), e[2]) for e in sel])
            cycles = sum(int(new[b, m].split(',')[0]) // 2 for b in bases)
            T = len(sel) / 2  # in 2-cycle units: two events per 2-cycle
            lam = T / 30
            out.append(f"{pname} 0^0={m} bases {bases[0]}-{bases[-1]}: 2-cycles {cycles}, near per offset {lam:.2f}, "
                       f"events {st['n']}, shared {st['shared']:.2f}, phi {st['phi']:.2f}; "
                       f"P(N <= obs) fixed {poisson_low(cycles, lam):.3f}, "
                       f"clustered {p_low_c(cycles, T, 30, st['phi'] / 2):.3f}")
    with open(os.path.join(D, 'r5e_cycles2_report.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
