"""Round 5, question 73: clusters among the near-factorions and the P values
of sections 17.4, 19.5 and 23.1.3.

Families (offsets D = j M, j = 1..30, at least L(b) - 5 digits):
    b1    M = b-1          data/r5e_fact_b1.txt (r5e_int_offsets.py fb1, odd bases)
    bb1   M = b(b-1)       data/r2c_fact_offsets_bb1.txt
    b2b1  M = b^2(b-1)     data/r2c_fact_offsets_b2b1.txt
    b3b1  M = b^3(b-1)     data/r2c_fact_offsets_b3b1.txt
    lcm   M = b^2 lcm(1..b+1)  data/r2c_fact_offsets_lcm.txt
Clusters: same multiset, or twins at one offset (last digits 0, 1, 2 under
w(0) = 0 and 1, 2 under w(0) = 1). N_0 per base from
data/r2c_qw_factorial.txt. Output: data/r5e_fact_report.txt.
"""
import math
import os
import statistics
from collections import Counter

from r5e_cluster import clusters, load_fact, load_r5e, twins_fact
from r5e_lib import clump_sizes, cluster_stats, p_low_c, poisson_low, rank_p_low

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'data')
ODD = list(range(15, 36, 2))


def ref_len(b):
    n, k = math.factorial(b - 1), 0
    while n:
        n //= b
        k += 1
    return k


def solutions():
    n0 = Counter()
    for line in open(os.path.join(D, 'r2c_qw_factorial.txt')):
        p = line.split()
        if p and p[0] == 'raw':
            b, m = int(p[1]), int(p[2])
            for s in p[5:]:
                if s.count(',') + 1 >= ref_len(b) - 5:
                    n0[b, m] += 1
    return n0


def family(name):
    if name == 'b1':
        ev, done = load_r5e(os.path.join(D, 'r5e_fact_b1.txt'))
        ev = [e for e in ev if e[2] > 0]
        done = {b: {k for k in ks if k > 0} for b, ks in done.items()}
    else:
        ev, done = load_fact(os.path.join(D, f'r2c_fact_offsets_{name}.txt'))
    return ev, done


def main():
    n0 = solutions()
    out = ["# r5e_fact_report.py: near-factorions, odd bases 15 to 35 unless stated"]
    out.append("# family m | bases | N_0 | T | mean | shared | phi | psi | J_eff | var/mean of totals | "
               "P(N_0 <= obs): fixed, independent, clustered, rank | min and max offset total")
    for name in ('b1', 'bb1', 'b2b1', 'b3b1', 'lcm'):
        ev, done = family(name)
        cid = clusters(ev, twins_fact)
        for m in (0, 1):
            bases = [b for b in ODD if b in done and len(done[b]) == 30]
            if name == 'lcm':
                bases = [b for b in bases if b >= 21]
            if not bases:
                continue
            sel = [(c, e) for c, e in zip(cid, ev) if e[1] == m and e[0] in bases]
            st = cluster_stats([(c, e[2]) for c, e in sel])
            sizes = clump_sizes([(c, e[2]) for c, e in sel])
            T = len(sel)
            J = 30
            per = Counter(e[2] for _, e in sel)
            totals = [per[j] for j in range(1, 31)]
            vm = statistics.variance(totals) / statistics.mean(totals)
            obs = sum(n0[b, m] for b in bases)
            lam = T / J
            out.append(f"{name} {m} | {bases[0]}-{bases[-1]} | {obs} | {T} | {lam:.2f} | {st['shared']:.2f} | "
                       f"{st['phi']:.2f} | {st['psi']:.2f} | {J * st['psi'] / st['phi']:.1f} | {vm:.2f} | "
                       f"{poisson_low(obs, lam):.4f}, {p_low_c(obs, T, J):.4f}, "
                       f"{p_low_c(obs, T, J, st['phi'], sizes):.4f}, {rank_p_low(obs, totals):.4f} | "
                       f"{min(totals)}, {max(totals)}")
    with open(os.path.join(D, 'r5e_fact_report.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
