"""Round 5, question 73: clusters among the negative-base near-solutions and
the P values of section 23.2.

Reads data/r5e_nega_offsets.txt (r5e_nega_offsets.py, bases -10 to -24,
families j step and j step b, j = 1..20, at least 3 digits), checks the
counts against data/r2c_nega_offsets.txt, groups the events by multiset
and twins (one cluster may reach both families), and redoes the tests of
section 23.2 with the clustered variance. The design effects of bases -10
to -24 stand in for -25 to -27, whose counts come from r2c_nega_offsets.txt.
Output: data/r5e_nega_report.txt.
"""
import math
import os
from collections import Counter, defaultdict

import r2c_nega_compare as R
from r5e_cluster import UF
from r5e_lib import clump_sizes, cluster_stats, p_low_c, poisson_low

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'data')
J = 20


def load():
    ev = []
    cnt = {}
    for line in open(os.path.join(D, 'r5e_nega_offsets.txt')):
        p = line.split()
        if p[0] == 'hit':
            ev.append((int(p[1]), int(p[2]), p[3], int(p[4]), tuple(map(int, p[5].split(',')))))
        elif p[0] == 'done':
            cnt[int(p[1]), int(p[2]), p[3], int(p[4])] = int(p[5])
    old = {}
    for line in open(os.path.join(D, 'r2c_nega_offsets.txt')):
        p = line.split()
        if p and p[0] == 'off':
            old[int(p[1]), int(p[2]), p[3], int(p[4])] = int(p[5])
    return ev, cnt, old


def cluster(ev):
    uf = UF(len(ev))
    seen, pre = {}, {}
    for i, (b, m, fam, j, s) in enumerate(ev):
        key = (b, m, tuple(sorted(s)))
        if key in seen:
            uf.union(i, seen[key])
        else:
            seen[key] = i
        if m == 0 and s[-1] in (0, 1):
            k = (b, m, fam, j, s[:-1])
            if k in pre:
                uf.union(i, pre[k])
            else:
                pre[k] = i
    return [uf.find(i) for i in range(len(ev))]


def main():
    ev, cnt, old = load()
    bad = [k for k, v in cnt.items() if old.get(k) != v]
    out = ["# r5e_nega_report.py: negative bases, offsets j step and j step b, j = 1..20",
           f"# counts checked against r2c_nega_offsets.txt: {len(cnt)} offsets, {len(bad)} differ"]
    cid = cluster(ev)
    _, sols = R.load_census()
    groups = {'multiples of 3': lambda b: b % 3 == 0, 'others': lambda b: b % 3 != 0, 'all': lambda b: True}
    stat = {}
    for gname, gsel in groups.items():
        for m in (0, 1):
            for fam in ('step', 'stepb'):
                sel = [(c, e) for c, e in zip(cid, ev) if e[1] == m and e[2] == fam and gsel(e[0])]
                st = cluster_stats([(c, e[3]) for c, e in sel])
                stat[gname, m, fam] = (st, clump_sizes([(c, e[3]) for c, e in sel]))
                out.append(f"{gname} m={m} {fam}: events {st['n']}, shared {st['shared']:.2f}, phi {st['phi']:.2f}, "
                           f"psi {st['psi']:.2f}, J_eff {J * st['psi'] / st['phi']:.1f}")
            # the two families together: covariance of their means
            both = [(c, e) for c, e in zip(cid, ev) if e[1] == m and gsel(e[0])]
            k = defaultdict(lambda: [0, 0])
            for c, e in both:
                k[c][e[2] == 'stepb'] += 1
            vs = sum(a * a for a, _ in k.values())
            vb = sum(b_ * b_ for _, b_ in k.values())
            cv = sum(a * b_ for a, b_ in k.values())
            ts = sum(a for a, _ in k.values())
            tb = sum(b_ for _, b_ in k.values())
            dn = (ts - tb) / J
            se_naive = math.sqrt(ts + tb) / J
            se_cl = math.sqrt(vs + vb - 2 * cv) / J
            out.append(f"{gname} m={m}: step {ts / J:.2f} vs stepb {tb / J:.2f} (bases -10 to -24), difference "
                       f"{dn:.2f}, z naive {dn / se_naive:.2f}, clustered {dn / se_cl:.2f}")
    # D = 0 against the family j step b, bases -10 to -27 as in section 23.2
    for gname, gsel in groups.items():
        for m in (0, 1):
            bases = [b for b in range(10, 28) if gsel(b)]
            n0 = sum(len(sols[(b, m)]) for b in bases)
            T = sum(old[b, m, 'stepb', j] for b in bases for j in range(1, J + 1))
            st, sizes = stat[gname, m, 'stepb']
            out.append(f"D=0 vs j step b, {gname}, m={m}, bases -10 to -27: N_0 {n0}, mean {T / J:.2f}; "
                       f"P(N <= N_0) fixed {poisson_low(n0, T / J):.3f}, independent {p_low_c(n0, T, J):.3f}, "
                       f"clustered {p_low_c(n0, T, J, st['phi'], sizes):.3f}")
        n0 = sum(len(sols[(b, m)]) for b in range(10, 28) for m in (0, 1) if gsel(b))
        T = sum(old[b, m, 'stepb', j] for b in range(10, 28) for m in (0, 1) if gsel(b) for j in range(1, J + 1))
        st0, s0 = stat[gname, 0, 'stepb']
        st1, s1 = stat[gname, 1, 'stepb']
        phi = (st0['phi'] * st0['n'] + st1['phi'] * st1['n']) / (st0['n'] + st1['n'])
        sizes = Counter()
        for s, st in ((s0, st0), (s1, st1)):
            for k_, v in s.items():
                sizes[k_] += v * st['n']
        tot = sum(sizes.values())
        sizes = {k_: v / tot for k_, v in sizes.items()}
        out.append(f"D=0 vs j step b, {gname}, both conventions: N_0 {n0}, mean {T / J:.2f}; "
                   f"P fixed {poisson_low(n0, T / J):.3f}, clustered {p_low_c(n0, T, J, phi, sizes):.3f}")
    with open(os.path.join(D, 'r5e_nega_report.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
