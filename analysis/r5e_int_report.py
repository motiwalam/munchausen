"""Round 5, question 73: clusters among the integer near-solutions.

Reads data/r5e_int_std.txt (D = 2j(b-1), j = 0..60) and
data/r5e_int_free.txt (offsets with no two a transposition apart), both
from r5e_int_offsets.py, numbers with at least b-6 digits. Groups the
events by multiset and twins (r5e_cluster.py), and reports per base and
per group: the share of near-solutions whose multiset recurs at another
offset, the design effects phi and psi, the variance of the per-offset
counts, the lags at which partners sit, and N_0 against the offsets with
naive and clustered P values (compound Poisson for the clumps at one
offset, gamma law with the design effect phi for the offset mean).
Output: data/r5e_int_report.txt.

    python3 r5e_int_report.py [b_max]
"""
import os
import statistics
import sys
from collections import Counter, defaultdict

from r5e_cluster import clusters, load_r5e, twins_pow
from r5e_lib import cluster_stats, p_high_c, p_low_c, poisson_high, poisson_low, rank_p_high, rank_p_low

HERE = os.path.dirname(os.path.abspath(__file__))


def lag_class(b, dk):
    """Name the move that links two events dk (b-1) apart."""
    a = abs(dk)
    if a <= b - 1:
        return 'last two digits'
    if a % b == 0 and a // b <= b - 1:
        return 'positions 1,2'
    if a % (b + 1) == 0 and a // (b + 1) <= b - 1:
        return 'positions 0,2'
    return 'other'


def analyse(path, bmax):
    ev, done = load_r5e(path)
    ev = [e for e in ev if e[0] <= bmax]
    cid = clusters(ev, twins_pow)
    out = {}
    lags = Counter()
    sol_linked = Counter()
    for b in sorted(done):
        if b > bmax:
            continue
        ks = sorted(k for k in done[b] if k > 0)
        if 0 not in done[b] or not ks:
            continue
        for m in (0, 1):
            sel = [(c, e) for c, e in zip(cid, ev) if e[0] == b and e[1] == m]
            offs = [(c, e[2]) for c, e in sel if e[2] > 0]
            st = cluster_stats(offs)
            n0 = sum(1 for c, e in sel if e[2] == 0)
            per = Counter(k for _, k in offs)
            counts = [per[k] for k in ks]
            mu = statistics.mean(counts)
            var = statistics.variance(counts) if len(counts) > 1 else 0.0
            byc = defaultdict(list)
            for c, k in offs:
                byc[c].append(k)
            for c, kl in byc.items():
                for i in range(len(kl)):
                    for j in range(i + 1, len(kl)):
                        if kl[i] != kl[j]:
                            lags[lag_class(b, kl[i] - kl[j])] += 1
            off_clusters = set(byc)
            for c, e in sel:
                if e[2] == 0:
                    sol_linked['linked' if c in off_clusters else 'alone'] += 1
            clumps = Counter(Counter(offs).values())
            out[b, m] = dict(st, n0=n0, J=len(ks), T=len(offs), mean=mu, vm=var / mu if mu else float('nan'),
                             counts=counts, clumps=clumps)
    return out, lags, sol_linked


def group_line(name, rows):
    n0 = sum(r['n0'] for r in rows)
    T = sum(r['T'] for r in rows)
    J = rows[0]['J']
    lam = T / J
    n = sum(r['n'] for r in rows)
    phi = sum(r['phi'] * r['n'] for r in rows) / n if n else 1.0
    psi = sum(r['psi'] * r['n'] for r in rows) / n if n else 1.0
    shared = sum(r['shared'] * r['n'] for r in rows) / n if n else 0.0
    totals = [sum(r['counts'][i] for r in rows) for i in range(J)]
    vm = statistics.variance(totals) / statistics.mean(totals)
    clumps = Counter()
    for r in rows:
        clumps.update(r['clumps'])
    tot = sum(clumps.values())
    sizes = {k: v / tot for k, v in clumps.items()}
    pl, ph = (p_low_c, poisson_low) if n0 < lam else (p_high_c, poisson_high)
    rk = rank_p_low(n0, totals) if n0 < lam else rank_p_high(n0, totals)
    side = '<=' if n0 < lam else '>='
    return (f"{name}: N_0 {n0}, offsets {lam:.2f} per offset (J {J}, T {T}), shared {shared:.2f}, "
            f"phi {phi:.2f}, psi {psi:.2f}, J_eff {J * psi / phi:.1f}, var/mean of offset totals {vm:.2f}; "
            f"P(N_0 {side} obs): fixed {ph(n0, lam):.3f}, independent {pl(n0, T, J):.3f}, "
            f"clustered {pl(n0, T, J, phi, sizes):.3f}, rank {rk:.3f}")


def main():
    bmax = int(sys.argv[1]) if len(sys.argv) > 1 else 99
    lines = ["# r5e_int_report.py: integer near-solutions, at least b-6 digits"]
    res = {}
    for fam in ('std', 'free'):
        path = os.path.join(HERE, 'data', f'r5e_int_{fam}.txt')
        if not os.path.exists(path):
            continue
        out, lags, sol_linked = analyse(path, bmax)
        res[fam] = out
        lines.append(f"## family {fam}")
        lines.append("# b m N_0 J T clusters shared distinct phi psi var/mean")
        for (b, m), r in sorted(out.items()):
            lines.append(f"{b} {m} {r['n0']} {r['J']} {r['T']} {r['clusters']} {r['shared']:.2f} "
                         f"{r['distinct']:.2f} {r['phi']:.2f} {r['psi']:.2f} {r['vm']:.2f}")
        tot = sum(lags.values())
        lines.append("partner pairs by move: " + ", ".join(f"{k} {v} ({v / tot:.2f})" for k, v in lags.most_common()))
        lines.append(f"solutions whose cluster reaches an offset: {sol_linked['linked']} of "
                     f"{sol_linked['linked'] + sol_linked['alone']}")
        for m in (0, 1):
            for par in (0, 1):
                rows = [r for (b, mm), r in out.items() if mm == m and b % 2 == par]
                if rows:
                    lines.append(group_line(f"{fam} 0^0={m} {'odd' if par else 'even'} bases "
                                            f"{min(b for (b, mm) in out if mm == m and b % 2 == par)}-"
                                            f"{max(b for (b, mm) in out if mm == m and b % 2 == par)}", rows))
            lines.append(group_line(f"{fam} 0^0={m} all bases", [r for (b, mm), r in out.items() if mm == m]))
    if 'std' in res and 'free' in res:
        lines.append("## std against free, mean per offset, bases in both")
        for m in (0, 1):
            common = sorted(b for (b, mm) in res['free'] if mm == m and (b, m) in res['std'])
            a = sum(res['std'][b, m]['mean'] for b in common)
            f = sum(res['free'][b, m]['mean'] for b in common)
            lines.append(f"0^0={m} bases {common[0]}-{common[-1]}: std {a:.2f}, free {f:.2f}")
    with open(os.path.join(HERE, 'data', 'r5e_int_report.txt'), 'w') as fh:
        fh.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == '__main__':
    main()
