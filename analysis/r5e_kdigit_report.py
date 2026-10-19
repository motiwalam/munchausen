"""Round 5, question 73: clusters in the kdigit offsets of section 19.2.

Reads data/r3c_offsets_k<k>_j.txt and _jL.txt (lines "D mode base digits"),
keeps the hits that section 19.2 counts (bases below 100, digits up to
X = 22 for k = 4 and 11 for k = 5), groups them by (base, multiset) and by
(base, multiset or common prefix of k-2 digits), and redoes the calibrated
P values of Tables 19.2.2 and 19.2.3 with the calibration error, first for
independent offsets and then with the cluster design effect.
Output: data/r5e_kdigit_report.txt.
"""
import os

from r5e_cluster import UF
from r5e_lib import cluster_stats, p_high, poisson_high

HERE = os.path.dirname(os.path.abspath(__file__))
X = {4: 22, 5: 11}

# (k, mode, family, observed N_0, calibrated lambda, label) from
# r3c_spectrum_report_k<k>.txt; T is recounted from the hits below.
ROWS = [
    (4, 1, 'j', 2, 1.29, 'primes'), (4, 1, 'j', 2, 0.74, 'p-adic'),
    (4, 1, 'jL', 2, 1.44, 'primes'), (4, 1, 'jL', 2, 0.63, 'p-adic'),
    (4, 0, 'j', 5, 2.41, 'primes'), (4, 0, 'j', 5, 2.11, 'p-adic'),
    (4, 0, 'jL', 5, 2.81, 'primes'), (4, 0, 'jL', 5, 1.76, 'p-adic'),
    (5, 1, 'j', 6, 2.95, 'primes'), (5, 1, 'j', 6, 3.53, 'p-adic'),
    (5, 1, 'jL', 6, 1.55, 'primes'), (5, 1, 'jL', 6, 1.82, 'p-adic'),
]


def load(k, fam):
    ev = []
    for line in open(os.path.join(HERE, 'data', f'r3c_offsets_k{k}_{fam}.txt')):
        if line.startswith('#') or not line.strip():
            continue
        D, mode, b, s = line.split()
        s = tuple(map(int, s.split(',')))
        b = int(b)
        if b < 100 and max(s) <= X[k]:
            ev.append((int(mode), b, int(D), s))
    return ev


def stats_for(ev, k, prefix):
    uf = UF(len(ev))
    seen = {}
    for i, (m, b, D, s) in enumerate(ev):
        keys = [('ms', m, b, tuple(sorted(s)))]
        if prefix:
            keys.append(('pre', m, b, s[:k - 2]))
        for key in keys:
            if key in seen:
                uf.union(i, seen[key])
            else:
                seen[key] = i
    return cluster_stats([(uf.find(i), e[2]) for i, e in enumerate(ev)])


def main():
    out = ["# r5e_kdigit_report.py: clusters among the kdigit offsets of section 19.2",
           "# k mode family hits clusters(multiset) shared phi_ms | clusters(+prefix) phi_pre"]
    phis = {}
    for k in (4, 5):
        for fam in ('j', 'jL'):
            ev = load(k, fam)
            for mode in (0, 1):
                e = [x for x in ev if x[0] == mode]
                a = stats_for(e, k, False)
                p = stats_for(e, k, True)
                phis[k, mode, fam] = (len(e), a['phi'], p['phi'])
                out.append(f"{k} {mode} {fam} {len(e)} {a['clusters']} {a['shared']:.2f} {a['phi']:.2f}"
                           f" | {p['clusters']} {p['phi']:.2f}")
    out.append("# calibrated P(N_0 >= obs): fixed lambda (as in 19.2) | with calibration error, "
               "independent | multiset clusters | multiset+prefix clusters")
    for k, mode, fam, obs, lam, label in ROWS:
        T, phi_ms, phi_pre = phis[k, mode, fam]
        J = T / lam
        out.append(f"k={k} 0^0={mode} D={fam} {label}: obs {obs}, lambda {lam:.2f}, T {T}: "
                   f"{poisson_high(obs, lam):.3f} | {p_high(obs, T, J):.3f} | "
                   f"{p_high(obs, T, J, phi=phi_ms):.3f} | {p_high(obs, T, J, phi=phi_pre):.3f}")
    with open(os.path.join(HERE, 'data', 'r5e_kdigit_report.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
