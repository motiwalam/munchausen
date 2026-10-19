"""Round 5, question 74: pairs among Pisot solutions and near-solutions.

Reads the census (data/r3t_pisot_search.txt, r3t_pisot_search12.txt) and
the near-solution lists of r5e_pisot_run.sh (data/r5e_pisot_list_*.txt,
offsets D = j x). For x >= 2 and each convention:

- every pair of solutions with |N - N'| <= 2x, with the digit change;
- the same pairs inside one offset class among near-solutions, per offset;
- clusters across offsets (same multiset, the swap lemma for positions k
  and -k), with the design effects;
- solutions against near-solutions with twins collapsed on both sides.

Output: data/r5e_pisot_pairs.txt.
"""
import glob
import os
import re
from collections import Counter, defaultdict

from r5e_cluster import UF
from r5e_lib import cluster_stats, p_high, poisson_high

HERE = os.path.dirname(os.path.abspath(__file__))


def parse_digits(s):
    """'3,4.3,1' -> {position: digit}."""
    if '.' in s:
        a, b = s.split('.')
    else:
        a, b = s, ''
    hi = [int(t) for t in a.split(',') if t != '']
    lo = [int(t) for t in b.split(',') if t != '']
    pos = {}
    for i, d in enumerate(reversed(hi)):
        pos[i] = d
    for i, d in enumerate(lo):
        pos[-1 - i] = d
    return pos


def change(p, q):
    keys = sorted(set(p) | set(q), reverse=True)
    return ' '.join(f"{k}:{p.get(k, 0)}->{q.get(k, 0)}" for k in keys if p.get(k, 0) != q.get(k, 0))


def is_twin(p, q):
    """q is p with the digit 0 at position 0 replaced by 1 (Proposition 21.13)."""
    keys = set(p) | set(q)
    diff = [k for k in keys if p.get(k, 0) != q.get(k, 0)]
    return diff == [0] and p.get(0, 0) == 0 and q.get(0, 0) == 1


def load():
    sols = defaultdict(list)
    for f in ('r3t_pisot_search.txt', 'r3t_pisot_search12.txt'):
        for line in open(os.path.join(HERE, 'data', f)):
            m = re.match(r'sol x (\d+) m (\d) T (\d+) N (\d+) digits (\S+)', line)
            if m:
                x, mm, T, N = map(int, m.groups()[:4])
                sols[x, mm].append((N, m.group(5)))
    near = defaultdict(list)
    xs_listed = set()
    for f in sorted(glob.glob(os.path.join(HERE, 'data', 'r5e_pisot_list_*.txt'))):
        for line in open(f):
            m = re.match(r'nearsol x (\d+) m (\d) j (\d+) T (\d+) N (\d+) digits (\S+)', line)
            if m:
                x, mm, j, T, N = map(int, m.groups()[:5])
                near[x, mm].append((j, N, m.group(6)))
            m = re.match(r'done search x (\d+)', line)
            if m:
                xs_listed.add(int(m.group(1)))
    return sols, near, xs_listed


def pairs(events, x):
    """events: list of (N, digits). Pairs with 0 < N' - N <= 2x."""
    ev = sorted(events)
    out = []
    for i in range(len(ev)):
        for k in range(i + 1, len(ev)):
            if ev[k][0] - ev[i][0] > 2 * x:
                break
            if ev[k][0] > ev[i][0]:
                out.append((ev[i], ev[k]))
    return out


def collapse(events):
    """Count events with each twin pair counted once."""
    ds = {N: parse_digits(s) for N, s in events}
    tw = sum(1 for N in ds if N + 1 in ds and is_twin(ds[N], ds[N + 1]))
    return len(events) - tw, tw


def near_clusters(nears):
    """(cluster, j) per near-solution: same multiset, or twins at one offset."""
    uf = UF(len(nears))
    seen = {}
    at = {}
    for i, (j, N, d) in enumerate(nears):
        key = tuple(sorted(parse_digits(d).values()))
        if key in seen:
            uf.union(i, seen[key])
        else:
            seen[key] = i
        at[j, N] = i
    for i, (j, N, d) in enumerate(nears):
        k = at.get((j, N + 1))
        if k is not None and is_twin(parse_digits(d), parse_digits(nears[k][2])):
            uf.union(i, k)
    return [(uf.find(i), j) for i, (j, N, d) in enumerate(nears)]


def main():
    sols, near, xs = load()
    out = ["# r5e_pisot_pairs.py: Pisot bases eps_x, x >= 2, offsets D = j x"]
    out.append("## pairs of solutions with |N - N'| <= 2x")
    for (x, m), ev in sorted(sols.items()):
        if x < 2:
            continue
        for a, b in pairs(ev, x):
            kind = 'twin' if is_twin(parse_digits(a[1]), parse_digits(b[1])) else 'other'
            out.append(f"x {x} m {m}: {a[0]} = {a[1]} and {b[0]} = {b[1]}, dN {b[0] - a[0]}, {kind}, "
                       f"change {change(parse_digits(a[1]), parse_digits(b[1]))}")
    out.append("## per x and convention: solutions (twins collapsed) | near-solutions per offset, "
               "all and twins collapsed | pairs within one offset per offset (twins, others) | "
               "solution pairs (twins, others) | clusters across offsets")
    agg = defaultdict(lambda: Counter())
    for x in sorted(xs):
        if x < 2:
            continue
        J = 10 if x >= 12 else 30
        for m in (0, 1):
            s = sols.get((x, m), [])
            s_col, s_tw = collapse(s)
            sp = pairs(s, x)
            sp_tw = sum(1 for a, b in sp if is_twin(parse_digits(a[1]), parse_digits(b[1])))
            byj = defaultdict(list)
            for j, N, d in near.get((x, m), []):
                byj[j].append((N, d))
            n_all = sum(len(v) for v in byj.values())
            n_col = sum(collapse(v)[0] for v in byj.values())
            np_tw = np_ot = 0
            for v in byj.values():
                for a, b in pairs(v, x):
                    if is_twin(parse_digits(a[1]), parse_digits(b[1])):
                        np_tw += 1
                    else:
                        np_ot += 1
            evs = near_clusters(near.get((x, m), []))
            st = cluster_stats(evs)
            out.append(f"x {x} m {m}: sols {len(s)} ({s_col}) | near {n_all / J:.2f} ({n_col / J:.2f}) | "
                       f"pairs/offset {np_tw / J:.2f}, {np_ot / J:.2f} | sol pairs {sp_tw}, {len(sp) - sp_tw} | "
                       f"shared {st['shared']:.2f} phi {st['phi']:.2f} psi {st['psi']:.2f}")
            g = ('even' if x % 2 == 0 else 'odd', m)
            a = agg[g]
            a['sols'] += len(s)
            a['sols_col'] += s_col
            a['T'] += n_all
            a['T_col'] += n_col
            a['lam'] += n_all / J
            a['lam_col'] += n_col / J
            a['solpairs_other'] += len(sp) - sp_tw
            a['nearpairs_other'] += np_ot / J
            a['n'] += st['n']
            a['phi_n'] += st['phi'] * st['n']
            a['psi_n'] += st['psi'] * st['n']
            a['J'] = J
    out.append("## groups: observed against the offsets, twins kept and twins collapsed")
    for g in sorted(agg):
        a = agg[g]
        phi = a['phi_n'] / a['n'] if a['n'] else 1
        psi = a['psi_n'] / a['n'] if a['n'] else 1
        J = 30
        out.append(f"{g[0]} x, 0^0={g[1]}: solutions {a['sols']} vs {a['lam']:.2f} per offset "
                   f"(P fixed {poisson_high(a['sols'], a['lam']):.4f}, clustered "
                   f"{p_high(a['sols'], a['lam'] * J, J, phi, psi):.4f}); twins collapsed {a['sols_col']} vs "
                   f"{a['lam_col']:.2f} (P fixed {poisson_high(a['sols_col'], a['lam_col']):.4f}, clustered "
                   f"{p_high(a['sols_col'], a['lam_col'] * J, J, phi / psi):.4f}); "
                   f"non-twin pairs: solutions {a['solpairs_other']}, near per offset {a['nearpairs_other']:.2f}; "
                   f"phi {phi:.2f} psi {psi:.2f}")
    with open(os.path.join(HERE, 'data', 'r5e_pisot_pairs.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
