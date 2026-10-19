"""Question 103: the P values of the library, taken together.

    python3 r6q_ledger.py [--list]

Reads data/r6q_ledger_raw.tsv (one row per reported test; built by reading
chapters 4 to 32). Keeps the current rows with a P value. For tests named in
advance that print only a count and a model mean, a two-sided Poisson P is
computed here (it ignores clustering and model error). A one-sided P
becomes two-sided as min(1, 2p); a z-score was already converted to a
two-sided normal P in the file. Tests on the same data (column dgroup) are
merged into one P per group in two ways: the smallest P with the Sidak
correction 1 - (1 - p)^k for the k tests of the group, and the first-listed
(primary) test of the group. Then:

- the share of group P values below 0.05, 0.01 and 0.1, against uniform;
- a Kolmogorov-Smirnov test against the uniform law;
- Fisher's combination -2 sum ln p against chi-square on 2n;
- the same for the groups named in advance (prereg yes) and the others;
- the same without the worlds where the library already found that the
  model fails for a known reason (F_q[T], the factorial system, the Pisot
  class modulo 2x);
- the sign of the deviation (excess or deficit) for groups with P < 0.2.

With --list, prints the group table (the QQ points are the sorted P values
against i / (n + 1)).
"""
import csv
import math
import os
import sys
from collections import OrderedDict

HERE = os.path.dirname(os.path.abspath(__file__))
KNOWN = {'ffield', 'factorial'}


def chi2_sf(x, k):
    """survival function of chi-square with even k degrees of freedom"""
    m = x / 2.0
    term = math.exp(-m)
    s = term
    for i in range(1, k // 2):
        term *= m / i
        s += term
    return min(1.0, s)


def ks_uniform(ps):
    ps = sorted(ps)
    n = len(ps)
    d = max(max((i + 1) / n - p, p - i / n) for i, p in enumerate(ps))
    # asymptotic Kolmogorov law, with the small-sample correction of Stephens
    t = d * (math.sqrt(n) + 0.12 + 0.11 / math.sqrt(n))
    pv = 2 * sum((-1) ** (j - 1) * math.exp(-2 * j * j * t * t) for j in range(1, 101))
    return d, max(0.0, min(1.0, pv))


def poisson_two(obs, exp):
    """two-sided Poisson P for a count against a model mean, or None"""
    try:
        o, lam = int(float(obs)), float(exp)
    except ValueError:
        return None
    if lam <= 0:
        return None
    term = math.exp(-lam) if lam < 700 else 0.0
    if term == 0.0:
        z = (o - lam) / math.sqrt(lam)
        return math.erfc(abs(z) / math.sqrt(2))
    cdf = 0.0
    for k in range(o + 1):
        if k:
            term *= lam / k
        cdf += term
    pk = term
    return min(1.0, 2 * min(cdf, 1 - cdf + pk))


def load():
    rows = []
    with open(os.path.join(HERE, 'data', 'r6q_ledger_raw.tsv')) as f:
        for r in csv.DictReader(f, delimiter='\t'):
            if r['status'] != 'current':
                continue
            p = None
            if r['p_two'].strip():
                p = float(r['p_two'])
            elif r['p_one'].strip():
                p = min(1.0, 2 * float(r['p_one']))
            if p is None and r['prereg'] == 'yes':
                p = poisson_two(r['observed'], r['expected'])
                if p is not None:
                    r['test'] += ' [P computed here, Poisson]'
            if p is None:
                continue
            r['p'] = max(p, 1e-12)
            rows.append(r)
    return rows


def groups(rows):
    g = OrderedDict()
    for r in rows:
        g.setdefault(r['dgroup'], []).append(r)
    out = []
    for key, rs in g.items():
        k = len(rs)
        pmin = min(r['p'] for r in rs)
        sidak = 1 - (1 - pmin) ** k
        prereg = 'yes' if any(r['prereg'] == 'yes' for r in rs) else (
            'no' if all(r['prereg'] == 'no' for r in rs) else 'unclear')
        best = min(rs, key=lambda r: r['p'])
        out.append(dict(key=key, k=k, sidak=sidak, primary=rs[0]['p'], world=rs[0]['world'],
                        prereg=prereg, direction=best['direction'], section=best['section'],
                        test=best['test']))
    return out


def report(name, ps):
    n = len(ps)
    if n == 0:
        return
    d, kp = ks_uniform(ps)
    fisher = -2 * sum(math.log(p) for p in ps)
    fp = chi2_sf(fisher, 2 * n)
    lt = [sum(p < a for p in ps) for a in (0.01, 0.05, 0.1)]
    print(f"{name}: n = {n}; below 0.01, 0.05, 0.1: {lt[0]}, {lt[1]}, {lt[2]} "
          f"(uniform {0.01 * n:.1f}, {0.05 * n:.1f}, {0.1 * n:.1f}); median {sorted(ps)[n // 2]:.2f}; "
          f"KS D = {d:.3f}, P = {kp:.3f}; Fisher {fisher:.1f} on {2 * n}, P = {fp:.2g}")


def main():
    rows = load()
    print(f"# {len(rows)} current tests with a P value, in {len(set(r['dgroup'] for r in rows))} data groups")
    report("all tests, unmerged", [r['p'] for r in rows])
    gs = groups(rows)
    for how in ('sidak', 'primary'):
        print(f"## groups merged by {how}")
        report("all groups", [g[how] for g in gs])
        report("groups named in advance", [g[how] for g in gs if g['prereg'] == 'yes'])
        report("groups not named in advance or unclear", [g[how] for g in gs if g['prereg'] != 'yes'])
        report("without F_q[T] and the factorial system", [g[how] for g in gs if g['world'] not in KNOWN])
        report("integers only", [g[how] for g in gs if g['world'] == 'integers'])
    low = [g for g in gs if g['sidak'] < 0.2 and g['direction'] in ('excess', 'deficit')]
    ex = sum(g['direction'] == 'excess' for g in low)
    print(f"## sign of the deviation, groups with Sidak P < 0.2: {ex} excess, {len(low) - ex} deficit")
    if '--list' in sys.argv:
        print("## groups, sorted by Sidak P: key, k, Sidak P, primary P, world, prereg, direction, section, test")
        for g in sorted(gs, key=lambda g: g['sidak']):
            print(f"{g['key']:22s} {g['k']:2d} {g['sidak']:.3g} {g['primary']:.3g} {g['world']:12s} "
                  f"{g['prereg']:8s} {g['direction']:8s} {g['section']:6s} {g['test'][:70]}")


if __name__ == '__main__':
    main()
