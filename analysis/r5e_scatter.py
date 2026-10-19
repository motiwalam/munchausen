"""Round 5, question 73: the per-base tests of sections 11.1, 11.2, 11.2a
and 23.5 with the clustered variance of the offset means.

The offset mean lambda(b) of data/defects_bulk_b1.txt (60 offsets
D = 2j(b-1), at least b-6 digits) has variance phi(b) lambda(b) / 60, not
the sample variance / 60 used so far. phi(b) is the swap-lemma prediction
of data/r5e_swap_model.txt, scaled per convention to the measured design
effects of data/r5e_int_report.txt (bases 12 to 26; the scale also absorbs
the twins under 0^0 = 0). Output: data/r5e_scatter.txt.
"""
import math
import os
import re
from collections import defaultdict

from scipy import stats

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'data')
J = 60


def load_bulk():
    rows = defaultdict(dict)
    for line in open(os.path.join(D, 'defects_bulk_b1.txt')):
        if line.startswith('#'):
            continue
        b, m, j, n = map(int, line.split())
        rows[b, m][j] = n
    out = {}
    for k, d in rows.items():
        ev = [n for j, n in d.items() if j and j % 2 == 0]
        lam = sum(ev) / len(ev)
        var = sum((e - lam) ** 2 for e in ev) / (len(ev) - 1)
        out[k] = dict(n0=d[0], lam=lam, svar=var, J=len(ev))
    return out


def load_phi():
    model = {}
    for line in open(os.path.join(D, 'r5e_swap_model.txt')):
        if line.startswith('#'):
            continue
        b, a, _ = line.split()
        model[int(b)] = float(a)
    meas = {}
    psi = {}
    fam = None
    for line in open(os.path.join(D, 'r5e_int_report.txt')):
        if line.startswith('## family'):
            fam = line.split()[2]
            continue
        p = line.split()
        if fam == 'std' and len(p) == 11 and p[0].isdigit():
            b, m = int(p[0]), int(p[1])
            meas[b, m] = (float(p[8]), float(p[9]), int(p[4]))
            psi[b, m] = float(p[9])
    scale = {}
    for m in (0, 1):
        num = sum(v[0] * v[2] for (b, mm), v in meas.items() if mm == m)
        den = sum(model[b] * v[2] for (b, mm), v in meas.items() if mm == m)
        scale[m] = num / den
    psim = {m: sum(v[1] * v[2] for (b, mm), v in meas.items() if mm == m) /
            sum(v[2] for (b, mm), v in meas.items() if mm == m) for m in (0, 1)}
    phi = {(b, m): model[b] * scale[m] for b in model for m in (0, 1)}
    return phi, scale, psim


def load_top():
    top = {}
    for line in open(os.path.join(D, 'r2c_top_model.txt')):
        p = line.split()
        if p and p[0] == 'base':
            top[int(p[1]), int(p[2]), int(p[3])] = (float(p[4]), float(p[5]))
    return top


def main():
    bulk = load_bulk()
    phi, scale, psim = load_phi()
    top = load_top()
    out = ["# r5e_scatter.py: per-base tests with the clustered variance of the offset means",
           f"# phi(b) = swap model x {scale[0]:.3f} (0^0 = 0), x {scale[1]:.3f} (0^0 = 1); "
           f"psi = {psim[0]:.3f}, {psim[1]:.3f}"]
    keys = sorted(k for k in bulk if 12 <= k[0] <= 32)
    # 11.1: dispersion of N_0 around lambda
    naive = sum((bulk[k]['n0'] - bulk[k]['lam']) ** 2 / bulk[k]['lam'] for k in keys)
    corr = sum((bulk[k]['n0'] - bulk[k]['lam']) ** 2 /
               (psim[k[1]] * bulk[k]['lam'] + phi[k] * bulk[k]['lam'] / J) for k in keys)
    n = len(keys)
    out.append(f"11.1 dispersion of N_0 over {n} cases: naive {naive:.1f} (P upper {stats.chi2.sf(naive, n):.3f}, "
               f"lower {stats.chi2.cdf(naive, n):.3f}); clustered {corr:.1f} (P upper {stats.chi2.sf(corr, n):.3f}, "
               f"lower {stats.chi2.cdf(corr, n):.3f})")
    # sample variance against the clustered variance of the mean
    rat = [phi[k] * bulk[k]['lam'] / bulk[k]['svar'] for k in keys if bulk[k]['svar'] > 0]
    out.append(f"ratio of clustered to naive variance of lambda: median {sorted(rat)[len(rat) // 2]:.2f}, "
               f"range {min(rat):.2f} to {max(rat):.2f}")
    # 11.2a and 23.5: lambda against the model, t = 0..4
    for m in (0, 1):
        ks = [k for k in keys if k[1] == m]
        for t in range(5):
            chi_n = chi_c = 0.0
            for k in ks:
                e, ese = top[k[0], m, t]
                lam = bulk[k]['lam']
                chi_n += (lam - e) ** 2 / (bulk[k]['svar'] / J + ese ** 2)
                chi_c += (lam - e) ** 2 / (phi[k] * lam / J + ese ** 2)
            out.append(f"lambda vs model 0^0={m} t={t}: chi2 naive {chi_n:.1f}, clustered {chi_c:.1f} on {len(ks)} bases "
                       f"(P {stats.chi2.sf(chi_n, len(ks)):.2g} -> {stats.chi2.sf(chi_c, len(ks)):.2g})")
    # the total: sum of lambda against the sum of the model
    for m in (0, 1):
        ks = [k for k in keys if k[1] == m]
        for t in (0, 3):
            L = sum(bulk[k]['lam'] for k in ks)
            E = sum(top[k[0], m, t][0] for k in ks)
            vn = sum(bulk[k]['svar'] / J + top[k[0], m, t][1] ** 2 for k in ks)
            vc = sum(phi[k] * bulk[k]['lam'] / J + top[k[0], m, t][1] ** 2 for k in ks)
            out.append(f"total 0^0={m} t={t}: lambda {L:.2f}, model {E:.2f}, ratio {L / E:.3f}; "
                       f"z naive {(L - E) / math.sqrt(vn):.2f}, clustered {(L - E) / math.sqrt(vc):.2f}")
    # base 19 under 0^0 = 0 at t = 3
    k = (19, 0)
    e, ese = top[19, 0, 3]
    lam = bulk[k]['lam']
    zn = (lam - e) / math.sqrt(bulk[k]['svar'] / J + ese ** 2)
    zc = (lam - e) / math.sqrt(phi[k] * lam / J + ese ** 2)
    out.append(f"base 19, 0^0=0, t=3: lambda {lam:.3f}, model {e:.3f}; z naive {zn:.2f}, clustered {zc:.2f}; "
               f"se naive {math.sqrt(bulk[k]['svar'] / J):.3f}, clustered {math.sqrt(phi[k] * lam / J):.3f}")
    # 11.2: expected number of bases with no long solution
    for m in (0, 1):
        for par, name in ((0, 'even'), (1, 'odd')):
            ks = [k for k in keys if k[1] == m and k[0] % 2 == par]
            e_n = sum(math.exp(-bulk[k]['lam']) for k in ks)
            e_c = 0.0
            for k in ks:
                lam = bulk[k]['lam']
                v = phi[k] * lam / J
                e_c += (1 + v / lam) ** (-lam * lam / v)
            obs = sum(1 for k in ks if bulk[k]['n0'] == 0)
            out.append(f"11.2 empty bases {name} 0^0={m}: expected {e_n:.2f} (fixed lambda), {e_c:.2f} "
                       f"(lambda with its clustered error); observed {obs}")
    with open(os.path.join(D, 'r5e_scatter.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
