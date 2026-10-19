"""Round 5, question 72: a pooled test of D = 0 against the near-solutions.

Eight worlds, per base and convention: the solution count N_0 and the offset
total T over J offsets of the same class. For each world:

    O = sum N_0,  E = sum T / J,
    Var(O - theta E) = theta psi E + theta^2 phi E / J,

with psi the clump factor at one offset (twins, triples) and phi the design
effect across offsets (the swap lemma), measured by the r5e_*_report.py
scripts or assumed (phi = 2) where no strings exist. Reports the naive
z-scores of question 72, the corrected ones, a common ratio with a
heterogeneity statistic and a parametric bootstrap, a random effect per
world on log theta (marginal likelihood by Gauss-Hermite), and the
leave-one-out heterogeneity. Output: data/r5e_pooled.txt.

    python3 r5e_pooled.py [pisot]   (pisot = 'library' or 'class'; default both)
"""
import math
import os
import re
import sys
from collections import defaultdict

import numpy as np
from scipy import optimize, special, stats

import r2c_nega_compare as RN

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, 'data')


def ref_len(b):
    n, k = math.factorial(b - 1), 0
    while n:
        n //= b
        k += 1
    return k


def w_integers():
    c = defaultdict(int)
    for line in open(os.path.join(D, 'defects_bulk_b1.txt')):
        if line.startswith('#'):
            continue
        b, m, j, n = map(int, line.split())
        c[b, m, j] = n
    rows = []
    for b in range(12, 33):
        for m in (0, 1):
            rows.append((c[b, m, 0], sum(c[b, m, j] for j in range(2, 121, 2)), 60))
    return rows


def fact_solutions():
    n0 = defaultdict(int)
    for line in open(os.path.join(D, 'r2c_qw_factorial.txt')):
        p = line.split()
        if p and p[0] == 'raw':
            b, m = int(p[1]), int(p[2])
            n0[b, m] += sum(1 for s in p[5:] if s.count(',') + 1 >= ref_len(b) - 5)
    return n0


def w_fact_odd():
    n0 = fact_solutions()
    T = defaultdict(int)
    for line in open(os.path.join(D, 'r3c_factorion_offsets.txt')):
        p = line.split()
        if p and p[0] == 'off':
            T[int(p[1]), int(p[3])] += int(p[4])
    return [(n0[b, m], T[b, m], 30) for b in range(15, 36, 2) for m in (0, 1)]


def w_fact_even():
    n0 = fact_solutions()
    T = defaultdict(int)
    for line in open(os.path.join(D, 'wgt_offsets_factorial.txt')):
        p = line.split()
        if p and p[0] == 'off':
            T[int(p[1]), int(p[3])] += int(p[4])
    return [(n0[b, m], T[b, m], 30) for b in range(14, 37, 2) for m in (0, 1)]


def w_nega():
    _, sols = RN.load_census()
    T = defaultdict(int)
    for line in open(os.path.join(D, 'r2c_nega_offsets.txt')):
        p = line.split()
        if p and p[0] == 'off' and p[3] == 'stepb':
            T[int(p[1]), int(p[2])] += int(p[5])
    return [(len(sols[(b, m)]), T[b, m], 20) for b in range(10, 28) for m in (0, 1)]


def w_rational():
    sols, near = {}, {}
    for line in open(os.path.join(D, 'r3t_afs_search.txt')):
        m = re.match(r'done p/q (\d+)/(\d+) sols0 (\d+) sols1 (\d+)', line)
        if m:
            p, q, s0, s1 = map(int, m.groups())
            sols[p, q] = (s0, s1)
        m = re.match(r'near p/q (\d+)/(\d+) m (\d) step \d+ counts (\S+)', line)
        if m:
            p, q, mm = map(int, m.groups()[:3])
            near[p, q, mm] = list(map(int, m.group(4).split(',')))
    rows = []
    for (p, q), s in sols.items():
        if q > 1 and (p, q, 0) in near:
            for mm in (0, 1):
                rows.append((s[mm], sum(near[p, q, mm]), len(near[p, q, mm])))
    return rows


def w_pisot(calib):
    sols = defaultdict(int)
    near = {}
    for f in ('r3t_pisot_search.txt', 'r3t_pisot_search12.txt'):
        for line in open(os.path.join(D, f)):
            m = re.match(r'sol x (\d+) m (\d)', line)
            if m:
                sols[int(m.group(1)), int(m.group(2))] += 1
            m = re.match(r'near x (\d+) m (\d) step \d+ counts (\S+)', line)
            if m:
                near[int(m.group(1)), int(m.group(2))] = list(map(int, m.group(3).split(',')))
    rows = []
    for x in range(2, 13):
        for mm in (0, 1):
            c = near[x, mm]
            if calib == 'class' and x % 2 == 0:
                c = c[1::2]  # j = 2, 4, ...: the class of 0 mod 2x
            rows.append((sols[x, mm], sum(c), len(c)))
    return rows


def w_eisen():
    rows = []
    for f in ('r3t_eisen12.txt', 'r3t_eisen3_m0.txt', 'r3t_eisen3_m1.txt'):
        for line in open(os.path.join(D, f)):
            m = re.match(r'total base (\S+) m (\d) d \S+ sols (\d+) near (\S+)', line)
            if m and m.group(1) in ('-2+w', '-3+w'):
                c = list(map(int, m.group(4).split(',')))
                rows.append((int(m.group(3)), sum(c), len(c)))
    return rows


def w_cycles():
    rows = []
    for line in open(os.path.join(D, 'r2c_cycles2.txt')):
        if line.startswith('summary'):
            A = list(map(int, re.search(r' A=([\d,]+)', line).group(1).split(',')))
            # cycles at D = 0 against near-2-cycle events / 2 per offset
            rows.append((A[0] // 2, sum(A[1:]) / 2, len(A) - 1))
    return rows


# (name, rows, phi, psi, source of phi and psi)
def worlds(calib):
    return [
        ('integers 12-32', w_integers(), 2.31, 1.06, 'measured, bases 12-26'),
        ('factorions odd 15-35', w_fact_odd(), 1.95, 1.11, 'measured, j b(b-1)'),
        ('factorions even 14-36', w_fact_even(), 2.34, 1.16, 'measured on odd bases, j(b-1)'),
        ('negative -10 to -27', w_nega(), 1.84, 1.06, 'measured, bases -10 to -24'),
        ('rational p <= 11', w_rational(), 2.0, 1.0, 'assumed'),
        ('Pisot x = 2..12', w_pisot(calib), 2.6, 1.2, 'measured, x = 2..10'),
        ('Eisenstein -2+w, -3+w', w_eisen(), 2.0, 1.0, 'assumed'),
        ('2-cycles 4-18', w_cycles(), 1.4, 1.0, 'measured, bases 4-16, in 2-cycle units'),
    ]


def nb_logpmf(x, r, p):
    return (special.gammaln(x + r) - special.gammaln(r) - special.gammaln(x + 1)
            + r * np.log(p) + x * np.log1p(-p))


def world_loglik(theta, O, E, J, phi, psi):
    """log P(O | theta): O/psi ~ Poisson(theta lambda'), lambda' gamma with
    shape E J / phi + 1/2 and rate J psi / phi (effective units)."""
    r = E * J / phi + 0.5
    rate = J * psi / phi
    p = rate / (rate + theta)
    return nb_logpmf(O / psi, r, p)


def analyse(calib, out):
    W = worlds(calib)
    agg = []
    for name, rows, phi, psi, src in W:
        O = sum(r[0] for r in rows)
        E = sum(r[1] / r[2] for r in rows)
        J = float(np.mean([r[2] for r in rows]))
        agg.append((name, O, E, J, phi, psi, src))
    out.append(f"## Pisot calibration: {calib}")
    out.append("# world | O | E | z naive | z corrected | phi | psi | source")
    zn2 = zc2 = 0.0
    for name, O, E, J, phi, psi, src in agg:
        zn = (O - E) / math.sqrt(E)
        zc = (O - E) / math.sqrt(psi * E + phi * E / J)
        zn2 += zn * zn
        zc2 += zc * zc
        out.append(f"{name} | {O} | {E:.1f} | {zn:+.2f} | {zc:+.2f} | {phi} | {psi} | {src}")
    k = len(agg)
    Ot = sum(a[1] for a in agg)
    Et = sum(a[2] for a in agg)
    out.append(f"total {Ot} against {Et:.1f}; sum of z^2: naive {zn2:.1f} (P {stats.chi2.sf(zn2, k - 1):.3f} on {k - 1} df), "
               f"corrected {zc2:.1f} (P {stats.chi2.sf(zc2, k - 1):.3f})")
    # common ratio and heterogeneity
    th = Ot / Et

    def Q(theta, a):
        return sum((O - theta * E) ** 2 / (theta * psi * E + theta ** 2 * phi * E / J) for _, O, E, J, phi, psi, _ in a)
    q0 = Q(th, agg)
    # parametric bootstrap: compound draws with clump size psi (approximately), gamma calibration
    rng = np.random.default_rng(72)
    nb = 20000
    qs = np.zeros(nb)
    for i in range(nb):
        sim = []
        for name, O, E, J, phi, psi, src in agg:
            lam = rng.gamma(E * J / phi, phi / J)  # offset mean with its clustered error
            Es = lam
            Os = psi * rng.poisson(th * E / psi)
            sim.append((name, Os, Es, J, phi, psi, src))
            # E is re-estimated: replace by the draw
        ths = sum(s[1] for s in sim) / sum(s[2] for s in sim)
        qs[i] = Q(ths, sim)
    pboot = float(np.mean(qs >= q0))
    out.append(f"common ratio theta = {th:.3f}; heterogeneity Q = {q0:.1f} on {k - 1} df, "
               f"P chi-square {stats.chi2.sf(q0, k - 1):.3f}, P bootstrap {pboot:.3f}")
    # random effect on log theta
    gh_x, gh_w = np.polynomial.hermite.hermgauss(40)

    def negll(par):
        mu, ls = par
        tau = math.exp(ls)
        tot = 0.0
        for _, O, E, J, phi, psi, _ in agg:
            th_w = np.exp(mu + tau * math.sqrt(2) * gh_x)
            ll = world_loglik(th_w, O, E, J, phi, psi)
            tot += special.logsumexp(ll, b=gh_w / math.sqrt(math.pi))
        return -tot

    best = optimize.minimize(negll, [math.log(th), math.log(0.2)], method='Nelder-Mead',
                             options=dict(xatol=1e-6, fatol=1e-8, maxiter=4000))
    mu, tau = best.x[0], math.exp(best.x[1])
    ll1 = -best.fun
    ll0 = -min(optimize.minimize_scalar(lambda m_: negll([m_, -30.0]), bounds=(-3, 3), method='bounded').fun,
               negll([math.log(th), -30.0]))
    lr = max(2 * (ll1 - ll0), 0.0)
    out.append(f"random effect: common ratio exp(mu) = {math.exp(mu):.3f}, tau = {tau:.3f} "
               f"(between-world sd of log theta); LR = {lr:.2f}, P = {0.5 * stats.chi2.sf(lr, 1):.4f}")
    # per-world posterior mean of theta
    parts = []
    for name, O, E, J, phi, psi, _ in agg:
        th_w = np.exp(mu + tau * math.sqrt(2) * gh_x)
        ll = world_loglik(th_w, O, E, J, phi, psi)
        wts = gh_w * np.exp(ll - ll.max())
        parts.append(f"{name}: {float(np.sum(wts * th_w) / np.sum(wts)):.2f} (raw {O / E:.2f})")
    out.append("posterior mean ratio per world: " + "; ".join(parts))
    # leave one out
    loo = []
    for i in range(k):
        a = agg[:i] + agg[i + 1:]
        t_ = sum(x[1] for x in a) / sum(x[2] for x in a)
        q_ = Q(t_, a)
        loo.append(f"{agg[i][0]}: Q {q_:.1f} (P {stats.chi2.sf(q_, k - 2):.3f})")
    out.append("leave one world out: " + "; ".join(loo))
    a = [x for x in agg if not x[0].startswith(('factorions odd', 'Pisot'))]
    t_ = sum(x[1] for x in a) / sum(x[2] for x in a)
    q_ = Q(t_, a)
    out.append(f"without the odd factorions and the Pisot bases: ratio {t_:.3f}, Q {q_:.1f} on {len(a) - 1} df "
               f"(P {stats.chi2.sf(q_, len(a) - 1):.3f})")


def main():
    calibs = sys.argv[1:] or ['library', 'class']
    out = ["# r5e_pooled.py: question 72"]
    for c in calibs:
        analyse(c, out)
    with open(os.path.join(D, 'r5e_pooled.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == '__main__':
    main()
