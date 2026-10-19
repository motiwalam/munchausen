"""Question 106 (and the residuals of question 93): are neighbouring bases independent?

    python3 r6q_neighbors.py residuals    lambda(b) / model per base, and their correlations
    python3 r6q_neighbors.py shared       multisets that are near-solutions in two bases
    python3 r6q_neighbors.py top N        joint law of the top digits of S in bases b, b+1

residuals: lambda(b, m) is the mean count of near-solutions over the offsets
D = j(b-1), j = 2..120 even, at least b-6 digits (data/defects_bulk_b1.txt,
bases 12 to 32). The models are the exact refined model of r6q_lib (t = 0)
and the top-digit model with t = 3 of data/r2c_top_model.txt. The standard
error of lambda is the clustered one of chapter 26 for bases 12 to 26
(strings in data/r5e_int_std.txt) and the sample one times the median
inflation sqrt(2.1) for bases 27 to 32. Prints the mean ratios per parity and
convention, the lag-1 correlation of the standardized residuals after the
parity-group means are removed, with a permutation P value, and the
correlation between conventions in one base for comparison.

shared: in data/r5e_int_std.txt, the multisets that are near-solutions (any
offset, j >= 0) in two different bases, against the number that independent
bases would give (the model chance of each such multiset in the other base).

top: random multisets of d = b-1 digits whose sum S has d digits in base b and
in base b+1; the forced-top factor of section 23.5 (t = 3) in each base, and
the correlation of the two factors.
"""
import math
import os
import random
import sys
from collections import defaultdict

import numpy as np

from r6q_lib import load_hits, refined_by_zeros, weights

HERE = os.path.dirname(os.path.abspath(__file__))


def offsets_counts():
    rows = defaultdict(dict)
    for line in open(os.path.join(HERE, 'data', 'defects_bulk_b1.txt')):
        if line.startswith('#'):
            continue
        b, m, j, n = map(int, line.split())
        rows[(b, m)][j] = n
    return rows


def clustered_se():
    """clustered standard error of lambda for bases 12-26 (chapter 26)"""
    ev, done = load_hits(os.path.join(HERE, 'data', 'r5e_int_std.txt'))
    from r6q_zeros import clusters
    ev = [e for e in ev if e[2] > 0]
    cid = clusters(ev)
    K = defaultdict(lambda: defaultdict(int))
    for c, (b, m, k, s) in zip(cid, ev):
        K[(b, m)][c] += 1
    out = {}
    for (b, m), d in K.items():
        J = len([k for k in done[b] if k > 0])
        out[(b, m)] = math.sqrt(sum(x * x for x in d.values())) / J
    return out


def models():
    t3 = {}
    for line in open(os.path.join(HERE, 'data', 'r2c_top_model.txt')):
        p = line.split()
        if p and p[0] == 'base' and p[3] == '3':
            t3[(int(p[1]), int(p[2]))] = (float(p[4]), float(p[5]))
    t0 = {}
    for b in range(12, 33):
        for m in (0, 1):
            w = weights(b, m)
            t0[(b, m)] = sum(refined_by_zeros(b, d, w).sum() for d in range(b - 6, b + 1))
    return t0, t3


def residuals():
    rows = offsets_counts()
    cse = clustered_se()
    t0, t3 = models()
    lam, se = {}, {}
    for (b, m), d in rows.items():
        ev = [n for j, n in d.items() if j and j % 2 == 0]
        lam[(b, m)] = sum(ev) / len(ev)
        naive = math.sqrt(sum((e - lam[(b, m)]) ** 2 for e in ev) / (len(ev) - 1) / len(ev))
        se[(b, m)] = cse.get((b, m), naive * math.sqrt(2.1))
    bases = list(range(12, 33))
    rng = np.random.default_rng(106)
    for name, mod in (('t=0 exact', {k: (v, 0.0) for k, v in t0.items()}), ('t=3', t3)):
        print(f"# model {name}")
        for m in (0, 1):
            for par in (0, 1):
                bs = [b for b in bases if b % 2 == par]
                r = [lam[(b, m)] / mod[(b, m)][0] for b in bs]
                o = sum(lam[(b, m)] for b in bs)
                e = sum(mod[(b, m)][0] for b in bs)
                v = sum(se[(b, m)] ** 2 + mod[(b, m)][1] ** 2 for b in bs)
                print(f"0^0={m} {'odd' if par else 'even'} bases: mean ratio {np.mean(r):.3f}, pooled "
                      f"{o / e:.3f}, z of pooled {(o - e) / math.sqrt(v):+.2f}")
            r = [lam[(b, m)] / mod[(b, m)][0] for b in bases]
            o = sum(lam[(b, m)] for b in bases)
            e = sum(mod[(b, m)][0] for b in bases)
            v = sum(se[(b, m)] ** 2 + mod[(b, m)][1] ** 2 for b in bases)
            print(f"0^0={m} all: mean ratio {np.mean(r):.3f}, pooled {o / e:.3f}, z {(o - e) / math.sqrt(v):+.2f}")
        z = {}
        for m in (0, 1):
            zz = np.array([(lam[(b, m)] - mod[(b, m)][0]) / math.sqrt(se[(b, m)] ** 2 + mod[(b, m)][1] ** 2)
                           for b in bases])
            for par in (0, 1):
                idx = [i for i, b in enumerate(bases) if b % 2 == par]
                zz[idx] -= zz[idx].mean()
            z[m] = zz
            obs = np.corrcoef(zz[:-1], zz[1:])[0, 1]
            null = []
            for _ in range(20000):
                # permute within parity classes, which keeps the alternation
                p = zz.copy()
                for par in (0, 1):
                    idx = [i for i, b in enumerate(bases) if b % 2 == par]
                    p[idx] = rng.permutation(p[idx])
                null.append(np.corrcoef(p[:-1], p[1:])[0, 1])
            null = np.array(null)
            lag2 = np.corrcoef(zz[:-2], zz[2:])[0, 1]
            print(f"0^0={m}: lag-1 correlation of residuals {obs:+.3f} (permutation P two-sided "
                  f"{np.mean(np.abs(null) >= abs(obs)):.3f}, null sd {null.std():.3f}); lag-2 {lag2:+.3f}")
        print(f"same base, the two conventions: correlation {np.corrcoef(z[0], z[1])[0, 1]:+.3f}")
        cross = np.corrcoef(z[0][:-1], z[1][1:])[0, 1]
        print(f"base b under 0^0=0 against base b+1 under 0^0=1: {cross:+.3f}")


def multiset_chance(b, c, S, J=61):
    """model chance that multiset c (digits < b) is a near-solution in base b at
    one of J offsets D = 2j(b-1), j = 0..J-1: zero unless S has d digits and
    S == digit sum (mod b-1); else J (b-1) arrangements / ((b-1) b^(d-1))"""
    d = len(c)
    if max(c) >= b or not (b ** (d - 1) <= S < b ** d):
        return 0.0
    if (S - sum(c)) % (b - 1):
        return 0.0
    cnt = defaultdict(int)
    for x in c:
        cnt[x] += 1
    arr = math.factorial(d)
    for v in cnt.values():
        arr //= math.factorial(v)
    arr = arr * (d - cnt[0]) / d
    return J * arr / b ** (d - 1)


def shared():
    ev, done = load_hits(os.path.join(HERE, 'data', 'r5e_int_std.txt'))
    per = defaultdict(set)  # (m, multiset) -> bases
    for b, m, k, s in ev:
        per[(m, tuple(sorted(s)))].add(b)
    for m in (0, 1):
        multi = {c: bs for (mm, c), bs in per.items() if mm == m and len(bs) > 1}
        exp_nb = exp_any = 0.0
        for (mm, c), bs in per.items():
            if mm != m:
                continue
            S = sum((x ** x if x else m) for x in c)
            for b in bs:
                for b2 in range(12, 27):
                    if b2 == b or b2 in bs:
                        continue
                    p = multiset_chance(b2, c, S)
                    exp_any += p
                    if abs(b2 - b) == 1:
                        exp_nb += p
        n = len([1 for (mm, c) in per if mm == m])
        print(f"0^0={m}: {n} distinct near-solution multisets in bases 12-26; in two or more bases: "
              f"{len(multi)} {sorted(multi.items())[:5]}; expected if independent: neighbours {exp_nb:.2e}, "
              f"any two bases {exp_any:.2e}")


def top(N):
    rng = random.Random(106)
    print("# b d: candidates in both bases among N strings; mean top factor in b, in b+1; "
          "E[f_b f_b+1] / (E f_b E f_b+1); correlation")
    for b in (12, 16, 20, 24, 30):
        for d in (b - 1, b - 2):
            fb, fb1 = [], []
            tried = 0
            while len(fb) < N and tried < 200 * N:
                tried += 1
                c = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(d - 1)]
                S = sum(x ** x if x else 1 for x in c)
                if not (b ** (d - 1) <= S < b ** d and (b + 1) ** (d - 1) <= S < (b + 1) ** d):
                    continue
                fs = []
                for bb in (b, b + 1):
                    L = d
                    top3 = [(S // bb ** (L - 1 - i)) % bb for i in range(3)]
                    cnt = defaultdict(int)
                    for x in c:
                        cnt[x] += 1
                    num = 1.0
                    for i, v in enumerate(top3):
                        num *= max(0, cnt[v]) / (d - i)
                        cnt[v] -= 1
                    base = (d - c.count(0)) / d
                    fs.append((bb - 1) * bb ** 2 * num / base)
                fb.append(fs[0])
                fb1.append(fs[1])
            fb, fb1 = np.array(fb), np.array(fb1)
            if len(fb) < 10:
                print(f"{b} {d}: {len(fb)} candidates of {tried}")
                continue
            ratio = np.mean(fb * fb1) / (fb.mean() * fb1.mean())
            print(f"{b} {d}: {len(fb)} of {tried}; {fb.mean():.3f} {fb1.mean():.3f}; joint ratio {ratio:.3f}; "
                  f"correlation {np.corrcoef(fb, fb1)[0, 1]:+.3f}")


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'residuals':
        residuals()
    elif cmd == 'shared':
        shared()
    elif cmd == 'top':
        top(int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
