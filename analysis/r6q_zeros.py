"""Questions 93 and 94: near-solutions and solutions split by their zero digits.

    python3 r6q_zeros.py model SEED b0 b1 [c]    exact refined model by zero class
    python3 r6q_zeros.py top SEED b0 b1 N TMAX   the same with the top digits forced (sampled)
    python3 r6q_zeros.py compare FILE SEED [c]   observed against model, per class
    python3 r6q_zeros.py comparetop FILE SEED T  the same against the forced-top model
    python3 r6q_zeros.py solutions               zero digits of long solutions (question 94)
    python3 r6q_zeros.py near FILE [SEED]        zero digits of near-solutions (question 94)

model: for each base and convention, the refined model (identity modulo
b - 1, lengths b-6..b) split by the number z of zeros (0, 1, 2, 3 or more),
computed exactly (r6q_lib.refined_by_zeros) with the weights of
`fast --perturb SEED` (SEED 0: true weights). Appends to
data/r6q_zero_model.txt: "model seed b m c E0 E1 E2 E3+", c the offset shift.

compare: reads near-solution strings (r5e_int_offsets.py or r6q_offsets.py
format) and the model file, and prints per parity, convention and zero
class the observed mean per offset, the model, the ratio and a z-score with
the clustered variance of chapter 26 (clusters: one multiset, plus twins
under 0^0 = 0). With c given, the file holds offsets 2j(b-1) + c, and the
model is computed with the residue condition of D == c (mod b - 1).
"""
import math
import os
import sys
from collections import defaultdict

from r6q_lib import load_hits, refined_by_zeros, weights

HERE = os.path.dirname(os.path.abspath(__file__))
MODEL = os.path.join(HERE, 'data', 'r6q_zero_model.txt')


def model(seed, b0, b1, shift=0):
    with open(MODEL, 'a') as f:
        for b in range(b0, b1 + 1):
            for m in (0, 1):
                w = weights(b, m, seed)
                tot = [0.0] * 4
                for d in range(b - 6, b + 1):
                    r = refined_by_zeros(b, d, w, shift=shift)
                    tot = [a + x for a, x in zip(tot, r)]
                f.write(f"model {seed} {b} {m} {shift} " + ' '.join(f"{x:.6f}" for x in tot) + "\n")
                f.flush()


def expected_top_z(b, d, w, N, tmax, rng, zmax=3):
    """r2c_top_model.expected_top for weights w, split by min(zeros, zmax):
    returns sums[t][z] and sums of squares, per string drawn (times b - 1)."""
    import numpy as np
    q = b - 1
    scale = (d - 1) * math.log(b)
    lw = np.array([math.log(v) if v > 0 else -1e9 for v in w])
    wr = np.exp(lw - scale)
    u = np.array([(w[v] - v) % q for v in range(b)], dtype=np.int64)
    sums = np.zeros((tmax + 1, zmax + 1))
    sq = np.zeros((tmax + 1, zmax + 1))
    done = 0
    while done < N:
        n = min(50_000, N - done)
        done += n
        c = rng.multinomial(d - 1, np.full(b, 1.0 / b), size=n)
        lead = rng.integers(1, b, size=n)
        c[np.arange(n), lead] += 1
        f = c @ wr
        ok = (f >= 1.0) & (f < b) & ((c @ u) % q == 0)
        c, f = c[ok], f[ok]
        k = len(f)
        if k == 0:
            continue
        zb = np.minimum(c[:, 0], zmax)
        rows = np.arange(k)
        base = (d - c[:, 0]) / d
        num = np.ones(k)
        digs = []
        g = f.copy()
        for z in range(zmax + 1):
            sums[0, z] += np.count_nonzero(zb == z)
            sq[0, z] += np.count_nonzero(zb == z)
        for t in range(1, tmax + 1):
            v = np.floor(g).astype(np.int64) % b
            g = (g - np.floor(g)) * b
            used = np.zeros(k, dtype=np.int64)
            for prev in digs:
                used += (prev == v)
            digs.append(v)
            num = num * np.maximum(0, c[rows, v] - used) / (d - t + 1)
            ratio_t = (b - 1) * float(b) ** (t - 1) * num / base
            for z in range(zmax + 1):
                sel = zb == z
                sums[t, z] += ratio_t[sel].sum()
                sq[t, z] += (ratio_t[sel] ** 2).sum()
    return sums * q / N, sq * q * q / (N * N)


def top_model(seed, b0, b1, N, tmax):
    """forced top digits, split by zeros: lines "top seed b m t E0 E1 E2 E3+ se0 se1 se2 se3" """
    import numpy as np
    rng = np.random.default_rng(93 + seed)
    with open(os.path.join(HERE, 'data', 'r6q_zero_top.txt'), 'a') as f:
        for b in range(b0, b1 + 1):
            for m in (0, 1):
                w = weights(b, m, seed)
                tot = np.zeros((tmax + 1, 4))
                var = np.zeros((tmax + 1, 4))
                for d in range(b - 6, b + 1):
                    s, v = expected_top_z(b, d, w, N, tmax, rng)
                    tot += s
                    var += v
                for t in range(tmax + 1):
                    f.write(f"top {seed} {b} {m} {t} " + ' '.join(f"{x:.5f}" for x in tot[t]) + ' '
                            + ' '.join(f"{math.sqrt(x):.5f}" for x in var[t]) + "\n")
                f.flush()


def load_top(t):
    """the forced-top model with t digits, keyed like load_model (shift 0)"""
    out = {}
    for line in open(os.path.join(HERE, 'data', 'r6q_zero_top.txt')):
        p = line.split()
        if p[0] == 'top' and int(p[4]) == t:
            out[(int(p[1]), int(p[2]), int(p[3]), 0)] = list(map(float, p[5:9]))
    return out


def load_model():
    out = {}
    for line in open(MODEL):
        p = line.split()
        if p[0] == 'model':
            out[(int(p[1]), int(p[2]), int(p[3]), int(p[4]))] = list(map(float, p[5:9]))
    return out


def clusters(ev):
    """cluster ids: same (b, m, multiset), or twins under 0^0 = 0 (last digit 0/1, same offset)"""
    parent = list(range(len(ev)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    first = {}
    pref = {}
    for i, (b, m, k, s) in enumerate(ev):
        key = (b, m, tuple(sorted(s)))
        if key in first:
            parent[find(i)] = find(first[key])
        else:
            first[key] = i
        if m == 0 and s[-1] in (0, 1):
            pk = (b, m, k, s[:-1])
            if pk in pref:
                parent[find(i)] = find(pref[pk])
            else:
                pref[pk] = i
    return [find(i) for i in range(len(ev))]


def compare(path, seed, c=None, top=None):
    ev, done = load_hits(path)
    ev = [e for e in ev if e[2] > 0]
    cid = clusters(ev)
    mod = load_model() if top is None else load_top(top)
    J = {b: len([k for k in ks if k > 0]) for b, ks in done.items()}
    obs = defaultdict(float)
    clus = defaultdict(lambda: defaultdict(float))
    for ci, (b, m, k, s) in zip(cid, ev):
        z = min(s.count(0), 3)
        obs[(b, m, z)] += 1.0 / J[b]
        clus[(b, m, z)][ci] += 1.0 / J[b]
    print(f"# {os.path.basename(path)}, seed {seed}" + (f", offsets 2j(b-1)+{c}" if c is not None else ""))
    print("# parity m z: observed per offset, model, ratio, z; the variance under the null is phi E / J,")
    print("# with phi = sum K^2 / sum K over the clusters of the group (chapter 26)")
    rows = {}
    for par in ('even', 'odd'):
        for m in (0, 1):
            bs = [b for b in sorted(J) if (b % 2 == 1) == (par == 'odd') and (seed, b, m, c or 0) in mod]
            k1 = sum(x for b in bs for z in range(4) for x in clus[(b, m, z)].values())
            k2 = sum(x * x * J[b] for b in bs for z in range(4) for x in clus[(b, m, z)].values())
            phi = k2 / k1 if k1 else 1.0
            Jm = sum(J[b] for b in bs) / len(bs)
            tot_o = tot_e = 0.0
            for z in range(4):
                o = sum(obs[(b, m, z)] for b in bs)
                e = sum(mod[(seed, b, m, c or 0)][z] for b in bs)
                tot_o += o
                tot_e += e
                rows[(par, m, z)] = (o, e, phi)
                zs = (o - e) / math.sqrt(phi * e / Jm) if e > 0 else float('nan')
                print(f"{par} {m} z={z}{'+' if z == 3 else ' '}: {o:7.3f} {e:7.3f} "
                      f"{o / e if e else float('nan'):6.3f} {zs:+5.2f}")
            zs = (tot_o - tot_e) / math.sqrt(phi * tot_e / Jm) if tot_e > 0 else float("nan")
            print(f"{par} {m} all : {tot_o:7.3f} {tot_e:7.3f} {tot_o / tot_e if tot_e else float("nan"):6.3f} {zs:+5.2f}   (phi {phi:.2f})")
    return rows


def zero_law(b, d, m, seed=0, zmax=14):
    """model weights of the zero counts 0..zmax-1 (and zmax or more) of a
    d-digit solution in the refined model, exact"""
    return refined_by_zeros(b, d, weights(b, m, seed), zmax=zmax)


def count_solutions():
    """Question 94: zero digits of the long solutions (at least b-6 digits),
    bases 12 to 43, against the refined model's law for their base and length,
    and against the binomial law of r4f_integer_types.py."""
    import ast
    from math import comb
    root = os.path.join(HERE, '..', 'output')
    sols = {0: {}, 1: {}}
    for name in ('b2-41-{m}.txt', 'b43-{m}.txt'):
        for m in (0, 1):
            for line in open(os.path.join(root, name.format(m=m))):
                b, _, _, rest = line.strip().split(':', 3)
                sols[m][int(b)] = ast.literal_eval('[' + rest + ']')
    print("# solutions with at least b-6 digits, bases 12-43: zero digits, observed against models")
    for m in (0, 1):
        for par in ('even', 'odd'):
            n = obs = em = vm = eb = vb = z0 = z0m = z0b = 0.0
            for b, lst in sorted(sols[m].items()):
                if b < 12 or (b % 2 == 1) != (par == 'odd'):
                    continue
                for s in lst:
                    d = len(s)
                    if d < b - 6:
                        continue
                    law = zero_law(b, d, m)
                    p = law / law.sum()
                    mean = sum(k * pk for k, pk in enumerate(p))
                    em += mean
                    vm += sum(k * k * pk for k, pk in enumerate(p)) - mean ** 2
                    bl = [comb(d - 1, k) * (1 / b) ** k * (1 - 1 / b) ** (d - 1 - k) for k in range(d)]
                    if m == 1 and b % 2 == 1:
                        bl = [x if k % 2 == 0 else 0.0 for k, x in enumerate(bl)]
                    tb = sum(bl)
                    bl = [x / tb for x in bl]
                    mb = sum(k * x for k, x in enumerate(bl))
                    eb += mb
                    vb += sum(k * k * x for k, x in enumerate(bl)) - mb ** 2
                    n += 1
                    obs += s.count(0)
                    z0 += s.count(0) == 0
                    z0m += p[0]
                    z0b += bl[0]
            print(f"0^0={m} {par}: {int(n)} solutions, zeros {int(obs)}, refined {em:.1f} +/- {vm ** 0.5:.1f}, "
                  f"binomial {eb:.1f} +/- {vb ** 0.5:.1f}; zero-free {int(z0)}, refined {z0m:.1f}, binomial {z0b:.1f}")


def count_near(path, seed=0):
    """Question 94: zero digits of the near-solutions per offset, against the
    refined model's mean, with the clustered variance."""
    ev, done = load_hits(path)
    ev = [e for e in ev if e[2] > 0]
    cid = clusters(ev)
    J = {b: len([k for k in ks if k > 0]) for b, ks in done.items()}
    cache = {}
    for b in J:
        for m in (0, 1):
            tot = sum(zero_law(b, d, m, seed) for d in range(b - 6, b + 1))
            cache[(b, m)] = (sum(k * x for k, x in enumerate(tot)), tot.sum())
    # residual of each event: its zeros minus the model's mean zeros per
    # near-solution in its base; summed per cluster for the variance
    res = defaultdict(float)
    for ci, (b, m, k, s) in zip(cid, ev):
        res[ci] += (s.count(0) - cache[(b, m)][0] / cache[(b, m)][1]) / J[b]
    print(f"# {os.path.basename(path)}: zero digits of near-solutions, observed against the refined model")
    for m in (0, 1):
        for par in ('even', 'odd'):
            o = n = r = v = e = en = 0.0
            seen = set()
            for ci, (b, mm, k, s) in zip(cid, ev):
                if mm != m or (b % 2 == 1) != (par == 'odd'):
                    continue
                o += s.count(0) / J[b]
                n += 1.0 / J[b]
                r += (s.count(0) - cache[(b, m)][0] / cache[(b, m)][1]) / J[b]
                if ci not in seen:
                    seen.add(ci)
                    v += res[ci] ** 2
            for b in J:
                if (b % 2 == 1) == (par == 'odd'):
                    e += cache[(b, m)][0]
                    en += cache[(b, m)][1]
            print(f"0^0={m} {par}: {n:.2f} near-solutions per offset (model {en:.2f}); zeros per near-solution "
                  f"{o / n:.3f} against {e / en:.3f}; zeros minus the model mean, per offset {r:+.3f} "
                  f"(z {r / math.sqrt(v):+.2f}, clustered)")


def summary():
    """Question 93: ratio observed / model for all near-solutions, the
    zero-free ones and those with zeros, true weights and perturbed worlds."""
    import contextlib
    import io
    runs = [('true, t=3', 'data/r5e_int_std.txt', 0, 3), ('true, t=0', 'data/r5e_int_std.txt', 0, None)]
    runs += [(f'perturbed {s}', f'data/r6q_pert_s{s}.txt', s, None) for s in range(1, 6)]
    runs += [(f'pert. {s}, t=3', f'data/r6q_pert_s{s}.txt', s, 3) for s in range(1, 6)]
    pooled = {}
    print("# observed / model per parity (e, o) and convention: all near-solutions, zero-free, with zeros")
    for name, path, seed, top in runs:
        with contextlib.redirect_stdout(io.StringIO()):
            rows = compare(os.path.join(HERE, '..', 'analysis', path) if not os.path.isabs(path) else path,
                           seed, None, top)
        out = []
        for par in ('even', 'odd'):
            for m in (0, 1):
                v = [sum(rows[(par, m, z)][i] for z in zs) for zs in ((0, 1, 2, 3), (0,), (1, 2, 3)) for i in (0, 1)]
                out.append(f"{par[0]}{m} {v[0] / v[1]:.3f} {v[2] / v[3]:.3f} {v[4] / v[5]:.3f}")
                if name.startswith('perturbed'):
                    acc = pooled.setdefault((par, m), [0.0] * 6)
                    for i in range(6):
                        acc[i] += v[i]
        # both parities: ratio per convention, and the gap R1 - R0. The zero-free
        # events are common to both conventions, so only the events with zeros
        # enter the variance of the gap (phi E / J with J = 60).
        R, Ez, var = {}, {}, 0.0
        for m in (0, 1):
            o = sum(rows[(p, m, z)][0] for p in ('even', 'odd') for z in range(4))
            e = sum(rows[(p, m, z)][1] for p in ('even', 'odd') for z in range(4))
            R[m] = (o / e, e)
            var += sum(rows[(p, m, z)][2] * rows[(p, m, z)][1] / 60 for p in ('even', 'odd') for z in (1, 2, 3))
        sd = math.sqrt(var) / ((R[0][1] + R[1][1]) / 2)
        out.append(f"R0 {R[0][0]:.3f} R1 {R[1][0]:.3f} gap {R[1][0] - R[0][0]:+.3f} +/- {sd:.3f}")
        print(f"{name:13s} " + ' | '.join(out))
    out = []
    for par in ('even', 'odd'):
        for m in (0, 1):
            v = pooled[(par, m)]
            out.append(f"{par[0]}{m} {v[0] / v[1]:.3f} {v[2] / v[3]:.3f} {v[4] / v[5]:.3f}")
    print(f"{'perturbed 1-5':13s} " + ' | '.join(out))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'summary':
        summary()
    if cmd == 'solutions':
        count_solutions()
    elif cmd == 'near':
        count_near(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 0)
    if cmd == 'model':
        model(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]) if len(sys.argv) > 5 else 0)
    elif cmd == 'top':
        top_model(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]))
    elif cmd == 'compare':
        compare(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else None)
    elif cmd == 'comparetop':
        compare(sys.argv[2], int(sys.argv[3]), None, int(sys.argv[4]))
