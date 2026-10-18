"""Questions 48 and 49: the defect spectrum of short strings against the
root heuristic.

Reads the kdigit offset runs (r3c_offsets.py) and the heuristic sums
(r3c_root_spectrum.py), and prints the tables of the draft.

    python3 r3c_spectrum_report.py 4 22 150
    python3 r3c_spectrum_report.py 5 11 60

The heuristic sums run over strings with digits up to X; the observed
counts are given both for digits up to X and for digits up to M.
"""
import math
import sys

from r3c_root_spectrum import BINS
from collections import defaultdict

L = 75600


def load_obs(path):
    """{(D, mode): [(base, digits)]}"""
    out = defaultdict(list)
    Ds = set()
    for line in open(path):
        if line.startswith('#'):
            if 'offset D=' in line:
                Ds.add(int(line.split('offset D=')[1].split(';')[0]))
            continue
        D, mode, b, ds = line.split()
        out[int(D), int(mode)].append((int(b), tuple(map(int, ds.split(',')))))
    return out, sorted(Ds)


def load_d0(k, M):
    out = defaultdict(list)
    for line in open(f'data/k{k}.txt'):
        if line.startswith('#'):
            continue
        kk, mode, b, ds = line.split()
        ds = tuple(map(int, ds.split(',')))
        if max(ds) <= M:
            out[0, int(mode)].append((int(b), ds))
    return out


def load_pred(path):
    """{(D, mode): dict of sums}"""
    out = {}
    for line in open(path):
        if line.startswith('#'):
            continue
        p = line.split()
        D, mode = int(p[2]), int(p[3])
        v = list(map(float, p[5:]))
        out[D, mode] = dict(plain=v[0], prime=v[1], padic=v[2], avgp=v[3], avga=v[4],
                            bins_prime=v[5::2], bins_padic=v[6::2])
    return out


def pois_ge(k, lam):
    return 1 - sum(math.exp(-lam) * lam ** i / math.factorial(i) for i in range(k))


def binof(b):
    return next(i for i, (lo, hi) in enumerate(BINS) if lo <= b < hi)


def main():
    k, X, M = map(int, sys.argv[1:4])
    obs = load_d0(k, M)
    classes = {}
    for name in ('j', 'jL'):
        o, Ds = load_obs(f'data/r3c_offsets_k{k}_{name}.txt')
        obs.update(o)
        classes[name] = Ds
    pred = load_pred(f'data/r3c_root_spectrum_k{k}.txt')
    print(f"## k = {k}: heuristic over digits <= {X}, kdigit over digits <= {M}")
    for mode in (1, 0):
        print(f"\n### 0^0 = {mode}\n")
        print("Base below 100 and digits <= X, unless stated.\n")
        print("| offsets | count | observed | mean per offset | variance / mean | plain, all bases | prime | p-adic | observed / prime | observed / p-adic | base >= 100: observed / prime | all bases, digits <= M |")
        print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
        rows = {}
        for name, Ds in [('D = 0', [0])] + [(('D = j' if n == 'j' else 'D = j L'), Ds) for n, Ds in classes.items()]:
            Ds = [D for D in Ds if (D, mode) in pred]
            nx = [sum(1 for b, s in obs[D, mode] if max(s) <= X and b < 100) for D in Ds]
            big = sum(1 for D in Ds for b, s in obs[D, mode] if max(s) <= X and b >= 100)
            nm = [len(obs[D, mode]) for D in Ds]
            mean = sum(nx) / len(Ds)
            var = sum((v - mean) ** 2 for v in nx) / max(1, len(Ds) - 1)
            sums = {'plain': sum(pred[D, mode]['plain'] for D in Ds)}
            for key in ('prime', 'padic'):
                sums[key] = sum(sum(pred[D, mode]['bins_' + key][:-1]) for D in Ds)
            bigp = sum(pred[D, mode]['bins_prime'][-1] for D in Ds)
            rows[name] = (Ds, nx, sums)
            print(f"| {name} | {len(Ds)} | {sum(nx)} | {mean:.3f} | {var / mean if mean else float('nan'):.2f} | "
                  f"{sums['plain']:.2f} | {sums['prime']:.2f} | {sums['padic']:.2f} | "
                  f"{sum(nx) / sums['prime']:.2f} | {sum(nx) / sums['padic']:.2f} | {big} / {bigp:.2f} | {sum(nm)} |")
        # by the size of the base
        print("\n| offsets | " + " | ".join(f"base {lo} to {hi - 1}: observed / prime / p-adic" if hi < 1e9 else f"base {lo} and up" for lo, hi in BINS) + " |")
        print("|---" * (len(BINS) + 1) + "|")
        for name, (Ds, nx, sums) in rows.items():
            cells = []
            for i in range(len(BINS)):
                o = sum(1 for D in Ds for b, s in obs[D, mode] if max(s) <= X and binof(b) == i)
                pp = sum(pred[D, mode]['bins_prime'][i] for D in Ds)
                pa = sum(pred[D, mode]['bins_padic'][i] for D in Ds)
                cells.append(f"{o} / {pp:.2f} / {pa:.2f}")
            print(f"| {name} | " + " | ".join(cells) + " |")
        # all bases: the offsets D = j L have no algebraic families at large bases
        print()
        for name, (Ds, nx, sums) in rows.items():
            o = sum(1 for D in Ds for b, s in obs[D, mode] if max(s) <= X)
            pp = sum(pred[D, mode]['prime'] for D in Ds)
            pa = sum(pred[D, mode]['padic'] for D in Ds)
            print(f"- {name}, all bases, digits <= X: observed {o}, prime {pp:.2f}, p-adic {pa:.2f}")
        # D = 0 against the calibrated means
        Ds0, nx0, s0 = rows['D = 0']
        print()
        for name in ('D = j', 'D = j L'):
            Ds, nx, sums = rows[name]
            for key in ('prime', 'padic'):
                c = sum(nx) / sums[key]
                lam = s0[key] * c
                print(f"- calibrated by {name}, {key}: factor {c:.2f}, so D = 0 expects {lam:.2f}; observed {nx0[0]}, "
                      f"P(N >= observed) = {pois_ge(nx0[0], lam):.3f}")
        # dispersion of the offsets around their own predictions
        for name in ('D = j', 'D = j L'):
            Ds, nx, sums = rows[name]
            for key in ('prime', 'padic'):
                c = sum(nx) / sums[key]
                e = {D: sum(pred[D, mode]['bins_' + key][:-1]) for D in Ds}
                chi = sum((n - c * e[D]) ** 2 / (c * e[D]) for D, n in zip(Ds, nx) if e[D] > 0)
                print(f"- {name}, {key}: sum (N_D - c E_D)^2 / (c E_D) = {chi:.1f} over {len(Ds)} offsets")
        # parity of D for the offsets D = j
        Ds, nx, sums = rows['D = j']
        for par in (0, 1):
            sel = [(D, n) for D, n in zip(Ds, nx) if D % 2 == par]
            o = sum(n for D, n in sel)
            pp = sum(sum(pred[D, mode]['bins_prime'][:-1]) for D, n in sel)
            pa = sum(sum(pred[D, mode]['bins_padic'][:-1]) for D, n in sel)
            print(f"- D = j with j {'even' if par == 0 else 'odd'}: observed {o}, prime {pp:.2f}, p-adic {pa:.2f}")


if __name__ == '__main__':
    main()
