"""Round 4, blocks: base-by-base defect spectra of short strings and blocks.

Runs r4b_spectrum.c for
- solutions: k-digit strings, V = P_s(b) - F(s) (L = k, m = 0);
- blocks: L-digit strings t at shift m, V = b^m P_t(b) - F(t);
under both conventions, and compares the count N_0 of V = 0 with the mean
count of V = D over the offsets D in the same class as 0 modulo multiples
of 2(b-1), with b <= |D| <= W = 0.05 b^(k-1) (k = L + m). That mean is a
model-free version of the root heuristic for one base: it uses the true
values of V for some 10^2 to 10^6 offsets per base.

    python3 r4b_spectrum.py [run|report]

`run` writes the raw outputs to the scratch directory given by R4B_SCRATCH
(default: fast/target/r4b) and `report` writes data/r4b_spectrum.txt.
"""
import math
import os
import subprocess
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
SCR = os.environ.get('R4B_SCRATCH', os.path.join(HERE, '..', 'fast', 'target', 'r4b'))
BIN = os.path.join(SCR, 'r4b_spectrum')
WFRAC = 0.05
H = 300
THREADS = os.environ.get('OMP_NUM_THREADS', '4')

# largest base per total length k = L + m: b^k must fit in 63 bits
BMAX = {2: 10 ** 5, 3: 20000, 4: 20000, 5: 5000, 6: 1400, 7: 500, 8: 200}
RANGES = [(3, 12), (13, 99), (100, 10 ** 9)]
# class moduli printed by the C program, as multiples of 2(b-1)
CLASSES = ['x4', 'x8', 'x9', 'x72', 'xb^2', 'xb', 'x16*27*25*49']


def configs():
    for k in range(4, 9):
        for mode in (1, 0):
            yield (k, 0, mode)
    for m in (1, 2, 3):
        for L in range(1, 9 - m):
            if L + m < 2:
                continue
            for mode in (1, 0):
                yield (L, m, mode)


def raw_path(L, m, mode):
    return os.path.join(SCR, f'r4b_spectrum_L{L}_m{m}_z{mode}.txt')


def build():
    os.makedirs(SCR, exist_ok=True)
    subprocess.run(['gcc', '-O2', '-fopenmp', '-Wall', '-o', BIN, os.path.join(HERE, 'r4b_spectrum.c'), '-lm'], check=True)


def run():
    build()
    for L, m, mode in configs():
        path = raw_path(L, m, mode)
        if os.path.exists(path):
            continue
        bmax = BMAX[L + m]
        with open(path + '.tmp', 'w') as f:
            subprocess.run([BIN, str(L), str(m), str(mode), '3', str(bmax), str(WFRAC), str(H)], stdout=f, check=True,
                           env=dict(os.environ, OMP_NUM_THREADS=THREADS))
        os.rename(path + '.tmp', path)
        print(f"done L={L} m={m} mode={mode} bases 3-{bmax}", flush=True)


def parse(path):
    bases = {}
    cur = None
    for line in open(path):
        p = line.split()
        if not p or p[0] == '#':
            continue
        if p[0] == 'B':
            b = int(p[1])
            d = dict(b=b, X=int(p[2]), W=int(p[3]), E=int(p[4]), nstr=int(p[5]), n0=int(p[6]), tot=int(p[7]),
                     cls=int(p[8]), ncls=int(p[9]), sols=[], hist={})
            bases[b] = d
            cur = d
        elif p[0] == 'C':
            cur['classes'] = [tuple(map(int, it.split(':'))) for it in p[2:]]
        elif p[0] == 'S':
            cur['sols'].append(p[2])
        elif p[0] == 'H':
            cur['hist'] = {int(a): int(c) for a, c in (it.split(':') for it in p[2:])}
    return bases


def pois_ge(n, lam):
    if n <= 0:
        return 1.0
    return 1 - sum(math.exp(-lam) * lam ** i / math.factorial(i) for i in range(n))


def estimates(d):
    """expected N_0 for one base: density only, and class means"""
    out = {}
    out['dens'] = d['tot'] / (2 * (d['W'] - d['E'] + 1)) if d['W'] >= d['E'] else float('nan')
    e2 = d['cls'] / d['ncls'] if d['ncls'] > 0 else float('nan')
    out['2(b-1)'] = e2
    for name, (M, c, n) in zip(CLASSES, d.get('classes', [])):
        out[name] = c / n if n > 0 else e2
    # near offsets 0 < |D| <= H in the class of 2(b-1)
    M2 = 2 * (d['b'] - 1)
    out['near_obs'] = sum(c for v, c in d['hist'].items() if v != 0 and v % M2 == 0)
    out['near_n'] = 2 * (H // M2)
    out['near_all'] = sum(c for v, c in d['hist'].items() if v != 0)
    return out


def summarize(bases, lo, hi):
    S = defaultdict(float)
    sols = []
    nb = 0
    for b, d in bases.items():
        if not lo <= b <= hi:
            continue
        nb += 1
        e = estimates(d)
        for key, v in e.items():
            if not (isinstance(v, float) and math.isnan(v)):
                S[key] += v
        S['n0'] += d['n0']
        S['near_exp'] += (e['2(b-1)'] if not math.isnan(e['2(b-1)']) else 0) * e['near_n']
        sols += [(b, s) for s in d['sols']]
    S['nb'] = nb
    return S, sols


def report():
    out = []
    pr = out.append
    pr("# r4b_spectrum.py report: N_0 against the class means of the same base")
    pr(f"# window b <= |D| <= {WFRAC} b^(k-1); class: D == 0 mod 2(b-1), or mod lcm(2(b-1), q)")
    pr("# columns: L m mode bases | observed N_0 | density only | class 2(b-1) | x8 | x9 | xb | xb^2 | P(N >= obs) for class 2(b-1)"
       " | near offsets 0 < |D| <= 300 in class 2(b-1): observed / expected")
    rows = []
    cells = []
    for L, m, mode in configs():
        path = raw_path(L, m, mode)
        if not os.path.exists(path):
            continue
        bases = parse(path)
        bmax = max(bases)
        for lo, hi in RANGES:
            hi = min(hi, bmax)
            if lo > hi:
                continue
            S, sols = summarize(bases, lo, hi)
            n0 = int(S['n0'])
            e2 = S['2(b-1)']
            pr(f"{L} {m} {mode} {lo}-{hi} | {n0} | {S['dens']:.3f} | {e2:.3f} | {S['x8']:.3f} | {S['x9']:.3f} | "
               f"{S['xb']:.3f} | {S['xb^2']:.3f} | {pois_ge(n0, e2):.4f} | {int(S['near_obs'])} / {S['near_exp']:.2f}")
            rows.append((L, m, mode, lo, hi, sols))
            if m == 0 and lo >= 13:
                cells.append((L, mode, lo, hi, n0, e2))
    pr("")
    # look-elsewhere: chance that some solution cell (k = 4 to 8, bases from 13 on) has a tail
    # probability as small as the smallest one observed, under Poisson laws with the class means
    for mode in (1, 0):
        cm = [c for c in cells if c[1] == mode]
        if not cm:
            continue
        pmin = min(pois_ge(n0, e) for L, md, lo, hi, n0, e in cm)
        tot = 0.0
        for L, md, lo, hi, n0, e in cm:
            # smallest n with P(N >= n) <= pmin, then the chance of reaching it
            n = 0
            while pois_ge(n, e) > pmin:
                n += 1
            tot += pois_ge(n, e)
        pr(f"# look-elsewhere, 0^0 = {mode}: {len(cm)} solution cells with bases >= 13; smallest P = {pmin:.4f}; "
           f"chance that some cell is as extreme: {1 - math.exp(-tot):.3f}")
    pr("")
    pr("# strings with V = 0, by configuration and base range (bases up to the limit of each run)")
    for L, m, mode, lo, hi, sols in rows:
        if sols:
            shown = sols if len(sols) <= 40 else sols[:40] + [('...', f'{len(sols) - 40} more')]
            pr(f"L={L} m={m} mode={mode} bases {lo}-{hi}: " + '; '.join(f"{s} in {b}" for b, s in shown))
    pr("")
    # partial blocks: counts of small remainders R, bases from 13 on
    pr("# partial blocks and near solutions, bases from 13 to the run limit, 0^0 = 1: counts N_R for R = -5..5;")
    pr("# then all 0 < |R| <= 300 against the density-only expectation 600 * density")
    for L, m, mode in configs():
        if mode != 1 or L == 1:
            continue
        path = raw_path(L, m, mode)
        if not os.path.exists(path):
            continue
        bases = parse(path)
        N = defaultdict(int)
        dens = 0.0
        for b, d in bases.items():
            if b < 13:
                continue
            for v, c in d['hist'].items():
                N[v] += c
            e = estimates(d)
            if not math.isnan(e['dens']):
                dens += e['dens']
        small = ' '.join(f"{v}:{N[v]}" for v in range(-5, 6))
        tot = sum(c for v, c in N.items() if v != 0)
        pr(f"L={L} m={m}: {small} | 0 < |R| <= {H}: {tot} against {2 * H * dens:.1f}")
    pr("")
    # per base detail for the 5-digit solutions, bases 3 to 99
    for mode in (1, 0):
        path = raw_path(5, 0, mode)
        if not os.path.exists(path):
            continue
        bases = parse(path)
        pr(f"# per base, 5-digit strings, 0^0 = {mode}: b X N_0 window-count density class-2(b-1) x8 xb")
        for b in range(3, 100):
            d = bases[b]
            e = estimates(d)
            pr(f"{b} {d['X']} {d['n0']} {d['tot']} {e['dens']:.4f} {e['2(b-1)']:.4f} {e['x8']:.4f} {e['xb']:.4f}")
        pr("")
    open(os.path.join(HERE, 'data', 'r4b_spectrum.txt'), 'w').write('\n'.join(out) + '\n')


def sensitivity():
    """k = 4, 5 and 6, bases 3 to 99, for several window sizes"""
    build()
    out = ["# window sensitivity: L m mode wfrac bases | N_0 | density | class 2(b-1) | x8 | xb"]
    for L in (4, 5, 6):
        for mode in (1, 0):
            for wf in (0.01, 0.02, 0.05, 0.1, 0.2, 0.4):
                p = subprocess.run([BIN, str(L), '0', str(mode), '3', '99', str(wf), str(H)], capture_output=True, text=True,
                                   check=True, env=dict(os.environ, OMP_NUM_THREADS=THREADS))
                path = os.path.join(SCR, 'sens.tmp')
                open(path, 'w').write(p.stdout)
                bases = parse(path)
                for lo, hi in RANGES[:2]:
                    S, sols = summarize(bases, lo, hi)
                    out.append(f"{L} 0 {mode} {wf} {lo}-{hi} | {int(S['n0'])} | {S['dens']:.3f} | {S['2(b-1)']:.3f} | "
                               f"{S['x8']:.3f} | {S['xb']:.3f}")
    open(os.path.join(HERE, 'data', 'r4b_spectrum_windows.txt'), 'w').write('\n'.join(out) + '\n')


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'report'
    if what == 'run':
        run()
    if what == 'sens':
        sensitivity()
    else:
        report()
