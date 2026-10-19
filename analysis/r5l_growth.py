"""Question 77: growth per base of the solver runs against the engine, d = b-1, 0^0 = 1.

Reads data/r5l_engine_dm1.txt, data/r5l_sat_counts.txt, data/r5l_cpsat_window.txt
and data/r5l_cpsat_exist.txt (the plain column model, first 5 bases are
infeasible so it certifies them). Fits exp(slope) of ln(metric) against b by
least squares over the bases where every metric is present.
"""
import math
import os

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data')


def read(name, cols):
    out = {}
    path = os.path.join(D, name)
    if not os.path.exists(path):
        return out
    for line in open(path):
        if line.startswith('#'):
            continue
        f = line.split()
        if f[-1] not in ('ok',) and name != 'r5l_engine_dm1.txt':
            continue
        out[int(f[0])] = {k: float(f[i]) for k, i in cols.items()}
    return out


def growth(xs, ys):
    n = len(xs)
    mx, my = sum(xs) / n, sum(ys) / n
    return math.exp(sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sum((x - mx) ** 2 for x in xs))


eng = read('r5l_engine_dm1.txt', {'nodes': 2, 'evals': 3, 'cpu': 4})
sat = read('r5l_sat_counts.txt', {'cpu': 5, 'decisions': 6, 'conflicts': 7})
win = read('r5l_cpsat_window.txt', {'cpu': 5, 'branches': 6, 'conflicts': 7})

print('| b | engine nodes | engine evals | CaDiCaL conflicts | CaDiCaL CPU s | CP-SAT window conflicts | CP-SAT window branches | CP-SAT window CPU s |')
print('|---:|---:|---:|---:|---:|---:|---:|---:|')
for b in sorted(eng):
    if b > max(list(sat) + list(win) + [0]):
        break
    s, w, e = sat.get(b), win.get(b), eng[b]
    f = lambda r, k, fmt: (fmt.format(r[k]) if r else '')
    print(f"| {b} | {int(e['nodes']):,} | {int(e['evals']):,} | {f(s, 'conflicts', '{:,.0f}')} | {f(s, 'cpu', '{:.2f}')} | "
          f"{f(w, 'conflicts', '{:,.0f}')} | {f(w, 'branches', '{:,.0f}')} | {f(w, 'cpu', '{:.2f}')} |")

for lo, hi in ((8, 17), (12, 17), (12, 99)):
    print(f'\ngrowth per base, bases {lo} to {hi} (where present):')
    for name, src, key in (('engine nodes', eng, 'nodes'), ('CaDiCaL conflicts', sat, 'conflicts'),
                           ('CaDiCaL CPU', sat, 'cpu'), ('CP-SAT window conflicts', win, 'conflicts'),
                           ('CP-SAT window branches', win, 'branches'), ('CP-SAT window CPU', win, 'cpu')):
        bs = [b for b in sorted(src) if lo <= b <= hi and src[b][key] > 0]
        if len(bs) >= 3:
            print(f'  {name}: {growth(bs, [math.log(src[b][key]) for b in bs]):.2f} (bases {bs[0]}-{bs[-1]})')

print('\nconflicts per engine node:')
for b in sorted(eng):
    parts = []
    if b in sat:
        parts.append(f"CaDiCaL {sat[b]['conflicts'] / eng[b]['nodes']:.0f}")
    if b in win:
        parts.append(f"CP-SAT window {win[b]['conflicts'] / eng[b]['nodes']:.2f}")
    if parts:
        print(f'  {b}: ' + ', '.join(parts))
