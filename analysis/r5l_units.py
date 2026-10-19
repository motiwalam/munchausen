"""Question 78: the law of the work-unit sizes of an exact run.

Usage:
  python r5l_units.py run B [--unit-depth U]       run `fast search B -j 1 --unit-stats`
                                                     into data/r5l_units_b<B>_u<U>.txt
  python r5l_units.py report B [B ...] [--unit-depth U]
  python r5l_units.py summary B [B ...]            one table row per base (one base: per unit depth)

`run` also records the nodes that build the unit list (a shard with no
units), so that the per-unit counts are exact. `report` prints, per base:
the number of units, the share of the largest unit and of the top 1%, the
quantiles of log10(nodes), a Hill estimate of the tail index, the share of
the variance of ln(nodes) explained by the unit type (digits, free slots,
known digits), list-scheduling makespans without splitting inside a unit,
the balance of --shard splits, and the error of a time estimate from one
shard.
"""
import argparse
import math
import os
import re
import statistics


def _sd(xs):
    m = sum(xs) / len(xs)
    return math.sqrt(sum((x - m) ** 2 for x in xs) / len(xs))
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
FAST = os.path.join(HERE, '..', 'fast', 'target', 'release', 'fast')
DATA = os.path.join(HERE, 'data')


def path(b, u):
    return os.path.join(DATA, f'r5l_units_b{b}_u{u}.txt')


def run(b, u):
    p = subprocess.run([FAST, 'search', str(b), '--unit-depth', str(u), '--shard', '999999/1000000', '-j', '1'],
                       capture_output=True, text=True, check=True)
    gen = int(re.search(r'(\d+) nodes', p.stderr).group(1))
    out = path(b, u)
    p = subprocess.run([FAST, 'search', str(b), '--unit-depth', str(u), '-j', '1', '--unit-stats', out + '.tmp'],
                       capture_output=True, text=True, check=True)
    total = int(re.search(r'(\d+) nodes', p.stderr).group(1))
    m = re.search(r'done in ([0-9.]+)s', p.stderr)
    with open(out + '.tmp') as f:
        body = f.read()
    with open(out, 'w') as f:
        f.write(f'# base {b} unit_depth {u} gen_nodes {gen} total_nodes {total} wall_s {m.group(1) if m else "?"}\n')
        f.write('# unit digits k free known start_s end_s cumulative_nodes thread\n')
        f.write(body)
    os.remove(out + '.tmp')
    print(open(out).readline().strip())


def load(b, u):
    rows = []
    p = path(b, u)
    import gzip
    opener = (lambda: gzip.open(p + '.gz', 'rt')) if not os.path.exists(p) else (lambda: open(p))
    with opener() as f:
        head = f.readline().split()
        gen, total = int(head[6]), int(head[8])
        for line in f:
            if line.startswith('#'):
                continue
            i, d, k, rf, known, t0, t1, cum, th = line.split()
            rows.append(dict(i=int(i), d=int(d), k=int(k), rf=int(rf), known=int(known),
                             t=float(t1) - float(t0), cum=int(cum)))
    rows.sort(key=lambda r: r['cum'])
    prev = gen
    for r in rows:
        r['nodes'] = r['cum'] - prev
        prev = r['cum']
    assert prev == total, (prev, total)
    rows.sort(key=lambda r: r['i'])
    return rows, gen, total


def makespan(sizes, P):
    """List scheduling in unit order: each free thread takes the next unit."""
    import heapq
    h = [0.0] * P
    for s in sizes:
        t = heapq.heappop(h)
        heapq.heappush(h, t + s)
    return max(h)


def hill(xs, frac):
    xs = sorted(xs, reverse=True)
    k = max(5, int(len(xs) * frac))
    xk = xs[k]
    return k / sum(math.log(x / xk) for x in xs[:k])


def report(b, u):
    rows, gen, total = load(b, u)
    n = [r['nodes'] for r in rows]
    tot = sum(n)
    U = len(n)
    srt = sorted(n, reverse=True)
    top1 = sum(srt[:max(1, U // 100)]) / tot
    lg = sorted(math.log10(x) for x in n)
    q = lambda p: lg[min(U - 1, int(p * U))]
    ln = [math.log(x) for x in n]
    mu, sd = statistics.mean(ln), statistics.pstdev(ln)
    cv = statistics.pstdev(n) / statistics.mean(n)
    # variance of ln(nodes) explained by the unit type
    groups = {}
    for r in rows:
        groups.setdefault((r['d'], r['rf'], r['known']), []).append(math.log(r['nodes']))
    within = sum(sum((x - statistics.mean(g)) ** 2 for x in g) for g in groups.values()) / U
    expl = 1 - within / (sd ** 2)
    print(f'## base {b}, unit depth {u}: {U} units, {tot} nodes in units, {gen} to build them')
    print(f'largest unit {srt[0] / tot:.4f} of the work, top 1% of units {top1:.3f}, CV {cv:.2f}')
    print(f'log10(nodes): median {q(0.5):.2f}, 90% {q(0.9):.2f}, 99% {q(0.99):.2f}, 99.9% {q(0.999):.2f}, max {lg[-1]:.2f}; '
          f'ln: mean {mu:.2f}, sd {sd:.2f}')
    print(f'Hill tail index: top 1% {hill(n, 0.01):.2f}, top 5% {hill(n, 0.05):.2f}')
    print(f'unit type (digits, free slots, known digits): {len(groups)} types, explains {expl:.2f} of var ln(nodes); '
          f'within-type sd of ln {math.sqrt(within):.2f}')
    for P in (8, 64, 512):
        ms = makespan(n, P)
        print(f'  {P} threads, no splitting: makespan / (total/P) = {ms / (tot / P):.3f}')
    for S in (3, 16, 64):
        sh = [sum(n[i::S]) for i in range(S)]
        print(f'  --shard x/{S}: max shard / mean = {max(sh) / (tot / S):.3f}; '
              f'estimate of the total from one shard: rel. sd {statistics.pstdev(sh) / statistics.mean(sh):.3f}, '
              f'worst {max(abs(x * S / tot - 1) for x in sh):.3f}')
    return rows


def summary(pairs):
    """One table row per (base, unit depth)."""
    print('| b | depth | units | nodes | largest unit | top 1% of units | sd of ln(nodes) | type explains | within-type sd | '
          'makespan 64 / 512 threads | 16 / 64 shards, max / mean |')
    print('|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for b, u in pairs:
        rows, gen, total = load(b, u)
        n = [r['nodes'] for r in rows]
        tot, U = sum(n), len(n)
        srt = sorted(n, reverse=True)
        ln = [math.log(x) for x in n]
        sd = _sd(ln)
        groups = {}
        for r in rows:
            groups.setdefault((r['d'], r['rf'], r['known']), []).append(math.log(r['nodes']))
        within = sum(len(g) * _sd(g) ** 2 for g in groups.values()) / U
        ms = [makespan(n, P) / (tot / P) for P in (64, 512)]
        sh = [max(sum(n[i::S]) for i in range(S)) / (tot / S) for S in (16, 64)]
        print(f'| {b} | {u} | {U:,} | {total:,} | {srt[0] / tot:.4f} | {sum(srt[:max(1, U // 100)]) / tot:.2f} | {sd:.2f} | '
              f'{1 - within / sd ** 2:.2f} | {math.sqrt(within):.2f} | {ms[0]:.2f} / {ms[1]:.2f} | {sh[0]:.2f} / {sh[1]:.2f} |')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('what')
    ap.add_argument('bases', type=int, nargs='+')
    ap.add_argument('--unit-depth', type=int, default=4)
    a = ap.parse_args()
    if a.what == 'summary':
        pairs = [(b, a.unit_depth) for b in a.bases]
        if len(a.bases) == 1:
            pairs = [(a.bases[0], u) for u in range(2, 9) if os.path.exists(path(a.bases[0], u)) or os.path.exists(path(a.bases[0], u) + '.gz')]
        summary(pairs)
        return
    for b in a.bases:
        if a.what == 'run':
            run(b, a.unit_depth)
        else:
            report(b, a.unit_depth)


if __name__ == '__main__':
    main()
