"""Round 6: how evenly --shard splits a base, by assignment rule.

Usage:
  python r6s_shards.py run B [--unit-depth U]      unit sizes of the current engine into
                                                   data/r6s_units_b<B>_u<U>.txt
  python r6s_shards.py B [B ...] [--unit-depth U] [--r6s]

Reads the unit sizes of data/r5l_units_b<B>_u<U>.txt(.gz) (made by
r5l_units.py run), or with --r6s those of data/r6s_units_b<B>_u<U>.txt. For 16, 64 and 256 shards it prints the largest shard
over the mean for three rules:

  modulo  unit i goes to shard i mod n (the rule of --shard so far);
  lpt     longest first by the predicted size of fast's progress estimate,
          about exp(0.656 rf - 0.44 L) scaled to the share of the digit
          count, each unit to the shard with the least predicted work, in
          the integer arithmetic of `fast search --shard-by size`;
  oracle  longest first by the true size (a lower bound for any rule that
          does not split units).

data/r6s_units_b30_u4.txt.gz holds base 30 at unit depth 4 for the engine
with the residue rule. The file for depth 6 (25 MB) is not in the
repository; `python r6s_shards.py run 30 --unit-depth 6` rebuilds it in
about a minute. FAST in the environment selects the build of `fast`.
"""
import heapq
import math
import sys

import os

import r5l_units
from r5l_units import load

SHARE = [0.205, 0.48, 0.21, 0.068, 0.014, 0.013, 0.005, 0.003, 0.001, 0.0003]


FRAC = [round(2 ** (j / 16) * 2 ** 20) for j in range(16)]
SHARE_PPM = [205_000, 480_000, 210_000, 68_000, 14_000, 13_000, 5_000, 3_000, 1_000, 300]


def predicted(rows, b):
    """The integer weights of shards_by_size in fast/src/main.rs."""
    exps = [(b - r['d'], 15 * r['rf'] - 10 * (r['d'] - r['known'])) for r in rows]
    emax = max(e for _, e in exps)
    raw = []
    for j, e in exps:
        c = (emax - e + 15) // 16
        f = 16 * c - (emax - e)
        raw.append((j, (FRAC[f] << 40) >> min(c, 127)))
    by_j = {}
    for j, w in raw:
        by_j[j] = by_j.get(j, 0) + w
    return [(SHARE_PPM[j] if j < len(SHARE_PPM) else 100) * (w << 20) // max(by_j[j], 1) for j, w in raw]


def lpt(order, n, key):
    h = [(0, s) for s in range(n)]
    out = [0] * len(key)
    for i in sorted(range(len(key)), key=lambda i: (-key[i], i)):
        w, s = heapq.heappop(h)
        out[i] = s
        heapq.heappush(h, (w + key[i], s))
    return out


def balance(sizes, assign, n):
    load = [0] * n
    for x, s in zip(sizes, assign):
        load[s] += x
    return max(load) / (sum(sizes) / n)


def main():
    args = sys.argv[1:]
    u = 4
    if '--r6s' in args or args[0] == 'run':
        args = [a for a in args if a != '--r6s']
        r5l_units.path = lambda b, u: os.path.join(r5l_units.DATA, f'r6s_units_b{b}_u{u}.txt')
    if '--unit-depth' in args:
        i = args.index('--unit-depth')
        u = int(args[i + 1])
        del args[i:i + 2]
    if args[0] == 'run':
        # FAST in the environment picks another build of the engine
        r5l_units.FAST = os.environ.get('FAST', r5l_units.FAST)
        r5l_units.run(int(args[1]), u)
        return
    print('| b | depth | units | shards | modulo | lpt | oracle |')
    print('|---:|---:|---:|---:|---:|---:|---:|')
    for b in map(int, args):
        rows, _, _ = load(b, u)
        sizes = [r['nodes'] for r in rows]
        pred = predicted(rows, b)
        for n in (16, 64, 256):
            mod = [i % n for i in range(len(rows))]
            print(f'| {b} | {u} | {len(rows):,} | {n} | {balance(sizes, mod, n):.2f} | '
                  f'{balance(sizes, lpt(None, n, pred), n):.2f} | {balance(sizes, lpt(None, n, sizes), n):.2f} |')


if __name__ == '__main__':
    main()
