"""How often is a base empty (no solution with >= b-6 digits under either
convention)? Compare residue-preserving perturbed weights with the model."""
import math
import subprocess
import sys
from empty_bases import expected_parts

FAST = '../fast/target/release/fast'


def union_count(b, extra):
    p = subprocess.run([FAST, 'search', str(b), '--min-digits', str(b - 6)] + extra, capture_output=True, text=True)
    sols = set()
    for line in p.stdout.splitlines():
        bb, m, n, ns = line.split(':', 3)
        for t in (eval('(' + ns + ',)') if ns.strip() else ()):
            sols.add(tuple(t))
    return len(sols)


b0, b1, seeds = map(int, sys.argv[1:4])
for par in (0, 1):
    exp_empty = obs_empty = runs = 0
    mean_obs = mean_exp = var_obs = 0.0
    counts = []
    for b in range(b0, b1 + 1):
        if b % 2 != par:
            continue
        e = sum(expected_parts(b, d, 40_000) for d in range(b - 6, b + 1))
        union = e[0] + e[1] - e[2]
        for s in range(1, seeds + 1):
            n = union_count(b, ['--perturb', str(1000 + s), '--keep-residues'])
            counts.append(n)
            obs_empty += n == 0
            exp_empty += math.exp(-union)
            mean_exp += union
            runs += 1
    mean = sum(counts) / runs
    var = sum((c - mean) ** 2 for c in counts) / (runs - 1)
    print(f"{'even' if par == 0 else 'odd'} bases {b0}-{b1}, {runs} perturbed runs: empty {obs_empty} "
          f"(Poisson model {exp_empty:.1f}); mean distinct solutions {mean:.2f} (model {mean_exp / runs:.2f}); variance {var:.2f}")
