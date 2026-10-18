"""Question 19: perturbed weights with forced residues modulo b-1.

For each base and seed, three weight sets: --perturb s (residues random),
--perturb s --set-residue 0 (w(x) == x mod b-1) and --perturb s
--set-residue 1 (w(x) == x+1 mod b-1). The engine finds every solution; the
refined model, run with the same exact weights, predicts the counts.

    python3 wgt_residue.py b0 b1 seeds > data/wgt_residue.txt
"""
import sys
from collections import Counter
from wgt_model import weights, model_counts, run_fast

b0, b1, seeds = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
VARIANTS = {'random': {}, 'r0': {'set_residue': 0}, 'r1': {'set_residue': 1}}

print("# variant seed base mode: observed nontrivial count, model (refined), observed count by length")
print("# pred variant seed base mode: model by length")
tot = Counter()
for b in range(b0, b1 + 1):
    for s in range(1, seeds + 1):
        for name, kw in VARIANTS.items():
            flags = ['--perturb', str(s)] + (['--set-residue', str(kw['set_residue'])] if kw else [])
            res, _ = run_fast(b, b, flags)
            w, zw = weights(b, perturb=s, **kw)
            # the random variant has random residues: the basic model applies
            mc = model_counts(b, w, zw, dmin=2, samples=30_000, seed=s)
            for mode in (0, 1):
                sols = [t for t in res[b, mode] if len(t) >= 2]
                pred = sum(v[0] if name == 'random' else v[1 + mode] for v in mc.values())
                lens = Counter(b - len(t) for t in sols)
                tot[name, mode, b % 2, 'obs'] += len(sols)
                tot[name, mode, b % 2, 'pred'] += pred
                tot[name, mode, b % 2, 'b-1'] += lens[1]
                tot[name, mode, b % 2, 'pred b-1'] += (mc[b - 1][0] if name == 'random' else mc[b - 1][1 + mode])
                tot[name, mode, b % 2, 'm'] += (b - 1)
                tot[name, mode, b % 2, 'runs'] += 1
                bulk = sum(1 for t in sols if len(t) >= b - 6)
                pbulk = sum(v[0] if name == 'random' else v[1 + mode] for d, v in mc.items() if d >= b - 6)
                tot[name, mode, b % 2, 'bulk'] += bulk
                tot[name, mode, b % 2, 'pred bulk'] += pbulk
                print(f"{name} {s} {b} {mode}: {len(sols)} {pred:.2f} "
                      + " ".join(f"b-{j}:{c}" for j, c in sorted(lens.items())), flush=True)
                print(f"pred {name} {s} {b} {mode} " + " ".join(
                    f"b-{b - d}:{v[0] if name == 'random' else v[1 + mode]:.4f}" for d, v in mc.items()), flush=True)

print("# totals per variant, convention and base parity")
for name in VARIANTS:
    for mode in (0, 1):
        for par in (0, 1):
            k = (name, mode, par)
            print(f"# {name} mode {mode} {'odd' if par else 'even'}: runs {tot[k + ('runs',)]}, "
                  f"sum(b-1) {tot[k + ('m',)]}, obs {tot[k + ('obs',)]}, pred {tot[k + ('pred',)]:.1f}, "
                  f"obs b-1 {tot[k + ('b-1',)]}, pred b-1 {tot[k + ('pred b-1',)]:.1f}, "
                  f"obs d>=b-6 {tot[k + ('bulk',)]}, pred d>=b-6 {tot[k + ('pred bulk',)]:.1f}")
