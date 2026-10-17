"""Does the arithmetic of x^x matter? Count bulk solutions (d >= b-6) with the
true weights, with randomly perturbed weights, and with perturbed weights that
keep their residues mod 2(b-1); compare with the refined model."""
import subprocess
import sys
from model import expected_refined

FAST = '../fast/target/release/fast'


def count(b, extra):
    p = subprocess.run([FAST, 'search', str(b), '--min-digits', str(b - 6)] + extra, capture_output=True, text=True)
    out = [0, 0]
    for line in p.stdout.splitlines():
        bb, m, n, ns = line.split(':', 3)
        out[int(m)] = int(n)
    return out


b0, b1, seeds = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
tot = {k: [0.0, 0.0] for k in ('model', 'true', 'random', 'residues')}
for b in range(b0, b1 + 1):
    model = [sum(expected_refined(b, d, m, 60_000)[0] for d in range(b - 6, b + 1)) for m in (0, 1)]
    true = count(b, [])
    rnd = [0, 0]
    res = [0, 0]
    for s in range(1, seeds + 1):
        c = count(b, ['--perturb', str(s)])
        rnd = [rnd[i] + c[i] / seeds for i in (0, 1)]
        c = count(b, ['--perturb', str(s), '--keep-residues'])
        res = [res[i] + c[i] / seeds for i in (0, 1)]
    for k, v in (('model', model), ('true', true), ('random', rnd), ('residues', res)):
        tot[k] = [tot[k][i] + v[i] for i in (0, 1)]
    print(f"base {b}: model {model[0]:.2f}/{model[1]:.2f}  true {true[0]}/{true[1]}  random {rnd[0]:.2f}/{rnd[1]:.2f}  residues {res[0]:.2f}/{res[1]:.2f}", flush=True)
print("totals (0^0=0 / 0^0=1):", {k: f"{v[0]:.1f}/{v[1]:.1f}" for k, v in tot.items()})
