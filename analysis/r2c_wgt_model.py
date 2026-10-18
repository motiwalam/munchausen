# Copied unchanged from analysis/wgt_model.py of branch q-weights (commit 2e67477),
# so that the round-2 scripts run on this branch.
"""The refined model of chapter 5 for general digit weights.

`weights` reproduces `search::weights` of the Rust engine exactly: x^(x+t),
x!, the pseudo-random perturbation of `--perturb`, and the residues forced by
`--keep-residues` and `--set-residue`. `expected` estimates, by sampling, the
expected number of d-digit solutions with these weights, in the basic model
and in the refined model (the digit-sum identity modulo b-1).

    python3 wgt_model.py check      compare the weights with the engine's
"""
import math
import numpy as np

M64 = (1 << 64) - 1


def _splitmix_limbs(state, count):
    out = []
    for _ in range(count):
        state = (state + 0x9E3779B97F4A7C15) & M64
        z = state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & M64
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & M64
        out.append((z ^ (z >> 31)) & 0xFFFFFFFF)
    return out


def weights(b, shift=0, factorial=False, perturb=0, keep_residues=False,
            set_residue=None, zero=1):
    """(w, zw): w[x] for x >= 1 (w[0] = 0) and the weight of 0 in the two
    conventions, exactly as the engine computes them."""
    if factorial:
        w = [0] + [math.factorial(x) for x in range(1, b)]
    else:
        w = [0] + [x ** (x + shift) for x in range(1, b)]
    if perturb:
        for j in range(2, b):
            room = w[j] // 4 + 1
            state = perturb ^ (b << 32) ^ ((j * 0x9E3779B97F4A7C15) & M64)
            limbs = _splitmix_limbs(state, room.bit_length() // 32 + 2)
            delta = sum(v << (32 * i) for i, v in enumerate(limbs)) % room
            if keep_residues:
                step = 2 * (b - 1)
                delta = delta // step * step
            w[j] += delta
    if set_residue is not None:
        m = b - 1
        for j in range(1, b):
            w[j] += ((j + set_residue) % m - w[j] % m) % m
    return w, (0, zero)


def expected(b, d, w, z, samples=200_000, rng=None, residues=None):
    """Monte Carlo estimate of E_d for weights w (w[0] ignored) and weight z
    of the digit 0. Returns (basic, refined, standard error of refined).

    residues: the residues u(x) = w(x) - x modulo b-1 for the refined model;
    by default they come from w and z. Pass a list to model perturbed weights
    whose residues are unknown, or None-like random draws.
    """
    rng = rng or np.random.default_rng(1)
    m = b - 1
    scale = float(b) ** (d - 1)
    wf = np.array([z / scale] + [w[x] / scale for x in range(1, b)])
    if residues is None:
        residues = [(z if x == 0 else w[x] - x) % m for x in range(b)]
    u = np.array(residues, dtype=np.int64)
    hits_basic = hits_ref = 0
    done = 0
    while done < samples:
        n = min(50_000, samples - done)
        counts = rng.multinomial(d - 1, np.full(b, 1.0 / b), size=n)
        lead = rng.integers(1, b, size=n)
        counts[np.arange(n), lead] += 1
        f = counts @ wf
        ok = (f >= 1.0) & (f < b)
        hits_basic += int(np.count_nonzero(ok))
        hits_ref += int(np.count_nonzero(ok & ((counts @ u) % m == 0)))
        done += n
    return hits_basic / samples, hits_ref * m / samples, math.sqrt(hits_ref) * m / samples


def model_counts(b, w, zw, dmin=2, samples=100_000, seed=1):
    """For every d from dmin to the length bound: (basic, refined 0^0 = zw[0],
    refined 0^0 = zw[1]), from one sample of digit strings per d."""
    rng = np.random.default_rng(seed + 1000 * b)
    m = b - 1
    out = {}
    for d in range(max(2, dmin), max_len(b, w, zw[1]) + 1):
        scale = float(b) ** (d - 1)
        wf = [np.array([z / scale] + [w[x] / scale for x in range(1, b)]) for z in zw]
        u = [np.array([(z if x == 0 else w[x] - x) % m for x in range(b)], dtype=np.int64) for z in zw]
        basic = 0
        ref = [0, 0]
        done = 0
        while done < samples:
            n = min(50_000, samples - done)
            counts = rng.multinomial(d - 1, np.full(b, 1.0 / b), size=n)
            lead = rng.integers(1, b, size=n)
            counts[np.arange(n), lead] += 1
            for i in (0, 1):
                f = counts @ wf[i]
                ok = (f >= 1.0) & (f < b)
                if i == 0:
                    basic += int(np.count_nonzero(ok))
                ref[i] += int(np.count_nonzero(ok & ((counts @ u[i]) % m == 0)))
            done += n
        out[d] = (basic / samples, ref[0] * m / samples, ref[1] * m / samples)
    return out


def run_fast(b0, b1, flags, fast='../fast/target/release/fast', threads=3):
    """Run the engine; return {(base, mode): [digit tuples]} and the stderr."""
    import re
    import subprocess
    p = subprocess.run(['nice', '-n', '10', fast, 'search', str(b0), str(b1), '-j', str(threads)] + flags,
                       capture_output=True, text=True, check=True)
    res = {}
    for line in p.stdout.splitlines():
        bb, mode, _, sols = line.split(':', 3)
        res[int(bb), int(mode)] = [tuple(int(x) for x in s.split(',') if x != '')
                                  for s in re.findall(r'\(([^)]*)\)', sols)]
    return res, p.stderr


def max_len(b, w, z=1):
    top = max(max(w), z, 0)
    d = 1
    while (d + 1) * top >= b ** d:
        d += 1
    return d


if __name__ == '__main__':
    import re
    import subprocess
    import sys
    fast = sys.argv[2] if len(sys.argv) > 2 else '../fast/target/release/fast'
    # every solution the engine prints must satisfy n = F(n) with these weights
    cases = [dict(shift=1), dict(shift=-1), dict(shift=2), dict(factorial=True),
             dict(perturb=3, set_residue=0), dict(perturb=5, set_residue=1),
             dict(perturb=2, keep_residues=True), dict(zero=3), dict(zero=-2)]
    for kw in cases:
        flags = []
        for k, v in kw.items():
            flag = '--' + k.replace('_', '-')
            flags += [flag] if v is True else [flag, str(v)]
        out = subprocess.run([fast, 'search', '10', '16', '-j', '3'] + flags,
                             capture_output=True, text=True, check=True).stdout
        n = 0
        for line in out.splitlines():
            bb, mode, _, sols = line.split(':', 3)
            bb, mode = int(bb), int(mode)
            w, zw = weights(bb, **kw)
            for s in re.findall(r'\(([^)]*)\)', sols):
                digits = [int(x) for x in s.split(',') if x != '']
                val = 0
                for x in digits:
                    val = val * bb + x
                assert val == sum(zw[mode] if x == 0 else w[x] for x in digits), (kw, bb, digits)
                n += 1
        print(kw, n, 'solutions agree')
