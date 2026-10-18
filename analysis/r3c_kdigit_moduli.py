"""Question 47: which moduli make the kdigit sieve fastest.

Runs fast/target/release/kdigit on one thread with several lists of moduli,
alternating the lists, and prints the survivors and the best CPU time of
`reps` runs per list. Single-thread CPU time is less sensitive to other jobs
on the machine than wall time.

    python3 r3c_kdigit_moduli.py k M reps >> data/r3c_kdigit_moduli.txt
    python3 r3c_kdigit_moduli.py singles "k M" ... > data/r3c_kdigit_singles.txt

The second form prints the share of candidates that each modulus removes
when it is tested first (the 18 primes up to 61 follow it, so the exact
step stays cheap).
"""
import os
import re
import resource
import subprocess
import sys

KDIGIT = os.path.join(os.path.dirname(__file__), '..', 'fast', 'target', 'release', 'kdigit')
PR = [13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]
BIG = [67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127]

LISTS = {
    'primes 2-61 (old)': [2, 3, 5, 7, 11] + PR,
    '4,9,5,7,11 + 13-61': [4, 9, 5, 7, 11] + PR,
    '8,9,5,7,11 + 13-61': [8, 9, 5, 7, 11] + PR,
    '16,27,25,7,11 + 13-61': [16, 27, 25, 7, 11] + PR,
    '32,27,25,7,11 + 13-61': [32, 27, 25, 7, 11] + PR,
    '64,27,25,7,11 + 13-61': [64, 27, 25, 7, 11] + PR,
    '32,81,25,7,11 + 13-61': [32, 81, 25, 7, 11] + PR,
    '32,27,5,7,11 + 13-61': [32, 27, 5, 7, 11] + PR,
    '32,27,25,49,11 + 13-61': [32, 27, 25, 49, 11] + PR,
    '7,11,13,32,27,25 + 17-61': [7, 11, 13, 32, 27, 25] + PR[1:],
    '27,32,25,7,11 + 13-61': [27, 32, 25, 7, 11] + PR,
    '32,27,25,7,11 + 13-61 + 67-127': [32, 27, 25, 7, 11] + PR + BIG,
    '64,81,125,49,121 + 13-61': [64, 81, 125, 49, 121] + PR,
    'default: 32,27,25,49,11 + 13-127': [32, 27, 25, 49, 11] + PR + BIG,
}


def run(k, M, mods):
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run([KDIGIT, str(k), str(M), '--moduli', ','.join(map(str, mods))],
                       capture_output=True, text=True, env=dict(os.environ, RAYON_NUM_THREADS='1'), check=True)
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    m = re.search(r'(\d+) strings, (\d+) passed', p.stderr)
    return after.ru_utime - before.ru_utime, int(m.group(1)), int(m.group(2)), p.stdout


def singles(kms):
    qs = [2, 4, 8, 16, 32, 64, 128, 3, 9, 27, 81, 5, 25, 125, 7, 49, 11, 121, 13, 17, 19, 23, 29, 31, 37,
          41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
    old = [2, 3, 5, 7, 11] + PR
    print("# share of the candidates removed by a modulus tested first; columns: k M q share")
    for km in kms:
        k, M = km.split()
        for q in qs:
            p = subprocess.run([KDIGIT, k, M, '--stats', '--moduli', ','.join(map(str, [q] + old))],
                               capture_output=True, text=True, check=True)
            line = [x for x in p.stderr.splitlines() if x.startswith('# ') and x[2].isdigit()][0]
            print(f"{k} {M} {q} {float(line.split()[-1]):.4f}", flush=True)


def main():
    if sys.argv[1] == 'singles':
        singles(sys.argv[2:])
        return
    k, M, reps = map(int, sys.argv[1:4])
    best = {}
    outs = {}
    for _ in range(reps):
        for name, mods in LISTS.items():
            t, strings, surv, out = run(k, M, mods)
            best[name] = min(best.get(name, 1e9), t)
            outs[name] = (strings, surv, out)
    ref = outs['primes 2-61 (old)']
    print(f"# kdigit {k} {M}, one thread, best user time of {reps} alternating runs")
    print(f"# list | survivors | share passed | user s | speedup over the old list | output equal")
    for name in LISTS:
        strings, surv, out = outs[name]
        print(f"{name} | {surv} | {surv / (2 * strings):.2e} | {best[name]:.3f} | "
              f"{best['primes 2-61 (old)'] / best[name]:.2f} | {out == ref[2]}", flush=True)


if __name__ == '__main__':
    main()
