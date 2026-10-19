"""Question 41: check the factorions with w(0) = 0 with a second engine.

    python3 r2c_fact0_check.py WORLDS b0 b1 > data/r2c_fact0_check.txt

The census of branch q-weights (data/r2c_qw_factorial.txt) comes from
`fast search --factorial`. This runs `worlds lanes B fact0` (an independent
tree search, fast/src/bin/worlds.rs) and, for bases up to 20, `worlds brute`,
and compares the solutions with at least 2 digits under w(0) = 0.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def census():
    out = {}
    for line in open(os.path.join(HERE, 'data', 'r2c_qw_factorial.txt')):
        p = line.split()
        if p and p[0] == 'raw' and p[2] == '0':
            out[int(p[1])] = sorted(s for s in p[4:] if ',' in s)
    return out


def run(worlds, engine, b):
    env = dict(os.environ, RAYON_NUM_THREADS='1')
    o = subprocess.run(['nice', '-n', '10', worlds, engine, str(b), 'fact0'], capture_output=True, text=True,
                       check=True, env=env).stdout
    return sorted(ln.split()[-1] for ln in o.splitlines() if ln.startswith('sol '))


def main():
    worlds, b0, b1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    ref = census()
    for b in range(b0, b1 + 1):
        engines = ['lanes'] + (['brute'] if b <= 20 else [])
        for e in engines:
            got = run(worlds, e, b)
            same = got == ref.get(b)
            print(f"base {b} {e}: {len(got)} solutions, {'same as' if same else 'DIFFERENT from'} fast search: {' '.join(got)}",
                  flush=True)


if __name__ == '__main__':
    main()
