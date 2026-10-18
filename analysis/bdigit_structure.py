"""Structure of b-digit near-solutions: copies of the digit b-1.

The model says a b-digit number with F(n) of b digits has 3 copies of b-1
in about 80% of cases and 4 or more in about 20%. This counts the copies in
the b-digit n with n - F(n) = j (b-1), j even, against that law.
"""
import random
import subprocess
import sys
from collections import Counter

FAST = '../fast/target/release/fast'


def model_law(b, mode, N=100000, rng=random.Random(1)):
    w = [mode] + [x ** x for x in range(1, b)]
    cc, hits = Counter(), 0
    for _ in range(N):
        s = [rng.randrange(1, b)] + [rng.randrange(b) for _ in range(b - 1)]
        F = sum(w[x] for x in s)
        if b ** (b - 1) <= F < b ** b:
            hits += 1
            cc[min(s.count(b - 1), 5)] += 1
    return hits / N, {k: v / hits for k, v in cc.items()}


if __name__ == '__main__':
    jmax = int(sys.argv[1])
    for b in map(int, sys.argv[2:]):
        for mode in (1, 0):
            seen = Counter()
            offs = 0
            for j in range(2, jmax + 1, 2):
                out = subprocess.run(['nice', '-n', '10', FAST, 'search', str(b), '-j', '2', '-m', str(mode),
                                      '--offset', str(j * (b - 1)), '--min-digits', str(b), '--max-digits', str(b)],
                                     capture_output=True, text=True).stdout
                offs += 1
                for line in out.splitlines():
                    ns = line.split(':', 3)[3]
                    for t in (eval('(' + ns + ',)') if ns.strip() else ()):
                        seen[min(t.count(b - 1), 5)] += 1
            p, law = model_law(b, mode)
            n = sum(seen.values())
            exp = {k: round(p * offs * v, 1) for k, v in sorted(law.items())}
            print(f"base {b}, 0^0={mode}, {offs} offsets: found {n} (model {p * offs:.1f}); copies of b-1 found "
                  f"{dict(sorted(seen.items()))}, model {exp}", flush=True)
