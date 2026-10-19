"""Round 5, families: 3-digit solutions under 0^0 = 1 up to the base of (1,6,46666).

Runs r5f_sieve3.c on
  (a) every string with two digits <= B and one digit <= X (three runs, one
      per position of the large digit), and
  (b) every string with all digits <= N,
and checks each survivor exactly: D = 4p(F - r) + q^2 must be a square s^2,
b = (s - q)/(2p) an integer, and b larger than every digit.

Why X = 46,700 suffices. Let b* = 46666^23333 - 3. A solution in a base
b < b* has F < (p+1) b^2 <= (M+1) b*^2 for its largest digit M, and F >= M^M.
So M^M / (M+1) < b*^2, and the script prints the largest such M.

Why (b) covers small bases. If M > N, then b^2 > M^M / (M+1) >=
(N+1)^(N+1) / (N+2), so every base below that bound is covered by (b).

    python3 analysis/r5f_sieve3.py B X N > analysis/data/r5f_sieve3.txt
"""
import math
import os
import subprocess
import sys
import tempfile

import gmpy2

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))


def w(d):
    return 1 if d == 0 else gmpy2.mpz(d) ** d


def build():
    tmp = os.environ.get('R5F_TMP', tempfile.gettempdir())
    exe = os.path.join(tmp, 'r5f_sieve3')
    subprocess.run(['gcc', '-O3', '-march=native', '-o', exe, os.path.join(HERE, 'r5f_sieve3.c')], check=True)
    return exe


def run(exe, mode, a, b, c):
    res = subprocess.run([exe, mode, str(a), str(b), str(c)], capture_output=True, text=True, check=True)
    sys.stdout.write(res.stderr)
    out = []
    for line in res.stdout.split('\n'):
        if line.strip():
            out.append(tuple(int(v) for v in line.split()))
    return out


def exact(s):
    p, q, r = s
    F = w(p) + w(q) + w(r)
    D = 4 * p * (F - r) + q * q
    if not gmpy2.is_square(D):
        return 'not a square'
    root = gmpy2.isqrt(D)
    if (root - q) % (2 * p):
        return 'D square, root not integral'
    b = (root - q) // (2 * p)
    if b <= max(s):
        return f'D square, root {int(b)} <= largest digit'
    assert p * b * b + q * b + r == F
    return ('solution', b)


def main():
    B, X, N = (int(v) for v in sys.argv[1:4])
    lbstar2 = 2 * (23333 * math.log(46666))  # log of b*^2, up to a relative 10^-100
    M = 2
    while M * math.log(M) - math.log(M + 1) < lbstar2:
        M += 1
    print(f"# largest digit of a solution in a base below b* = 46666^23333 - 3: M <= {M - 1}")
    assert X >= M - 1
    lcube = ((N + 1) * math.log10(N + 1) - math.log10(N + 2)) / 2
    print(f"# part (b) covers every base below 10^{lcube:.1f}")
    exe = build()
    surv = set()
    surv |= set(run(exe, 'last', B, B, X))
    surv |= set(run(exe, 'mid', B, X, B))
    surv |= set(run(exe, 'lead', X, B, B))
    surv |= set(run(exe, 'last', N, N, N))
    print(f"# distinct survivors: {len(surv)}")
    sols = []
    kinds = {}
    for s in sorted(surv):
        e = exact(s)
        if isinstance(e, tuple):
            sols.append((s, e[1]))
        else:
            key = 'D square, root <= largest digit' if '<=' in e else e
            kinds[key] = kinds.get(key, 0) + 1
    for k, v in sorted(kinds.items()):
        print(f"# survivors that are not solutions: {k}: {v}")
    print("# solutions (digits, base or log10 of base):")
    for s, b in sorted(sols, key=lambda t: t[1]):
        bs = str(int(b)) if b < 10 ** 30 else f"10^{float(gmpy2.log10(b)):.4f}"
        print(f"  {s} base {bs}")


if __name__ == '__main__':
    main()
