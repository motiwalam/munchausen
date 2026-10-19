"""k(B) against omega(B - 1) in F_q[T] (question 82).

k(B) is the corank of D -> sum_j (Frob^j - 1) D_j mod (B - 1), with D_j of
degree <= j (Theorem 21.6). omega(B - 1) is computed as the corank of
x -> x^q - x on F_q[T]/(B - 1) (Berlekamp: the fixed ring of Frobenius has
dimension equal to the number of distinct irreducible factors).

usage:
  python3 r5m_kB.py scan Q E        all B of degree E, monic up to scalars
  python3 r5m_kB.py census FILE...  check the k column of r4f census files
"""
import re
import sys
from collections import Counter

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from r4f_lib import trim, padd, pdivmod, decode, pmul


def rank_mod(rows, q):
    rows = [list(r) for r in rows]
    if not rows:
        return 0
    ncol = len(rows[0])
    rank = 0
    for col in range(ncol):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col] % q), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        iv = pow(rows[rank][col], q - 2, q)
        rows[rank] = [x * iv % q for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] % q:
                c = rows[i][col]
                rows[i] = [(x - c * y) % q for x, y in zip(rows[i], rows[rank])]
        rank += 1
    return rank


def vec(p, e):
    p = list(p)
    return p + [0] * (e - len(p))


def mono_mod(deg, M, q):
    """T^deg mod M by repeated squaring"""
    result, base, k = [1], pdivmod([0, 1], M, q)[1], deg
    while k:
        if k & 1:
            result = pdivmod(pmul(result, base, q), M, q)[1]
        base = pdivmod(pmul(base, base, q), M, q)[1]
        k >>= 1
    return result


def k_and_omega(B, q):
    e = len(B) - 1
    M = padd(B, [q - 1], q)
    rows = []
    for j in range(1, e):
        for t in range(j + 1):
            v = padd(mono_mod(t * q ** j, M, q), [0] * t + [q - 1], q)
            rows.append(vec(pdivmod(v, M, q)[1], e))
    k = e - rank_mod(rows, q)
    brows = [vec(pdivmod(padd(mono_mod(t * q, M, q), [0] * t + [q - 1], q), M, q)[1], e) for t in range(e)]
    omega = e - rank_mod(brows, q)
    return k, omega


def factor_degrees(M, q):
    """degrees with multiplicity of the irreducible factors of M (via PARI/GP)"""
    import subprocess
    pol = '+'.join(f'{c}*x^{i}' for i, c in enumerate(M) if c)
    out = subprocess.run(['gp', '-q', '-f'], input=f'f=factormod({pol},{q});print(vector(#f~,i,[poldegree(f[i,1]),f[i,2]]))\n',
                         capture_output=True, text=True).stdout.strip()
    return out


def scan(q, e):
    lo = q ** e
    stats = Counter()
    bad = []
    for c in range(lo, 2 * lo):  # monic B; scaling B changes nothing here
        B = decode(c, q, e + 1)
        k, om = k_and_omega(B, q)
        stats[(k, om)] += 1
        if k != om:
            bad.append(B)
    print(f"q {q} e {e} bases {lo} (k, omega) counts {dict(sorted(stats.items()))}")
    for B in bad:
        M = padd(B, [q - 1], q)
        print(f"  k != omega: B = {B} (low first)  B-1 factor degrees {factor_degrees(M, q)}  k,omega = {k_and_omega(B, q)}")
    return bad


def census(paths):
    for path in paths:
        q, e = map(int, re.search(r'q(\d+)e(\d+)', path).groups())
        n = bad = 0
        for line in open(path):
            m = re.match(r'orbit (\d+) size (\d+) k (\d+)', line)
            if not m:
                continue
            B = decode(int(m.group(1)), q, e + 1)
            k, om = k_and_omega(B, q)
            n += 1
            if k != int(m.group(3)):
                print(f"  {path}: k mismatch at orbit {m.group(1)}: file {m.group(3)}, recomputed {k}")
            if k != om:
                bad += 1
                print(f"  {path}: orbit {m.group(1)} size {m.group(2)} k {k} omega {om} line: {line.strip()}")
        print(f"{path}: {n} orbits, {bad} with k != omega")


if __name__ == '__main__':
    if sys.argv[1] == 'scan':
        scan(int(sys.argv[2]), int(sys.argv[3]))
    else:
        census(sys.argv[2:])
