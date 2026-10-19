"""Summary of the F_q[T] census (question 61), from analysis/data/r3t_ffield_frob.txt.

For each (q, e, convention): number of bases, nontrivial solutions observed,
the basic and refined model totals, and the same split by r = the number of
roots of B - 1 in F_q. Also the dispersion sum (N - E)^2 / E over bases.
usage: python3 r3t_ffield_summary.py [file]
"""
import sys
import re
from collections import defaultdict


def polymod(a, b, q):
    """a mod b over F_q, lists low to high."""
    a = a[:]
    inv = pow(b[-1], q - 2, q)
    while len(a) >= len(b):
        c = a[-1] * inv % q
        sh = len(a) - len(b)
        for i, y in enumerate(b):
            a[sh + i] = (a[sh + i] - c * y) % q
        while a and a[-1] == 0:
            a.pop()
    return a


def omega(code, q, e):
    """number of distinct monic irreducible factors of B - 1 over F_q"""
    from sympy import Poly, symbols
    T = symbols('T')
    b = []
    x = code
    for _ in range(e + 1):
        b.append(x % q)
        x //= q
    b[0] = (b[0] - 1) % q
    f = Poly(list(reversed(b)), T, modulus=q)
    return len(f.factor_list()[1])


def corank(code, q, e):
    """e - rank of D -> sum_j (Frob^j - 1) D_j modulo B - 1 (the free residue dimension)."""
    b = []
    x = code
    for _ in range(e + 1):
        b.append(x % q)
        x //= q
    bm1 = b[:]
    bm1[0] = (bm1[0] - 1) % q
    rows = []
    for j in range(e):
        for t in range(j + 1):
            v = [0] * (t * q ** j + 1)
            v[-1] = 1
            v[t] = (v[t] - 1) % q
            r = polymod(v, bm1, q)
            rows.append(r + [0] * (e - len(r)))
    rank = 0
    for col in range(e):
        piv = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][col], q - 2, q)
        for i in range(len(rows)):
            if i != rank and rows[i][col]:
                c = rows[i][col] * inv % q
                rows[i] = [(u - c * w) % q for u, w in zip(rows[i], rows[rank])]
        rank += 1
    return e - rank

path = sys.argv[1] if len(sys.argv) > 1 else 'analysis/data/r3t_ffield_frob.txt'
rows = defaultdict(list)
cur = None
for line in open(path):
    m = re.match(r'# frob q (\d+) e (\d+) m (\d+)', line)
    if m:
        cur = tuple(map(int, m.groups()))
        continue
    m = re.match(r'base (\S+) code (\d+) irred (\d) roots (\d+) sols (\d+) basic (\S+) refined (\S+)', line)
    if m:
        b, code, irr, r, s, ba, re_ = m.groups()
        rows[cur].append(dict(base=b, code=int(code), irred=int(irr), r=int(r), sols=int(s),
                              basic=float(ba), refined=max(0.0, float(re_)),
                              k=corank(int(code), cur[0], cur[1]),
                              w=omega(int(code), cur[0], cur[1])))

print("| q | e | 0^0 | bases | observed | basic | refined | dispersion |")
print("|---:|---:|---:|---:|---:|---:|---:|---:|")
for key in sorted(rows):
    q, e, m = key
    R = rows[key]
    obs = sum(x['sols'] for x in R)
    ba = sum(x['basic'] for x in R)
    rf = sum(x['refined'] for x in R)
    disp = sum((x['sols'] - x['refined']) ** 2 / x['refined'] for x in R if x['refined'] > 0)
    print(f"| {q} | {e} | {m} | {len(R)} | {obs} | {ba:.1f} | {rf:.1f} | {disp:.1f} |")

print()
print("By r = number of roots of B - 1 in F_q (observed / refined, per base):")
print("| q | e | 0^0 | r | bases | observed per base | refined per base | basic per base |")
print("|---:|---:|---:|---:|---:|---:|---:|---:|")
for key in sorted(rows):
    q, e, m = key
    byr = defaultdict(list)
    for x in rows[key]:
        byr[x['r']].append(x)
    for r in sorted(byr):
        R = byr[r]
        n = len(R)
        print(f"| {q} | {e} | {m} | {r} | {n} | {sum(x['sols'] for x in R)/n:.2f} | "
              f"{sum(x['refined'] for x in R)/n:.2f} | {sum(x['basic'] for x in R)/n:.2f} |")

print()
print("By the corank k of the identity map (free residues q^k): observed, refined, basic * q^k, per base")
print("| q | e | 0^0 | k | bases | observed per base | refined per base | basic * q^k |")
print("|---:|---:|---:|---:|---:|---:|---:|---:|")
for key in sorted(rows):
    q, e, m = key
    byk = defaultdict(list)
    for x in rows[key]:
        byk[x['k']].append(x)
    for k in sorted(byk):
        R = byk[k]
        n = len(R)
        print(f"| {q} | {e} | {m} | {k} | {n} | {sum(x['sols'] for x in R)/n:.2f} | "
              f"{sum(x['refined'] for x in R)/n:.2f} | {sum(x['basic'] for x in R)/n * q**k:.2f} |")

print()
print("Corank k against omega = number of distinct irreducible factors of B - 1:")
for key in sorted(rows):
    q, e, m = key
    if m:
        continue
    pairs = defaultdict(int)
    for x in rows[key]:
        pairs[(x['w'], x['k'])] += 1
    print(f"q {q} e {e}: (omega, k): bases =", dict(sorted(pairs.items())))
