"""Round 4, blocks: every exact self-paying block with small length and digits.

A block is (t, b, m) with t = (t_1, ..., t_L), t_1 >= 1, t_L >= 1, m >= 1,
b > max(t) and

    b^m P_t(b) = F(t),

with the zeros inside t weighing 0^0. Then t followed by any tail u of m
digits with P_u(b) = F(u) is a solution of L + m digits.

Under 0^0 = 0 the block is the solution (t, 0, ..., 0) of kdigit; under
0^0 = 1 it is the string (t, 0, ..., 0) at offset D = -m, because the m
trailing zeros weigh 1 each. So kdigit with --offset 0 and -m finds all
blocks with digits up to M, complete for b^(L+m) <= (M+1)^(M+1).

    python3 r4b_blocks.py > data/r4b_blocks.txt
"""
import os
import subprocess
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
KDIGIT = os.path.join(HERE, '..', 'fast', 'target', 'release', 'kdigit')
THREADS = os.environ.get('RAYON_NUM_THREADS', '4')
# digit bound per total length k = L + m
MK = {2: 400, 3: 150, 4: 80, 5: 40, 6: 24, 7: 16}


def kdigit(k, M, D):
    p = subprocess.run([KDIGIT, str(k), str(M), '--offset', str(D)], capture_output=True, text=True,
                       env=dict(os.environ, RAYON_NUM_THREADS=THREADS), check=True)
    out = []
    for line in p.stdout.splitlines():
        kk, mode, b, ds = line.split()
        out.append((int(mode), int(b), tuple(map(int, ds.split(',')))))
    return p.stderr.strip(), out


def P(t, b):
    v = 0
    for d in t:
        v = v * b + d
    return v


def F(t, mode):
    return sum(mode if d == 0 else d ** d for d in t)


def main():
    blocks = defaultdict(set)   # (L, m, mode) -> {(b, t)}
    print("# exact blocks (t, b, m): b^m P_t(b) = F(t), t_1 >= 1, t_L >= 1")
    for k, M in MK.items():
        for m in range(1, min(3, k - 1) + 1):
            for D, mode in ((0, 0), (-m, 1)):
                head, sols = kdigit(k, M, D)
                print(f"# {head}")
                for md, b, s in sols:
                    if md != mode or any(s[-m:]) or s[k - m - 1] == 0:
                        continue
                    t = s[:k - m]
                    assert b ** m * P(t, b) == F(t, mode)
                    blocks[len(t), m, mode].add((b, t))
    print()
    print("# L m mode digits-up-to complete-for-bases count | bases <= 99 | 100 to 10^6 | above 10^6")
    for (L, m, mode) in sorted(blocks):
        M = MK[L + m]
        s = sorted(blocks[L, m, mode])
        n1 = sum(1 for b, t in s if b <= 99)
        n2 = sum(1 for b, t in s if 100 <= b <= 10 ** 6)
        n3 = sum(1 for b, t in s if b > 10 ** 6)
        print(f"{L} {m} {mode} {M} b^{L + m}<=(M+1)^(M+1) {len(s)} | {n1} | {n2} | {n3}")
    print()
    for (L, m, mode) in sorted(blocks):
        s = sorted(blocks[L, m, mode])
        print(f"## L={L} m={m} 0^0={mode}: {len(s)} blocks")
        for b, t in s:
            tag = 'self-paying digit' if L == 1 else ''
            print(f"{b} {','.join(map(str, t))} {tag}".rstrip())


if __name__ == '__main__':
    main()
