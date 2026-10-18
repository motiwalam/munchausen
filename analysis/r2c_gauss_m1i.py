"""Question 43: integers in base -1+i are base -4 numbers in disguise.

    python3 r2c_gauss_m1i.py [N]

Checks, for every integer n with |n| <= N (default 10^6) and for random
integers up to 10^60, that the base -1+i digits of n are the base -4 digits
B_j of n, each written as the block (B mod 2, 0, [B >= 2], [B >= 2]) at
positions 4j to 4j+3. Then the length of a positive n is 8m+1 or 8m+4.
Also lists every Munchausen number of base -1+i under both conventions:
F counts the ones (0^0 = 0) or the digits (0^0 = 1).
"""
import random
import sys


def digits_gauss(a, b):
    """Base -1+i digits of a + bi, least significant first."""
    out = []
    while a or b:
        d = (a + b) % 2
        out.append(d)
        a -= d
        # (a + bi) / (-1 + i) = (a + bi)(-1 - i) / 2 = ((b - a) + (-a - b) i) / 2
        a, b = (b - a) // 2, (-a - b) // 2
    return out


def digits_nega(n, b):
    out = []
    while n:
        r = n % b
        out.append(r)
        n = -((n - r) // b)
    return out


def blocks(n):
    out = []
    for B in digits_nega(n, 4):
        out += [B % 2, 0, B // 2, B // 2]
    while out and out[-1] == 0:
        out.pop()
    return out


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 6
    rng = random.Random(1)
    tests = list(range(-N, N + 1)) + [rng.randrange(-10 ** 60, 10 ** 60) for _ in range(10 ** 4)]
    lens = set()
    for n in tests:
        g = digits_gauss(n, 0)
        assert g == blocks(n), n
        if n > 0:
            lens.add(len(g) % 8)
            assert len(g) % 8 in (1, 4), n
    print(f"checked {len(tests)} integers; lengths of positive ones mod 8: {sorted(lens)}")
    # Munchausen numbers. A solution n = F(n) is a positive integer. If its
    # base -4 representation has J+1 digits (J even), then n > (4^J - 1)/5,
    # while F(n) <= length <= 4J + 4. So J <= 2 and n <= 19 suffice.
    for m in (0, 1):
        sols = []
        for n in range(1, 10 ** 4):
            g = digits_gauss(n, 0)
            f = sum(g) if m == 0 else len(g)
            if f == n:
                sols.append((n, ''.join(map(str, reversed(g)))))
        print(f"0^0 = {m}: " + ', '.join(f"{n} = ({','.join(s)})" for n, s in sols))


if __name__ == '__main__':
    main()
