"""abc bounds for 3-digit strings with one large digit (round 6, question 102).

Completing the square (Theorem 25.7) gives U^2 = N + R, N = 4 l w(x), with l the
leading digit and R != 0 outside the family (i). For a coprime triple the
explicit form c < rad(abc)^(7/4) (Laishram and Shorey, from Baker's explicit
abc conjecture) gives, after removing g = gcd(N, R) (section 4 of the draft),

    log N < 7 log 2 + 14 log(rad(N) |R|).

The script prints, for x^x (either convention) and for x! (either
convention), the largest x allowed in each position when the two other digits
are at most B, and the largest B for which this x is at most 2000 (the range
of Theorem 25.11 (a)).

    python3 analysis/r6f_abc3.py > analysis/data/r6f_abc3.txt
"""
import math

THETA = 1.01624  # theta(x) < 1.01624 x for x > 0 (Rosser and Schoenfeld 1962)


def logw(x, kind):
    return x * math.log(x) if kind == 'pow' else math.lgamma(x + 1)


def lograd(x, l, kind):
    """log of an upper bound for rad(4 l w(x)); l = 0 means l = x (leading)"""
    if kind == 'pow':
        return math.log(2 * x) + (math.log(l) if l else 0)
    return THETA * x + (math.log(l) if l and l > x else 0)


def logadd(*a):
    m = max(a)
    return m + math.log(sum(math.exp(t - m) for t in a))


def logR(x, B, pos, kind):
    """log of the bound for |R| of Theorem 25.7 (w of a small digit at most w(B))"""
    lwB = B * math.log(B) if kind == 'pow' else math.lgamma(B + 1)
    lx = math.log(x)
    if pos == 'last':  # 4B (2 w(B) + x) + B^2
        return logadd(math.log(8 * B) + lwB, math.log(4 * B) + lx, 2 * math.log(B))
    if pos == 'middle':  # 8B w(B) + x^2
        return logadd(math.log(8 * B) + lwB, 2 * lx)
    return logadd(math.log(8) + lx + lwB, 2 * math.log(B))  # 8 x w(B) + B^2


def allowed(x, B, pos, kind):
    l = 0 if pos == 'leading' else B
    logN = math.log(4) + (math.log(l) if l else math.log(x)) + logw(x, kind)
    return logN < 7 * math.log(2) + 14 * (lograd(x, l, kind) + logR(x, B, pos, kind))


def xmax(B, pos, kind):
    """largest allowed x: coarse geometric scan, then a linear scan of the last step"""
    xc, x = 2, 2.0
    while x < 1e15:
        if allowed(int(x), B, pos, kind):
            xc = int(x)
        x = x * 1.01 + 1
    best = xc
    for y in range(xc, int(xc * 1.01) + 3):
        if allowed(y, B, pos, kind):
            best = y
    return best


def main():
    print("# largest x allowed by c < rad^(7/4), two other digits <= B")
    print("# weight B last middle leading")
    for kind in ('pow', 'fact'):
        for B in (1, 2, 5, 10, 20, 50, 100, 150, 200, 201, 202, 210, 500, 1000):
            row = [xmax(B, pos, kind) for pos in ('last', 'middle', 'leading')]
            print(f"{'x^x' if kind == 'pow' else 'x!'} {B} {row[0]} {row[1]} {row[2]}  ratio max/B {max(row) / B:.2f}")
    # the largest B with every position at most 2000, for x^x
    B = 1
    while max(xmax(B + 1, pos, 'pow') for pos in ('last', 'middle', 'leading')) <= 2000:
        B += 1
    print(f"# x^x: positions at B = {B}: " + str([xmax(B, pos, 'pow') for pos in ('last', 'middle', 'leading')]))
    print(f"# x^x: largest B with x_max <= 2000 in every position: {B}")


if __name__ == '__main__':
    main()
