"""Question 75: the entropy bound of Theorem 10.1 for other orders of revealing counts.

A search reveals the counts of a set R of m digit values. In the model, the
interval of S(c) has width about rf * w(u), where u is the largest value not
in R and rf = d (b - m) / b is the number of positions that hold values
outside R. So the unknown suffix has L(u) = min(d, log_b(rf u^u) + 1) digits,
and the node above a planted solution has the law of the suffix counts of
the values in R: m independent Poisson(L / b) counts. Its entropy is
H(R) = m * H(Poisson(L(u) / b)). This is the formula of analysis/exponents.py
with the top m values replaced by any set R.

The script evaluates the peak over the levels m of H(R_m) for several orders,
and checks by brute force for small b that the top values minimize H(R) among
all sets of size m.
"""
import itertools
import math
import random

from exponents import h_poisson


def L_of(b, d, m, u):
    rf = max(1.0, d * (b - m) / b)
    if u <= 1:
        return min(d, math.log(rf) / math.log(b) + 1)
    return min(d, (math.log(rf) + u * math.log(u)) / math.log(b) + 1)


def H_of(b, d, R):
    m = len(R)
    rest = [v for v in range(b) if v not in R]
    if not rest:
        return 0.0
    u = max(rest)
    return m * h_poisson(L_of(b, d, m, u) / b)


def profile(b, order, d=None):
    d = d or b - 1
    R, out = set(), []
    for v in order:
        R.add(v)
        out.append(H_of(b, d, R))
    return out


def orders(b, seed=1):
    rnd = random.Random(seed)
    top = list(range(b - 1, -1, -1))
    mid = sorted(range(b), key=lambda v: (abs(v - b / 2), v))
    shuffled = list(range(b))
    rnd.shuffle(shuffled)
    return {
        'top-down': top,
        'bottom-up': list(range(b)),
        'middle-out': mid,
        'random': shuffled,
        'odd first, each class top-down': [v for v in top if v % 2] + [v for v in top if v % 2 == 0],
        'by residue mod 3, each class top-down': [v for r in (0, 1, 2) for v in top if v % 3 == r],
        'upper half bottom-up, then the lower half top-down': list(range(b // 2, b)) + list(range(b // 2 - 1, -1, -1)),
    }


def brute_check(b):
    """For every m, min over |R| = m of H(R) is reached by the top m values."""
    d = b - 1
    bad = 0
    for m in range(1, b):
        best = min(H_of(b, d, set(R)) for R in itertools.combinations(range(b), m))
        top = H_of(b, d, set(range(b - m, b)))
        if top > best + 1e-12:
            bad += 1
    return bad


if __name__ == '__main__':
    for b in range(4, 15):
        assert brute_check(b) == 0, b
    print('brute force, b = 4..14: the top m values minimize H(R) at every m')
    print()
    print('peak entropy max_m H(R_m) in nats, as a multiple of b, and e^(peak/b)')
    print('| order | b = 40 | b = 100 | b = 1000 |')
    print('|---|---:|---:|---:|')
    for name in orders(40):
        cells = []
        for b in (40, 100, 1000):
            if name == 'random':
                peaks = [max(profile(b, orders(b, s)['random'])) for s in range(20)]
                pk = sum(peaks) / len(peaks)
            else:
                pk = max(profile(b, orders(b)[name]))
            cells.append(f'{pk:.1f} = {pk / b:.3f} b ({math.exp(pk / b):.3f}^b)')
        print(f'| {name} | ' + ' | '.join(cells) + ' |')
    print()
    print('stage at which the largest value b-1 is revealed fixes the peak of every other order;')
    print('before it, u = b-1, L = d and H(R) = m H(Poisson(d/b)):')
    print(f'H(Poisson(1)) = {h_poisson(1.0):.4f}, H(Poisson((b-1)/b)) at b=40: {h_poisson(39 / 40):.4f}')
