"""Brute-force check of Theorem 35.1 and Corollary 35.2 (docs/library/35-existence.md).

For random multisets of k = 4..8 digits in bases 20..30 and a random q in
3..13 prime to b(b-1), enumerate all arrangements (nonzero leading digit),
and compare max_a |q P(n == a) - 1| with the bounds:

  - conditional on the leading digit x0: Theorem 35.1 with the best m, and
    Corollary 35.2, with gamma computed from the other digits;
  - unconditional: the largest conditional bound of Theorem 35.1.

    python3 r6h_bound_check.py [TRIALS]
"""
import cmath
import math
import random
import sys
from collections import Counter
from itertools import permutations


def gamma_of(digits, q):
    k = len(digits)
    g = 0.0
    for h in range(1, q):
        s = sum(cmath.exp(2j * math.pi * h * x / q) for x in digits)
        g = max(g, abs(s) / k)
    return g


def bounds(digits, q):
    """(Theorem 35.1 with the best m, Corollary 35.2) for the non-leading digits."""
    kp = len(digits)
    g = gamma_of(digits, q)
    best = 1.0
    for m in range(kp // 2 + 1):
        p = 1.0
        for j in range(m):
            rho = min(1.0, (g * kp + 2 * j) / (kp - 2 * j))
            p *= math.sqrt((1 + rho * rho) / 2)
        best = min(best, p)
    cor = math.exp(1 / 8) * math.exp(-(1 - g) ** 2 * kp / 64)
    return (q - 1) * best, (q - 1) * cor


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    rng = random.Random(7)
    cases = viol = 0
    worst_cond = worst_unc = 0.0
    for _ in range(trials):
        b = rng.randint(20, 30)
        qs = [q for q in range(3, 14) if math.gcd(q, b * (b - 1)) == 1]
        if not qs:
            continue
        q = rng.choice(qs)
        k = rng.randint(4, 8)
        digs = [rng.randint(1, b - 1)] + [rng.randint(0, b - 1) for _ in range(k - 1)]
        by_lead = {}
        for p in {p for p in permutations(digs) if p[0] != 0}:
            v = 0
            for x in p:
                v = v * b + x
            by_lead.setdefault(p[0], Counter())[v % q] += 1
        total = Counter()
        bmax = 0.0
        for x0, cnt in by_lead.items():
            n = sum(cnt.values())
            total.update(cnt)
            dev = max(abs(q * cnt[a] / n - 1) for a in range(q))
            rest = list(digs)
            rest.remove(x0)
            thm, cor = bounds(rest, q)
            cases += 1
            if dev > thm + 1e-9 or dev > cor + 1e-9:
                viol += 1
            worst_cond = max(worst_cond, dev / thm)
            bmax = max(bmax, thm)
        n = sum(total.values())
        dev = max(abs(q * total[a] / n - 1) for a in range(q))
        if dev > bmax + 1e-9:
            viol += 1
        worst_unc = max(worst_unc, dev / bmax)
    print(f"conditional cases {cases}, violations {viol}")
    print(f"largest deviation / bound: conditional {worst_cond:.3f}, unconditional {worst_unc:.3f}")


if __name__ == '__main__':
    main()
