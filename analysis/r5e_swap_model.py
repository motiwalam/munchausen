"""Round 5, question 73: the design effect predicted by the swap lemma.

By Lemma 1.1 of the draft, a near-solution n at offset D has a partner at
D + (n' - n) for every rearrangement n' of its digits. So the cluster of a
multiset is fixed by its digits, and for a near-solution picked at random

    phi = E[K^2] / E[K] = 1 + E[number of partners in the offset set].

With uniform low digits (Table 24.6.1) and D uniform over the offset set,
this script computes E[partners] by Monte Carlo over the bottom t digits
(rearrangements of higher digits move n by at least b^t, beyond every
window used here). Families as in r5e_int_offsets.py: std (k = 2j,
j = 1..60) and free (r5e_lib.swap_free_ks). Output:
data/r5e_swap_model.txt.

    python3 r5e_swap_model.py [samples]
"""
import itertools
import os
import random
import sys

from r5e_lib import swap_free_ks

HERE = os.path.dirname(os.path.abspath(__file__))


def partners(digs, b, D, offs):
    """digs: bottom digits, position 0 first. Count distinct rearrangements
    n' != n with D + (n' - n) in offs."""
    n = sum(d * b ** i for i, d in enumerate(digs))
    seen = set()
    cnt = 0
    for p in set(itertools.permutations(digs)):
        if p == tuple(digs) or p in seen:
            continue
        seen.add(p)
        n2 = sum(d * b ** i for i, d in enumerate(p))
        if D + n2 - n in offs:
            cnt += 1
    return cnt


def predict(b, ks, samples, t, rng):
    offs = set((b - 1) * k for k in ks if k > 0)
    lst = sorted(offs)
    tot = 0
    for _ in range(samples):
        digs = [rng.randrange(b) for _ in range(t)]
        D = rng.choice(lst)
        tot += partners(digs, b, D, offs)
    return 1 + tot / samples


def main():
    samples = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rng = random.Random(73)
    lines = ["# r5e_swap_model.py: phi = 1 + E[partners], uniform bottom digits",
             "# b phi_std phi_free"]
    for b in range(12, 33):
        std = [2 * j for j in range(61)]
        free = swap_free_ks(b, 61, even=True)
        t = 4 if (b - 1) * max(free) < b ** 4 else 5
        a = predict(b, std, samples, 4, rng)
        f = predict(b, free, samples, t, rng)
        lines.append(f"{b} {a:.3f} {f:.3f}")
        print(lines[-1], flush=True)
    with open(os.path.join(HERE, 'data', 'r5e_swap_model.txt'), 'w') as fh:
        fh.write("\n".join(lines) + "\n")


if __name__ == '__main__':
    main()
