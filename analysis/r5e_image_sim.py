"""Round 5, question 85: does keeping the top digits of S explain the image?

For base b, take every distinct value S(c) over the zero-free multisets c of
1 to b digits (the image under both conventions is the set of multisets of
these values, Proposition 7.1 of the draft). Count the distinct multisets
of digits of these values: that is the true image. Then replace each value
by a random integer with the same number of digits, the same digit sum mod
b-1, and the same top t digits, and count the distinct multisets again
(t = 0 is the class-lumped random mapping on distinct sums). Five seeds.
Output: data/r5e_image_sim.txt.

    python3 r5e_image_sim.py b0 b1
"""
import itertools
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def sums(b):
    w = [x ** x for x in range(1, b)]
    vals = set()

    def rec(i, left, s):
        if i == len(w):
            if s > 0:
                vals.add(s)
            return
        for c in range(left + 1):
            rec(i + 1, left - c, s + c * w[i])
    rec(0, b, 0)
    return np.array(sorted(vals), dtype=np.uint64)


def digits(vals, b, L):
    """Digit matrix, least significant first, L columns."""
    out = np.zeros((len(vals), L), dtype=np.int64)
    v = vals.copy()
    for i in range(L):
        out[:, i] = (v % np.uint64(b)).astype(np.int64)
        v //= np.uint64(b)
    return out


def image_count(dg, lens, b):
    """Distinct multisets: histogram rows plus the length."""
    hist = np.zeros((len(dg), b + 1), dtype=np.int64)
    for i in range(dg.shape[1]):
        present = i < lens
        np.add.at(hist, (np.arange(len(dg))[present], dg[present, i]), 1)
    hist[:, b] = lens
    return len(np.unique(hist, axis=0))


def simulate(dg, lens, b, t, rng):
    q = b - 1
    n, L = dg.shape
    new = dg.copy()
    target = dg.sum(axis=1) % q
    todo = np.ones(n, dtype=bool)
    keep = np.zeros_like(dg, dtype=bool)
    for i in range(L):
        keep[:, i] = (i >= lens - t) | (i >= lens)
    while todo.any():
        idx = np.nonzero(todo)[0]
        r = rng.integers(0, b, size=(len(idx), L))
        cand = np.where(keep[idx], dg[idx], r)
        # leading digit nonzero when it is randomized
        top = lens[idx] - 1
        lead = cand[np.arange(len(idx)), top]
        ok = (lead > 0) & ((cand * (np.arange(L)[None, :] < lens[idx, None])).sum(axis=1) % q == target[idx])
        new[idx[ok]] = cand[ok]
        todo[idx[ok]] = False
    new[np.arange(L)[None, :] >= lens[:, None]] = 0
    return new


def main():
    b0, b1 = int(sys.argv[1]), int(sys.argv[2])
    out = ["# r5e_image_sim.py: true image against values randomized below the top t digits",
           "# b values true_image | t=0 t=1 t=2 t=3 (mean of 5 seeds)"]
    for b in range(b0, b1 + 1):
        vals = sums(b)
        L = int(np.ceil(np.log(float(vals.max()) + 1) / np.log(b))) + 1
        dg = digits(vals, b, L)
        lens = np.array([len(np.nonzero(r)[0]) and (np.nonzero(r)[0].max() + 1) for r in dg])
        true = image_count(dg, lens, b)
        res = []
        for t in range(4):
            cs = []
            for seed in range(5):
                rng = np.random.default_rng(1000 * b + 10 * t + seed)
                cs.append(image_count(simulate(dg, lens, b, t, rng), lens, b))
            res.append(sum(cs) / len(cs))
        out.append(f"{b} {len(vals)} {true} | " + " ".join(f"{x:.0f}" for x in res))
        print(out[-1], flush=True)
    with open(os.path.join(HERE, 'data', f'r5e_image_sim_{b0}_{b1}.txt'), 'w') as f:
        f.write("\n".join(out) + "\n")


if __name__ == '__main__':
    main()
