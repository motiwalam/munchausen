"""Question 42: the negative-base census extended past -35, against the model.

    cd analysis && python3 r2c_nega_compare.py

Adds data/r2c_negabase_census_36_41.txt (r2c_nega_run.py) to the census of
chapter 14 and data/r2c_negamodel_37_41.txt (wld_negamodel.py) to its model,
then runs the tables of wld_negacompare.py. The last part tests the
multiples of 3: empty bases among them against the model, with the three
bases -3, -6, -9 that were named before the first census set aside.
"""
import math
import random
from collections import defaultdict

import wld_negacompare as W

D = "data/"
BASE_MODEL = W.load_model


def load_census():
    sols = defaultdict(list)
    bases = set()
    for fn in ("wld_negabase_census.txt", "r2c_negabase_census_36_41.txt"):
        try:
            lines = open(D + fn).readlines()
        except FileNotFoundError:
            continue
        for line in lines:
            f = line.split()
            if not f:
                continue
            if f[0] == "total":
                bases.add(-int(f[2]))
            if f[0] == "sol":
                b, m = -int(f[2]), int(f[4][3])
                sols[(b, m)].append(tuple(map(int, f[8].split(","))))
    # a base counts only if both conventions are done
    done = defaultdict(int)
    for fn in ("wld_negabase_census.txt", "r2c_negabase_census_36_41.txt"):
        try:
            for line in open(D + fn):
                f = line.split()
                if f and f[0] == "total":
                    done[-int(f[2])] += 1
        except FileNotFoundError:
            pass
    return sorted(b for b in bases if done[b] >= 2), sols


def load_model():
    model = BASE_MODEL()
    try:
        for line in open(D + "r2c_negamodel_37_41.txt"):
            if line.startswith("#"):
                continue
            b, d, e, r0, r1, zf = line.split()
            model.setdefault((int(b), int(d)), (float(e), float(r0), float(r1), float(zf)))
    except FileNotFoundError:
        pass
    return model


def main():
    W.load_census = load_census
    W.load_model = load_model
    W.main()
    bases, sols = load_census()
    model = load_model()
    print()
    print("multiples of 3 against the other bases (the named bases -3, -6, -9 left out)")
    rows = []
    for b in bases:
        e = {m: sum(model[(b, d)][1 + (m == 1)] for d in range(3, b + 2, 2)) for m in (0, 1)}
        zf = sum(model[(b, d)][3] for d in range(3, b + 2, 2))
        p = math.exp(-(e[0] + e[1] - zf))
        empty = not (sols[(b, 0)] or sols[(b, 1)])
        rows.append((b, p, empty))
    for lab, sel in (("multiples of 3, from -12", lambda b: b % 3 == 0 and b >= 12),
                     ("others, from -10", lambda b: b % 3 != 0 and b >= 10)):
        r = [x for x in rows if sel(x[0])]
        obs = sum(1 for x in r if x[2])
        exp = sum(x[1] for x in r)
        random.seed(1)
        hits = sum(1 for _ in range(200000) if sum(random.random() < x[1] for x in r) >= obs)
        print(f"{lab}: {len(r)} bases, empty {obs} {[-x[0] for x in r if x[2]]}, expected {exp:.2f}, "
              f"P(at least {obs}) = {hits / 200000:.3f}")


if __name__ == "__main__":
    main()
