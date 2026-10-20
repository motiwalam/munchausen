"""Round 6, k-length, referee: the census against the complete 4-digit list.

data/k4.txt lists every 4-digit solution in every base up to 10^186.5,
both conventions (section 11.5). Every such solution with three digits at
most B and the fourth digit x <= X must appear as a survivor of the census
for each way of calling one of its digits x. Conversely every census
survivor with x <= 230 lies in a base below 10^186.5, so it must be in the
list or fail the exact test.

usage: r6k_crosscheck.py CENSUSFILE B X
"""
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from r6k_runs import digits_of, solve  # noqa: E402


def main():
    path, B, X = sys.argv[1], int(sys.argv[2]), int(float(sys.argv[3]))
    surv = set()
    for line in open(path):
        if line.startswith("survivor"):
            f = line.split()
            k, j, m = int(f[1]), int(f[2]), int(f[3])
            ds = tuple(map(int, f[4:7]))
            x = int(f[7])
            surv.add((j, m, ds, x))
    known = []
    for line in open(__file__.rsplit("/", 1)[0] + "/data/k4.txt"):
        if line.startswith("#"):
            continue
        k, m, b, s = line.split()
        known.append((int(m), int(b), tuple(map(int, s.split(",")))))
    missing = 0
    expected = 0
    for m, b, s in known:
        for ix in range(4):
            x = s[ix]
            small = s[:ix] + s[ix + 1:]
            if max(small) > B or x > X or x < 1:
                continue
            if m == 0 and ix == 0 and small[:2] == (0, 0) and small[2] in (0, 1):
                continue  # the self-paying patterns are not in the census
            if ix != 0 and small[0] == 0:
                continue
            expected += 1
            key = (3 - ix, m if 0 in small else 1, small, x)
            if key not in surv:
                missing += 1
                print("missing from the census:", m, b, s, "x at index", ix)
    print("known solutions expected in the census: %d, missing: %d" % (expected, missing))
    knownset = {(m, s) for m, b, s in known}
    bad = 0
    nsmall = 0
    for (j, m, ds, x) in sorted(surv):
        if x > 230:
            continue
        nsmall += 1
        s = tuple(digits_of(4, j, ds, x))
        b = solve(list(s), m)
        inlist = (m, s) in knownset
        if (b is not None) != inlist:
            bad += 1
            print("disagreement:", j, m, ds, x, "base", b, "in list", inlist)
    print("survivors with x <= 230: %d, disagreements with the list: %d" % (nsmall, bad))


if __name__ == "__main__":
    main()
