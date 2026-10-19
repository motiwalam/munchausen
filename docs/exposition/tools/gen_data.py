#!/usr/bin/env python3
"""Copy the solution lists of the repository into docs/exposition/data.

Typst can only read files below docs/exposition, so the tables of the
appendix read CSV files that this script writes. Run it from any directory
after the lists in output/ or analysis/data/ change:

    python3 docs/exposition/tools/gen_data.py
"""

import csv
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPO = HERE.parent
REPO = EXPO.parent.parent
OUT = EXPO / "data"


def parse_output_line(line):
    """Parse 'base:conv:count: (d,...), (d,...)' into (base, conv, [tuples])."""
    head, _, rest = line.partition(": ")
    base, conv, _count = head.split(":")
    tuples = re.findall(r"\(([^()]*)\)", rest)
    sols = []
    for t in tuples:
        digits = [int(x) for x in t.split(",") if x.strip() != ""]
        sols.append(digits)
    return int(base), int(conv), sols


def nontrivial(digits):
    return len(digits) >= 2


def read_bases():
    files = [REPO / "output" / "b2-41-0.txt", REPO / "output" / "b2-41-1.txt",
             REPO / "output" / "b43-0.txt", REPO / "output" / "b43-1.txt"]
    rows = []
    for f in files:
        for line in f.read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            base, conv, sols = parse_output_line(line)
            for d in sols:
                if nontrivial(d):
                    rows.append((base, conv, d, "exact"))
    inexact = REPO / "analysis" / "data" / "b44-inexact.txt"
    for line in inexact.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        base, conv, sols = parse_output_line(line)
        for d in sols:
            if nontrivial(d):
                rows.append((base, conv, d, "inexact"))
    big = REPO / "analysis" / "data" / "b39-127-d30.txt"
    for line in big.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        base, conv, sols = parse_output_line(line)
        if base <= 43:
            continue
        for d in sols:
            if nontrivial(d):
                rows.append((base, conv, d, "upto30"))
    rows.sort(key=lambda r: (r[0], r[1], len(r[2]), r[2]))
    return rows


def write_bases(rows):
    with open(OUT / "solutions-by-base.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["base", "conv", "length", "digits", "zeros", "search"])
        for base, conv, d, how in rows:
            w.writerow([base, conv, len(d), ",".join(map(str, d)),
                        d.count(0), how])
    # Counts per base for the exhaustive range.
    counts = {}
    for base, conv, d, how in rows:
        if how != "exact":
            continue
        c = counts.setdefault(base, {"n0": 0, "n1": 0, "shared": set(),
                                     "longest": 0})
        c["n%d" % conv] += 1
        if 0 not in d:
            c["shared"].add(tuple(d))
        c["longest"] = max(c["longest"], len(d))
    with open(OUT / "counts-by-base.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["base", "n0", "n1", "shared", "longest"])
        for base in list(range(2, 42)) + [43]:
            c = counts.get(base, {"n0": 0, "n1": 0, "shared": set(),
                                  "longest": 0})
            w.writerow([base, c["n0"], c["n1"], len(c["shared"]),
                        c["longest"] if c["longest"] else "-"])


def perfect_power(n):
    """Return (r, t) with n = r^t and t maximal, or None if t = 1."""
    best = None
    t = 2
    while (1 << t) <= n:
        r = round(n ** (1.0 / t))
        for cand in (r - 1, r, r + 1):
            if cand >= 2 and cand ** t == n:
                best = (cand, t)
        t += 1
    return best


def base_display(b):
    if b < 10 ** 6:
        return str(b)
    pp = perfect_power(b)
    if pp:
        return "%d^%d" % pp
    return "%d" % b


def is_self_paying_family(digits, b):
    """(x, 0, ..., 0, e) with e in {0, 1} and x b^(k-1) = x^x."""
    k = len(digits)
    x = digits[0]
    if k < 2 or any(digits[1:-1]) or digits[-1] not in (0, 1):
        return False
    return x * b ** (k - 1) == x ** x


def read_short():
    data = REPO / "analysis" / "data"
    sources = [("k3.txt", 3), ("k4.txt", 4), ("k5.txt", 5), ("k6.txt", 6),
               ("r3c_k7_M32.txt", 7), ("r3c_k8_M24.txt", 8)]
    rows = []
    for name, k in sources:
        for line in (data / name).read_text().splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            kk, conv, base, digits = line.split()
            d = [int(x) for x in digits.split(",")]
            b = int(base)
            family = "self-paying" if is_self_paying_family(d, b) else ""
            rows.append((int(kk), int(conv), b, d, family))
    rows.sort(key=lambda r: (r[0], r[1], r[2], r[3]))
    with open(OUT / "short-solutions.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["k", "conv", "base", "base_display", "digits", "family"])
        for k, conv, b, d, family in rows:
            w.writerow([k, conv, b, base_display(b), ",".join(map(str, d)),
                        family])


def read_negabase():
    files = [REPO / "analysis" / "data" / "wld_negabase_census.txt",
             REPO / "analysis" / "data" / "r2c_negabase_census_36_41.txt"]
    lines = []
    for f in files:
        if f.exists():
            lines += f.read_text().splitlines()
    rows = []
    for line in lines:
        if not line.startswith("sol "):
            continue
        parts = line.split()
        base = int(parts[2])
        conv = 1 if parts[4] == "pow1" else 0
        digits = parts[-1]
        rows.append((base, conv, len(digits.split(",")), digits))
    rows.sort(key=lambda r: (-r[0], r[1], r[2], r[3]))
    with open(OUT / "negative-bases.csv", "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["base", "conv", "length", "digits"])
        for r in rows:
            w.writerow(r)


def main():
    OUT.mkdir(exist_ok=True)
    write_bases(read_bases())
    read_short()
    read_negabase()


if __name__ == "__main__":
    main()
