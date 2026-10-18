"""Question 46: prefixes whose free last digit is excluded by 81 or by 125.

A prefix (s_1, ..., s_(k-1)) with A(r) = sum s_i r^(k-i) and weight F0 has
no solution (prefix, x) in any base if A(r) - F0 mod q avoids T(q) for every
residue r (Theorem 15.13 for q = 27; Corollaries 2.6 and 2.7 of the round 3
draft for q = 81 and 125). The script counts such prefixes with small
digits, lists the first ones that 81 excludes but 27 does not, finds prefixes
excluded by 125, and checks a few of them directly: for each last digit x
up to XMAX it finds the real root of Q_s and checks that it is not an
integer above the digits.

usage: python3 analysis/r3nt_cover_examples.py
"""
import itertools
import sys

XMAX = 1500


def T(q, p):
    e = 0
    t = q
    while t > 1:
        t //= p
        e += 1
    return {(pow(x, x, q) - x) % q for x in range(1, q * (p - 1) + e + 1)}


T27, T81, T125 = T(27, 3), T(81, 3), T(125, 5)


def vals(prefix, q, m=1):
    F0 = sum(pow(d, d, q) if d else m for d in prefix) % q
    out = set()
    for r in range(q):
        v = 0
        for d in prefix:
            v = (v * r + d) % q
        out.add((v * r - F0) % q)
    return out


def excluded(prefix, q, Tq, m=1):
    return not (vals(prefix, q, m) & Tq)


def is_solution_somewhere(ds, m=1):
    """Exact test: is the digit string ds a solution in some base?"""
    k = len(ds)
    F = sum(d ** d if d else m for d in ds)
    lo = max(ds) + 1

    def val(b):
        v = 0
        for d in ds:
            v = v * b + d
        return v
    if val(lo) > F:
        return False
    hi = lo
    while val(hi) < F:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if val(mid) <= F:
            lo = mid
        else:
            hi = mid
    return val(lo) == F


def check_direct(prefix):
    for x in range(1, XMAX + 1):
        if is_solution_somewhere(list(prefix) + [x]):
            return x
    return None


def main():
    for k, M in ((3, 40), (4, 12), (5, 7)):
        n27 = n81 = n125 = tot = 0
        first81 = []
        first125 = []
        for prefix in itertools.product(range(1, M + 1), repeat=k - 1):
            tot += 1
            a = excluded(prefix, 27, T27)
            b = excluded(prefix, 81, T81)
            c = excluded(prefix, 125, T125)
            n27 += a
            n81 += b
            n125 += c
            if b and not a and len(first81) < 6:
                first81.append(prefix)
            if c and len(first125) < 6:
                first125.append(prefix)
        print(f'k = {k}, prefix digits 1..{M}: {tot} prefixes; excluded by 27: {n27}, '
              f'by 81: {n81}, by 125: {n125}')
        print(f'   first excluded by 81 but not by 27: {first81}')
        print(f'   first excluded by 125: {first125}')
        sys.stdout.flush()
    # prefixes with A(r) == 0 mod 5 for all r: s_1 r^5 + ... + s_5 r with
    # s_1 == 1, s_5 == 4 and the middle digits == 0 mod 5
    hits = []
    for mid in itertools.product((5, 10, 15, 20), repeat=3):
        for s1 in (1, 6, 11):
            for s5 in (4, 9, 14):
                pre = (s1,) + mid + (s5,)
                if excluded(pre, 125, T125):
                    hits.append(pre)
    print(f'k = 6, prefixes (s1, s2, s3, s4, s5) with s1 == 1, s5 == 4 mod 5 and the rest '
          f'in {{5,10,15,20}}: {len(hits)} excluded by 125; first: {hits[:5]}')
    tests = []
    for k, M in ((3, 40), (4, 12)):
        for prefix in itertools.product(range(1, M + 1), repeat=k - 1):
            if excluded(prefix, 81, T81) and not excluded(prefix, 27, T27):
                tests.append(prefix)
                break
    tests += hits[:2]
    for pre in tests:
        x = check_direct(pre)
        print(f'direct check of {pre} + (x) for 1 <= x <= {XMAX}: '
              f'{"no solution" if x is None else "SOLUTION at x = %d" % x}')


if __name__ == '__main__':
    main()
