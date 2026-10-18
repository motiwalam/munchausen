"""Solutions under 0^0 = 1 made of power digits (question 15).

In base b = r^t (r not a perfect power) the digit r^u (0 <= u < t) at
position p has value r^(u + t p) and weight r^(u r^u). A solution whose
nonzero digits are all powers of r, with distinct exponents on each side,
is a matching between these exponents. Each weight r^(u r^u) is paid by the
digit r^v at position p with v + t p = u r^u, so v = phi(u) = u r^u mod t
and p = pos(u) = u r^u div t. Following phi gives:

- closed cycles of phi on 1..t-1: self-paying digits (length 1), swaps
  (length 2) and longer chains. Each has balance zero.
- an open chain from a digit c = r^u0 at position 0 to a digit 1 (u = 0).
  Its balance is r^u0 - 1 on the value side.

Under 0^0 = 1 every zero weighs 1, so a solution is one open chain plus a
set of closed cycles, all on distinct positions, with exactly c - 1 zeros
(Theorem 15.1 in the draft). The script enumerates these for bases r^t and
counts them per base. It checks each one by exponent bookkeeping, and with
exact integers when the number has at most 3000 digits.

Carries (two equal exponents, possible for r = 2) are not considered, so
the counts are lower bounds for N_1(b).

usage: python3 analysis/dyn_power_digits.py <rmax> <tmax>
"""
import sys
from itertools import combinations

import gmpy2


def is_power(r):
    return r > 1 and gmpy2.is_power(r)


def cycles_of(phi, t):
    seen, cyc = set(), []
    for u in range(1, t):
        path, x = [], u
        while x not in seen and x not in path and x != 0:
            path.append(x)
            x = phi[x]
        if x in path:
            cyc.append(path[path.index(x):])
        seen.update(path)
    return cyc


def placements_of_cycle(cy, pos):
    """Digit exponent -> position: u sits where its predecessor's weight is paid."""
    out = []
    for i, u in enumerate(cy):
        pred = cy[i - 1]
        out.append((u, pos[pred]))
    return out


def chain_from(u0, phi, pos):
    """Placements of the open chain from u0 at position 0, or None."""
    pl = [(u0, 0)]
    seen = {u0}
    u = u0
    while True:
        v, p = phi[u], pos[u]
        pl.append((v, p))
        if v == 0:
            return pl
        if v in seen:
            return None
        seen.add(v)
        u = v


def exact_check(r, t, pl):
    b = r ** t
    top = max(p for _, p in pl)
    if top > 3000:
        return None
    digits = [0] * (top + 1)
    for u, p in pl:
        digits[p] = r ** u
    n = sum(d * b ** p for p, d in enumerate(digits))
    F = sum(d ** d if d else 1 for d in digits)
    return n == F


def search(r, t):
    phi = [(u * r ** u) % t for u in range(t)]
    pos = [(u * r ** u) // t for u in range(t)]
    cycles = cycles_of(phi, t)
    cyc_pl = [placements_of_cycle(cy, pos) for cy in cycles]
    sols = []
    for u0 in range(0, t):
        ch = [(0, 0)] if u0 == 0 else chain_from(u0, phi, pos)
        if ch is None:
            continue
        cpos = [p for _, p in ch]
        if len(set(cpos)) != len(cpos) or any(p == 0 for p in cpos[1:]):
            continue
        c = r ** u0
        usable = [pl for pl in cyc_pl if all(p >= 1 for _, p in pl)
                  and not (set(p for _, p in pl) & set(cpos))]
        if len(usable) > 18:
            usable = usable[:18]
        for k in range(len(usable) + 1):
            for sub in combinations(range(len(usable)), k):
                pl = list(ch)
                ps = set(cpos)
                ok = True
                for i in sub:
                    for u, p in usable[i]:
                        if p in ps:
                            ok = False
                        ps.add(p)
                        pl.append((u, p))
                if not ok:
                    continue
                top = max(ps)
                zeros = top + 1 - len(pl)
                if zeros == c - 1 and len(pl) >= 2:
                    sols.append(pl)
    return cycles, sols


def main():
    rmax, tmax = int(sys.argv[1]), int(sys.argv[2])
    best = []
    total = 0
    for r in range(2, rmax + 1):
        if is_power(r):
            continue
        for t in range(2, tmax + 1):
            cycles, sols = search(r, t)
            if not sols:
                continue
            total += len(sols)
            checks = [exact_check(r, t, pl) for pl in sols]
            if any(c is False for c in checks):
                print('  EXACT CHECK FAILED', r, t)
            best.append((len(sols), r, t))
            for pl, chk in zip(sols, checks):
                desc = ' '.join(f'{r}^{u}@{p}' for u, p in sorted(pl, key=lambda x: -x[1]))
                top = max(p for _, p in pl)
                print(f'base {r}^{t}: {top + 1} digits: {desc}; exact check: {chk}')
    best.sort(reverse=True)
    print(f'{total} power-digit solutions in bases r^t, r <= {rmax}, t <= {tmax}')
    print('most per base:', best[:10])


if __name__ == '__main__':
    main()
