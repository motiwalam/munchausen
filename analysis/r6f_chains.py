"""Long structured solutions under 0^0 = 1 from Theorem 15.14 (round 6, question 99).

Base b = r^t. A chain u_0 -> u_1 -> ... -> u_j = 0 with u_(i+1) = u_i r^(u_i) mod t
puts c = r^(u_0) at position 0 and r^(u_(i+1)) at position
pi(u_i) = floor(u_i r^(u_i) / t). A self-paying digit r^v (t | v (r^v - 1)) sits
at position v (r^v - 1) / t. A set S of self-paying digits off the chain gives
a solution exactly when the positions differ and the number has c - 1 zeros:

    T = c + j + |S| - 1,   T = the top position used.

For every r (not a perfect power) and t in the given ranges the script finds
all chains with every position at most CAP and every admissible size of S,
and reports the solutions by length L = T + 1 against ln b = t ln r.

    python3 analysis/r6f_chains.py 20000 > analysis/data/r6f_chains.txt
"""
import math
import sys

CAP = 10 ** 6


def chains(r, t):
    lr = math.log(r)
    sp = []  # (position, v)
    v = 1
    while v < t and math.log(v) + v * lr - math.log(t) < math.log(CAP) + 1:
        if (v * (pow(r, v, t) - 1)) % t == 0:
            pos = v * (r ** v - 1) // t
            if 0 < pos <= CAP:
                sp.append((pos, v))
        v += 1
    out = []
    u0 = 1
    while u0 < t and u0 * lr <= math.log(CAP):
        c = r ** u0
        u, pos_list, ok = u0, [], True
        seen = set()
        while u != 0:
            if u in seen or math.log(u) + u * lr - math.log(t) > math.log(CAP) + 1:
                ok = False
                break
            seen.add(u)
            val = u * r ** u
            pos = val // t
            nu = val % t
            if pos == 0 or pos > CAP:
                ok = False
                break
            pos_list.append(pos)
            u = nu
        if ok and len(set(pos_list)) == len(pos_list):
            j = len(pos_list)
            Tc = max(pos_list)
            chain_pos = set(pos_list)
            free = sorted(p for p, _ in sp if p not in chain_pos)
            # top position from the chain
            avail = sum(1 for p in free if p < Tc)
            k = Tc - c - j + 1
            if 0 <= k <= avail:
                out.append((Tc + 1, c, j, k, avail, 'chain top'))
            # top position from a self-paying digit above the chain
            for i, P in enumerate(free):
                if P <= Tc:
                    continue
                k = P - c - j + 1  # size of S, including the top digit
                if 1 <= k <= 1 + i:
                    out.append((P + 1, c, j, k, i, 'self-paying top'))
        u0 += 1
    return out, len(sp)


def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    rs = [r for r in range(2, 41) if all(round(r ** (1 / e)) ** e != r for e in range(2, 6))]
    rs = rs if len(sys.argv) <= 2 else rs[:int(sys.argv[2])]
    print(f"# bases r^t, r in {rs}, 2 <= t <= {T}, positions <= {CAP}")
    print("# r t | length L, c, chain digits j, |S|, self-paying digits available, top | L / ln b")
    best = []
    total = 0
    lens = {}
    for r in rs:
        for t in range(2, T + 1):
            out, nsp = chains(r, t)
            for L, c, j, k, avail, top in out:
                total += 1
                ratio = L / (t * math.log(r))
                best.append((ratio, r, t, L, c, j, k, avail, top))
                lens[L] = lens.get(L, 0) + 1
                if L >= 8:
                    print(f"{r} {t} | {L} {c} {j} {k} {avail} {top} | {ratio:.4f}")
        sys.stdout.flush()
    best.sort(reverse=True)
    print(f"# configurations: {total}")
    print(f"# lengths: {sorted(lens.items())}")
    print("# best by L / ln b:")
    for row in best[:15]:
        print("#   ", row)


if __name__ == '__main__':
    main()
