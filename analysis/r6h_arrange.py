"""Question 91: how the arrangements of a digit multiset spread modulo q.

For a multiset c of k digits in base b, the arrangements are the distinct
strings with the multiset c and a nonzero leading digit. share(a) is the
fraction of them whose value is == a (mod q). The local factor of c at q in
base b is q * share(F(c) mod q).

Exact computation: the value mod q depends only on how many copies of each
digit sit in each class of positions with the same b^i mod q. A dynamic
program over the digit values distributes the copies over the classes; a
string with class occupancy a[x][u] is counted n_u! / prod_x a[x][u]! times
per class.

    python3 r6h_arrange.py table [N]    > data/r6h_arrange.txt
        for k = 3..12, q in 3,4,5,7,8,9, bases 9..30: N random candidate
        multisets per cell (digits up to X_k(b)), the deviation
        max_a |q share(a) - 1| and the factor q share(F(c)), by the type of
        q in base b (coprime to b(b-1), dividing b - 1, other).
    python3 r6h_arrange.py rho [N]      > data/r6h_arrange_rho.txt
        Proposition 35.3: the mean of N_s(q) (roots of Q_s mod q) over the
        arrangements of c equals the sum over r mod q of share_r(F(c)), and
        its split into r == 1, r == 0 mod p, and the rest.
    python3 r6h_arrange.py resid        > data/r6h_arrange_resid.txt
        the residue factor of the refined model at q | b - 1 for short
        strings: q P(sum g(x) == 0 mod q), k uniform digits (section 35.1.4).
"""
import math
import random
import sys
from functools import lru_cache

QS = (3, 4, 5, 7, 8, 9)
FACT = [math.factorial(i) for i in range(40)]


def xmax(b, k):
    """largest digit x < b with x^x < b^k"""
    x = 1
    while x + 1 < b and (x + 1) ** (x + 1) < b ** k:
        x += 1
    return x


def classes(b, k, q):
    """position classes: list of (u, capacity, top) with u = b^i mod q;
    position k-1 is its own class (top, no zero digit)."""
    cap = {}
    for i in range(k - 1):
        u = pow(b, i, q)
        cap[u] = cap.get(u, 0) + 1
    out = [(u, n, False) for u, n in sorted(cap.items())]
    out.append((pow(b, k - 1, q), 1, True))
    return out


def compositions(c, caps, allow):
    """all vectors a with 0 <= a_i <= caps_i, a_i = 0 where not allow_i, sum c"""
    n = len(caps)

    def rec(i, left):
        if i == n:
            if left == 0:
                yield ()
            return
        hi = min(left, caps[i]) if allow[i] else 0
        for v in range(hi + 1):
            for rest in rec(i + 1, left - v):
                yield (v,) + rest
    return list(rec(0, c))


def shares(counts, b, q):
    """counts: dict digit -> count. Returns list share[a], a mod q."""
    k = sum(counts.values())
    cl = classes(b, k, q)
    us = [u for u, _, _ in cl]
    caps0 = tuple(n for _, n, _ in cl)
    states = {caps0: [0.0] * q}
    states[caps0][0] = 1.0
    for x, c in sorted(counts.items()):
        allow = [not (top and x == 0) for _, _, top in cl]
        new = {}
        for caps, vec in states.items():
            for a in compositions(c, caps, allow):
                wgt = 1.0
                shift = 0
                for ai, u in zip(a, us):
                    wgt /= FACT[ai]
                    shift += ai * u
                shift = (shift * x) % q
                nc = tuple(cp - ai for cp, ai in zip(caps, a))
                tgt = new.get(nc)
                if tgt is None:
                    tgt = new[nc] = [0.0] * q
                for r in range(q):
                    if vec[r]:
                        tgt[(r + shift) % q] += vec[r] * wgt
        states = new
    vec = states[tuple(0 for _ in cl)]
    tot = sum(vec)
    return [v / tot for v in vec]


def qtype(q, b):
    if math.gcd(q, b * (b - 1)) == 1:
        return 'coprime'
    if math.gcd(q, b - 1) > 1 and math.gcd(q, b) == 1:
        return 'shares_b-1'
    return 'shares_b'


def sample(b, k, rng, m):
    X = xmax(b, k)
    s = [rng.randint(1, X)] + [rng.randint(0, X) for _ in range(k - 1)]
    cnt = {}
    for x in s:
        cnt[x] = cnt.get(x, 0) + 1
    F = sum(x ** x if x else m for x in s)
    return cnt, F


def table(N):
    rng = random.Random(91)
    print("# k q type bases cells median_dev p90_dev mean_factor rms(factor-1) share_dev<0.1")
    for k in range(3, 13):
        for q in QS:
            agg = {}
            for b in range(9, 31):
                t = qtype(q, b)
                for _ in range(N):
                    cnt, F = sample(b, k, rng, 1)
                    sh = shares(cnt, b, q)
                    dev = max(abs(q * v - 1) for v in sh)
                    fac = q * sh[F % q]
                    agg.setdefault(t, []).append((dev, fac))
            for t, rows in sorted(agg.items()):
                devs = sorted(d for d, _ in rows)
                facs = [f for _, f in rows]
                n = len(rows)
                med = devs[n // 2]
                p90 = devs[int(0.9 * n)]
                mf = sum(facs) / n
                rms = math.sqrt(sum((f - 1) ** 2 for f in facs) / n)
                small = sum(1 for d in devs if d < 0.1) / n
                print(f"{k} {q} {t} {n // N} {n} {med:.4f} {p90:.4f} {mf:.4f} {rms:.4f} {small:.3f}", flush=True)


def roots_mod(digs, F, q):
    """number of r mod q with P_s(r) == F (mod q)"""
    cnt = 0
    for r in range(q):
        v = 0
        for x in digs:
            v = (v * r + x) % q
        if v == F % q:
            cnt += 1
    return cnt


def rho(N):
    """Proposition 35.3 on random multisets: the mean of N_s(q) over the
    arrangements equals the sum over r mod q of share_r(F(c)). Checked by
    brute force for k <= 6; split by the type of r for k = 3..12."""
    from itertools import permutations
    rng = random.Random(913)
    print("# k q: mean over multisets (b uniform in 9..30) of avg_arr N_s(q) = "
          "r == 1 part + parts with gcd(r, q) > 1 + coprime part; brute-force check error")
    for k in range(3, 13):
        for q in (3, 5, 7, 9):
            tot = [0.0, 0.0, 0.0]
            maxerr = 0.0
            for _ in range(N):
                b = rng.randint(9, 30)
                cnt, F = sample(b, k, rng, 1)
                parts = [0.0, 0.0, 0.0]
                for r in range(q):
                    s = shares(cnt, r, q)[F % q]
                    if r == 1 % q:
                        parts[0] += s
                    elif math.gcd(r, q) > 1:
                        parts[1] += s
                    else:
                        parts[2] += s
                if k <= 6:
                    digs = []
                    for x, c in cnt.items():
                        digs += [x] * c
                    arr = {p for p in permutations(digs) if p[0] != 0}
                    avg = sum(roots_mod(p, F, q) for p in arr) / len(arr)
                    maxerr = max(maxerr, abs(avg - sum(parts)))
                for i in range(3):
                    tot[i] += parts[i]
            chk = f"{maxerr:.1e}" if k <= 6 else "-"
            print(f"{k} {q}: {sum(tot) / N:.4f} = {tot[0] / N:.4f} (r=1) + {tot[1] / N:.4f} (gcd>1) "
                  f"+ {tot[2] / N:.4f} (coprime; {sum(1 for r in range(2, q) if math.gcd(r * (r - 1), q) == 1)}/{q} expected) ; check {chk}", flush=True)


def resid():
    """q P(sum_{i<k} g(X_i) == 0 mod q) for X_i uniform on 0..b-1 with b == 1 mod q,
    averaged over such b in 10..60, 0^0 = 1 and 0^0 = 0."""
    print("# q m k factor (mean over bases b in 10..60 with q | b - 1)")
    for q in (2, 3, 4, 5, 7, 8, 9):
        for m in (0, 1):
            for k in (2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 30):
                vals = []
                for b in range(10, 61):
                    if (b - 1) % q:
                        continue
                    g = [((pow(x, x, q) if x else m) - x) % q for x in range(b)]
                    dist = [0.0] * q
                    for v in g:
                        dist[v] += 1.0 / b
                    cur = [0.0] * q
                    cur[0] = 1.0
                    for _ in range(k):
                        nxt = [0.0] * q
                        for a in range(q):
                            if cur[a]:
                                for v in range(q):
                                    nxt[(a + v) % q] += cur[a] * dist[v]
                        cur = nxt
                    vals.append(q * cur[0])
                print(f"{q} {m} {k} {sum(vals) / len(vals):.4f}")


def main():
    mode = sys.argv[1]
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    if mode == 'table':
        table(N)
    elif mode == 'rho':
        rho(N)
    elif mode == 'resid':
        resid()


if __name__ == '__main__':
    main()
