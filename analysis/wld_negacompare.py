"""Compare the negative-base census with the model.

Reads
  data/wld_negabase_census.txt  (`worlds lanes -b powM`, bases -2 to -35)
  data/wld_negabase_exact.txt   (`worlds brute -b powM`: exact model sums)
  data/wld_negamodel_19_36.txt  (wld_negamodel.py: sampled model sums)
and prints the per-base table, the totals by base parity, the length shares
and the emptiness test.
"""
import math
import random
from collections import defaultdict

D = "data/"


def load_census():
    sols = defaultdict(list)  # (b, m) -> list of digit tuples
    bases = set()
    for line in open(D + "wld_negabase_census.txt"):
        f = line.split()
        if f[0] == "total":
            bases.add(-int(f[2]))
        if f[0] == "sol":
            b, m = -int(f[2]), int(f[4][3])
            sols[(b, m)].append(tuple(map(int, f[8].split(","))))
    return sorted(bases), sols


def load_model():
    # model[(b, d)] = (basic, ref0, ref1, zerofree)
    model = {}
    rows = defaultdict(dict)
    for line in open(D + "wld_negabase_exact.txt"):
        f = line.split()
        if f[0] != "len":
            continue
        b, m, d = -int(f[2]), int(f[4][3]), int(f[6])
        rows[(b, d)][m] = (float(f[12]), float(f[14]), float(f[16]))
    for (b, d), r in rows.items():
        model[(b, d)] = (r[1][0], r[0][1], r[1][1], r[1][2])
    for line in open(D + "wld_negamodel_19_36.txt"):
        if line.startswith("#"):
            continue
        b, d, e, r0, r1, zf = line.split()
        if (int(b), int(d)) not in model:
            model[(int(b), int(d))] = (float(e), float(r0), float(r1), float(zf))
    return model


def poisson_cdf(k, lam):
    return sum(math.exp(-lam) * lam ** i / math.factorial(i) for i in range(k + 1))


def check_rules(sols):
    """The congruences of section 1.1 of the draft, on every solution."""
    bad = 0
    n = 0
    for (b, m), ss in sols.items():
        for s in ss:
            n += 1
            assert len(s) % 2 == 1 and len(s) <= b + 1
            w = [m] + [x ** x for x in range(1, b)]
            assert (sum(w[x] - x for x in s)) % (b + 1) == 0
            if b % 2 == 1 and m == 1 and s.count(0) % 2:
                bad += 1
            if b % 4 == 3 and m == 0 and sum(1 for x in s if x % 4 == 2) % 2:
                bad += 1
            if b % 3 == 2 and m == 0 and sum(1 for x in s if x % 6 == 2) % 3:
                bad += 1
            v = 0
            for x in s:
                v = v * (-b) + x
            assert v == sum(w[x] for x in s)
    print(f"{n} solutions checked: values, odd length <= b+1, identity mod b+1; {bad} break a parity rule")


def main():
    bases, sols = load_census()
    check_rules(sols)
    model = load_model()
    print("base | N_1 | E_1 | N_0 | E_0 | distinct | E_union | P(empty) | lengths (m=1; m=0)")
    tot = defaultdict(lambda: [0, 0.0, 0.0])
    pe = {}
    for b in bases:
        e = {m: sum(model[(b, d)][1 + (m == 1)] for d in range(3, b + 2, 2)) for m in (0, 1)}
        eb = sum(model[(b, d)][0] for d in range(3, b + 2, 2))
        zf = sum(model[(b, d)][3] for d in range(3, b + 2, 2))
        eu = e[0] + e[1] - zf
        distinct = len(set(sols[(b, 0)]) | set(sols[(b, 1)]))
        pe[b] = (math.exp(-eu), distinct == 0)
        lens = "; ".join(",".join(str(len(s)) for s in sols[(b, m)]) for m in (1, 0))
        print(f"-{b} | {len(sols[(b, 1)])} | {e[1]:.2f} | {len(sols[(b, 0)])} | {e[0]:.2f} | {distinct} | {eu:.2f} | {math.exp(-eu):.3f} | {lens}")
        if b >= 10:
            par = "odd" if b % 2 else "even"
            for m in (0, 1):
                t = tot[(m, par)]
                t[0] += len(sols[(b, m)])
                t[1] += e[m]
                t[2] += eb
    print()
    print("bases 10-%d: convention, parity, observed, refined, basic, P(X <= obs)" % bases[-1])
    for k, (o, er, eb) in sorted(tot.items()):
        print(k, o, f"{er:.1f}", f"{eb:.1f}", f"{poisson_cdf(o, er):.3f}")

    # length shares: J = (largest possible length) - d
    print()
    print("length shares, bases 10 and up, both conventions")
    for par in ("even", "odd"):
        obs = defaultdict(int)
        exp = defaultdict(float)
        for b in bases:
            if b < 10 or (b % 2 == 1) != (par == "odd"):
                continue
            top = b + 1 if b % 2 == 0 else b
            for m in (0, 1):
                for s in sols[(b, m)]:
                    obs[top - len(s)] += 1
                for d in range(3, top + 1, 2):
                    exp[top - d] += model[(b, d)][1 + (m == 1)]
        no, ne = sum(obs.values()), sum(exp.values())
        for j in sorted(exp):
            if j <= 8:
                print(par, f"d = top-{j}", obs[j], f"{exp[j]:.1f}", f"{obs[j] / no:.3f}", f"{exp[j] / ne:.3f}")
        print(par, "rest", sum(v for j, v in obs.items() if j > 8), f"{sum(v for j, v in exp.items() if j > 8):.1f}")

    # emptiness
    print()
    nobs = sum(1 for b in pe if pe[b][1])
    nexp = sum(p for p, _ in pe.values())
    print("bases with no solution in either convention:", [b for b in pe if pe[b][1]])
    print(f"observed {nobs}, expected {nexp:.2f}")
    # chance of at least nobs empty bases, by simulation of independent bases
    random.seed(1)
    probs = [p for p, _ in pe.values()]
    hits = sum(1 for _ in range(100000) if sum(random.random() < p for p in probs) >= nobs)
    print(f"P(at least {nobs} empty bases) = {hits / 100000:.4f}")
    m3 = [b for b in pe if b % 3 == 0]
    print("multiples of 3:", m3, "empty:", [b for b in m3 if pe[b][1]],
          f"expected empty {sum(pe[b][0] for b in m3):.2f}")


if __name__ == "__main__":
    main()
