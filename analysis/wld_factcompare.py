"""Factorions (n = sum of x! over the base-b digits, 0! = 1) against the model.

Reads data/wld_factorion_census.txt (worlds lanes b fact, bases 2-41),
data/wld_factorion_exact.txt (worlds brute: exact model, bases 2-16) and
data/wld_factorion_model.txt (wld_factmodel.py: sampled model).
Lengths are measured from L(b) = floor(log_b (b-1)!) + 1.
"""
import math
from collections import defaultdict

sols = defaultdict(list)
bases = []
for line in open("data/wld_factorion_census.txt"):
    f = line.split()
    if f[0] == "sol":
        sols[int(f[2])].append(len(f[8].split(",")))
    if f[0] == "total":
        bases.append(int(f[2]))
model = defaultdict(dict)  # b -> d -> (basic, refined)
for line in open("data/wld_factorion_model.txt"):
    if line.startswith("#"):
        continue
    b, L, d, e, r = line.split()
    model[int(b)][int(d)] = (float(e), float(r))
for line in open("data/wld_factorion_exact.txt"):
    f = line.split()
    if f[0] == "len":
        model[int(f[2])][int(f[6])] = (float(f[12]), float(f[14]))


def L(b):
    return math.floor(math.lgamma(b) / math.log(b)) + 1


print("base | L(b) | theta | solutions | lengths - L | E basic | E refined")
obs = defaultdict(int)
exp = defaultdict(float)
tot_o = tot_e = 0
empty_o = empty_e = 0
for b in bases:
    eb = sum(v[0] for v in model[b].values())
    er = sum(v[1] for v in model[b].values())
    th = math.lgamma(b) / math.log(b) % 1
    print(f"{b} | {L(b)} | {th:.2f} | {len(sols[b])} | {','.join(str(x - L(b)) for x in sols[b])} | {eb:.2f} | {er:.2f}")
    if b >= 10:
        tot_o += len(sols[b])
        tot_e += eb
        empty_o += len(sols[b]) == 0
        empty_e += math.exp(-eb)
        for x in sols[b]:
            obs[x - L(b)] += 1
        for d, v in model[b].items():
            exp[d - L(b)] += v[0]
print(f"\nbases 10-{bases[-1]}: {tot_o} factorions, model {tot_e:.1f}; empty bases {empty_o}, model {empty_e:.1f}")
print("length - L | observed | model")
for j in sorted(exp):
    if exp[j] > 0.05 or obs[j]:
        print(f"{j:+d} | {obs[j]} | {exp[j]:.1f}")
print("\nlarge bases, model shares by length - L:")
for b in (100, 300, 1000, 10000):
    tot = sum(v[0] for v in model[b].values())
    print(b, f"lambda = L/b = {L(b) / b:.3f}", " ".join(f"{d - L(b):+d}:{v[0] / tot:.3f}" for d, v in sorted(model[b].items()) if v[0] / tot > 0.005), f"total {tot:.2f}")
