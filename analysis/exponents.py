"""Asymptotic growth rates of the search tree, from the level formula.

At level k = kappa*b the unknown suffix has L_k digits, with
L_k = log_b(rf (k-1)^(k-1)) ~ k (1 + ln(kappa)/ln b) for large b.
- exact tree: every vector of high counts that fits the prefix,
  C(L + m, m) with m = b - k.
- typical tree: the posterior over nodes, given that a solution lies below,
  is the multinomial law of the high digits in L random positions: each of
  the m high values appears Poisson(L/b) times. Its entropy is
  m * H(Poisson(L/b)), and any method that enumerates nodes and finds the
  solution's node with probability 1/2 must try about exp(entropy) nodes.
"""
import math


def h_poisson(mu):
    if mu <= 0:
        return 0.0
    h, p, j = 0.0, math.exp(-mu), 0
    while j < 200:
        if p > 0:
            h -= p * math.log(p)
        j += 1
        p *= mu / j
        if j > mu + 40 and p < 1e-300:
            break
    return h


def lnC(n, r):
    return math.lgamma(n + 1) - math.lgamma(r + 1) - math.lgamma(n - r + 1)


def rates(b, d=None):
    d = d or b - 1
    best_exact = best_typ = (0, 0)
    for k in range(3, b):
        m = b - k
        rf = max(1.0, d * k / b)
        L = min(d, (math.log(rf) + (k - 1) * math.log(k - 1)) / math.log(b) + 1)
        ex = lnC(L + m, m)
        ty = m * h_poisson(L / b)
        best_exact = max(best_exact, (ex, k))
        best_typ = max(best_typ, (ty, k))
    return best_exact, best_typ


if __name__ == '__main__':
    # asymptotic: L = kappa b
    grid = [i / 1000 for i in range(1, 1000)]
    # C(b, q b) ~ exp(b H(q)) with the binary entropy H
    ex = max((-(q * math.log(q) + (1 - q) * math.log(1 - q)), q) for q in grid)
    ty = max(((1 - q) * h_poisson(q), q) for q in grid)
    print(f"b -> infinity: exact tree exp({ex[0]:.4f} b) = {math.exp(ex[0]):.3f}^b at kappa {ex[1]:.2f}; "
          f"typical exp({ty[0]:.4f} b) = {math.exp(ty[0]):.3f}^b at kappa {ty[1]:.2f}")
    print(" base   exact-tree growth  (peak k/b)   typical growth  (peak k/b)")
    for b in (20, 30, 40, 60, 100, 200, 500, 1000, 3000, 10000):
        (e1, k1), (t1, kt1) = rates(b)
        (e2, _), (t2, _) = rates(b + 1)
        print(f"{b:6d}   {math.exp(e2 - e1):.3f}              {k1 / b:.2f}         {math.exp(t2 - t1):.3f}          {kt1 / b:.2f}")
