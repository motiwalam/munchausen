"""Question 76: certificates of emptiness made of interval tests.

Usage: python r5l_cert.py B0 B1 [--weights true|random] [--seed S] [--mode 0|1]
       [--no-ilp] [--no-opt]

The universe is the set C_d of count vectors with sum d = b-1 over the
allowed values (w(v) < b^d). A cylinder x = (R, c_R) fixes the counts of a
set R of values; its completions put rf = d - sum c_R copies on the other
values U. Its interval is
    [sum_R c_v w(v) + rf min_U w, sum_R c_v w(v) + rf max_U w],
clipped to the d-digit numbers, and P(x) is the common prefix of the
clipped ends. x fails if the interval is empty, if P(x) holds more than c_v
copies of some v in R, or more than rf digits outside R. A cylinder with
rf = 0 or |U| = 1 is a single vector and fails if that vector is not a
solution. A certificate of emptiness is a set of failing cylinders that
covers every non-solution of C_d.

For each base the script prints:
  vectors   |C_d|
  topdown   failing cylinders evaluated by the top-down tree (its certificate)
  nodes     surviving nodes of the top-down tree
  opt_tree  the smallest certificate of a tree that branches on one count
            per node, in any order chosen node by node (dynamic programming)
  min_cover the smallest certificate of any kind (an exact set cover by
            CP-SAT over the maximal failing cylinders)
  lower     max_k N_k, the fooling-set bound of Theorem 76.2
"""
import argparse
import itertools
import os
import random
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)


def make_weights(b, kind, mode, seed):
    W = [mode] + [v ** v for v in range(1, b)]
    if kind == 'random':
        rnd = random.Random(seed * 1000 + b)
        W = [W[0], 1] + [v ** v + rnd.randrange(v ** v // 4 + 1) for v in range(2, b)]
    return W


class Inst:
    def __init__(self, b, d, W):
        self.b, self.d, self.W = b, d, W
        self.B0, self.B1 = b ** (d - 1), b ** d - 1
        self.vals = [v for v in range(b) if W[v] <= self.B1]
        self.pw = [b ** i for i in range(d + 1)]

    def digits_top(self, n):
        b, out = self.b, []
        for i in range(self.d - 1, -1, -1):
            out.append(n // self.pw[i] % b)
        return out

    def prefix(self, lo, hi):
        """Common leading digits of two d-digit numbers lo <= hi."""
        out = []
        for i in range(self.d - 1, -1, -1):
            a, c = lo // self.pw[i] % self.b, hi // self.pw[i] % self.b
            if a != c:
                break
            out.append(a)
        return out

    def is_solution(self, c):
        """c: dict value -> count (sum d)."""
        S = sum(self.W[v] * k for v, k in c.items())
        if not (self.B0 <= S <= self.B1):
            return False
        h = {}
        for x in self.digits_top(S):
            h[x] = h.get(x, 0) + 1
        return all(h.get(v, 0) == c.get(v, 0) for v in set(h) | set(c))

    def fails(self, R):
        """R: tuple of (value, count) sorted by value."""
        d, W = self.d, self.W
        rv = {v for v, _ in R}
        s = sum(k for _, k in R)
        rf = d - s
        if rf < 0:
            return True
        U = [v for v in self.vals if v not in rv]
        if rf == 0 or len(U) <= 1:
            if rf > 0 and not U:
                return True
            c = dict(R)
            if rf > 0:
                c[U[0]] = c.get(U[0], 0) + rf
            return not self.is_solution(c)
        t = sum(W[v] * k for v, k in R)
        lo = max(t + rf * min(W[v] for v in U), self.B0)
        hi = min(t + rf * max(W[v] for v in U), self.B1)
        if lo > hi:
            return True
        P = self.prefix(lo, hi)
        cr = dict(R)
        out = 0
        h = {}
        for x in P:
            h[x] = h.get(x, 0) + 1
        for x, k in h.items():
            if x in cr:
                if k > cr[x]:
                    return True
            else:
                out += k
        return out > rf

    def is_singleton(self, R):
        rv = {v for v, _ in R}
        rf = self.d - sum(k for _, k in R)
        return rf == 0 or len(self.vals) - len(rv) <= 1


def vectors(inst):
    vals, d = inst.vals, inst.d
    for comb in itertools.combinations_with_replacement(vals, d):
        c = {}
        for v in comb:
            c[v] = c.get(v, 0) + 1
        yield c


def key_of(c, vals):
    return tuple(c.get(v, 0) for v in vals)


def topdown(inst):
    """Top-down tree with the same test: (certificate size, surviving nodes)."""
    vals = sorted(inst.vals, reverse=True)
    cert = nodes = 0

    def rec(i, R, rf):
        nonlocal cert, nodes
        nodes += 1
        v = vals[i]
        for e in range(rf + 1):
            R2 = tuple(sorted(R + ((v, e),)))
            if inst.fails(R2):
                cert += 1
            elif inst.is_singleton(R2):
                cert += 1  # a solution leaf: counted as an evaluated leaf
            else:
                rec(i + 1, R2, rf - e)

    rec(0, (), inst.d)
    return cert, nodes


def opt_tree(inst):
    vals = inst.vals

    @lru_cache(maxsize=None)
    def opt(R):
        if inst.fails(R) or inst.is_singleton(R):
            return 1
        rv = {v for v, _ in R}
        rf = inst.d - sum(k for _, k in R)
        best = None
        for v in vals:
            if v in rv:
                continue
            tot = 0
            for e in range(rf + 1):
                tot += opt(tuple(sorted(R + ((v, e),))))
                if best is not None and tot >= best:
                    break
            if best is None or tot < best:
                best = tot
        return best

    r = opt(())
    n = opt.cache_info().currsize
    opt.cache_clear()
    return r, n


def all_cylinders(inst):
    vals, d = inst.vals, inst.d
    for m in range(0, len(vals) + 1):
        for Rv in itertools.combinations(vals, m):
            def gen(i, left):
                if i == len(Rv):
                    yield ()
                    return
                for e in range(left + 1):
                    for rest in gen(i + 1, left - e):
                        yield ((Rv[i], e),) + rest
            for R in gen(0, d):
                yield R


def min_cover(inst, sols, workers=2, tlimit=600):
    from ortools.sat.python import cp_model
    vals, d = inst.vals, inst.d
    # failing status of every cylinder, then keep the maximal failing ones
    fail = {}
    for R in all_cylinders(inst):
        if not inst.is_singleton(R):
            fail[R] = inst.fails(R)
    dominated = {}
    for R in sorted(fail, key=len):
        dom = False
        for i in range(len(R)):
            R2 = R[:i] + R[i + 1:]
            if R2 in fail and (fail[R2] or dominated[R2]):
                dom = True
                break
        dominated[R] = dom
    maximal = [R for R in fail if fail[R] and not dominated[R]]
    universe = [key_of(c, vals) for c in vectors(inst)]
    universe = [u for u in universe if u not in sols]
    idx = {u: i for i, u in enumerate(universe)}
    m = cp_model.CpModel()
    covers = [[] for _ in universe]
    xs = []
    pos = {v: i for i, v in enumerate(vals)}
    for R in maximal:
        x = m.new_bool_var('')
        xs.append(x)
        rv = {v for v, _ in R}
        U = [v for v in vals if v not in rv]
        rf = d - sum(k for _, k in R)
        base = [0] * len(vals)
        for v, k in R:
            base[pos[v]] = k
        for comb in itertools.combinations_with_replacement(U, rf):
            u = list(base)
            for v in comb:
                u[pos[v]] += 1
            u = tuple(u)
            if u in idx:
                covers[idx[u]].append(x)
    for i, u in enumerate(universe):
        y = m.new_bool_var('')  # the leaf check of u itself
        xs.append(y)
        m.add_bool_or(covers[i] + [y])
    m.minimize(sum(xs))
    s = cp_model.CpSolver()
    s.parameters.num_workers = workers
    s.parameters.max_time_in_seconds = tlimit
    st = s.solve(m)
    return int(s.objective_value), int(s.best_objective_bound), s.status_name(st), len(maximal)


def lower_bound(inst, sols):
    """Theorem 76.2: max over k of N_k, with the thresholds theta(c)."""
    b, d, W, vals = inst.b, inst.d, inst.W, inst.vals
    g = {}
    for u in vals:
        below = [W[u] - W[m] for m in vals if m < u]
        g[u] = min(below) if below else -1
    N = {k: set() for k in vals}
    cnt_g = 0
    for c in vectors(inst):
        key = key_of(c, vals)
        if key in sols:
            continue
        S = sum(W[v] * k for v, k in c.items())
        if not (inst.B0 <= S <= inst.B1):
            continue
        top = inst.digits_top(S)
        if (top[0] == 1 and top[1] == 0) or (top[0] == b - 1 and top[1] == b - 1):
            continue
        h, lam = {}, 0
        for x in top:
            h[x] = h.get(x, 0) + 1
            if h[x] > c.get(x, 0):
                break
            lam += 1
        if lam < 1:
            continue
        cnt_g += 1
        thr = b ** (d - lam - 1)
        theta = None
        for t in sorted(vals, reverse=True):
            if g[t] >= thr:
                theta = t
            else:
                break
        if theta is None:
            continue
        for k in vals:
            if k >= theta:
                N[k].add(tuple(c.get(v, 0) for v in vals if v >= k))
    best = max((len(s), k) for k, s in N.items())
    return best, cnt_g


def thresholds(inst):
    """theta_of(lam): the least t such that g(u) >= b^(d-lam-1) for every u >= t."""
    b, d, W, vals = inst.b, inst.d, inst.W, inst.vals
    g = {}
    for u in vals:
        below = [W[u] - W[m] for m in vals if m < u]
        g[u] = min(below) if below else -1

    def theta_of(lam):
        thr = b ** (d - lam - 1)
        theta = None
        for t in sorted(vals, reverse=True):
            if g[t] >= thr:
                theta = t
            else:
                break
        return theta
    return theta_of


def lam_of(inst, c):
    """lambda(c), or None if c is outside G* (Theorem 76.2)."""
    b = inst.b
    S = sum(inst.W[v] * k for v, k in c.items())
    if not (inst.B0 <= S <= inst.B1):
        return None
    top = inst.digits_top(S)
    if (top[0] == 1 and top[1] == 0) or (top[0] == b - 1 and top[1] == b - 1):
        return None
    h, lam = {}, 0
    for x in top:
        h[x] = h.get(x, 0) + 1
        if h[x] > c.get(x, 0):
            break
        lam += 1
    return lam if lam >= 1 else None


def lower_tree(inst):
    """A lower bound on N_k for every k from witnesses built in the top-down tree.

    A surviving level-k node y is counted if some completion c of y (the
    forced digits of the prefix, the other free copies on one value) lies in
    G*, is not a solution, and has theta(c) <= k. Distinct y give distinct
    restrictions to V_k, so the count is at most N_k. Also returns the number
    of surviving nodes per level.
    """
    vals = sorted(inst.vals, reverse=True)
    theta_of = thresholds(inst)
    d, W = inst.d, inst.W
    Nk, Tk = {}, {}

    def witness(R, rf, k):
        cr = dict(R)
        t = sum(W[v] * e for v, e in R)
        U = [v for v in inst.vals if v < k]
        lo = max(t + rf * min(W[v] for v in U), inst.B0)
        hi = min(t + rf * max(W[v] for v in U), inst.B1)
        if lo > hi:
            return False
        forced = {}
        for x in inst.prefix(lo, hi):
            if x < k:
                forced[x] = forced.get(x, 0) + 1
        left = rf - sum(forced.values())
        if left < 0:
            return False
        for v in U:
            c = dict(cr)
            for x, e in forced.items():
                c[x] = c.get(x, 0) + e
            c[v] = c.get(v, 0) + left
            c = {x: e for x, e in c.items() if e}
            lam = lam_of(inst, c)
            if lam is None or inst.is_solution(c):
                continue
            th = theta_of(lam)
            if th is not None and th <= k:
                return True
        return False

    def rec(i, R, rf):
        k = vals[i]  # the values >= k are fixed in R... after this level
        for e in range(rf + 1):
            R2 = R + ((k, e),)
            R2s = tuple(sorted(R2))
            if inst.fails(R2s) or inst.is_singleton(R2s):
                continue
            Tk[k] = Tk.get(k, 0) + 1
            if witness(R2, rf - e, k):
                Nk[k] = Nk.get(k, 0) + 1
            rec(i + 1, R2, rf - e)

    rec(0, (), d)
    return Nk, Tk


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('b0', type=int)
    ap.add_argument('b1', type=int)
    ap.add_argument('--weights', default='true')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--mode', type=int, default=1)
    ap.add_argument('--no-ilp', action='store_true')
    ap.add_argument('--no-opt', action='store_true')
    ap.add_argument('--tree-only', action='store_true', help='only the top-down tree and the bound from its witnesses')
    a = ap.parse_args()
    if a.tree_only:
        print(f'# weights={a.weights} seed={a.seed} mode={a.mode} d=b-1')
        print('# b topdown_cert nodes widest_level(k) lower_from_witnesses(k) ratio_tree/lower')
        for b in range(a.b0, a.b1 + 1):
            inst = Inst(b, b - 1, make_weights(b, a.weights, a.mode, a.seed))
            td, nodes = topdown(inst)
            Nk, Tk = lower_tree(inst)
            wk = max((n, k) for k, n in Tk.items())
            lk = max((n, k) for k, n in Nk.items())
            print(f'{b} {td} {nodes} {wk[0]}({wk[1]}) {lk[0]}({lk[1]}) {td / lk[0]:.2f}', flush=True)
        return
    print(f'# weights={a.weights} seed={a.seed} mode={a.mode} d=b-1')
    print('# b vectors sols topdown nodes opt_tree min_cover(bound,status,maximal) lower(k) |G*|')
    for b in range(a.b0, a.b1 + 1):
        d = b - 1
        inst = Inst(b, d, make_weights(b, a.weights, a.mode, a.seed))
        sols = {key_of(c, inst.vals) for c in vectors(inst) if inst.is_solution(c)}
        nvec = sum(1 for _ in vectors(inst))
        td, nodes = topdown(inst)
        ot = opt_tree(inst)[0] if not a.no_opt else '-'
        mc = min_cover(inst, sols) if not a.no_ilp else '-'
        (lb, k), ng = lower_bound(inst, sols)
        print(f'{b} {nvec} {len(sols)} {td} {nodes} {ot} {mc} {lb}({k}) {ng}', flush=True)


if __name__ == '__main__':
    main()
