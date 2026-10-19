"""Question 77: Munchausen numbers as a pure CNF problem for a CDCL solver.

Usage: python r5l_sat.py B0 B1 [--mode 0|1] [--solver cadical195] [--model counts|direct]
       [--time T] [--dimacs DIR]

Runs on the venv ~/.local/share/venvs/munchausen (python-sat).

The encoding is a Tseitin circuit in binary arithmetic.
  x[i][v]  one-hot digits of n, i = 0 (least significant) .. d-1
  counts:  c_v = popcount of x[.][v], in binary (adder tree);
           column j sums A[v][j] * c_v by shift-and-add of the constant
  direct:  column j sums the binary numbers D_j(n_i) = A[n_i][j], whose bits
           are ORs of the one-hot digit variables
  in both: column sum + carry_j == n_j + b * carry_(j+1), carry_0 = carry_d = 0.
Every solution is blocked after it is found, so the last call proves that
there is no other d-digit solution. Checks against output/b2-41-<mode>.txt.
"""
import argparse
import os
import resource
import sys
import time

from pysat.solvers import Solver

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from r5l_cpsat import known, weight, digits  # noqa: E402


class CNF:
    def __init__(self):
        self.n = 1  # variable 1 is constant true
        self.clauses = [[1]]

    def var(self):
        self.n += 1
        return self.n

    @property
    def T(self):
        return 1

    @property
    def F(self):
        return -1

    def AND(self, a, b):
        if a == self.F or b == self.F:
            return self.F
        if a == self.T:
            return b
        if b == self.T:
            return a
        y = self.var()
        self.clauses += [[-y, a], [-y, b], [y, -a, -b]]
        return y

    def OR(self, xs):
        xs = [x for x in xs if x != self.F]
        if any(x == self.T for x in xs):
            return self.T
        if not xs:
            return self.F
        if len(xs) == 1:
            return xs[0]
        y = self.var()
        self.clauses.append([-y] + xs)
        for x in xs:
            self.clauses.append([y, -x])
        return y

    def XOR(self, a, b):
        if a == self.F:
            return b
        if b == self.F:
            return a
        if a == self.T:
            return -b
        if b == self.T:
            return -a
        y = self.var()
        self.clauses += [[-y, a, b], [-y, -a, -b], [y, -a, b], [y, a, -b]]
        return y

    def full_add(self, a, b, c):
        s1 = self.XOR(a, b)
        s = self.XOR(s1, c)
        cy = self._maj(a, b, c)
        return s, cy

    def _maj(self, a, b, c):
        xs = [a, b, c]
        nf = sum(1 for x in xs if x == self.F)
        nt = sum(1 for x in xs if x == self.T)
        if nf >= 2:
            return self.F
        if nt >= 2:
            return self.T
        if nf == 1:
            p, q = [x for x in xs if x != self.F]
            return self.AND(p, q)
        if nt == 1:
            p, q = [x for x in xs if x != self.T]
            return self.OR([p, q])
        y = self.var()
        self.clauses += [[-y, a, b], [-y, a, c], [-y, b, c], [y, -a, -b], [y, -a, -c], [y, -b, -c]]
        return y

    def add(self, A, B):
        """Binary numbers as lists of literals, least significant bit first."""
        n = max(len(A), len(B))
        A = A + [self.F] * (n - len(A))
        B = B + [self.F] * (n - len(B))
        out, cy = [], self.F
        for a, b in zip(A, B):
            s, cy = self.full_add(a, b, cy)
            out.append(s)
        out.append(cy)
        while len(out) > 1 and out[-1] == self.F:
            out.pop()
        return out

    def sum_all(self, nums):
        nums = [x for x in nums if x and any(l != self.F for l in x)]
        if not nums:
            return [self.F]
        while len(nums) > 1:
            nxt = []
            for i in range(0, len(nums) - 1, 2):
                nxt.append(self.add(nums[i], nums[i + 1]))
            if len(nums) % 2:
                nxt.append(nums[-1])
            nums = nxt
        return nums[0]

    def const_mul(self, k, X):
        terms = []
        sh = 0
        while k:
            if k & 1:
                terms.append([self.F] * sh + X)
            k >>= 1
            sh += 1
        return self.sum_all(terms)

    def equal(self, A, B):
        n = max(len(A), len(B))
        A = A + [self.F] * (n - len(A))
        B = B + [self.F] * (n - len(B))
        for a, b in zip(A, B):
            self.clauses += [[-a, b], [a, -b]]

    def exactly_one(self, xs):
        self.clauses.append(list(xs))
        # sequential at-most-one
        s_prev = None
        for i, x in enumerate(xs[:-1]):
            s = self.var()
            self.clauses.append([-x, s])
            if s_prev is not None:
                self.clauses += [[-s_prev, s], [-x, -s_prev]]
            s_prev = s
        if s_prev is not None:
            self.clauses.append([-xs[-1], -s_prev])


def bits_of_digit(cnf, xi, b, f):
    """Binary number f(n_i) for one-hot digit literals xi, f: value -> int."""
    width = max(f(v) for v in range(b)).bit_length()
    return [cnf.OR([xi[v] for v in range(b) if (f(v) >> t) & 1]) for t in range(width)]


def encode(b, d, mode, model_kind):
    cnf = CNF()
    W = [weight(v, mode) for v in range(b)]
    allowed = [v for v in range(b) if W[v] < b ** d]
    x = [[cnf.var() for v in range(b)] for i in range(d)]
    for i in range(d):
        cnf.exactly_one(x[i])
        for v in range(b):
            if v not in allowed:
                cnf.clauses.append([-x[i][v]])
    cnf.clauses.append([-x[d - 1][0]])
    A = [digits(W[v], b, d) for v in range(b)]
    cw = (d * b).bit_length() + 1
    carry = [[cnf.F] * cw] + [[cnf.var() for _ in range(cw)] for _ in range(d - 1)] + [[cnf.F] * cw]
    if model_kind == 'counts':
        c = {v: cnf.sum_all([[x[i][v]] for i in range(d)]) for v in allowed}
    for j in range(d):
        if model_kind == 'counts':
            col = cnf.sum_all([cnf.const_mul(A[v][j], c[v]) for v in allowed if A[v][j]] + [carry[j]])
        else:
            col = cnf.sum_all([bits_of_digit(cnf, x[i], b, lambda v: A[v][j] if v in allowed else 0) for i in range(d)] + [carry[j]])
        nj = bits_of_digit(cnf, x[j], b, lambda v: v)
        rhs = cnf.add(nj, cnf.const_mul(b, carry[j + 1]))
        cnf.equal(col, rhs)
    return cnf, x


def solve(b, d, mode, model_kind, name, tlimit, dimacs=None):
    cnf, x = encode(b, d, mode, model_kind)
    if dimacs:
        with open(os.path.join(dimacs, f'r5l_b{b}_d{d}_m{mode}_{model_kind}.cnf'), 'w') as f:
            f.write(f'p cnf {cnf.n} {len(cnf.clauses)}\n')
            for cl in cnf.clauses:
                f.write(' '.join(map(str, cl)) + ' 0\n')
    sols = []
    r0 = resource.getrusage(resource.RUSAGE_SELF)
    t0 = time.perf_counter()
    status = 'done'
    with Solver(name=name, bootstrap_with=cnf.clauses, use_timer=True) as s:
        while True:
            if time.perf_counter() - t0 > tlimit:
                status = 'timeout'
                break
            if not s.solve():
                break
            model = set(l for l in s.get_model() if l > 0)
            digs = []
            for i in range(d):
                vs = [v for v in range(b) if x[i][v] in model]
                digs.append(vs[0])
            sols.append(tuple(reversed(digs)))
            s.add_clause([-x[i][digs[i]] for i in range(d)])
        st = s.accum_stats()
    t = time.perf_counter() - t0
    r1 = resource.getrusage(resource.RUSAGE_SELF)
    cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
    return status, sorted(sols), t, cpu, st.get('decisions', 0), st.get('conflicts', 0), cnf.n, len(cnf.clauses)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('b0', type=int)
    ap.add_argument('b1', type=int)
    ap.add_argument('--mode', type=int, default=1)
    ap.add_argument('--solver', default='cadical195')
    ap.add_argument('--model', default='counts')
    ap.add_argument('--time', type=float, default=600)
    ap.add_argument('--dimacs')
    a = ap.parse_args()
    ref = known(a.mode)
    print(f'# solver={a.solver} model={a.model} mode={a.mode}')
    print('# b d status sols wall_s cpu_s decisions conflicts vars clauses check')
    for b in range(a.b0, a.b1 + 1):
        d = b - 1
        st, sols, t, cpu, dec, cf, nv, nc = solve(b, d, a.mode, a.model, a.solver, a.time, a.dimacs)
        want = sorted(s for s in ref.get(b, ()) if len(s) == d)
        ok = ('ok' if sols == want else 'MISMATCH') if st == 'done' else 'timeout'
        print(f'{b} {d} {st} {len(sols)} {t:.3f} {cpu:.3f} {dec} {cf} {nv} {nc} {ok}', flush=True)
        if st != 'done':
            return


if __name__ == '__main__':
    main()
