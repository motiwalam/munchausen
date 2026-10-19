"""Question 77: Munchausen numbers as a CP-SAT problem.

Usage: python r5l_cpsat.py B0 B1 [--mode 0|1] [--all-d] [--time T] [--model counts|direct]
       [--workers W]

Runs on the venv ~/.local/share/venvs/munchausen (ortools).

Model "counts" (the positional form of question 77):
  x[i][v]  one-hot digits of n, i = 0 (least significant) .. d-1
  c_v      = sum_i x[i][v]
  column j: sum_v a[j][v] c_v + carry_j = n_j + b carry_(j+1)
  where a[j][v] is digit j of w(v) = v^v (w(0) = mode).
Model "direct" drops the counts: column j sums a[j][n_i] over the positions
i, with a[j][n_i] an element constraint. Both models enumerate every
d-digit solution, so the run ends with a proof that there are no others.

Prints one line per (b, d): status, solutions, wall time, branches,
conflicts, and checks the solutions against output/b2-41-<mode>.txt.
"""
import argparse
import os
import resource
import sys
import time

from ortools.sat.python import cp_model

HERE = os.path.dirname(os.path.abspath(__file__))


def known(mode):
    """Solutions of output/b2-41-<mode>.txt as {b: set of digit tuples, most significant first}."""
    out = {}
    with open(os.path.join(HERE, '..', 'output', f'b2-41-{mode}.txt')) as f:
        for line in f:
            b, _, _, rest = line.split(':', 3)
            sols = set()
            for part in rest.split('(')[1:]:
                ds = part.split(')')[0].strip().rstrip(',')
                sols.add(tuple(int(x) for x in ds.split(',') if x.strip() != ''))
            out[int(b)] = sols
    return out


def weight(v, mode):
    return mode if v == 0 else v ** v


def digits(n, b, k):
    out = []
    for _ in range(k):
        out.append(n % b)
        n //= b
    return out


def build(b, d, mode, model_kind):
    m = cp_model.CpModel()
    W = [weight(v, mode) for v in range(b)]
    allowed = [v for v in range(b) if W[v] < b ** d]
    x = [[m.new_bool_var(f'x{i}_{v}') for v in range(b)] for i in range(d)]
    for i in range(d):
        m.add_exactly_one(x[i])
        for v in range(b):
            if v not in allowed:
                m.add(x[i][v] == 0)
    m.add(x[d - 1][0] == 0)  # d digits exactly
    n = [m.new_int_var(0, b - 1, f'n{i}') for i in range(d)]
    for i in range(d):
        m.add(n[i] == sum(v * x[i][v] for v in range(1, b)))
    A = [digits(W[v], b, d) for v in range(b)]
    carry = [m.new_int_var(0, d, f'k{j}') for j in range(d + 1)]
    m.add(carry[0] == 0)
    m.add(carry[d] == 0)
    if model_kind in ('counts', 'window'):
        c = [m.new_int_var(0, d, f'c{v}') for v in range(b)]
        for v in range(b):
            m.add(c[v] == sum(x[i][v] for i in range(d)))
        for j in range(d):
            m.add(sum(A[v][j] * c[v] for v in allowed if A[v][j]) + carry[j] == n[j] + b * carry[j + 1])
    if model_kind == 'window':
        # Redundant super-columns of g digits, counted from the top, so that
        # bound propagation sees the interval of the top g digits of S:
        # sum_v c_v (floor(w(v)/b^j) mod b^g) + carry_j = sum_(i<g) n_(j+i) b^i + b^g carry_(j+g)
        g = 1
        while (b ** (g + 1)) * (d + 1) * b < 2 ** 60:
            g += 1
        j1 = d
        while j1 > 0:
            j0 = max(0, j1 - g)
            q = [(W[v] // b ** j0) % b ** (j1 - j0) for v in range(b)]
            m.add(sum(q[v] * c[v] for v in allowed if q[v]) + carry[j0]
                  == sum(n[i] * b ** (i - j0) for i in range(j0, j1)) + b ** (j1 - j0) * carry[j1])
            j1 = j0
        c_sum = sum(c[v] for v in allowed)
        m.add(c_sum == d)
    else:
        for j in range(d):
            terms = []
            for i in range(d):
                terms.append(sum(A[v][j] * x[i][v] for v in allowed if A[v][j]))
            m.add(sum(terms) + carry[j] == n[j] + b * carry[j + 1])
    return m, n


class Collect(cp_model.CpSolverSolutionCallback):
    def __init__(self, n):
        super().__init__()
        self.n = n
        self.sols = []

    def on_solution_callback(self):
        self.sols.append(tuple(self.value(v) for v in reversed(self.n)))


def solve(b, d, mode, model_kind, tlimit, workers, exist=False):
    m, n = build(b, d, mode, model_kind)
    s = cp_model.CpSolver()
    s.parameters.enumerate_all_solutions = not exist
    s.parameters.num_workers = workers
    s.parameters.max_time_in_seconds = tlimit
    cb = Collect(n)
    r0 = resource.getrusage(resource.RUSAGE_SELF)
    t0 = time.perf_counter()
    st = s.solve(m, cb)
    t = time.perf_counter() - t0
    r1 = resource.getrusage(resource.RUSAGE_SELF)
    cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
    return s.status_name(st), sorted(cb.sols), t, cpu, s.num_branches, s.num_conflicts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('b0', type=int)
    ap.add_argument('b1', type=int)
    ap.add_argument('--mode', type=int, default=1)
    ap.add_argument('--all-d', action='store_true')
    ap.add_argument('--time', type=float, default=600)
    ap.add_argument('--model', default='counts')
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--exist', action='store_true', help='stop at the first solution (full presolve)')
    a = ap.parse_args()
    ref = known(a.mode)
    print(f'# model={a.model} mode={a.mode} workers={a.workers} exist={a.exist}')
    print('# b d status sols wall_s cpu_s branches conflicts check')
    for b in range(a.b0, a.b1 + 1):
        ds = range(2, b + 1) if a.all_d else [b - 1]
        for d in ds:
            st, sols, t, cpu, br, cf = solve(b, d, a.mode, a.model, a.time, a.workers, a.exist)
            want = sorted(s for s in ref.get(b, ()) if len(s) == d)
            done = st in ('OPTIMAL', 'INFEASIBLE')
            if a.exist:
                done = st in ('OPTIMAL', 'FEASIBLE', 'INFEASIBLE')
                ok = ('ok' if (len(sols) > 0) == (len(want) > 0) and set(sols) <= set(want) else 'MISMATCH') if done else 'timeout'
            else:
                ok = ('ok' if sols == want else 'MISMATCH') if done else 'timeout'
            print(f'{b} {d} {st} {len(sols)} {t:.3f} {cpu:.3f} {br} {cf} {ok}', flush=True)
            if ok == 'MISMATCH':
                print('# found', sols, 'expected', want, file=sys.stderr)
            if not done:
                return


if __name__ == '__main__':
    main()
