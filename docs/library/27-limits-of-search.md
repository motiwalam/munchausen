# 27. Limits of search

This chapter answers questions 77, 75, 76, 79 and 78 of
`questions-round5.md` (workload 2, directions A2 and A3). It asks whether
any method can beat the top-down tree of `fast`, and how the work of an
exact run is spread over its work units.

Each statement carries one mark:

- proven: a proof is in this chapter;
- computed: an exact enumeration or a measurement, with its range;
- heuristic: an estimate with a stated assumption, usually the model of
  chapter 5 in the form of section 10.1.

All solver and toy runs reproduce the solutions of `output/b2-41-1.txt` for
the lengths and bases they cover. The two changes to the engine, a new
`--unit-stats` option and a work estimate in the lines of `--progress`,
leave the default output unchanged:
`fast search 2 30` matches the first 29 lines of `output/b2-41-0.txt` and
`output/b2-41-1.txt`, and `cargo test --release` passes.

## Summary

| section | question | result | status |
|---|---|---|---|
| 27.1 | 77, a constraint solver | CP-SAT and CaDiCaL list all solutions with `b - 1` digits correctly for bases 8 to 20 and 8 to 18. Their conflicts grow 1.95 and 1.96 per base, as fast as the engine's nodes (1.89), at 2 to 5 (CP-SAT, with the interval made visible) and 57 to 153 (CaDiCaL) conflicts per engine node, and `10^4` to `10^5` times the engine's time. Without the interval, CP-SAT grows 4 times per base. Learned clauses do not cut across branches. | computed; heuristic (why) |
| 27.2 | 75, other orders | In the model, every order of revealing counts, fixed or chosen node by node, has at each level `m` at least the entropy of the top-down order at level `m` (Theorem 27.2). So the floor `1.638^b` of Theorem 10.1 covers all of them, and top-down is the only order that reaches it. Bottom-up, middle-out and random orders peak near `1.30 b` nats, that is `3.6^b`; the best order by residue mod 2 peaks at `0.70 b`. | proven (in the model); computed |
| 27.3 | 76, certificates | In an oracle model where a query reveals the interval of `S` for a partial assignment of counts, every certificate of emptiness needs at least `N_k` queries for every level `k` (Theorem 27.5, a fooling-set bound that needs no model). For bases 5 to 21, `max_k N_k` is at least 0.86 times the widest level of the exact tree. So no oracle method beats the exact tree by more than a polynomial factor: the smallest certificate for `b = 10` has 414 queries, the top-down tree uses 794. | proven; computed |
| 27.4 | 79, bottom digits in base `2^k` | The bottom `L` digits of `S` are fixed only once the counts of all odd values, of 0 and of a few small even values are known: at least `b/2 + 2` values (Proposition 27.8). A top-down tree learns them only at its leaves, so a bottom check prunes nothing there (Corollary 27.9). Orders that reveal the odd counts early lose more than they gain: in base 16 the hybrid tree is 2.5 times and the odd-first tree 307 times the plain tree; in base 32 the hybrid tree is 13.3 times the plain tree (`3.4 * 10^9` against `2.5 * 10^8` nodes, exact) and the odd-first tree about `10^11` to `10^12` (estimate). The answer is no. | proven; computed |
| 27.5 | 78, work units | With `--unit-stats` (new), bases 24 to 34: the largest 1% of the units hold 47% to 81% of the work, and the pooled law has a power-like tail. The type of a unit (digits, free slots, known digits) explains 93% to 97% of the variance of `ln(nodes)`; within a type the law is light-tailed, and each free slot multiplies the size by 1.93. Scheduling on 8 threads is within 0.1% of ideal; shards of 64 are up to 2.6 times unbalanced at depth 4. A weighted progress estimate (new in `--progress`) is off by at most 0.10 against 0.49 for the unit count. | computed; heuristic |

Scripts: `analysis/r5l_cpsat.py`, `analysis/r5l_sat.py` and
`analysis/r5l_engine_baseline.py` (section 27.1), `analysis/r5l_orders.py` and
`analysis/r5l_optchoice.py` (section 27.2), `analysis/r5l_cert.py`
(section 27.3), `analysis/r5l_bottom.py` and `fast/src/bin/r5l_bottom.rs`
(section 27.4), `analysis/r5l_units.py` (section 27.5). Data:
`analysis/data/r5l_*`.

Software. The solvers come from PyPI, installed in a virtual environment
at `~/.local/share/venvs/munchausen` (Python 3.14): `ortools` 9.15.6755
(CP-SAT) and `python-sat` 1.9.dev16 (CaDiCaL 1.9.5 as `cadical195`), with
their dependencies `numpy` 2.5.4 and `protobuf` 6.33.6. Run the solver
scripts with `~/.local/share/venvs/munchausen/bin/python`.

Machine. Other jobs kept the load average at 15 to 30 on 8 threads during
all runs. Wall times are therefore 2 to 4 times the CPU times. The tables
give CPU seconds of one thread and machine-independent counts (nodes,
branches, conflicts).

## 27.1 A constraint solver as a search that is not a tree (question 77)

### 27.1.1 Encodings

The problem is "list every solution with `d = b - 1` digits under
`0^0 = 1`". A solver that ends with no further solution has proven that
there are no others, so its run is an exact search like the engine's.
Three encodings:

- Columns (`r5l_cpsat.py`, model `counts`). One-hot digits `x[i][v]`,
  counts `c_v = sum_i x[i][v]`, and for each position `j` the column sum
  `sum_v a[j][v] c_v + carry_j = n_j + b carry_(j+1)`, where `a[j][v]` is
  digit `j` of `v^v`. `carry_0 = carry_d = 0`, `n_(d-1) != 0`. This is the
  positional form of question 77.
- Columns with windows (model `window`). The same, plus redundant
  constraints over blocks of `g` digits from the top, with `g` as large as
  64-bit coefficients allow (`g = 10` for `b = 22`):
  `sum_v c_v (floor(v^v / b^j) mod b^g) + carry_j = sum_(i<g) n_(j+i) b^i + b^g carry_(j+g)`.
  With `0 <= carry_j <= d`, bound propagation on the top block is the
  interval test of the engine. Without it the solver has to find the
  interval through `d` carries, each of which it only knows up to `d`.
- CNF (`r5l_sat.py`). The column form as a Tseitin circuit: the counts are
  binary popcounts of the one-hot digits, the column sums are shift-and-add
  circuits of the constant digits, and each column is an equality of binary
  numbers. Each found solution is blocked, and the last call is UNSAT. The
  solver is CaDiCaL 1.9.5 (`cadical195`). Kissat 4.0.4 took about the
  same CPU time on bases 8 to 12, which have no solution with `b - 1`
  digits (`r5l_kissat_counts.txt`). It cannot add the clauses that block
  found solutions, so it was not run further.

A variant without counts (column `j` sums `a[j][n_i]` over the positions)
was slower in both solvers (`r5l_cpsat_direct.txt`, `r5l_sat_direct.txt`).

Every run found exactly the solutions of `output/b2-41-1.txt` with
`b - 1` digits. All runs used one thread.

### 27.1.2 Growth (computed)

Table 27.1.1. `d = b - 1`, `0^0 = 1`. The engine column is
`fast search b --min-digits b-1 --max-digits b-1 -j 1`, which also covers
`0^0 = 0`.

| b | engine nodes | engine evals | CaDiCaL conflicts | CaDiCaL CPU s | CP-SAT window conflicts | CP-SAT window branches | CP-SAT window CPU s |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 8 | 22 | 76 | 1,251 | 0.05 | 60 | 766 | 0.04 |
| 9 | 54 | 179 | 5,706 | 0.29 | 137 | 1,753 | 0.12 |
| 10 | 102 | 319 | 10,768 | 0.65 | 268 | 6,603 | 0.40 |
| 11 | 197 | 649 | 22,737 | 1.49 | 404 | 9,452 | 0.49 |
| 12 | 341 | 1,132 | 37,265 | 2.87 | 1,143 | 20,739 | 1.12 |
| 13 | 692 | 2,276 | 73,538 | 6.07 | 2,052 | 46,520 | 2.93 |
| 14 | 987 | 3,298 | 149,895 | 17.00 | 2,781 | 85,868 | 4.78 |
| 15 | 2,290 | 7,564 | 300,434 | 42.64 | 6,302 | 79,234 | 6.78 |
| 16 | 4,158 | 13,606 | 389,932 | 49.92 | 10,107 | 160,038 | 16.00 |
| 17 | 7,592 | 24,828 | 1,054,380 | 164.35 | 26,935 | 377,901 | 51.96 |
| 18 | 16,120 | 53,466 | 2,471,432 | 604.77 | 55,982 | 1,014,878 | 136.15 |
| 19 | 26,324 | 87,101 |  |  | 102,075 | 1,874,713 | 283.38 |
| 20 | 40,807 | 135,463 |  |  | 206,532 | 3,674,407 | 671.27 |

The plain column model, without windows, took 0.13, 0.27, 1.4, 4.8 and
33 s of CPU time for bases 8 to 12 under CP-SAT (`r5l_cpsat_counts.txt`),
about 4 times per base, and was not run further. I stopped CaDiCaL after
base 18 (605 s). CP-SAT with windows finished base 20 (671 s) and hit its
limit of 1,800 s of wall time in base 21, after it had found the one
solution with 20 digits.

Growth per base, least squares:

| measure | bases 8 to 17 | bases 12 to 18 (CaDiCaL) or 20 (CP-SAT) |
|---|---:|---:|
| engine nodes | 1.88 | 1.89 (bases 12 to 30) |
| CaDiCaL conflicts | 1.99 | 1.96 |
| CaDiCaL CPU time | 2.31 | 2.33 |
| CP-SAT window conflicts | 1.92 | 1.95 |
| CP-SAT window branches | 1.92 | 1.89 |
| CP-SAT window CPU time | 2.06 | 2.23 |

At base 18 the engine needs 0.006 s on one thread, CP-SAT with windows
136 s and CaDiCaL 605 s. No solver comes near the floor of 1.64 per base
that question 77 asks about, and none beats the engine's 1.89.

### 27.1.3 Why the solvers lose

The conflicts track the engine's nodes. CP-SAT with windows needs 2.0 to
5.1 conflicts per engine node at every base from 8 to 20. CaDiCaL needs 57
to 153 conflicts per node. If learned clauses cut across branches,
conflicts per node would fall as `b` grows. They do not; if anything they
rise slowly. A conflict is a refuted partial assignment, and the learned
clause excludes about one subtree of the engine's tree (heuristic).

There are two reasons.

1. The interval is the only cheap pruning, and a column encoding hides it.
   The top digits of `S` depend on every lower column through the carries.
   Unit propagation and bound propagation on single columns cannot see that
   a few large counts already fix the leading digits. Without the windows,
   CP-SAT grows about 4 times per base. CaDiCaL's conflicts still grow like
   the tree, but it needs about 100 of them per node of the tree.
2. Once the interval is visible, a solver can learn only what section 27.3
   allows. A learned clause states that a set of partial assignments fails.
   If it comes from the interval, Theorem 27.5 bounds how many such sets an
   exact proof needs, and the bound is of the order of the widest level of
   the tree. If it comes from the low columns, it uses the low digits of
   `S`, which the model treats as random. Then it excludes one combination
   of counts and says nothing about its neighbours.

So clause learning is not the "search that is not a tree" that beats
the floor. With the interval made visible, it is a top-down tree with a
cost per node about `10^4` times that of `fast`.

## 27.2 The entropy bound for other orders (question 75)

### 27.2.1 Any set of revealed values

A tree that reveals counts has, at level `m`, the counts of a set `R` of `m`
digit values. In section 10.1 `R` holds the `m` largest values. Here `R` is
any set, and it can depend on the node.

Let `u` be the largest value outside `R` and `rf` the number of free
positions. The free positions hold values outside `R`, so `S` lies in an
interval of width at most `rf w(u)`. The node knows the leading digits of
`S` down to that size. The unknown part has about

    L(u) = min(d, (ln rf + u ln u) / ln b + 1)

digits, with `rf = d (b - m) / b` in the model. For the top `m` values,
`u = b - 1 - m`, and this is the formula of `analysis/exponents.py`.

Assumption M(R). Given that a solution lies below a node with revealed set
`R`, the copies of the values of `R` among the `L(u)` unknown positions are
independent Poisson(`L(u) / b`) counts. For the top values this is the
assumption of Theorem 10.1. The node law then has the entropy

    H(R) = m h(L(u) / b),     h(lambda) = entropy of Poisson(lambda).

Lemma 27.1 (proven). For every set `R` of `m` values, `H(R) >= H(top m)`.
Equality holds only if `L(u)` is the same as for the top `m` values, in
particular for `R` = the top `m` values.

Proof. The complement of `R` has `b - m` values, so its largest value is
`u >= b - 1 - m`, with equality only for the top `m` values. `u ln u` is
nondecreasing for integers `u >= 0` (with `0 ln 0 = 0`), so `L(u)` is
nondecreasing in `u`. Finally `h` is increasing. Poisson(`lambda + mu`) is
the law of `X + Y` with independent `X ~ Poisson(lambda)` and
`Y ~ Poisson(mu)`, and `H(X + Y) >= H(X + Y | Y) = H(X)`.

Write `H_m = H(top m)` for the entropy of the top-down tree at level `m`.

Theorem 27.2 (proven, in the model). Take a tree that reveals one count per
level, in an order that can depend on the node. Let `S` be a set of nodes of
level `m` that it tries, and `p` the probability that `S` contains the node
above the solution. Then for every `t > 0`

    |S| >= (p - V / t^2) e^(H_m - t),

where `V` is the largest varentropy of the node law over the sets `R` of
size `m`.

Proof. Let `X` be the node above the solution and `R(X)` its revealed set.
The path from the root determines `R(X)`, so `R(X)` is a function of `X`,
and `P(X = x) <= P(X = x | R = R(x))`. Put `Y = -ln P(X | R(X))`. Given
`R = r`, `Y` has mean `H(r) >= H_m` by Lemma 27.1 and variance at most `V`.
By Chebyshev's inequality, `P(Y <= H_m - t) <= V / t^2`. A node `x` with
`P(x) >= e^(-H_m + t)` has `Y <= H_m - t`, so these nodes hold probability
at most `V / t^2`. Every other node of `S` has probability below
`e^(-H_m + t)`. So `p <= V / t^2 + |S| e^(-H_m + t)`.

`V` is `O(b)`, as in section 10.2. So every order needs `e^(H_m - O(sqrt b))`
nodes at every level `m`. At the peak level of the top-down tree
`H_m = 0.4933 b` in the limit. Theorem 10.1 therefore extends to all orders,
fixed or chosen node by node: every tree that reveals counts needs about
`1.638^b` nodes, and the top-down order is the only one that can reach this
floor.

### 27.2.2 The peak entropy of some orders (computed)

`analysis/r5l_orders.py` evaluates `max_m H(R_m)` for `d = b - 1`. It also
checks Lemma 27.1 by brute force over all sets `R` for `b = 4` to 14.

| order | `b = 40` | `b = 100` | `b = 1000` |
|---|---:|---:|---:|
| top-down | `0.432 b` (`1.540^b`) | `0.439 b` (`1.551^b`) | `0.453 b` (`1.573^b`) |
| bottom-up | `1.258 b` (`3.519^b`) | `1.286 b` (`3.619^b`) | `1.303 b` (`3.680^b`) |
| middle-out | `1.226 b` (`3.407^b`) | `1.273 b` (`3.572^b`) | `1.302 b` (`3.675^b`) |
| random, mean of 20 orders | `1.120 b` (`3.064^b`) | `1.188 b` (`3.280^b`) | `1.271 b` (`3.563^b`) |
| odd values first, each class top-down | `0.679 b` (`1.972^b`) | `0.689 b` (`1.993^b`) | `0.700 b` (`2.013^b`) |
| by residue mod 3, each class top-down | `0.871 b` (`2.389^b`) | `0.870 b` (`2.388^b`) | `0.870 b` (`2.387^b`) |
| upper half bottom-up, then the lower half top-down | `0.613 b` (`1.846^b`) | `0.637 b` (`1.890^b`) | `0.651 b` (`1.917^b`) |

The top-down row repeats section 10.2 (17.3, 43.9 and 453.1 nats). The
other rows have one cause. As long as `b - 1` is not revealed, `u = b - 1`,
the interval says nothing (`L = d`), and every revealed count costs the full
entropy `h(d / b)`, about 1.30 nats. Bottom-up and middle-out reveal `b - 1`
last and peak near `1.30 b`, the entropy of a whole count vector. A random
order reveals `b - 1` at a random level. Orders by residue keep a large
value unrevealed for a whole class. The upper half bottom-up keeps `b - 1`
unrevealed for `b/2` levels.

### 27.2.3 The best adaptive tree in small bases (computed)

Section 27.3 computes, for small bases, the smallest exact tree that chooses the
value to branch on node by node (column "best adaptive tree" of Table 27.3.1).
It is 0.83 to 0.91 times the top-down tree for `b = 5` to 10.
`analysis/r5l_optchoice.py` walks this optimal tree: it branches on the
largest unrevealed value at 78% to 86% of its internal nodes. So in small
bases the best order is top-down up to small local changes, as
Lemma 27.1 predicts.

Theorem 27.2 is a statement about the model and about trees whose nodes are
partial assignments of counts. Section 27.3 proves a statement for exact
searches without the model and without the tree.

## 27.3 Certificates of emptiness in an oracle model (question 76)

### 27.3.1 The model and the bound

Fix `b`, `d` and the weights `w`. `C_d` is the set of count vectors with
sum `d`. A query is a cylinder `x = (R, c_R)`: a set `R` of values with
counts `c_R`, `sum c_R <= d`. Its completions put the
`rf = d - sum c_R` free copies on the values `U` outside `R`. The oracle
answers with the interval test of `fast`:

    I(x) = [t + rf min_U w, t + rf max_U w] intersected with [b^(d-1), b^d - 1],

where `t = sum over R of c_v w(v)`. Let `P(x)` be the common leading digits
of the ends of `I(x)`. The cylinder fails if `I(x)` is empty, if `P(x)`
holds more than `c_v` copies of some `v` in `R`, or if `P(x)` holds more
than `rf` digits outside `R`. A cylinder with `rf = 0` or with one value
outside `R` is a single vector, and the oracle then says whether it is a
solution (a leaf check).

Lemma 27.3 (proven). A failing cylinder contains no solution.

Proof. If `c` in `x` is a solution, then `S(c)` lies in `I(x)` and starts
with `P(x)`, so `P(x)` holds each value `v` at most `c_v` times. For `v` in
`R` this is `(c_R)_v`. The digits outside `R` number at most the sum of
`c_v` over `U`, which is `rf`.

A certificate of emptiness is a set of failing cylinders whose union is
`C_d`. To list all solutions, a certificate covers `C_d` minus the
solutions.

Proposition 27.4 (proven). In the oracle model, every algorithm that
correctly reports that there is no solution with `d` digits has queried a
certificate. This holds for any order, for trees, for searches that are
not trees, and for randomized algorithms.

Proof. The model makes the instance a pair (weights, solution set), where
the solution set can be any set that meets no failing cylinder. Lemma 27.3
says that the true set is one of them. If some `c` lies in no failing
queried cylinder, then `c` was never checked as a leaf, and the instance
with solution set `{c}` gives the same answers to every query. The
algorithm must answer the same on both instances, so it is wrong on one.

The question is how small a certificate can be. The bound below uses the
largest prefix of `S(c)` that `c` itself is consistent with.

Definitions. Let `G` be the set of non-solutions `c` in `C_d` such that
`S(c)` has `d` digits and does not start with the digits `1, 0` or
`b-1, b-1`. For `c` in `G`, let `lambda(c)` be the largest `l` such that
the top `l` digits of `S(c)` hold each value `v` at most `c_v` times, and
require `lambda(c) >= 1`. Let `g(u)` be the smallest of `w(u) - w(m)` over
`m < u`, and `theta(c)` the least `t` such that `g(u) >= b^(d - lambda(c) - 1)`
for every `u >= t`. For a level `k`, let `V_k` be the values `>= k`, and
`N_k` the number of distinct restrictions `c|V_k` over the `c` in `G` with
`theta(c) <= k`.

Theorem 27.5 (proven). Every certificate of emptiness has at least `N_k`
cylinders, for every `k`.

Proof. First a claim. Let a failing cylinder `x` contain `c` in `G`, and
let `x` not be a single vector. Then every value outside `R` is below
`theta(c)`.

Suppose that some value `>= theta(c)` lies outside `R`, and let `u` be
the largest value outside `R`. Since `x` is not a single vector, `rf >= 1`
and `U` holds a value `m < u`. If `I(x)` is not clipped, its width is
`rf (max_U w - min_U w) >= w(u) - w(m) >= g(u)`, and `u >= theta(c)`.
That is at least `b^(d - lambda - 1)`, so the ends of `I(x)` differ in a
digit at position `d - lambda - 1` or above, and `P(x)` has at most
`lambda` digits. If `I(x)` is clipped at `b^(d-1)` or at `b^d - 1`, then
`P(x)` is a common prefix of `S(c)` and of `1, 0, 0, ...` or of
`b-1, b-1, ...`. `S(c)` starts with neither pair, so `P(x)` has at most one
digit. In both cases `P(x)` is a prefix of the top `lambda(c)` digits of
`S(c)`. So it holds each `v` at most `c_v` times, and `x` passes as in
Lemma 27.3. This contradicts the assumption that `x` fails.

Now take `c != c'` in `G` with `theta(c), theta(c') <= k` and
`c|V_k != c'|V_k`. A failing cylinder that contains both is not a single
vector. By the claim, `R` contains every value `>= theta(c)`, so all of
`V_k`. A cylinder fixes the counts on `R`, so `c` and `c'` agree on `V_k`.
This is a contradiction. One vector per restriction gives `N_k` vectors, no
two of them in one failing cylinder, so a certificate needs `N_k`
cylinders.

Remark 27.6 (proven). The engine's test also forces the leading digits below
`k` and checks the first unknown digit (`docs/algorithm.md`). The theorem
holds for that test too, with `b^(d - lambda)` in place of
`b^(d - lambda - 1)` and `lambda >= 2`. Two vectors `c != c'` in one
cylinder each contain every forced digit. If the forced digits filled all
`rf` free slots, `c` and `c'` would be equal. So at least one free slot
stays open, every interval of the forcing loop keeps the width `g(u)`, and
`P(x)` stays within the top `lambda - 1` digits of both sums. The first
unknown digit is then a digit of `S(c)` within its top `lambda` digits, and
it has a copy left in `c`.

Corollary 27.7 (proven). `N_k` is at least the number of surviving nodes `y`
of level `k` of the top-down tree that have a witness. A witness is the
completion of `y` that adds the forced digits of `P(y)` and puts the other
free copies on one value, if it lies in `G`, is not a solution and has
`theta <= k`. Distinct nodes give distinct restrictions to `V_k`.

The corollary needs only a walk of the top-down tree, so it reaches larger
bases than Theorem 27.5 itself.

### 27.3.2 Smallest certificates in small bases (computed)

`analysis/r5l_cert.py` builds every cylinder for `d = b - 1` under
`0^0 = 1` and tests it. It keeps the maximal failing cylinders and solves
the set cover exactly with CP-SAT. It also computes the smallest
certificate of a tree that chooses its branching value node by node (by
dynamic programming over all cylinders), the top-down certificate (the
failing cylinders that the top-down tree evaluates, with the same test), and
`max_k N_k` from Theorem 27.5.

Table 27.3.1. True weights `x^x`. All covers are proven optimal by CP-SAT.

| `b` | `\|C_d\|` | top-down nodes | top-down certificate | best adaptive tree | smallest certificate | `max_k N_k` |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 70 | 7 | 18 | 16 | 16 | 4 |
| 6 | 252 | 15 | 40 | 33 | 29 | 7 |
| 7 | 924 | 20 | 60 | 53 | 51 | 9 |
| 8 | 3,432 | 56 | 184 | 167 | 113 | 21 |
| 9 | 12,870 | 118 | 368 | 325 | 229 | 41 |
| 10 | 48,620 | 233 | 794 | 682 | 414 | 76 |

Random weights `w(x) = x^x + U[0, x^x / 4]` for `x >= 2`, `b = 9`, three
seeds: top-down certificates 266, 553 and 576; best adaptive trees 214, 477
and 490; smallest certificates 165, 314 and 365; `max_k N_k` 22, 53 and 57.

So in these bases a certificate that is not a tree saves a factor 1.6 to 1.9
over the top-down tree, and an adaptive tree saves 9% to 20%. The bound of
Theorem 27.5 is 0.18 times the optimum for `b = 8` to 10, with no trend.

Table 27.3.2. The bound of Corollary 27.7 against the top-down tree, true
weights, `d = b - 1` (`r5l_cert.py --tree-only`).

| `b` | top-down nodes | widest level | witness bound on `N_k` | bound / widest level | certificate / bound |
|---:|---:|---:|---:|---:|---:|
| 10 | 233 | 65 | 64 | 0.98 | 12.4 |
| 12 | 900 | 214 | 209 | 0.98 | 17.1 |
| 14 | 2,527 | 576 | 563 | 0.98 | 19.1 |
| 16 | 11,173 | 2,294 | 2,248 | 0.98 | 26.9 |
| 18 | 43,791 | 8,609 | 7,465 | 0.87 | 32.3 |
| 20 | 119,669 | 22,156 | 19,893 | 0.90 | 38.1 |
| 21 | 229,527 | 41,585 | 38,695 | 0.93 | 36.8 |

From base 12 to 21 the bound grows 1.79 per base, the tree 1.87 per base,
and its certificate 1.98 per base. The ratio of the certificate to the bound
grows about linearly in `b`, as it must: a tree has at most `b` levels, and
a node has at most `d + 1` children.

### 27.3.3 What this says

Every exact method that learns about `S` only through interval queries on
partial assignments of counts needs at least `max_k N_k` queries. For
bases 5 to 21 this is at least 0.86 times the widest level of the exact
tree. In the model the widest level holds about `C(L + m, m)` nodes with
`m + L` near `b` (section 9.1), that is `2^(b - O(log b))`. So, if the
witness share stays bounded below as it does up to base 21 (heuristic), the
answer to question 76 is yes: the smallest certificate is of the order of the
exact tree, up to a polynomial factor. Section 9.1 argued this; Theorem
27.5 proves it for the oracle model.

A faster exact method must therefore use what the oracle hides: the low
digits of `S`, that is the arithmetic of `x^x`. Section 27.1 tests a solver
that sees the low digits through column sums, and section 27.4 tests the only
exact low-digit structure known, in bases `2^k`.

## 27.4 Bottom digits in bases with a small radical (question 79)

### 27.4.1 Which counts fix the bottom digits

Proposition 27.8 (proven). In base `b`, `w(v) = v^v` is divisible by
`b^L` if and only if `v * v_p(v) >= L v_p(b)` for every prime `p | b`. If
every value outside `R` has this property, the bottom `L` digits of `S` are
`sum over R of c_v w(v) mod b^L`, known exactly. Every value prime to `b`,
in particular `v = 1` with `w(1) = 1`, and `v = 0` under `0^0 = 1`, never
has it.

Proof. `v_p(v^v) = v v_p(v)`, and `v_p(b^L) = L v_p(b)`.

In base `2^k` the values that fix the bottom `L` digits are therefore the
`b/2` odd values, 0, and the even values with `v v2(v) < k L`
(`r5l_bottom.py table`):

| `b` | `L = 1` | `L = 2` | `L = 3` | `L = 4` | `L = 5` |
|---:|---:|---:|---:|---:|---:|
| 32 | 18 (0.56 b) | 20 (0.62 b) | 22 (0.69 b) | 23 (0.72 b) | 26 (0.81 b) |
| 64 | 34 (0.53 b) | 37 (0.58 b) | 38 (0.59 b) | 40 (0.62 b) | 43 (0.67 b) |
| 128 | 67 (0.52 b) | 69 (0.54 b) | 71 (0.55 b) | 75 (0.59 b) | 77 (0.60 b) |

For example in base 32 the counts of the odd values, of 0 and of 2 fix the
last digit; adding 4 and 6 fixes the last two digits. Bases `2^k` need the
fewest values: in a base with a larger radical fewer weights vanish.

Corollary 27.9 (proven). In the top-down order the values 1 and 0 come
last. The bottom digits are known only when at most the value 0 is
unrevealed, and then the node is a single vector, which the leaf check
tests exactly anyway. So a bottom check never prunes a top-down tree.

To use bottom digits early, a tree must reveal the small odd counts before
the large counts, and Theorem 27.2 says what that costs.

### 27.4.2 Toy trees (computed)

`analysis/r5l_bottom.py` and its exact Rust port `fast/src/bin/r5l_bottom.rs`
(the two agree on bases 8 and 16 and on the top five levels of base 32) count
the nodes of four trees for `d = b - 1` under `0^0 = 1`. All use the
interval test of section 27.3. The trees with bottom checks also test, at
every node where the revealed counts fix `L >= 1` bottom digits, that the
leading and the bottom digits together fit the counts.

- plain: top-down, no bottom check;
- plain+bot: top-down with bottom checks;
- hybrid: top-down down to `b/2`, then the odd values below `b/2`, then 0,
  then the even values in the order in which they unlock bottom digits,
  then the rest;
- odd-first: the odd values top-down, then 0, then the even values as in
  hybrid.

| `b` | plain | plain+bot | hybrid | odd-first |
|---:|---:|---:|---:|---:|
| 8 | 56 | 56 | 65 (1.16x) | 348 (6.2x) |
| 16 | 11,178 | 11,178 | 27,512 (2.46x) | 3,426,255 (307x) |
| 32 | 253,827,862 | 253,827,862 | 3,381,869,941 (13.3x) | about `10^11` to `10^12` (estimate) |

The engine, with forcing and the first-digit test, visits 87,615,529 nodes
for base 32 and `d = 31`. The plain toy tree took 1,918 s and the hybrid
tree 8,233 s on 2 threads in Rust. The odd-first tree in base 32 is too large to count. Its odd levels
alone hold all count vectors of the 16 odd values with sum at most 31 that
the weak interval leaves, up to `C(47, 16) = 1.5 * 10^12`; Knuth's random
probes (`r5l_bottom.py trees 32`, 5,000 probes) give `5.5 * 10^11` with a
standard error as large as the estimate. The same probes give
`1.7 * 10^7` for the plain tree, 15 times too low, so they are only a rough
guide.

### 27.4.3 Why bottom digits do not pay (heuristic)

To read even one bottom digit, the tree must know the counts of at least
`b/2 + 2` values, including every small odd value. Before the value `b - 1`
is revealed, each count costs about 1.30 nats of entropy (section 27.2.2).
Revealing the 16 odd counts of base 32 first costs about `e^21 = 10^9`
nodes; the plain toy tree has `2.5 * 10^8` nodes in all. One bottom digit
then removes a node only when its value has no copy left, which in the
model happens with probability below `1/2`. The hybrid tree postpones the cost to the lower
half of the values, where the top-down tree is already narrow, and still
loses a factor 2.5 in base 16 and 13.3 in base 32. The loss grows with
the base. In base 32, 64 and 128 the radical is 2, the
smallest possible, and the bottom digits still cost more than they prune. I
expect the same in every base. The answer to question 79 is no.

## 27.5 The law of the work-unit sizes (question 78)

### 27.5.1 Measurements (computed)

`fast search` has a new option `--unit-stats <file>`. It writes one line per
finished work unit: its index, its digit count `d`, the next digit `k`, the
free slots `rf`, the known leading digits, its start and end times and the
running node count. With `-j 1` the difference of the node counts is the
size of the unit. `analysis/r5l_units.py run` makes these runs, and adds the
nodes that build the unit list (a `--shard` with no units). The sum of the
unit sizes equals the node count of the run in every base.

Table 27.5.1. All bases, both conventions, unit depth 4 (the default). The
makespan columns simulate list scheduling in unit order without splitting a
unit, relative to the ideal `total / P`. The shard columns give the largest
`--shard i/n` part relative to the mean.

| b | depth | units | nodes | largest unit | top 1% of units | sd of ln(nodes) | type explains | within-type sd | makespan 64 / 512 threads | 16 / 64 shards, max / mean |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 24 | 4 | 14,034 | 1,430,261 | 0.0102 | 0.47 | 1.92 | 0.93 | 0.50 | 1.04 / 5.30 | 1.45 / 2.12 |
| 26 | 4 | 22,331 | 4,955,060 | 0.0114 | 0.55 | 2.10 | 0.94 | 0.51 | 1.02 / 5.92 | 1.31 / 1.72 |
| 27 | 4 | 28,152 | 9,510,641 | 0.0108 | 0.60 | 2.20 | 0.95 | 0.51 | 1.01 / 5.63 | 1.27 / 1.58 |
| 28 | 4 | 32,977 | 18,025,432 | 0.0126 | 0.65 | 2.30 | 0.95 | 0.50 | 1.12 / 6.50 | 1.28 / 2.23 |
| 29 | 4 | 39,730 | 33,546,007 | 0.0110 | 0.66 | 2.41 | 0.96 | 0.50 | 1.02 / 5.71 | 1.30 / 1.89 |
| 30 | 4 | 48,595 | 66,246,690 | 0.0135 | 0.70 | 2.50 | 0.96 | 0.51 | 1.07 / 7.01 | 1.16 / 2.56 |
| 31 | 4 | 60,158 | 121,387,604 | 0.0102 | 0.74 | 2.57 | 0.95 | 0.55 | 1.02 / 5.29 | 1.20 / 1.81 |
| 32 | 4 | 71,211 | 214,709,067 | 0.0102 | 0.75 | 2.68 | 0.96 | 0.53 | 1.01 / 5.34 | 1.16 / 1.85 |
| 33 | 4 | 84,571 | 464,274,849 | 0.0096 | 0.80 | 2.78 | 0.96 | 0.54 | 1.02 / 5.00 | 1.25 / 1.95 |
| 34 | 4 | 97,649 | 824,063,470 | 0.0109 | 0.81 | 2.88 | 0.97 | 0.54 | 1.01 / 5.65 | 1.31 / 1.86 |

The unit sizes are very uneven, and more so in larger bases: the largest 1%
of the units hold 47% of the work in base 24 and 81% in base 34. The pooled
law has a heavy tail. The Hill estimate of its tail index, from the largest
1% of the units, falls from 1.45 in base 24 to 0.95 in base 32, that of a
Pareto law with infinite mean. The largest single unit stays near 1% of
the work.

### 27.5.2 Type and branching (computed; heuristic)

The type of a unit is its digit count `d`, its free slots `rf` and its known
digits. The type explains 93% to 97% of the variance of `ln(nodes)` in
every base. Within a type the standard deviation of `ln(nodes)` is 0.50 to
0.55, a factor of 1.65, and the tail is light. In bases 28, 30, 32 and 33,
2.6% of the units exceed twice the mean of their type, 0.03% to 0.07% exceed
four times, and none exceeds twelve times.

For `d = b - 1` a two-term fit explains 98% of the variance:

    ln(nodes) = 10.5 + 0.656 rf - 0.457 L     (base 30, L = unknown digits)
    ln(nodes) = 11.1 + 0.657 rf - 0.429 L     (base 33)

Each free slot multiplies the subtree by `e^0.656 = 1.93`, the growth of
the whole search per base. So a unit with `rf` free slots behaves like a
search over a base with about `rf` digits.

This is the branching-process picture of direction A3 (heuristic). Within a
type, a subtree is a branching process with bounded offspring: a node has at
most `rf + 1` children. For a Galton-Watson process with bounded offspring
the normalized size `Z / E Z` has exponential moments, a classical fact.
The process here is not homogeneous, but the same light tail is what the
data show: no unit of a given type is much larger than its mean. The heavy
tail of the pooled law comes from mixing the types. `E Z` grows like
`1.93^rf`, and `rf` varies from 1 to about `b - 6` across the units of
depth 4. A spread of `rf` turns into a spread of `ln(nodes)` with the
factor 0.656, which is why the pooled tail looks like a power law and why
its standard deviation grows with `b`.

### 27.5.3 Scheduling and unit depth (computed)

Table 27.5.2. Base 30 at every unit depth from 2 to 7.

| b | depth | units | nodes | largest unit | top 1% of units | sd of ln(nodes) | type explains | within-type sd | makespan 64 / 512 threads | 16 / 64 shards, max / mean |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 30 | 2 | 1,547 | 66,246,690 | 0.0971 | 0.60 | 3.64 | 0.98 | 0.51 | 6.23 / 49.72 | 2.15 / 7.72 |
| 30 | 3 | 9,934 | 66,246,690 | 0.0346 | 0.69 | 2.99 | 0.96 | 0.56 | 2.34 / 17.71 | 1.72 / 4.19 |
| 30 | 4 | 48,595 | 66,246,690 | 0.0135 | 0.70 | 2.50 | 0.96 | 0.51 | 1.07 / 7.01 | 1.16 / 2.56 |
| 30 | 5 | 185,561 | 66,246,690 | 0.0046 | 0.68 | 2.13 | 0.94 | 0.53 | 1.00 / 2.56 | 1.14 / 1.38 |
| 30 | 6 | 573,204 | 66,246,690 | 0.0020 | 0.62 | 1.84 | 0.92 | 0.52 | 1.00 / 1.25 | 1.05 / 1.22 |
| 30 | 7 | 1,444,186 | 66,246,690 | 0.0006 | 0.55 | 1.62 | 0.90 | 0.51 | 1.00 / 1.01 | 1.07 / 1.20 |

The per-unit files for depths 6 and 7 (6 and 15 MB compressed) are not in
the repository; `r5l_units.py run 30 --unit-depth 7` rebuilds them in about
a minute. Each extra level of unit depth divides the largest unit by 2.3 to
3.4.
Building the units is serial and costs 194 nodes at depth 2 and 819,036
at depth 7, 1.2% of the run.

On one machine the unit depth does not matter. With 8 threads, list
scheduling of the units of depth 4 in index order finishes within 0.1% of
the ideal time in every base from 24 to 34, even without the splitting
inside a unit that `fast` also does (`--par-depth`). Up to 64 threads it
stays within 12%. Only at 512 parallel workers do the largest units bound the
run: the makespan is 5 to 7 times the ideal at depth 4, because one unit
holds about 1% of the work. Deeper units fix this (Table 27.5.2). A rule that
fits Table 27.5.2: choose the unit depth at which the largest unit holds less
than `1/(4P)` of the work for `P` workers or shards. In base 30 that is
depth 4 up to about 16 workers, depth 6 for 64 and depth 7 for about
400.

Shards are the weak point. `--shard i/n` takes every `n`-th unit, and with
units this uneven a shard of 16 can get 1.16 to 1.45 times the mean work, a
shard of 64 up to 2.6 times. A shard cannot be smaller than its largest
unit. For many machines, use a deeper unit depth: in base 30, 64 shards
are within 1.22 of the mean at depth 6 (Table 27.5.2). An assignment
by predicted size (longest first, with the size predicted from the type)
helps less than the deeper units: for 64 shards at depth 4 it gives 1.40 to
1.47 instead of 1.85 to 2.56, in bases 28 to 33.

### 27.5.4 Time estimates (computed)

Before a run. The node count of the previous base times 1.9 is the best
estimate. From base 26 to 34 the ratio of consecutive bases is 1.77 to
2.16, mean 1.90, standard deviation 0.13. A sample of the units is worse:
the total from one shard of 16 is off by 10% to 24% (standard deviation)
and from one shard of 64 by 29% to 43%, because a shard misses or catches
the few large units.

During a run. The progress line of `--progress` reported the number of
finished units. In unit order, when half the work is done only 27% to 33% of
the units are; the error of the unit fraction reaches 0.39 to 0.49. The
progress line now adds "about x% of the work (estimate)". It weights each
unit by `exp(0.656 rf - 0.44 L)` within its digit count, and gives the digit
counts `d = b, b-1, b-2, b-3, ...` the measured shares 0.205, 0.48, 0.21,
0.068 and so on. Replayed on the unit data in index order, its largest
error is 0.054 to 0.095 in bases 26 to 33. In a live run of base 31 on 2
threads it said 55% when 47% of the nodes were done. The weights are fitted
to the exact search with the weights `x^x`; with other options they are
only a rough guide. The option changes nothing but the progress lines.

### 27.5.5 Answer

The unit sizes follow a mixture of light-tailed laws, one per type, whose
means grow like `1.93^rf`. The pooled law has a power-like tail and grows
more skewed with the base. On one machine this costs nothing: the scheduling
of `fast` is within 0.1% of the ideal at 8 threads. It matters for many
shards and for time estimates. For time estimates, use the previous base
times 1.9 before the run, and the weighted progress during it. No constant
factor in speed is available from scheduling on one machine.

## 27.6 Status

| question | answer | status |
|---|---|---|
| 77, a solver that is not a tree | CP-SAT and CaDiCaL are exact but grow 1.95 to 2.3 per base against 1.89 for `fast`, at `10^4` to `10^5` times its cost; learned clauses do not cut across branches (section 27.1) | computed |
| 75, other orders | every order, fixed or adaptive, has at each level at least the entropy of top-down; top-down is optimal, others peak at `0.6 b` to `1.30 b` nats (Theorem 27.2) | proven in the model; computed |
| 76, certificates | every certificate in the interval oracle model has at least `max_k N_k` queries (Theorem 27.5), at least 0.86 of the widest level for bases 5 to 21; the smallest certificate is 0.52 to 0.62 of the top-down one in bases 8 to 10 | proven; computed; the asymptotic `2^(b - O(log b))` is heuristic |
| 79, bottom digits in base `2^k` | useless for top-down trees (Corollary 27.9), and a loss for every order that reveals the odd counts early | proven; computed |
| 78, work units | type-determined, light-tailed within a type, heavy-tailed overall; scheduling on one machine is already ideal; deeper units for many shards; previous base times 1.9 and the new weighted progress for time estimates | computed; heuristic |

Open: a proof that the witness share of Corollary 27.7 stays bounded below
as `b` grows, which would make the `2^(b - O(log b))` bound of question 76 a
theorem in the oracle model. And an oracle that also reveals low digits:
Theorem 27.5 says nothing about methods that use them, and sections 27.1 and 27.4
only show that the two natural ones lose.
