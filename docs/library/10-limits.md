# 10. How fast a randomized search can be, and the length window

Chapter 9 built a search that skips unlikely parts of the tree. It grows about
1.71x per base instead of 1.89x. This chapter asks how far that idea can go.
It derives the growth rates of the exact tree and of its likely part, proves a
lower bound for every search of this kind, and gives a rule that comes close
to it with a miss rate that does not grow with the base. It then checks the
other ideas for a large speedup and explains why each one fails. The last part
tests the length window of Conjecture 9.4 and sharpens it.

## 10.1 Three growth rates

Section 9.1 counts the nodes at level `k`. With `kappa = k / b`, the unknown
suffix has about `kappa b` digits for large `b`, and `m = (1 - kappa) b` digit
values are decided. This gives two growth rates.

- Exact tree. Every vector of counts that fits the prefix is a node. That is
  `C(b, kappa b)` nodes, which is largest at `kappa = 1/2`. So the exact tree
  grows like `2^b`, slowly, from below.
- Likely part. Suppose that a solution lies below some node of level `k`. In
  the model, the copies of the large digits in the suffix then follow a
  multinomial law: each of the `m` values appears about Poisson(`kappa`) times.
  The entropy of this law is `H = (1 - kappa) b * H(Poisson(kappa))`. It is
  largest at `kappa = 0.37`, where it equals `0.4933 b`. So the likely part
  grows like `e^0.4933 = 1.638` per base.

`analysis/exponents.py` evaluates both formulas at finite `b`:

| base | exact tree, growth per base | likely part, growth per base |
|---:|---:|---:|
| 20 | 1.85 | 1.55 |
| 40 | 1.88 | 1.55 |
| 100 | 1.92 | 1.56 |
| 1,000 | 1.94 | 1.58 |
| 10,000 | 1.96 | 1.59 |
| limit | 2 | 1.638 |

The exact search measures 1.89 per base from base 30 to 43, as the formula
says. The exact search therefore gets slightly worse in larger bases. The gap
between the two columns, `(2 / 1.638)^b = 1.22^b` in the limit, is all that
skipping unlikely nodes can gain.

## 10.2 A lower bound for tree searches

Theorem 10.1. Fix a level `k`. In the model, let `P` be the law of the node of
level `k` that lies above the solution, given that there is one, and let `H` and
`V` be the entropy and the varentropy of `P`. A search that tries a set `S` of
level-`k` nodes and contains the right one with probability `p` has

    |S| >= (p - V / t^2) e^(H - t)      for every t > 0.

Proof. A node `x` with `P(x) >= e^(-H + t)` is rare in the sense that the
probability of `-ln P(X) < H - t` is at most `V / t^2`, by Chebyshev's
inequality. All other nodes in `S` have probability below `e^(-H + t)` each,
so together they hold at most `|S| e^(-H + t)`. So `p <= V / t^2 + |S| e^(-H + t)`.

`V` grows linearly with `b`, so the choice `t = sqrt(2V / p)` gives
`|S| >= (p/2) e^(H - O(sqrt b))`. At the peak level:

| base | peak level `k` | `H` | `sqrt(V)` | `e^H` |
|---:|---:|---:|---:|---:|
| 40 | 17 | 17.3 | 3.7 | `3.2 * 10^7` |
| 100 | 42 | 43.9 | 5.9 | `1.1 * 10^19` |
| 1,000 | 406 | 453.1 | 18.7 | `6.3 * 10^196` |

So any search that walks the tree from the largest digit down, exact or not,
needs about `1.638^b` nodes in large bases if it is to find a solution with
probability one half. For the exact tree at base 40 the bound is 1,300 times
smaller than the tree.

The theorem is a statement about the model. In it, the copies of the large
digits in the unknown suffix are random. For real weights `x^x` this is the
assumption that chapter 5 tests.

## 10.3 A rule that reaches the bound

The entropy argument says which nodes to keep: those whose probability is
close to `e^-H`. The search computes for each node the expected number of
solutions `E` of section 9.2. In the model, `E` is the probability of the
observed multinomial outcome, so `ln E` has mean `-H` and standard deviation
`sqrt(V)`. The option `--zscore c` drops a node if

    ln E < -H - c sqrt(V).

The engine precomputes `H` and `V` for each level and each number of unknown
positions, with the Poisson approximation. The approximation gets the mean
right within 2% and overestimates the standard deviation by up to 2x at the
middle levels (checked by sampling). At the top levels only a few digit values
are decided, and `ln E` has a long left tail. Most misses came from there,
and the tree is narrow there anyway, so the rule only applies at levels
`k <= 3/4 (kmax + 1)`.

`analysis/zscore_sweep.py` measures it like section 9.3:

| rule | growth, bases 24-30 | growth, bases 30-38 | nodes at base 38 | missed |
|---|---:|---:|---:|---:|
| exact | 1.89 | 1.89 | about `10^10` (extrapolated) | 0 |
| `--zscore 3` | 1.74 | 1.75 | `1.17 * 10^9` | 0 of 112, bases 10-38 |
| `--zscore 2.5` | 1.72 | 1.71 | `7.4 * 10^8` | 0 of 84, bases 10-30 |
| `--zscore 2` | 1.70 | 1.70 | `4.5 * 10^8` | 6 of 112, bases 10-38 |
| `--deficit 2 --band 2.5` | 1.71 | | | 3 of 93, bases 10-32 |

The miss rate is what makes this rule better than the deficit rule of chapter
9. `analysis/min_zscore.py` replays each solution's path and records its worst
score `z_min`. The rule with threshold `c` misses the solution exactly when
`z_min < -c`. For planted solutions:

| base | median `z_min` | `P(z_min < -2.5)` | `P(z_min < -3)` | `P(z_min < -3.5)` |
|---:|---:|---:|---:|---:|
| 30 | -0.69 | 0.037 | 0.020 | 0.010 |
| 45 | -0.76 | 0.030 | 0.010 | 0.003 |
| 60 | -0.77 | 0.055 | 0.028 | 0.010 |
| 100 | -0.80 | 0.030 | 0.010 | 0.000 |
| 150 | -0.98 | 0.020 | 0.013 | 0.000 |
| 200 | -0.98 | 0.053 | 0.027 | 0.013 |
| 300 | -1.03 | 0.033 | 0.017 | 0.017 |

From base 30 to base 300 the miss rate at `c = 3` stays between 1% and 3%. For
the deficit rule it grew from 2% to 10% over the same range (section 9.5). On
the 54 real solutions with at least `b-6` digits in bases 20 to 43,
`--zscore 3` misses 2 (3.7%).

The measured growth, 1.75, is above the bound of section 10.1 for these bases,
1.55. The reason is the width of the kept band: `c sqrt(V)` grows like
`sqrt(b)`, which adds a factor of about `e^(c sqrt(V) / (2 b))` per base, or
1.15 at base 35 for `c = 3`. That factor tends to 1, so the rule's growth tends to the
bound. In the limit it saves `1.22^b` against the exact search with a fixed
miss rate.

## 10.4 Ideas for a larger speedup, and why they fail

Theorem 10.1 covers every search that walks the tree from the largest digit
down. A larger gain needs information that the tree does not use. I tried the
candidates below.

Iterating `F`. Solutions are the fixed points of `n -> F(n)`. From 200 random
starting numbers per base (`analysis/dynamics.py`, `0^0 = 1`):

| base | median steps before a repeat | median cycle length | orbits that end at a solution |
|---:|---:|---:|---:|
| 14 | 662 | 271 | 0 |
| 18 | 4,788 | 5,382 | 0 |
| 22 | 94,114 | 28,923 | 0 |

The orbits grow about 1.85x per base from base 14 to 22, and none ends at a
solution. All orbits fall into 2 to 5 cycles per base. A random map on the
`C(2b, b) ~ 4^b` digit multisets behaves the same way: its orbits have length
about `2^b`, and a fixed point attracts only a vanishing share of the starting
points. So iteration is worse than the tree.

Other invariants. The tree uses the leading digits of `n`. The only other
cheap information would be a residue `n mod M` that the digit multiset
determines.

Proposition 10.2. If `n mod M` depends only on the multiset of digits for all
numbers with `d >= 2` digits, then `M` divides `b - 1`.

Proof. Swap the last two digits `x` and `y`. The value changes by
`(x - y)(b - 1)`. With `x - y = 1` this must be `0 mod M`.

So the digit-sum identity of section 1.6 is the only such invariant. It
removes a factor of `b - 1`, which does not change the growth rate.

Update (chapter 31). The factor is a share of the nodes, not a factor
`b - 1` of the leaves. Tested on the nodes with one free slot, the
congruence removes 12% to 25% of the exact tree in bases 15 to 35, with no
trend in the base (Table 31.2.2). So it is a constant factor of about 1.1
to 1.35, as this section says. The other count and residue results of the
library add nothing to it: the interval test implies them, or their test
costs more than it saves (section 31.4).

Splitting the digit values. Split the digits into large values (with counts
`c_H`) and small values (with counts `c_S`), and try to join two lists. The
small digits only change the last `L` digits of `n`. Their digits are
`(W(c_H) + W(c_S)) mod b^L`, which depends on both halves through the residue
`rho = W(c_H) mod b^L`. A join must therefore use `rho` as part of its key. For
each value of `rho`, the small side must be recomputed. The cost is
`|H| + b^L |S|`, and `|H|` already includes the widest level of the tree.
Section 6.3 gives the same argument for a split by positions.

Representation technique. The best algorithms for random subset sum split a
solution into two halves in many ways and filter by a residue (Howgrave-Graham
and Joux 2010, Becker, Coron and Joux 2011). Here `W` is additive in the
counts, but the target `n` is not fixed: it is the unknown itself. Guessing its
residue costs as much as the filter saves. My estimate for a full multiset
search is `e^(1.28 b)`, worse than the tree.

Quantum search. Montanaro (2018) showed that a quantum computer can search a
backtracking tree of `T` nodes in about `sqrt(T)` steps. Applied here, this
gives about `1.41^b` exactly and `1.28^b` for the likely part. It is the only
known way past Theorem 10.1, and it needs a quantum computer.

In short, the leading digits are the only information that a partial
assignment of counts reveals cheaply. Theorem 10.1 shows what that information
is worth. A large classical speedup would need a new source of information
about the low digits of `n`, and Proposition 10.2 rules out the residues.

## 10.5 The length window

Conjecture 9.4 says that under `0^0 = 1`, almost all solutions with `k >= 3`
digits lie in bases `k < b <= k + (1 + eps) ln k`. This section tests it.

The model at finite `b` (`analysis/length_law.py`). Expected number of
solutions with `J = b - k`:

| `J` | base 50 | base 100 | base 200 | base 800 | limit |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.078 | 0.080 | 0.081 | 0.078 | 0.080 |
| 1 | 0.554 | 0.554 | 0.546 | 0.553 | 0.552 |
| 2 | 0.237 | 0.234 | 0.233 | 0.231 | 0.233 |
| 4 | 0.036 | 0.034 | 0.033 | 0.031 | 0.032 |
| 8 | 0.0029 | 0.0021 | 0.0018 | 0.0010 | 0.0006 |
| 10 | 0.00023 | 0.00035 | 0.00027 | 0.00023 | 0.00008 |
| 12 | 0.00030 | 0.00009 | 0.00002 | 0.00003 | 0.00001 |

For `J` up to about `ln b` the law matches the limit of section 5.2, which
falls by a factor `e` per step.
Beyond that the values are about 3 times the limit, with dips at some `J`.
The cause is the largest digit. A digit `x` can only appear if
`x^x < b^(b-J)`, and `(b-J+1)^(b-J+1)` is about `b^(b-J+1) e^-(J-1)`. So once
`J > ln b + 1`, the digit `b-J+1` becomes possible and adds solutions. After
that the decay is again about `e^-1` per step.

So the expected number of solutions in base `b` with `J >= j` is
`C e^-j` for some bounded `C`. Summing over bases gives the sharp form of the
conjecture.

Conjecture 10.3 (length window, `0^0 = 1`). For every `eps > 0`:

- only finitely many solutions with `k >= 3` digits have
  `b > k + ln k + (1 + eps) ln ln k`, apart from algebraic families such as
  those of chapter 22;
- infinitely many have `b > k + ln k + (1 - eps) ln ln k`.

Reason. The expected number of solutions in base `b` with
`J > ln b + a ln ln b` is about `C / (b (ln b)^a)`. The sum over `b` is finite
for `a > 1` and infinite for `a <= 1`. In the model the bases are independent,
so the two Borel-Cantelli lemmas give the two statements. This is the same law
as for the longest run of heads in coin flips.

Correction. The second half uses the second Borel-Cantelli lemma, which
needs the events in different bases to be independent. The model assumes
this, but no test of it exists (question 106 of `questions-round6.md`). The
first half needs no independence.

Update (chapter 34). Question 106 is now tested. In the model the only
link between two bases is a multiset that is a candidate in both, and its
share is negligible (Heuristic 34.15). In the data no near-solution
multiset of bases 12 to 26 is a near-solution in a second base, the forced
top digits of one multiset in bases `b` and `b + 1` are uncorrelated, and
the residuals of neighbouring bases show no correlation once the top digits
are forced (Table 34.5.1.1). This tests the model's assumption. It is not a
proof for the true weights.

The data split into two kinds of exceptions. Count the solutions with `k >= 3`
and `J > ln b + 2` (`analysis/length_window2.py`):

| region | digits | expected (model) | observed |
|---|---|---:|---:|
| bases 10-41 and 43, every length | 3 to 5 | 0.96 | 5 |
| | 6 to 10 | 0.86 | 0 |
| | 11 or more | 1.21 | 2 |
| bases 44-127, up to 30 digits | 3 to 5 | 0.05 | 2 |
| | 11 or more | 0.00 | 1 |
| bases 128-5000 | 3 to 5 | 0.01 | 2 |

The long exceptions agree with the model: 3 observed against about 1.2
expected, and one of the three is in base 64, which has self-paying digits.
The short exceptions do not: 9 observed against 1.0. That is expected. The
model of chapter 5 treats each base separately. For a short digit string the
base is the root of a polynomial (section 3.5), and the right heuristic is the
chance that this root is an integer. That heuristic gives a finite total for
each `k >= 3`, and the searches of chapter 3 have found every short solution
up to very large bases. But the heuristic misses algebraic identities: the
binomial families of chapter 22 give infinitely many short exceptions, in
bases above `10^108942`. So the short exceptions are not a finite list. The
long ones follow Conjecture 10.3.

Fixed length. For a large `k`, the bases with a `k`-digit solution are
`b = k` with probability 8%, `k+1` with 55%, `k+2` with 23%, `k+3` with 9%, and
so on. The expected number of such bases is about 1. So a length has no base
with probability about `e^-1 = 37%`, as in section 3.4, and two or more bases
with probability about 26%.

One statement is proven for every `k`.

Proposition 10.4. The number of bases up to `B` with a `k`-digit solution is at
most `X (X + 1)^(k-1)`, where `X = X_k(B)` is the largest digit with
`X^X < B^k`. This is `O((k ln B / ln(k ln B))^k)`.

Proof. By Proposition 1.2 every digit is at most `X`, and by Proposition 1.3
each digit string is a solution in at most one base.

So the bases with a solution of a fixed length are very sparse: their number
up to `B` grows like a power of `ln B`. Conjecture 10.3 says that, apart from
finitely many and from algebraic families, they all lie in a window of width
`ln k + ln ln k` above `k`.

Update (chapter 28). The z-score law of section 10.3 overstates the standard
deviation of `ln E` by 1.15x to 3.8x. Conditioning the cells on their total
(`--zlaw cond`) fixes it, so a threshold gives the same miss rate in every
base, with 1.1 to 1.3x fewer nodes at equal miss rate.

Update (chapter 27). Constraint solvers (CP-SAT, CaDiCaL) grow 1.95 to 2.3
per base, worse than the tree. Theorem 27.2 extends Theorem 10.1 to every
order of revealing counts, and bottom digits do not help even in bases
`2^k`. See chapter 27.

## 10.6 Status

| question | status |
|---|---|
| growth of the exact search | `2^b` in the limit, 1.89 per base now (10.1, model) |
| best possible tree search | about `1.638^b`; proven within the model (Theorem 10.1) |
| a rule that reaches it | `--zscore`: 1.75 per base now at a 1-3% miss rate that does not grow with `b` (10.3) |
| a larger classical speedup | none found; iteration, splits, representations and residues all fail (10.4) |
| quantum search | square root of the tree, about `1.41^b` exact (10.4) |
| length window under `0^0 = 1` | sharpened to `ln k + ln ln k` (Conjecture 10.3); long exceptions match the model; short ones include the infinite binomial families (chapter 22) |
| bases with a `k`-digit solution | at most a power of `ln B` up to `B` (Proposition 10.4) |
