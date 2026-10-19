# 9. Faster search with a known miss rate, and what the counts look like

Chapter 6 shows that the exact search grows about 1.9x per base, and chapter 8
explains why a proof of a better bound is out of reach. This chapter takes the
other way out. It builds a search that can skip a solution, measures how often
it does, and asks how fast such a search can be. The second half collects new
results on the counts: which bases are empty, how far apart the bases with many
solutions are, and how the length of a solution relates to its base.

## 9.1 Where the exact tree comes from, as a formula

At level `k`, the search has fixed the counts of the `m = b - k` largest
digits. Suppose that a node at this level knows `l` leading digits of `n`, so
`L = d - l` digits are unknown. Then exactly `C(L + m, m)` count vectors for the
large digits fit the known prefix, whatever the prefix is. The unknown part
spans about as many digits as the remaining uncertainty `rf (k-1)^(k-1)`.

`analysis/tree_model.py` adds up `C(L_k + m, m)` over the levels:

| base | predicted nodes, `d = b-1` | measured nodes, all lengths |
|---:|---:|---:|
| 30 | `2.6 * 10^8` | `7.1 * 10^7` |
| 35 | `5.6 * 10^9` | `1.6 * 10^9` |
| 40 | `1.5 * 10^11` | `4.3 * 10^10` |
| 43 | `1.1 * 10^12` | `2.9 * 10^11` |

The formula for `d = b-1` alone gives 3.5 to 3.9 times the measured count for
all lengths together. It counts every vector that fits the prefix and leaves
out the forced digits, so it overestimates by a roughly constant factor. It
predicts a growth of 1.94 to 1.96 per base for bases 40 to 1000. The measured growth from base 30 to 43 is
1.90. The widest level is near `k = 0.55 b`.

The formula also says where the cost goes. Most of the `C(L + m, m)` vectors
put far more large digits into the unknown part than a random number has. If
only vectors with a typical number of large digits are counted, the predicted
growth drops to between 1.5 and 1.7 per base. Chapter 6 measured 1.60 for this
typical tree in bases 16 to 23.

An exact search cannot drop the atypical nodes. Every node in the tree is
consistent with all the information that the search has: the interval for `n`,
the known prefix and the counts. So a solution below an atypical node is not
impossible, only unlikely.

Exact tests that look further into the interval help only by a constant
factor. The search now checks that the first unknown digit can still be one of
its allowed values, as Knuth's `back-pdi.w` does. This removes 6.2% to 7.5% of
the nodes in bases 20, 24, 30 and 32, with no trend. The unknown part has
`L` free positions and needs only `sum need_x <= L` of them for the large
digits. A test that looks at a bounded number of positions leaves the other
positions free. So I expect every such test to remove only a constant share of
the atypical nodes.

## 9.2 Four rules that drop unlikely nodes

The search in `fast/` accepts four optional rules. Each rule drops a node that
the model says is unlikely to lead to a solution.

| option | the node is dropped if |
|---|---|
| `--cap c` | one digit value has more than `c` copies |
| `--band z` | the number of digits `>= k` is more than `z` standard deviations from its mean in a random `d`-digit number |
| `--deficit z` | the known prefix holds fewer digits `>= k` than expected, by more than `z` standard deviations |
| `--ratio r` | the expected number of solutions below the node is less than `r` times the same number for its parent |

The deficit rule uses the hypergeometric law. If `m` of the `d` digits are
`>= k`, a random arrangement puts on average `l m / d` of them into the first
`l` positions. A node whose prefix holds far fewer has to put the rest into the
unknown part, which is exactly the atypical case of section 9.1.

The ratio rule uses the expected number of solutions below a node:

    E = pp! k^rf / (prod_x need_x! * rf! * b^pp)

Here `pp` is the number of unknown positions, `rf` the number of free digits
below `k`, and `need_x` the copies of a large digit `x` that still have to
appear in the unknown part. A rule that compares `E` with a fixed threshold
fails, because `E` is tiny at every node of a large base. It drops all
solutions. Comparing a child with its parent works. The search adds `E` of
every dropped node to a total, so each run reports its own expected number of
missed solutions.

## 9.3 Speed against misses

`analysis/inexact_sweep.py` runs the search with each set of rules. The growth
rate is fitted over bases 24 to 32. The missed solutions are counted against
the exact results for bases 10 to 32, which hold 93 nontrivial solutions.

| rules | growth per base | nodes at base 32 | missed | self-reported |
|---|---:|---:|---:|---:|
| none (exact) | 1.891 | `2.31 * 10^8` | 0 | |
| `--ratio 1e-3` | 1.828 | `1.16 * 10^8` | 0 | 0.07 |
| `--ratio 3e-3` | 1.798 | `8.1 * 10^7` | 0 | 0.27 |
| `--band 2.5` | 1.806 | `1.00 * 10^8` | 2 | |
| `--deficit 2` | 1.764 | `8.0 * 10^7` | 1 | |
| `--ratio 1e-2` | 1.744 | `4.6 * 10^7` | 2 | 1.02 |
| `--deficit 2 --band 2.5` | 1.712 | `4.4 * 10^7` | 3 | |
| `--ratio 1e-2 --deficit 2` | 1.693 | `2.8 * 10^7` | 3 | 0.99 |
| `--ratio 3e-2` | 1.677 | `1.8 * 10^7` | 10 | 2.90 |
| `--deficit 1.5 --band 2` | 1.646 | `1.7 * 10^7` | 12 | |
| `--deficit 1 --band 2` | 1.616 | `7.3 * 10^6` | 19 | |

At a few percent of missed solutions, the growth drops from 1.89 to about 1.71.
That is a factor of 1.1 per base. The saving is 5.3x at base 32. Extrapolated,
it is about 85x at base 60 and 1,700x at base 90. The self-reported totals of
the ratio rule have the right size for the mild settings. For `--ratio 3e-2`
they are too low: 2.9 reported against 10 missed.

A demonstration on a base that no one had searched: base 44, both conventions,
with `--deficit 2 --band 2.5`. The run took 31 minutes on 8 threads and visited
`2.7 * 10^10` nodes. An exact search needs about `5.5 * 10^11` nodes, or about
7 hours. It found one solution under `0^0 = 1`, with 43 digits:

    (32,32,36,30,0,0,37,23,32,33,4,5,17,4,30,7,31,25,43,25,15,21,38,19,18,7,
     35,10,34,39,4,30,25,33,24,43,27,26,13,1,38,24,22)

It contains two zeros, so it is not a solution under `0^0 = 0`. The run found
no solution under `0^0 = 0`. Before the run, the model gave this convention
1.08 expected solutions, so no solution at all had probability 0.34. The rules
miss about 15% of solutions at this size. Given that the run found none, base
44 has no solution under `0^0 = 0` with probability about 0.85. Only an exact
search can settle it.

## 9.4 How often a rule misses, without a search

The path from the root to a solution is fixed by the solution. At level `k`,
the counts of the digits `>= k` are the solution's own counts, and the known
prefix is the solution's own leading digits. `analysis/walk.py` replays this
path with the same interval logic as the search and applies the rules on the
way. On all 93 solutions of bases 10 to 32, the replay drops exactly the
solutions that the search misses.

The replay needs no search, so it works in any base. Two uses:

- Real solutions. Among the 54 solutions with at least `b-6` digits in bases
  20 to 43, `--deficit 2` drops 3 (6%), `--ratio 3e-3` drops 2 (4%) and
  `--deficit 2 --band 2.5` drops 5 (9%).
- Planted solutions. The model says that a solution looks like a random digit
  string whose weight has the right number of digits. `walk.planted` draws such
  strings, with the length distribution of chapter 5, and replays them.

Planted miss rates, 400 strings per base (200 at base 100):

| rules | base 30 | base 40 | base 60 | base 100 |
|---|---:|---:|---:|---:|
| `--ratio 3e-3` | 0.005 | 0.028 | 0.055 | 0.075 |
| `--ratio 1e-2` | 0.065 | 0.083 | 0.158 | 0.245 |
| `--deficit 2` | 0.025 | 0.045 | 0.092 | 0.115 |
| `--deficit 2 --band 2.5` | 0.052 | 0.083 | 0.170 | 0.190 |
| `--deficit 1.5` | 0.135 | 0.155 | 0.265 | 0.305 |

The planted rates at base 30 and 40 agree with the real ones. At a fixed
threshold every rate grows with `b`. The question is how fast.

## 9.5 How the threshold must grow

One replay gives the worst standardized deficit `z_min` on the whole path.
A deficit rule with threshold `c` drops the solution exactly when
`z_min < -c`. So the law of `z_min` gives the miss rate for every threshold at
once (`analysis/min_deficit.py`, 400 planted strings per base, 150 at bases 150
and 200, 60 at base 300):

| base | median `z_min` | 10% quantile | `P(z_min < -2)` | `P(z_min < -2.5)` | `P(z_min < -3)` |
|---:|---:|---:|---:|---:|---:|
| 20 | -0.42 | -1.28 | 0.015 | 0.000 | 0.000 |
| 30 | -0.67 | -1.57 | 0.035 | 0.003 | 0.000 |
| 45 | -0.85 | -1.77 | 0.052 | 0.018 | 0.005 |
| 60 | -1.03 | -1.91 | 0.085 | 0.018 | 0.000 |
| 100 | -1.22 | -2.08 | 0.117 | 0.018 | 0.003 |
| 150 | -1.24 | -2.07 | 0.120 | 0.040 | 0.027 |
| 200 | -1.35 | -2.22 | 0.187 | 0.047 | 0.013 |
| 300 | -1.51 | -2.41 | 0.317 | 0.100 | 0.000 |

The law drifts down slowly. The median fits `2.40 - 1.63 sqrt(ln b)` within
0.15 at every base in the table. The deficit at one level is a sum of many
small independent parts, so it is close to Gaussian. The deficits at
neighbouring levels share most of their parts. The worst of them behaves like
the minimum of `N` nearly independent Gaussians, which moves like
`sqrt(2 ln N)`. The fit says that `N` grows like a small power of `b`. A
bounded number of scales would give the slower `sqrt(ln ln b)`, and the data
do not show that.

Either way, a threshold `c(b) = O(sqrt(ln b))` keeps the miss rate below any
fixed `delta`. Such a threshold keeps the count vectors within
`O(sqrt(b ln b))` of their mean. That window is small against `b`, so it does
not change the exponential growth rate of the tree. This gives:

Conjecture 9.1. For every `delta > 0` there is a search that, under the model,
misses each solution with probability at most `delta`, and whose cost grows like
`(g + o(1))^b`, where `g` is the growth rate of the typical tree of section 9.1.

The measurements put `g` between 1.6 and 1.7, against 1.9 for the exact search.

A safe threshold already shows the trend. With `--deficit 3`, the planted miss
rate stays near 1% up to base 300. The search then keeps this share of the
exact tree:

| base | 24 | 26 | 28 | 30 | 32 |
|---|---:|---:|---:|---:|---:|
| nodes with `--deficit 3` | `1.31 * 10^6` | `4.50 * 10^6` | `1.56 * 10^7` | `5.34 * 10^7` | `1.65 * 10^8` |
| share of the exact tree | 92% | 91% | 87% | 81% | 77% |

The share falls faster as the base grows, so the saving grows with
`b` at a fixed miss rate. This is what Conjecture 9.1 predicts.
A proof would need the model, so this is a statement about random digit strings,
and not about Munchausen numbers themselves. That is the price of being
inexact: the miss rate is a probability under the model. The replay of real
solutions in section 9.4 is the check that the model is good enough for this.

## 9.6 The parity effect is caused by the weights

The refined model of chapter 5 explains the parity effect through the
digit-sum identity: `n` and `F(n)` must agree modulo `b - 1`. To test this
directly, the search accepts `--perturb seed`. It adds to each weight `x^x` a
random amount of up to a quarter of its size. With `--keep-residues` the
amount is a multiple of `2(b - 1)`, so the residues of the weights stay the
same.

`analysis/perturb_experiment.py` counts the solutions with at least `b-6`
digits in bases 16 to 28, three seeds per base:

| weights | `0^0 = 0` | `0^0 = 1` |
|---|---:|---:|
| refined model | 20.1 | 14.9 |
| true weights | 16 | 16 |
| random perturbation | 13.7 | 13.3 |
| perturbation that keeps residues | 19.6 | 14.9 |

Random weights lose the parity effect. The extra solutions in odd bases under
`0^0 = 0` disappear, and the total falls to the basic model's value. Weights
that keep their residues bring the effect back, at exactly the refined model's
size. So the residues of `x^x` cause the effect, and nothing else in their
arithmetic matters for the counts.

The same experiment settles the excess of `(b-1)`-digit solutions under
`0^0 = 1` (section 5.5). Over all lengths from `b-6` to `b`, the true counts
fit the refined model: 16 against 14.9 in bases 16 to 28, and 17 against 14.6
in bases 29 to 41. The excess at `b-1` digits is a fluctuation in how the
solutions spread over the lengths. Their total is normal.

## 9.7 Bases without solutions

A base is empty if it has no nontrivial solution under either convention. The
model gives the chance of this. Let `E_0` and `E_1` be the expected numbers of
solutions under each convention, and `E_s` the expected number of solutions
without a zero, which count under both. If solutions occur independently, a
base is empty with probability `exp(-(E_0 + E_1 - E_s))`.

`analysis/empty_bases.py` computes this for bases 10 to 41:

| bases | `E_0 + E_1 - E_s` | chance of being empty |
|---|---:|---:|
| even, 10 to 41 | 1.7 to 2.0 | 14% to 18% |
| odd, 10 to 41 | 2.4 to 3.2 | 4% to 9% |

Odd bases are rarely empty, because the parity effect doubles `E_0`. At base
40 the chance is 17% for an even base and 8% for an odd one. As `b` grows,
the short lengths contribute less, and the chances rise to the large-base
limits of section 4.5, 20% and 9%.

The perturbed weights of section 9.6 test this law. In 240 runs on even bases
16 to 27, 47 were empty, against 44.8 predicted. In 240 runs on odd bases, 16
were empty, against 20.6. So the emptiness law holds in the perturbed world,
where only the residues are kept.

The real bases deviate in one direction:

| bases 10 to 41 | expected empty | observed |
|---|---:|---:|
| even | 2.62 | 0 |
| odd | 1.13 | 3 (19, 27, 35) |

The chance of no empty even base is 0.057 under the model. Base 44, also even,
has a solution (section 9.3). This is the strongest unexplained deviation from
the model in the data. Since the perturbed world matches the model, a
mechanism, if there is one, must depend on more than the residues of `x^x`.

What can be said for certain about empty bases:

- A base has a solution if one of the families of chapter 2 applies. Under
  `0^0 = 0`, every perfect power `r^t` with `t | s (r^s - 1)` for some
  `1 <= s < t` has a self-paying digit and so a solution. Under both
  conventions, `b` has a 2-digit solution exactly when
  `b = (a^a + w(c) - c) / a > max(a, c)` for some digits `a | w(c) - c`. These
  families cover few bases: 55 of the bases up to `10^9` have a 2-digit
  solution under `0^0 = 0`.
- Every other base is empty or not by coincidence. Proving that a base is
  empty takes a full search, and chapter 8 explains why no argument can cover
  infinitely many bases at once with current methods.
- If the model is right, about one base in eight near base 40 is empty (the
  average of 17% and 8%), and one in seven in the large-base limit (20% and
  9%, section 4.5). So infinitely many are. The data agree for odd bases. For
  even bases they show fewer empty bases than expected, at a level that chance
  explains with probability 0.06.

## 9.8 Bases with many solutions are far apart

Theorem 9.2. For every `n >= 3`, base `b = n^(n-1)` has at least
`2^(n-1) - 2` nontrivial solutions under `0^0 = 0`.

Proof. For `1 <= s <= n-2`, the digit `a = n^s` is below `b` and
`a^(a-1) = n^(s (n^s - 1))`. Since `n - 1` divides `n^s - 1`, this is
`b^k` with `k = s (n^s - 1) / (n - 1)`. So base `b` has `n - 2` self-paying
digits, and Corollary 2.4 gives `2^(n-1) - 2` solutions.

Here `ln b = (n - 1) ln n`, so `n` grows like `ln b / ln ln b`. The count is
therefore `b^((ln 2 + o(1)) / ln ln b)`. That grows faster than any power of
`log b`, but slower than any power of `b`.

The smallest base with at least `C` self-paying digits
(`analysis/record_bases.py`):

| `C` | smallest base | size | solutions under `0^0 = 0`, at least |
|---:|---|---:|---:|
| 1 | `2^3` | `10^0.9` | 2 |
| 2 | `2^6` | `10^1.8` | 6 |
| 3 | `5^4` | `10^2.8` | 14 |
| 5 | `7^6` | `10^5.1` | 62 |
| 8 | `10^9` | `10^9.0` | 510 |
| 14 | `2^60` | `10^18.1` | 32,766 |
| 23 | `5^48` | `10^33.6` | 16,777,214 |
| 30 | `2^155` | `10^46.7` | 2,147,483,646 |
| 39 | `41^40` | `10^64.5` | 1,099,511,627,774 |

Most records are bases `(C+2)^(C+1)` from Theorem 9.2. The others are powers of
2, 3, 5 and 6 with an exponent that has many divisors. In this range,
`C` is about `1.3 ln b / ln ln b`.

These bases are rare.

Proposition 9.3. Let `c >= 1`. At most
`X^(1/(c+1)) + X^(1/(c+2)) log2 X` bases up to `X` have `c` or more
self-paying digits. So their number is `X^(1/(c+1)) (1 + o(1))`.

Proof. By Proposition 2.2, a base with a self-paying digit is `r^t`, where `r`
is not a perfect power, and its self-paying digits are `r^s` with
`1 <= s < t`. So `c` of them need `t >= c + 1`. Such a base need not be a
perfect `(c+1)`-th power: base `8 = 2^3` has the self-paying digit 4, and 8
is not a square. For each `t`, at most `X^(1/t)` bases `r^t` lie below `X`,
and `t <= log2 X`. The sum over `t >= c + 1` is at most
`X^(1/(c+1)) + X^(1/(c+2)) log2 X`.

Up to `X = 10^9` the counts for `c = 1, 2, 3, 4` are 16,540, 419, 76 and 24,
below `X^(1/(c+1))` (computed).

So the structure that produces many solutions lives on a set of density zero,
and its counts grow only like `b^(O(1/ln ln b))`. The average count in the
model, 1.5 under `0^0 = 0`, comes from the coincidences of chapter 5, which
follow a Poisson law with no heavy tail. The extremes come from a different
source than the average. The record counts are attained at towers like `n^(n-1)`,
and between two such towers the count drops back to the Poisson range.

## 9.9 Length against base

Write `J = b - k` for a `k`-digit solution in base `b`. Chapter 1 shows
`k <= b`, so `J >= 0`.

Model. In a large base, the share of solutions with `J = 0, 1, 2, 3` is 8%,
55%, 23% and 9%, and after that the share falls by a factor of about
`e^-1` per step. So `P(J >= j)` is about `e^(-(j-1))` for `j >= 1`.

In bases 10 to 41 the data show this law plus the families:

| `J` | 0 | 1 | 2 | 3 | 4 to 9 | 12 or more |
|---|---:|---:|---:|---:|---:|---:|
| `0^0 = 0` | 2 | 30 | 10 | 7 | 8 | 9 |
| `0^0 = 1` | 0 | 30 | 8 | 6 | 6 | 6 |

The solutions with a large `J` are short. Under `0^0 = 1` they are the short
coincidences of chapter 3, such as 3435 in base 10 with `J = 6`.

This gives two answers to the question of chapter 3.

Fixed base. The likely lengths of a solution in base `b` are `b-1`, then `b-2`,
`b`, `b-3`, in that order. A solution with `J > (1 + eps) ln b` is very
unlikely: its expected number in base `b` is about `b^(-1-eps)`.

Fixed length. Summing `b^(-1-eps)` over all bases gives a finite number. By the
Borel-Cantelli lemma, under the model only finitely many solutions have
`J > (1 + eps) ln b`. That gives:

Conjecture 9.4. Under `0^0 = 1` and for every `eps > 0`, all but finitely many
solutions with `k >= 3` digits lie in a base `b` with
`k < b <= k + (1 + eps) ln k`.

In all data, which includes the short solutions up to bases near `10^51`, only
12 solutions under `0^0 = 1` with `k >= 3` have `J > ln b + 2`. All of them lie
in bases up to 904. Conjecture 9.4 implies the finiteness conjecture of chapter
3 for each fixed `k`: the bases for length `k` lie in a window of width about
`ln k` above `k`, plus finitely many exceptions.

Correction. Conjecture 9.4 is false as stated. The binomial families of
chapter 22 give infinitely many solutions of every length `k >= 3` in bases
far above `k` (Corollary 22.7). The model describes random coincidences, and
these solutions come from an algebraic identity. Whether the conjecture holds
for all solutions outside such families is question 64.

Under `0^0 = 0` the window does not hold, because of the families. Proposition
2.7 puts a `k`-digit solution in base `(2k-1)^2`, so the smallest base with a
`k`-digit solution is at most `(2k-1)^2`. In bases up to 41 the smallest base
is `k+1` or `k+2` for most `k`. The exceptions are `k = 11` (base 64) and
`k = 21` (base 81), both perfect powers.

## 9.10 Literature

- Kures (2021) proves the length bound of Proposition 1.1 and describes the
  2-digit family `(1, c)`.
- Knuth's program `back-pdi.w` searches for decimal perfect digital
  invariants. It uses the same leading-digit bounds as this search, with three
  refinements. Its pruning is exact, so it has the same problem with atypical
  nodes as section 9.1.
- Equations that mix terms like `x^x` are solved only in special shapes. Ko
  and Mills found infinite families for `x^x y^y = z^z` (Erdos problem 674).
  Cipu (2019) proved that `x^y + y^x = z^z` has no solution with
  `min(x, y) > 1`. These proofs use the multiplicative structure of a few
  terms. A sum of many weights, as in `F(n)`, has none.
- Mahler (Mathematika 4, 1957) proved that `(3/2)^k` stays at distance more
  than `c^k` from the nearest integer, for every `c < 1` and large `k`,
  without an effective bound. Zudilin (2007) gave the effective constant
  0.5803. These are the closest known results to the near-integer problems of
  section 8.2.
- Berman (1978) and Mahaney (1982) give the results on sparse languages used in
  section 8.1.

## 9.11 Status

| question | status |
|---|---|
| a search faster than `1.9^b` | yes if a small miss rate is allowed: about `1.71^b` at a few percent (measured, 9.3); `(g + o(1))^b` with `g` near 1.6 conjectured for any fixed miss rate (9.5) |
| how often it misses | measured on real solutions up to base 43 and on planted ones up to base 200 (9.4, 9.5) |
| the parity effect | caused by the residues of `x^x` (experiment, 9.6) |
| excess of `(b-1)`-digit solutions | resolved: the total over the bulk lengths fits the model (9.6) |
| bases without solutions | 14% to 18% of even and 4% to 9% of odd bases from 10 to 41 in the model (20% and 9% in the large-base limit), confirmed in the perturbed world; real even bases have fewer, with probability 0.06 (9.7) |
| bases with many solutions | at least `2^(n-1) - 2` in base `n^(n-1)`; on a set of density zero (9.8) |
| length against base | `J = b - k` falls like `e^(-J)`; conjectured window `k < b <= k + (1 + eps) ln k` under `0^0 = 1` (9.9) |
