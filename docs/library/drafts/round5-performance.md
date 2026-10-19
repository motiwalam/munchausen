# Round 5: a sharper z-score rule, length windows, and the GPU

Chapter 10 gave the inexact search its best rule, `--zscore 3`: a node is
dropped when `ln E`, the log of its expected number of solutions, lies more
than 3 standard deviations below its mean. This draft does three things. It
replaces the law behind that rule by one with the right standard deviation,
and measures the gain at equal miss rate. It measures what a window on the
length of a solution saves. It runs the rule on the GPU, together with
`--shard`.

Each statement carries one mark:

- proven: a proof is in this draft;
- computed: a measurement, with its range;
- heuristic: an estimate that rests on the model of chapter 5.

All runs used the test laptop (8 threads, Arc 140V GPU). Other jobs shared
it during almost all runs, with a 1-minute load average of 1 to 32. Node counts do
not depend on the load. Wall times do, so each table of times gives the
load.

## Summary

| section | statement | result | status |
|---|---|---|---|
| 1.1 | the law of `ln E` | the Poisson law of chapter 10 gets the mean right but overstates the standard deviation by 1.15x to 3.8x (Table 1.1). Conditioning the cells on their total (`--zlaw cond`) is within 5% of a direct simulation. | computed |
| 1.2 | calibration on planted paths | under `cond` the z-score of a planted solution has mean 0.03 to 0.25 and standard deviation 0.89 to 1.01 at every level from 0.3 to 0.9 of `kmax`, in bases 40 to 200. Under `poisson` the standard deviation rises from 0.5 at level 0.3 to 1.0 at level 0.9. | computed |
| 1.3 | forced top digits | a planted solution whose top 3 digits are those of `F`, as in the second-order model, has the same z-score law within sampling error. The rule only tests levels where the top digits are already known. | computed |
| 1.4 | one run per curve (Lemma 1.2) | a run at a loose threshold that records each node's smallest z on its path gives the node count of every stricter threshold exactly | proven, checked |
| 1.5 | gain at equal miss rate (Proposition 1.3) | at a planted miss rate of 1% or 2%, `--zlaw cond` visits 1.10x to 1.34x fewer nodes and makes 1.04x to 1.20x fewer interval evaluations than the default law, in bases 30 to 40. The gain grows with the base. | computed |
| 1.6 | other rules | starting the test at the top level, a threshold that changes with the level, and a cost-aware rule that keeps the nodes with the largest `E / T` all reach the same gain, or less | computed |
| 1.7 | wall time | the time follows the interval evaluations: 1.07x to 1.18x faster at equal miss rate (bases 34, 36, 42) | computed |
| 1.8 | larger bases | at a fixed threshold the miss rate of `cond` stays at 2.0% to 2.4% from base 30 to 200; that of `poisson` falls from 2.0% to 0.7%, so the default rule spends more nodes per miss as the base grows | heuristic |
| 2.1 | cost per length | each length `d = b - J` costs about its share of the solutions: `J = 0` holds 11% to 17% of the nodes and 8% of the solutions, `J = 1` holds 42% to 60% and 55% | computed |
| 2.2 | length windows (Proposition 2.2) | every window is dominated by a lower threshold: a window saves 1.03x to 1.45x at 2 to 21 points of extra miss rate, a lower threshold saves 1.3x to 6x at the same miss rate | computed |
| 3.1 | GPU with the z-score rule (Lemma 3.1) | the GPU runs `--zscore` with every law option in fixed point. Same node counts as the CPU at every base tested (10 to 26 in the test suite, 28, 30, 31, 33). | proven (bound), computed |
| 3.2 | GPU with shards | `--gpu` and `--hybrid` accept `--shard`; three hybrid shards of base 31 merge to the output of one run | computed |
| 3.3 | speed (Proposition 3.2) | `--hybrid` with the z-score rule runs 2.6x to 2.9x faster than 8 CPU threads at base 38, under a load of 7 to 14 | computed |

## 1. A sharper z-score rule

### 1.1 The law of ln E

At a node of level `k`, the counts of the digits `k` to `kmax` are fixed.
The node has `pp` unknown positions and `rf` free digits below `k`, and
`need_x` copies of each decided digit `x` must still appear among the
unknown positions. The engine computes

    ln E = ln pp! - sum_x ln need_x! - ln rf! + rf ln k - pp ln b.

Under the model the unknown positions of a solution are a uniform draw from
the `kk = kmax + 1` usable digits. So the vector `(need_x, rf)` is
multinomial with `pp` trials, and `ln E + pp ln(b / kk)` is the log
probability of the outcome. The rule of chapter 10 needs the mean and the
standard deviation of that log probability.

The default law (`--zlaw poisson`) treats the `m = kk - k` decided cells and
the cell of the digits below `k` as independent Poisson variables. It takes
their entropy and varentropy and subtracts those of the total. The
subtraction is right for the entropy. It is wrong for the varentropy,
because the log probability and the total are correlated.

The new law (`--zlaw cond`) conditions on the total by linear regression.
Write `h(n) = ln n! - n ln p` for a cell with probability `p`, and
`X = sum h(N_i)` over independent Poisson cells `N_i` with mean `pp p_i`.
Then

    E[-ln P | S = pp] = E X - ln pp!,
    Var[-ln P | S = pp] = Var X - Cov(X, S)^2 / Var S,

with `S = sum N_i` and `Var S = pp`. The engine sums the three moments of
`h` over the two kinds of cells.

Table 1.1 (computed, `analysis/r5p_mc.py`, `analysis/data/r5p_mc.txt`).
Base 40, `kmax = 39`, 200,000 multinomial draws per cell. Mean and standard
deviation of `ln E`.

| `k` | `pp` | simulation | `poisson` | `cond` |
|---:|---:|---|---|---|
| 30 | 25 | -10.37, 1.98 | -10.29, 2.27 | -10.78, 2.07 |
| 25 | 22 | -14.54, 2.26 | -14.41, 2.83 | -14.90, 2.33 |
| 20 | 18 | -17.34, 2.39 | -17.16, 3.36 | -17.65, 2.43 |
| 15 | 12 | -17.04, 2.33 | -16.77, 3.89 | -17.26, 2.34 |
| 10 | 8 | -15.65, 1.95 | -15.32, 4.29 | -15.80, 1.92 |
| 6 | 4 | -10.69, 1.15 | -10.28, 4.39 | -10.73, 1.12 |

The Poisson standard deviation is 1.15x too large at the top and 3.8x too
large at the bottom. The conditioned one is within 5% everywhere. Its mean
is 0.05 to 0.4 too low, a shift that the next section measures on real
paths.

### 1.2 Calibration on search paths

The multinomial is the law of a random suffix. The node on the path of a
solution is not a random node: its prefix length `pp` depends on the counts.
So the calibration must use search paths.

`analysis/r5p_trace.py` draws planted solutions as in chapter 9 (a uniform
digit string whose sum `F` has the right length, with the length law of
section 9.9) and replays their path with the engine's interval logic. It
records `k`, `pp`, `rf` and `ln need!` at every level. `r5p_calib.py`
computes the z-score of each level under both laws.

Table 1.2 (computed, `analysis/data/r5p_calib.txt`). Mean and standard
deviation of the z-score of planted solutions, by level fraction
`u = k / (kmax + 1)`. 10,000 strings at bases 40 and 100, 4,000 at base
200.

| base | law | `u` = 0.3 | 0.5 | 0.7 | 0.9 |
|---:|---|---|---|---|---|
| 40 | `poisson` | -0.05, 0.51 | -0.10, 0.75 | -0.12, 0.90 | -0.21, 1.08 |
| 40 | `cond` | +0.12, 0.91 | +0.07, 0.99 | +0.11, 0.98 | +0.25, 0.89 |
| 100 | `poisson` | -0.05, 0.60 | -0.05, 0.76 | -0.06, 0.88 | -0.15, 1.02 |
| 100 | `cond` | +0.04, 1.01 | +0.06, 1.00 | +0.09, 0.98 | +0.20, 0.92 |
| 200 | `poisson` | -0.03, 0.59 | -0.04, 0.77 | -0.07, 0.89 | -0.12, 1.02 |
| 200 | `cond` | +0.04, 0.99 | +0.03, 1.01 | +0.04, 1.00 | +0.15, 0.96 |

Observation 1.1 (computed). Under `cond` the z-score of a solution's path is
close to a standard normal variable at every level from `u = 0.3` to 0.9,
in every base from 30 to 200. Under `poisson` its spread shrinks to 0.5 at
the lower levels. So the default rule with threshold 3 cuts at about 6
true standard deviations there, and at about 3 near `u = 0.75`. At base 40
and threshold 3, the worst level of the 178 planted misses (of 10,000) lies
at `u >= 0.6` for 146 of them and below 0.4 for none. Under `cond` at
3.35, 105 of 221 misses come from `u < 0.6`. The calibrated rule spreads
its misses over all tested levels.

### 1.3 The forced top digits

Section 11.2a and chapter 24 found that the top 2 or 3 digits of `F` are
fixed by the largest digits, and that the digits below them are uniform.
A planted string with uniform digits ignores this. `r5p_trace.py` order 2
builds the second-order version: it keeps the multiset of the planted
string, puts the top 3 digits of `F` in front, arranges the rest at random,
and weights the string by the forced-top ratio of `analysis/forced_top.py`
(0 when the top digits do not fit the multiset). 24% of the draws have a
nonzero weight at base 40.

Observation 1.2 (computed, `analysis/data/r5p_calib.txt`,
`analysis/data/r5p_planted.txt`). The weighted z-score law of order 2
agrees with order 1 within two standard errors at bases 30 to 200. At base
40 and threshold 3 the miss rates of orders 1 and 2 are 1.78% and 1.98%
under `poisson`, and 3.74% and 4.59% under `cond`. The standard errors are
about 0.15 points for order 1 and 0.4 points for order 2.

The reason is where the rule looks. The top digits are known after the
first few levels, and the rule only tests levels `k <= 3/4 (kmax + 1)`.
There the known prefix holds the forced digits, and `E` only describes the
uniform part below them. So the second-order model does not change the
per-node likelihood. I use the order-1 rates below, and the order-2 rates
as a check.

### 1.4 Measuring a whole curve in one run

The new option `--zhist <file>` gives every node the smallest z-score on its
path, among the tested levels, and records the nodes and the interval
evaluations in bins of 0.05 of that value, per length.

Lemma 1.2 (proven). Fix the law and all other options. The nodes that
`--zscore c` visits are exactly the nodes of a run with `--zscore c0`,
`c0 >= c`, whose smallest z-score is at least `-c`. The same holds for the
interval evaluations, counted at their parent.

Proof. A node is visited if and only if every test on its path passes. With
the same law, the tests of `--zscore c` are those of `--zscore c0` with a
higher bar, so the tree of `c` is a subtree of the tree of `c0`, and a
node of the larger tree is in the smaller one exactly when every z on its
path is at least `-c`.

Check (computed). At base 32 the histogram of a run with `c0 = 3` predicts
24,246,186 nodes and 109,842,900 evaluations for `c = 2.5`, and 15,571,223
and 75,488,606 for `c = 2`. Direct runs give the same numbers.

So one run with `c0 = 5` per base and law gives the node count for every
threshold up to 5. The miss rate at each threshold comes from the planted
paths: a planted solution is cut exactly when its smallest z is below
`-c`.

### 1.5 The gain at equal miss rate

`analysis/r5p_curves.py` combines the two curves. For a target planted miss
rate, it finds the threshold of each law that reaches it and reads off the
nodes.

Table 1.3 (computed, `analysis/data/r5p_curves.txt`). Nodes and interval
evaluations at the same planted miss rate. 10,000 planted strings per base;
the thresholds carry a sampling error of about 0.05.

| base | miss | `poisson` threshold | nodes | `cond` threshold | nodes | fewer nodes | fewer evaluations |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 30 | 1% | 3.39 | `1.77 * 10^7` | 3.89 | `1.61 * 10^7` | 1.10x | 1.04x |
| 30 | 2% | 3.01 | `1.43 * 10^7` | 3.38 | `1.25 * 10^7` | 1.14x | 1.07x |
| 32 | 1% | 3.35 | `4.42 * 10^7` | 3.77 | `3.79 * 10^7` | 1.17x | 1.09x |
| 32 | 2% | 2.94 | `3.40 * 10^7` | 3.27 | `2.83 * 10^7` | 1.20x | 1.10x |
| 34 | 1% | 3.33 | `1.57 * 10^8` | 3.82 | `1.35 * 10^8` | 1.16x | 1.08x |
| 34 | 2% | 2.93 | `1.20 * 10^8` | 3.32 | `1.00 * 10^8` | 1.20x | 1.10x |
| 36 | 1% | 3.33 | `4.90 * 10^8` | 3.82 | `4.05 * 10^8` | 1.21x | 1.11x |
| 36 | 2% | 2.94 | `3.65 * 10^8` | 3.37 | `2.96 * 10^8` | 1.23x | 1.12x |
| 38 | 1% | 3.33 | `1.55 * 10^9` | 3.83 | `1.21 * 10^9` | 1.27x | 1.15x |
| 38 | 2% | 2.91 | `1.09 * 10^9` | 3.40 | `8.92 * 10^8` | 1.22x | 1.10x |
| 40 | 1% | 3.33 | `4.68 * 10^9` | 3.81 | `3.48 * 10^9` | 1.34x | 1.19x |
| 40 | 2% | 2.94 | `3.28 * 10^9` | 3.42 | `2.55 * 10^9` | 1.29x | 1.15x |

Proposition 1.3 (computed). At equal planted miss rate, `--zlaw cond`
visits 1.10x to 1.34x fewer nodes than the default law in bases 30 to 40,
and the gain grows with the base. The interval evaluations fall by 1.04x to
1.19x. The thresholds `3.4` for 2% and `3.8` for 1% hold in every base of
the table.

The evaluations gain less than the nodes. A likely reason: the calibrated
rule cuts more at the lower levels, where a node has few children, and
less near the top of the tested range, where a cursor evaluates many values
of `e`. Section
1.7 measures the time.

The planted miss rate is a model quantity. On the real solutions the two
rules behave alike (`analysis/r5p_realmiss.py`). Of the 86 distinct
solutions with at least 3 digits in bases 10 to 41 and 43, `poisson` at
2.94 cuts one, the 40-digit solution of base 41, and `cond` at 3.37 cuts none. At the
looser 1% thresholds neither cuts any. `fast search 10 41 --zscore 3.4
--zlaw cond --hybrid` finds all 122 nontrivial solutions of bases 10 to
41, both conventions, in 285 s (load 11).

### 1.6 Other rules that do not do better

I tried three more ways to spend the same miss rate, all through
`--zhist` and planted paths, at base 32 and partly at 36.

- Test every level (`--zfrom 1`). Under `cond` the top levels are well
  calibrated too (Table 1.2), but cutting there costs miss rate and saves
  few nodes. At 1% and 2% miss it visits 0.91x to 1.07x the nodes of
  `poisson` (bases 32 to 40), worse than `cond` from 0.75. Under `poisson`
  it is 2x worse, as chapter 10 found.
- A threshold that changes with the level (`--zslope s`, threshold
  `c + s (u - 1/2)`). Slopes from -4 to 6, with the test from 0.75 or
  from the top, give 0.67x to 1.28x fewer nodes than `poisson` at 1% to 3%
  miss at base 32. The best, slope 4 from the top, gives 1.18x to 1.28x,
  against 1.17x to 1.20x for slope 0 from 0.75. That is within the
  sampling error.
- A cost-aware rule. A node's value is `E` and its cost is the size `T` of
  its subtree. Keeping the nodes with the largest `E / T` solves the
  knapsack greedily. `--tree-stats` measures the mean `T` per length,
  level and `pp`, and `analysis/r5p_ztable.py` turns `ln T` into a table
  for `--ztable`. At base 32 it gains 1.17x to 1.20x nodes and 1.16x to
  1.17x evaluations over `poisson`; at base 36 1.11x to 1.14x nodes and
  1.08x to 1.12x evaluations. That is the same as `cond`, or less.

Heuristic 1.4. Rules that judge one node at a time by its `E` lie on one
frontier. Theorem 10.1 bounds every such rule by the entropy of the path
law, and the calibrated rule loses only the width of its band,
`c sqrt(V)`. The cost-aware rule and the slopes move nodes between levels
but do not shrink that band. A larger gain needs information that `E` does
not carry, as section 10.4 says.

### 1.7 Wall time

Other jobs kept the load high, so Table 1.4 gives the CPU seconds (user
plus system) next to the wall times. Each line is the median of alternating
runs (`analysis/r5p_timing.py`, `analysis/data/r5p_timing.txt` and
`r5p_timing_idle.txt`). The thresholds are those of Table 1.3.

Table 1.4 (computed). `poisson` against `cond` at the same planted miss
rate.

| run | miss | load | `poisson` | `cond` | gain |
|---|---:|---:|---|---|---:|
| base 34, 1 thread, 5 runs | 2% | 8 to 22 | 49.6 s CPU | 46.3 s CPU | 1.07x |
| base 34, 1 thread, 5 runs | 1% | 8 to 22 | 70.8 s CPU | 60.3 s CPU | 1.18x |
| base 36, 8 threads, 3 runs | 2% | 9 to 15 | 27.0 s, 157.1 s CPU | 24.2 s, 145.3 s CPU | 1.08x CPU |
| base 36, 8 threads, 3 runs | 2% | 1 to 14 | 29.1 s, 157.8 s CPU | 27.4 s, 145.6 s CPU | 1.08x CPU |
| base 36, 8 threads, 3 runs | 1% | 1 to 14 | 36.4 s, 202.0 s CPU | 38.5 s, 184.9 s CPU | 1.09x CPU |
| base 42, `--hybrid`, 1 run | 2% | 9 to 10 | 229.4 s, `9.21 * 10^9` nodes | 206.2 s, `7.03 * 10^9` nodes | 1.11x |

Observation 1.6 (computed). The time follows the interval evaluations, not
the nodes: the calibrated rule saves 1.07x to 1.18x of the time where it
saves 1.10x to 1.31x of the nodes. The base 42 runs use `--zscore 2.94` and
`--zscore 3.4 --zlaw cond`.

### 1.8 Larger bases

Exhaustive answers stop at base 43, and node counts at equal miss rate need
full runs. Above base 40 the comparison rests on the planted paths.

Table 1.5 (computed, `analysis/r5p_planted.py`,
`analysis/data/r5p_planted.txt`). Planted miss rate at a fixed threshold,
order 1 (10,000 strings; 4,000 at base 200).

| base | `poisson` 3.0 | `poisson` 3.33 | `cond` 3.35 | `cond` 3.82 |
|---:|---:|---:|---:|---:|
| 30 | 2.0% | 1.1% | 2.1% | 1.0% |
| 40 | 1.8% | 1.0% | 2.2% | 1.0% |
| 50 | 1.5% | 0.8% | 2.2% | 1.0% |
| 60 | 1.6% | 0.8% | 2.4% | 1.0% |
| 80 | 1.2% | 0.7% | 2.0% | 0.8% |
| 100 | 1.1% | 0.6% | 2.3% | 0.9% |
| 150 | 1.3% | 0.5% | 2.4% | 1.0% |
| 200 | 0.7% | 0.3% | 2.2% | 0.6% |

Heuristic 1.5. The miss rate of `cond` at a fixed threshold does not depend
on the base, so one threshold serves every base. The default rule becomes
stricter in miss rate and looser in nodes as the base grows: at base 200 it
needs `c` near 2.65 to miss 2%, and at that threshold its band covers more
of the lower levels than the calibrated band. So the gain of Proposition
1.3, which grows from 1.10x to 1.34x between bases 30 and 40, keeps growing
above 40. I have no node counts there to say by how much.

## 2. Length windows

### 2.1 Cost per length

`--zhist` records the histogram per length `d`, so the runs of section 1
also give the cost of each `J = b - d`. A run with `--zscore 1000` tests
nothing and gives the exact tree.

Table 2.1 (computed, `analysis/r5p_lengths.py`,
`analysis/data/r5p_lengths.txt`). Share of the nodes per `J` under
`--zscore 3.35 --zlaw cond`, and the share of solutions in the model
(section 10.5).

| `J` | base 30 | base 34 | base 36 | base 40 | solutions |
|---:|---:|---:|---:|---:|---:|
| 0 | 13.5% | 12.0% | 11.5% | 14.5% | 8.0% |
| 1 | 54.2% | 56.7% | 52.8% | 50.6% | 55.2% |
| 2 | 20.9% | 23.1% | 22.0% | 22.1% | 23.3% |
| 3 | 7.1% | 3.5% | 8.7% | 8.3% | 8.6% |
| 4 to 8 | 4.1% | 4.5% | 4.7% | 4.4% | 4.9% |

The exact tree spends more on `J = 0` (computed, `--zscore 1000`, which
tests nothing; `analysis/data/r5p_zhist/b<base>_exact.txt`):

| `J` | base 30 | base 32 | base 34 |
|---:|---:|---:|---:|
| 0 | 20.0% | 24.3% | 19.0% |
| 1 | 49.5% | 40.8% | 51.2% |
| 2 | 20.3% | 23.7% | 22.0% |
| 3 | 7.0% | 7.1% | 4.0% |
| 4 and more | 3.2% | 4.1% | 3.8% |

The totals are the exact counts, 66,246,690, 214,709,067 and 824,063,470
nodes. In the exact search `--max-digits b-1` saves 1.24x to 1.32x and
gives up the `b`-digit solutions: 8% of them in the model, and 2 of 122 in
bases 10 to 41 (bases 15 and 16, both under `0^0 = 0`).

Proposition 2.1 (computed). Under the z-score rule, in bases 30 to 40, every
length costs about its share of the solutions. The exception is `J = 0`,
the `b`-digit numbers, which cost 1.4x to 1.8x their share (2.4x to 3x in
the exact tree). The lengths with `J >= 4` together
cost 4% to 5% of the tree.

A likely reason: `E` is the expected number of solutions below a node.
The rule keeps the nodes of every length in proportion to their
probability, and the tree of a length grows with the number of its
multisets, as its expected number of solutions does.

### 2.2 What a window saves

A window keeps the lengths with `J` in `[j0, j1]`. Its planted miss rate
adds the share of planted solutions outside the window to the misses of
the rule inside it. The alternative spends the same miss rate on a lower
threshold over all lengths.

Table 2.2 (computed, `analysis/data/r5p_lengths.txt`). Base 40, starting
from `--zscore 3.35 --zlaw cond` (planted miss 2.2%, `2.43 * 10^9` nodes).

| window | fewer nodes | planted miss | lower threshold at that miss | its saving |
|---|---:|---:|---:|---:|
| `J <= 4` | 1.03x | 4.1% | 2.93 | 1.43x |
| `J <= 3` | 1.05x | 7.3% | 2.54 | 2.03x |
| `J >= 1` | 1.17x | 9.7% | 2.35 | 2.45x |
| `J <= 2` | 1.15x | 15.6% | 2.01 | 3.32x |
| `1 <= J <= 3` | 1.24x | 14.8% | 2.04 | 3.23x |
| `1 <= J <= 2` | 1.38x | 23.2% | 1.68 | 4.35x |

Proposition 2.2 (computed). In bases 30 to 40, under both laws, every
window in Table 2.2 saves less than a lower threshold that reaches the
same planted miss rate, by a factor of 1.2 to 4.5.

So a length window does not pay, and it does not pay in combination with
the z-score rule either: the rule already prices each length by its `E`.
Conjecture 10.3 says where long solutions lie, but the tree of the unlikely
lengths is cheap for the same reason that they are unlikely. The one
window with a small cost is `J <= 4` (`--min-digits b-4`), which saves 3%
and loses the 2% of model solutions with `J >= 5`, plus the short
solutions that the model does not cover (section 9.9). I do not recommend
it.

## 3. The GPU with the inexact search and shards

### 3.1 The z-score rule in fixed point

Before this round the GPU path refused every inexact rule and `--shard`.
The rule needs `ln E` per child. The GPU does not keep `lneed` on its
stack, but it does not need to. The child's counts `cnt` and the histogram
`hp` of its known leading digits are already in the lanes. So
`lneed = sum over x >= k of ln((cnt_x - hp_x)!)` is one table lookup per
lane and one subgroup sum.

The host rewrites the test `ln E < thr(k, pp)` as

    lneed + G(k, rf) > A(k, pp),
    G(k, rf) = ln rf! - rf ln k,
    A(k, pp) = ln pp! - pp ln b - thr(k, pp),

and stores `ln n!`, `G` and `A` rounded to multiples of `2^-20` as 32-bit
integers. A cell that the rule does not test (`k` above `zfrom`) holds the
largest integer. The threshold `thr` comes from the CPU's own table, so
every law option works: `--zlaw`, `--zfrom`, `--zslope`, `--ztable`.

Lemma 3.1 (proven). The GPU and the CPU make the same decision for every
child whose `ln E` differs from its threshold by more than
`(d + 3) 2^-21`.

Proof. `ln 0!` and `ln 1!` are 0 exactly, so `lneed` adds a rounded term
only for the cells with `need_x >= 2`, at most `d / 2` of them. With `G`
and `A` that is at most `d / 2 + 2` rounded terms, each off by at most
`2^-21`. The CPU's own sum in double precision is off by far less. All
values stay far below `2^11` in size (`ln 62! < 197`, `pp ln b < 300`), so
the 32-bit integers do not overflow; a threshold so low that `A` would
exceed that range never cuts on either side.

Computed. The test `gpu_zscore_matches_cpu` runs three rules (`poisson`
3, `cond` 2 from the top with slope 2, `poisson` 2.5 on wide vectors) on
bases 10 to 26 (10 to 24 for wide vectors) and finds the same solutions and the same node and
evaluation counts, on the GPU alone and in hybrid mode. Runs of
`--zscore 3` at bases 28, 30 and 33 gave the same node counts on the CPU,
the GPU and in hybrid mode.

In hybrid mode the CPU threads take GPU work items too. An item does not
carry the model's bookkeeping, so the CPU rebuilds `m` and `lneed` from the
counts and the known prefix before it continues.

What the GPU still does not run: `--cap`, `--band`, `--deficit`,
`--ratio`, `--epsilon`, `--zhist`, `--tree-stats`, `--journal`, and other
weights. It handles bases up to 64, since a lane indexes a digit value.
The reported expected number of solutions in skipped subtrees counts only
the nodes that the CPU skipped.

### 3.2 Shards

`--shard i/n` with `--gpu` or `--hybrid` now gives the GPU the units whose
index is `i` modulo `n`. Three hybrid shards of base 31 with
`--zscore 3 --zlaw cond` visited 5,245,911, 5,725,349 and 5,147,960
nodes, and `fast merge` of their outputs equals the output of one CPU run
(16,090,402 nodes; each shard also counts the nodes that build the unit
list). So a large base can be split over machines, each with its own GPU.

### 3.3 Speed

Table 3.3 (computed, `analysis/data/r5p_timing.txt` and
`r5p_timing_idle.txt`). Median wall times of alternating runs. The load
from other jobs was 7 to 14 in these runs. It slows the CPU threads but
hardly the GPU, so the GPU columns look better than on an idle machine.

| run | CPU, 8 threads | `--gpu` | `--hybrid` | hybrid against CPU |
|---|---:|---:|---:|---:|
| base 34, exact (3 runs) | 34.1 s | 20.3 s | 13.2 s | 2.6x |
| base 34, exact (2 runs) | 38.6 s | 20.3 s | 13.7 s | 2.8x |
| base 38, `--zscore 3` (3 runs) | 74.4 s | 43.9 s | 28.3 s | 2.6x |
| base 38, `--zscore 3` (2 runs) | 81.3 s | 44.2 s | 29.5 s | 2.8x |
| base 38, `--zscore 3.4 --zlaw cond` (3 runs) | 66.5 s | | 24.2 s | 2.7x |
| base 38, `--zscore 3.4 --zlaw cond` (2 runs) | 70.5 s | 37.0 s | 24.7 s | 2.9x |

With the rule on, the GPU alone visits 24 to 27 million nodes per second
at base 38. In the exact search at base 34 it visits 41 million. The rule
costs one table lookup per lane and one subgroup sum for each child that
passes the exact tests. The pruned tree also makes 4.4 interval evaluations
per node, against 3.3 in the exact tree.

Proposition 3.2 (computed). With the z-score rule, `--hybrid` runs 2.6x to
2.9x faster than 8 CPU threads at base 38 under a load of 7 to 14, as fast
relative to the CPU as in the exact search at base 34. The earlier
measurement on a quieter machine gave 1.6x to 1.8x for the exact search;
the true gain on an idle machine lies between.

The settings stack. At base 38, `--zscore 3.4 --zlaw cond --hybrid` took
24.2 s against 74.4 s for `--zscore 3` on the CPU, 3.1x faster. The node
count falls 1.32x. Of this, 1.22x is the calibrated law at equal miss rate
(Table 1.3), and the rest comes from the higher miss rate of the new
setting, 2.1% against 1.7% planted. At equal miss rate the law gives about
1.1x in time and the GPU 2.6x to 2.9x.

## Recommended settings for large bases

- Use `--zscore 3.4 --zlaw cond` for a miss rate of about 2% per solution,
  and `--zscore 3.8 --zlaw cond` for about 1%. Both rates hold from base 30
  to 200 in the model (Table 1.5).
- Do not restrict the length (section 2).
- On a machine with the GPU, add `--hybrid`. It ran 2.6x to 2.9x faster
  than the CPU alone in these measurements. Above base 64 the GPU cannot
  help.
- To spread a base over machines, use `--shard i/n` with `--hybrid` on
  each, then `fast merge`. `--journal` does not work with the GPU, so a
  GPU run that stops must start again.

## Scripts and data

| file | contents |
|---|---|
| `fast/src/search.rs` | `--zlaw`, `--zfrom`, `--zslope`, `--ztable`, `--zhist`, `--tree-stats` |
| `fast/src/search/gpu.rs`, `fast/shaders/search.comp` | the z-score rule on the GPU, shards |
| `analysis/r5p_law.py` | the two laws of `ln E`, and the trace reader |
| `analysis/r5p_trace.py` | planted search paths, order 1 and order 2 |
| `analysis/r5p_real.py` | the search paths of the real solutions (`data/r5p_trace_real.txt`) |
| `analysis/r5p_mc.py` | Table 1.1 |
| `analysis/r5p_calib.py` | Table 1.2 and the miss rates by law |
| `analysis/r5p_curves.py` | Table 1.3 and section 1.6, from `data/r5p_zhist/` |
| `analysis/r5p_ztable.py` | the `E / T` table for `--ztable` |
| `analysis/r5p_realmiss.py` | the real solutions cut by each rule |
| `analysis/r5p_planted.py` | Table 1.5 |
| `analysis/r5p_lengths.py` | Tables 2.1 and 2.2 |
| `analysis/r5p_timing.py` | Tables 1.4 and 3.3, `data/r5p_timing.txt` |
| `analysis/data/r5p_zhist/` | the `--zhist` histograms, `b<base>_<law>_<zfrom>[_s<slope>].txt`, `b<base>_table_1.txt` for `E / T`, `b<base>_exact.txt` for the exact tree, and the logs of the runs |
| `analysis/data/r5p_tree_b32_cond5.txt`, `r5p_tree_b36_cond5.txt` | `--tree-stats` at `--zscore 5 --zlaw cond --zfrom 1` |
| `analysis/data/r5p_ztable_b32.txt`, `r5p_ztable_b36.txt` | the `E / T` tables |
| `analysis/data/r5p_check_cond3.4.txt` | `fast search 10 41 --zscore 3.4 --zlaw cond --hybrid` |
| `analysis/data/r5p_b42_*.err` | the two base 42 runs of Table 1.4 |

The planted paths are too large for the repository (145 MB). They are
rebuilt with `python3 r5p_trace.py <b> <n> <order> <seed>`, with `n =
10,000` (4,000 for bases 150 and 200), seed `b` for order 1 and `b + 1000`
for order 2, for the bases 30, 32, 34, 35, 36, 38, 40, 45, 50, 60, 80, 100,
150 and 200.
