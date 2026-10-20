# 31. Pruning by the residue and balanced shards

This chapter collects the results of the library that restrict digit
counts or residues, and asks which of them the exact search of `fast` can
use. One of them pays: the congruence of Proposition 1.5, tested on the
nodes with one free slot. The others are implied by the interval test
already, or prune too little to pay for their test. A second, smaller
change splits a base into shards of more even size. Each statement is
marked proven (a proof is here), computed (a measurement, with its range)
or heuristic (the model of chapter 5, or a judgment from data).

## Summary

| section | question | result | status |
|---|---|---|---|
| 31.1 | where the tree spends its nodes | 43% of the nodes have one free slot and 25% have two (base 28). Their subtrees are tiny. The tree dies in the middle levels, not at the leaves. | computed |
| 31.2 | the congruence mod `b - 1` as a pruning rule | a node with one free slot fails if no digit below `k` completes its residue (Theorem 31.1). The rule removes 12% to 25% of the nodes in bases 15 to 35 and saves 10% to 18% of the cycles (1.11x to 1.22x) in bases 24 to 31. With one convention (`-m 0` or `-m 1`) it removes 13% to 30% (1.22x to 1.29x in cycles at bases 28 and 31). The GPU is 1.18x faster at base 30. The `--zscore` search visits 9% to 13% fewer nodes. | proven; computed |
| 31.3 | the fixed-point interval | the engine already iterates the forced digits to a fixed point. The iteration saves 1.46x to 1.47x nodes in every base from 20 to 33, a constant factor. The interval it reaches is the exact hull of the reachable sums (Lemma 31.4), so the worst-case bound on the free slots is not loose. | proven; computed |
| 31.4 | other count and residue results | Proposition 1.6 and the bound of section 1.7 are implied by the interval test (Proposition 31.5). The parity rules of section 1.6 are parts of the congruence of section 31.2. The residue test with zero or two free slots costs more cycles than it saves. A test on the last one or two digits with one free slot did too in this chapter; with a mask and tables it pays (chapter 37). Self-paying digits and blocks give no rule. | proven; computed |
| 31.5 | splitting a base into jobs | `--shard-by size` (new) deals the units out by predicted size. The largest of 64 shards drops from 2.12 to 1.35 times the mean at unit depth 4, and from 1.21 to 1.14 at depth 6 (base 30). | computed |
| 31.6 | the inexact search | the residue rule is exact, so it keeps the miss rate of `--zscore` and its calibration. No other change to the thresholds follows from the theory. | heuristic; computed |

Scripts: `analysis/r6s_residue.py` (Table 31.2.1), `analysis/r6s_nodes.py`
(node tables from the stderr of `fast search`), `analysis/r6s_shards.py`
(section 31.5), `analysis/r6s_cyc.c` and `analysis/r6s_cycbench.py` (cycle
counts). Data: `analysis/data/r6s_*`. Engine: `fast/src/search.rs`,
`fast/src/search/gpu.rs`, `fast/shaders/search.comp`, `fast/src/main.rs`,
`fast/src/merge.rs`, `fast/src/journal.rs`.

Machine. The test laptop (4 P-cores, 4 E-cores, Arc 140V GPU). Other
agents kept the 1-minute load at 8 to 28 during the runs. So the tables
give user-mode cycles of one thread pinned to core 0, counted with
`perf_event_open`, and node counts, which do not depend on the load. Each
cycle count is the median of 2 or 3 alternating runs of the old and the new
build. Repeated runs differ by less than 1%.

Checks. `fast search 2 32`, `-m 0` and `-m 1` give the lines of
`output/b2-41-0.txt` and `output/b2-41-1.txt`, and bases 33 to 35 give the
same output as the old build. `cargo test --release` passes, with a new
test that runs every rule mask in bases 2 to 20 against the reference
search, and an assertion (in test builds) that the residue each node
carries equals the residue recomputed from its counts and prefix. The GPU
tests give the same node and evaluation counts on the GPU and the CPU.

## 31.1 Where the exact tree spends its nodes

### 31.1.1 Notation

A node of level `k` has fixed the counts `c_x` of the digits `x >= k`. Its
known prefix holds the top `d - pp` digits of the sum, and `pp` is the
number of unknown positions. Every digit of the prefix below `k` was
forced: it took one free slot and added its weight to `t`. The node has
`rf` free slots left, and each of them holds a digit below `k`. So the
multiset of a completion is

    {c_x copies of x, x >= k} + {the forced digits} + {y_1, ..., y_rf},  y_i < k,

and its sum is `S = t + w(y_1) + ... + w(y_rf)`, plus `m` for every zero
under `0^0 = m`. The interval `[t, t + z + rf W(k-1)]` of the node holds
every such `S` (`docs/algorithm.md`).

### 31.1.2 Nodes by free slots (computed)

`--tree-stats` counts nodes by level and unknown positions. A build that
keys the same table by `rf` instead of `pp` (a one-line change, not
committed) gives the table below.

Table 31.1.1. Base 28, both conventions. Share of the nodes by free slots,
the mean size of their subtrees, and their mean level. Before: the engine
of 17 October 2026 (18.0 million nodes). After: with the residue rule of
section 31.2 (13.6 million nodes).

| `rf` | nodes before | share | subtree | level | nodes after | share | subtree |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 7,794,012 | 0.433 | 1.23 | 15.7 | 3,365,947 | 0.248 | 1.22 |
| 2 | 4,558,024 | 0.253 | 2.13 | 16.2 | 4,558,007 | 0.335 | 1.61 |
| 3 | 2,536,402 | 0.141 | 3.68 | 16.7 | 2,536,401 | 0.187 | 2.80 |
| 4 | 1,414,463 | 0.079 | 6.46 | 17.2 | 1,414,463 | 0.104 | 4.90 |
| 5 | 776,173 | 0.043 | 11.4 | 17.6 | 776,173 | 0.057 | 8.63 |
| 6 | 431,898 | 0.024 | 20.5 | 18.0 | 431,886 | 0.032 | 15.5 |
| 8 | 126,490 | 0.007 | 68.0 | 18.9 | 126,492 | 0.009 | 51.4 |
| 10 | 36,196 | 0.002 | 226 | 19.7 | 36,174 | 0.003 | 171 |

43% of the nodes have one free slot, and 25% have two. Their subtrees are
tiny: a node with `rf = 1` has 0.23 descendants on average. Each further
free slot multiplies the subtree by about 1.8, the growth per base of the
whole search (section 27.5 found 1.93 per slot for work units). The tree
dies in the middle levels: the nodes with one free slot sit at level 15.7
of 27 on average, with about 12 unknown positions. The leaf of the engine
runs only 3 to 10 times per base (`fast/README.md`).

This decides which results can help. A rule that needs all counts runs only
at the leaves and saves nothing; this is why section 6.3 found that
congruences "only prune near the leaves". A rule that needs only a few
unknowns can act on the two thirds of the nodes with one or two free slots.

## 31.2 The residue rule

### 31.2.1 The rule

Write `q = b - 1` and `r_m(x) = w(x) - x mod q`, with `w(0) = m` under
`0^0 = m`. For a node, let `R_m` be the sum of `r_m(x)` over the known part
of its multiset (decided and forced digits), modulo `q`.

Theorem 31.1 (proven). Let a node have exactly one free slot, holding a
digit below `k`. If no `y < k` has `R_m + r_m(y) == 0 (mod q)`, then no
completion of the node is a solution under `0^0 = m`.

Proof. A completion has the multiset of the node plus one digit `y < k`.
By Proposition 1.5 a solution under `0^0 = m` has
`sum over its digits of (w(x) - x) == 0 (mod b - 1)`, and that sum is
`R_m + r_m(y)` modulo `q`.

The engine keeps `R_0` and `R_1` in every node. A child adds `e r(k)`, and
each forced digit `x` adds `r_m(x)`; the two conventions differ only in the
forced zeros. A table holds, for each level `k` and convention `m`, the set
`{-r_m(y) : y < k}` as 128 bits, so the test is two shifts and an `or`.
The search drops a node with `rf = 1` whose residues fail under every
convention it reports (both by default, one with `-m`). It runs the test at
two points:

- after the forced digits of a child, if the child has one free slot left;
- before the interval of child `e = rf - 1` of a cursor. That child has one
  free slot before its forced digits. A forced digit only names the digit
  `y` of the slot, so the test is the same, and it saves the interval
  evaluation.

Corollary 31.2 (proven). The search with the residue rule finds every
solution of the conventions that it reports. With both conventions it
finds every solution that the old search finds.

Proof. The old search was exact (`docs/algorithm.md`, "Why the search
misses nothing"). The new rule removes a node only by Theorem 31.1, applied
to every reported convention.

The rule also acts while the engine builds the work units, so a base now
has fewer units (base 12: 114 instead of 118). A journal of an older build
then names another unit count, and the new build refuses it; `--no-residue`
builds the old units and resumes it. A journal written with `-m 0` or
`-m 1` records the convention, and a run with another `-m` refuses it.

The rule is the congruence of section 6.3 and Proposition 10.2 used where
it bites. Section 10.4 said that it "removes a factor of `b - 1`, which
does not change the growth rate". That is right for the growth. But the
factor is not a factor `b - 1` of the leaves; it is a share of the nodes
with one free slot, which are 43% of the tree.

### 31.2.2 How much it can remove (heuristic)

The rule removes the share `1 - p` of the nodes with one free slot, where
`p` is the share of residues `R` that some `y < k` completes. With both
conventions a node passes if one of them passes.

Table 31.2.1. The share of residues that pass, for `k = 0.57 b`, the mean
level of the nodes with one free slot. `either` is for a node with one
known zero, so that `R_1 = R_0 + 1` (`analysis/r6s_residue.py`).

| b | `q` | `k` | f = 1: `m = 0`, `m = 1`, either | f = 2: `m = 0`, `m = 1`, either |
|---:|---:|---:|---|---|
| 24 | 23 | 14 | 0.48, 0.48, 0.70 | 1.00, 1.00, 1.00 |
| 25 | 24 | 14 | 0.25, 0.29, 0.50 | 0.46, 0.71, 0.92 |
| 28 | 27 | 16 | 0.33, 0.37, 0.63 | 0.67, 0.93, 0.96 |
| 30 | 29 | 17 | 0.45, 0.48, 0.72 | 1.00, 1.00, 1.00 |
| 31 | 30 | 18 | 0.20, 0.23, 0.40 | 0.43, 0.63, 0.87 |
| 32 | 31 | 18 | 0.42, 0.45, 0.77 | 1.00, 1.00, 1.00 |
| 33 | 32 | 19 | 0.34, 0.38, 0.69 | 0.50, 0.84, 1.00 |
| 37 | 36 | 21 | 0.19, 0.22, 0.39 | 0.39, 0.58, 0.78 |
| 64 | 63 | 36 | 0.29, 0.30, 0.54 | 0.78, 0.94, 1.00 |
| 100 | 99 | 57 | 0.28, 0.29, 0.54 | 0.78, 0.93, 1.00 |
| 127 | 126 | 72 | 0.18, 0.19, 0.37 | 0.39, 0.57, 0.78 |

The values `r(y)` for `y < k` take only 20% to 48% of the classes. The
residue laws of chapter 20 explain why: modulo 2, `x^x == x` always;
modulo 3 and 5, `x^x - x` misses whole classes (Theorems 20.11 and 20.12).
So the rule removes most where `b - 1` has the factors 2, 3 and 5 (bases
25, 31, 37, 127) and least where `b - 1` is prime (24, 30, 32). With one
free slot the rule passes 40% to 77% of the nodes under both conventions,
and 18% to 48% under one. With two free slots almost every class is
reachable, so a test there removes almost nothing (section 31.4.2).

Heuristic 31.3. The rule removes about `0.43 (1 - p)` of the tree, where
`0.43` is the share of the nodes with one free slot. For `p = 0.4` to 0.77
this is 10% to 26%, and with one convention (`p` = 0.18 to 0.48) 22% to
35%. The share of these nodes, and `p` at the level `0.57 b`, change little
with `b` (Tables 31.1.1 and 31.2.1), so the gain is a constant factor, as
section 10.4 predicted, of size 1.1 to 1.35. Table 31.2.2 measures 12% to 25%
for both conventions, as estimated, and 13% to 30% for one, a little
below the estimate. The estimate takes `p` at one level and treats the
residue of a node as uniform; I have not checked which of the two fails.

### 31.2.3 Nodes (computed)

Table 31.2.2. Nodes of `fast search b`, old engine against the residue rule,
for both conventions together and for each alone. The output is the same in
every base.

| b | old | both | ratio | `-m 0` | ratio | `-m 1` | ratio |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 15 | 4,985 | 4,178 | 0.838 | 4,147 | 0.832 | 3,896 | 0.782 |
| 16 | 8,908 | 7,054 | 0.792 | 6,580 | 0.739 | 6,830 | 0.767 |
| 17 | 17,339 | 15,064 | 0.869 | 14,968 | 0.863 | 14,087 | 0.812 |
| 18 | 32,886 | 26,681 | 0.811 | 25,101 | 0.763 | 25,676 | 0.781 |
| 19 | 56,327 | 43,654 | 0.775 | 43,297 | 0.769 | 41,454 | 0.736 |
| 20 | 103,099 | 82,463 | 0.800 | 76,785 | 0.745 | 78,889 | 0.765 |
| 21 | 184,506 | 163,033 | 0.884 | 161,967 | 0.878 | 150,051 | 0.813 |
| 22 | 379,435 | 302,261 | 0.797 | 283,177 | 0.746 | 290,711 | 0.766 |
| 23 | 715,196 | 579,030 | 0.810 | 574,460 | 0.803 | 540,260 | 0.755 |
| 24 | 1,430,261 | 1,166,554 | 0.816 | 1,108,633 | 0.775 | 1,108,115 | 0.775 |
| 25 | 2,498,800 | 1,993,518 | 0.798 | 1,967,526 | 0.787 | 1,843,721 | 0.738 |
| 26 | 4,955,060 | 3,894,520 | 0.786 | 3,622,854 | 0.731 | 3,705,366 | 0.748 |
| 27 | 9,510,641 | 7,720,378 | 0.812 | 7,638,459 | 0.803 | 7,069,475 | 0.743 |
| 28 | 18,025,432 | 13,596,926 | 0.754 | 12,663,714 | 0.703 | 12,965,612 | 0.719 |
| 29 | 33,546,007 | 26,908,928 | 0.802 | 26,637,042 | 0.794 | 24,433,581 | 0.728 |
| 30 | 66,246,690 | 53,636,804 | 0.810 | 50,520,624 | 0.763 | 51,487,751 | 0.777 |
| 31 | 121,387,604 | 92,205,006 | 0.760 | 91,257,673 | 0.752 | 86,091,750 | 0.709 |
| 32 | 214,709,067 | 178,023,228 | 0.829 | 165,276,010 | 0.770 | 168,142,954 | 0.783 |
| 33 | 464,274,849 | 404,543,412 | 0.871 | 402,086,747 | 0.866 | 366,973,422 | 0.790 |
| 34 | 824,063,470 | 616,527,547 | 0.748 | | | | |
| 35 | 1,513,176,601 | 1,219,355,059 | 0.806 | | | | |

The ratio for both conventions lies between 0.75 and 0.88, and follows the
factors of `b - 1`: the best bases are 34 (`q = 33`), 28 (`q = 27`) and 31
(`q = 30`). It shows no trend with the base. With one convention it lies between 0.70 and 0.87. The old
engine explored the same tree for `-m 0`, `-m 1` and both.

### 31.2.4 Time (computed)

Table 31.2.3. User-mode cycles of `fast search b -j 1` on one P-core.

| b | run | cycles, old | cycles, new | ratio | speedup |
|---:|---|---:|---:|---:|---:|
| 24 | both | 0.423 G | 0.381 G | 0.900 | 1.11x |
| 26 | both | 1.369 G | 1.202 G | 0.878 | 1.14x |
| 27 | both | 2.552 G | 2.286 G | 0.896 | 1.12x |
| 28 | both | 4.830 G | 4.075 G | 0.844 | 1.19x |
| 29 | both | 9.090 G | 8.002 G | 0.880 | 1.14x |
| 30 | both | 18.15 G | 15.93 G | 0.877 | 1.14x |
| 31 | both | 41.37 G | 34.00 G | 0.822 | 1.22x |
| 28 | `-m 0` | 4.838 G | 3.836 G | 0.793 | 1.26x |
| 28 | `-m 1` | 4.832 G | 3.930 G | 0.813 | 1.23x |
| 31 | `-m 0` | 41.32 G | 33.77 G | 0.817 | 1.22x |
| 31 | `-m 1` | 41.53 G | 32.29 G | 0.777 | 1.29x |

Base 30 is one run of each build; the others are medians of 2 or 3.

The cycles fall less than the nodes. Every evaluation now updates two
residues, and the instructions grow by 6% to 13%. The removed nodes are
cheap: a node with one free slot has two children, and most of its work is
those two interval evaluations.

Correction (chapter 37, 2026-10-19). The added instructions cost no
cycles: on the same tree the residue engine with its rule off runs 35%
more instructions than the old engine and 2% fewer cycles (Table 37.3.1).
They are moves of the two byte residues that fill idle issue slots. The
cycles track the interval evaluations, and the removed nodes are cheap,
as said above.

Table 31.2.4. Wall time and user time of `fast search b -j 8`, median of 3
(base 32) or 2 (base 33) alternating runs, with a load of 5 to 9 from
other jobs.

| run | wall, old | wall, new | speedup | user, old | user, new | speedup |
|---|---:|---:|---:|---:|---:|---:|
| base 32 | 7.27 s | 6.45 s | 1.13x | 54.1 s | 48.3 s | 1.12x |
| base 33 | 17.18 s | 15.09 s | 1.14x | 118.7 s | 109.0 s | 1.09x |
| base 33, `-m 1` | 17.63 s | 14.37 s | 1.23x | 119.8 s | 102.8 s | 1.17x |

The wall times scatter by 10% to 20% between runs of the same build under
this load; the cycle counts of Table 31.2.3 are the better measure.

GPU. The shader runs the same test (a subgroup sum of the counts times the
residues of the digit values), and the GPU and the CPU visit the same nodes
and evaluations in the test suite (bases 2 to 26, with and without
`--zscore`). Base 30 with `--gpu`: 1.03 s against 1.21 s with
`--no-residue` (median of 3 alternating runs), 1.18x.

## 31.3 The fixed-point interval

### 31.3.1 The engine already iterates to a fixed point

A proposed rule: once the counts of the digits `>= k` are fixed, every
digit `v < k` among the determined leading digits of `S` forces
`c_v >= k_v`, its multiplicity there. The free slots then add between
`sum k_v w(v) + r' w_min` and `sum k_v w(v) + r' W(k-1)`, with
`r' = rf - sum k_v`. Prune if `r'` is negative or exceeds the unknown
positions, narrow the interval, read off more leading digits, and repeat
until nothing changes.

This is the forcing loop of the engine (`settle` in `fast/src/search.rs`,
"Forced digits" in `docs/algorithm.md`). A forced digit `v` adds `w(v)` to
`t`, lowers `hi` by `W(k-1) - w(v)`, uses one free slot, and fails the node
if no slot is left. The loop runs until no new leading digit appears. The
test "`r'` at most the unknown positions" never fires: the unknown
positions hold the missing copies of the decided digits and the free slots,
so `pp = sum over x >= k of (c_x - occ_x) + rf` is an identity.

### 31.3.2 What the iteration is worth (computed)

A test build stops the forcing loop after its first round: the forced
digits of the first round still go into `t` and `hi`, but the search does
not look for new leading digits in the narrower interval at that node.
The next level finds them.

Table 31.3.1. Both builds without the residue rule, bases 20 to 33, same
output.

| b | nodes, fixed point | nodes, one round | ratio | evaluations, ratio |
|---:|---:|---:|---:|---:|
| 20 | 103,099 | 151,874 | 1.473 | 1.165 |
| 21 | 184,506 | 272,522 | 1.477 | 1.167 |
| 22 | 379,435 | 559,191 | 1.474 | 1.165 |
| 23 | 715,196 | 1,049,480 | 1.467 | 1.162 |
| 24 | 1,430,261 | 2,094,323 | 1.464 | 1.160 |
| 25 | 2,498,800 | 3,655,633 | 1.463 | 1.158 |
| 26 | 4,955,060 | 7,259,392 | 1.465 | 1.158 |
| 27 | 9,510,641 | 13,907,993 | 1.462 | 1.155 |
| 28 | 18,025,432 | 26,286,789 | 1.458 | 1.153 |
| 29 | 33,546,007 | 49,061,189 | 1.463 | 1.155 |
| 30 | 66,246,690 | 97,030,094 | 1.465 | 1.157 |
| 31 | 121,387,604 | 178,140,597 | 1.468 | 1.159 |
| 32 | 214,709,067 | 315,888,504 | 1.471 | 1.161 |
| 33 | 464,274,849 | 681,998,250 | 1.469 | 1.161 |

The iteration saves a factor 1.46 to 1.47 in nodes and 1.16 in interval
evaluations, the same in every base. It changes the constant, not the
growth.

### 31.3.3 The interval cannot be narrowed further

Lemma 31.4 (proven). Let a node have `rf >= 1` free slots. The ends of its
interval are sums of completions of the node: `lo = t` is the sum of the
completion with every free slot 0 under `0^0 = 0`, and
`hi = t + z + rf W(k-1)` is the sum of the completion with every free slot
`k - 1` under `0^0 = 1` (true weights, `k >= 2`).

Proof. Under `0^0 = 0` a zero adds nothing, so the first completion has
sum `t`. In the second, the zeros are the `z` known ones, each adds 1, and
each free slot adds `w(k-1) = W(k-1)`.

So the interval is the exact hull of the sums that the known counts allow.
The bound on the free slots is attained, not loose. A narrower range must
use the digits of the completions themselves, which the levels below the
node test one count at a time, or residues, as in section 31.2.

The gap between the measured growth 1.89 and the floor 1.638 has another
cause (section 10.1). The floor counts the nodes that are likely in the
model, `e^H` with the entropy of the Poisson counts of the suffix. The
exact tree keeps every count vector that fits the prefix, about
`C(b, kappa b)` at level `kappa b`, and grows like `2^b` from below.
Theorem 27.5 shows that this is not a weakness of the tree: every
certificate built from interval queries has at least `N_k` queries, and
`N_k` is 0.86 to 0.98 times the widest level of the tree in bases 10 to 21.

## 31.4 The other results, one by one

### 31.4.1 Results that the interval test already implies (proven)

Proposition 31.5 (proven). The exact search never creates a node of length
`d = b` with at most two copies of `b - 1` (Proposition 1.6, `b >= 7`), nor
a node of length `d = b - 1` with three or more copies of `b - 1`
(section 1.7).

Proof. For `d = b` the root decides `c_(b-1) = e`. Child `e <= 2` has no
known digits yet, so `hi = e (b-1)^(b-1) + (b - e) (b-2)^(b-2)`. The proof
of Proposition 1.6 shows that this is below `b^(b-1)` for `b >= 7`, so the
child fails the test `hi >= b^(d-1)`. For
`d = b - 1`, child `e >= 3` has `lo = e (b-1)^(b-1) > b^(b-1)`, so it fails
`lo < b^d`, and the loop over `e` stops.

The same holds for every bound of the form "a `d`-digit solution needs at
least (at most) so many copies of the top digits": such bounds come from
comparing the extreme sums with `b^(d-1)` and `b^d`, which the root and its
first descendants do anyway.

The parity rules of section 1.6 (an even number of zeros in odd bases under
`0^0 = 1`, the counts of digits `== 2 (mod 4)` or `== 2 (mod 6)`) are the
parts of Proposition 1.5 modulo the prime powers of `b - 1`. The residue
rule tests the whole congruence, so it contains them. They bite only where
the multiset is known up to one digit, like the full congruence.

### 31.4.2 Tests that cost more than they save (computed)

All at base 26, cycles relative to the build with the residue rule
(1.20 G cycles, 3.89 million nodes).

| variant | nodes | cycles |
|---|---:|---:|
| residue rule (committed) | 3,894,520 | 1.000 |
| also test child `e = rf` (no free slot) by residue | 3,894,510 | 1.022 |
| also test nodes with two free slots by residue | -0.03% to -0.9% in bases 23 to 29 | not measured |
| one free slot: last digit of `S` must be in the unknown positions | 3,222,980 | 1.020 |
| one free slot: last two digits | 2,947,567 | 1.073 |
| residue test only after the forced digits (not before the interval) | 3,894,520 | 1.055 |
| residue of a child computed only after its forced digits, from a table of `e r(k)` | 3,894,520 | 1.004 |

Child `e = rf` has no free slot. Its residue passes with probability about
`2/q`, but the child nearly always fails its interval too, so the test only
saves an evaluation that fails early anyway, and its branch mispredicts.

Two free slots: the sums `r(y_1) + r(y_2)` reach 87% to 100% of the
classes under one of the two conventions (Table 31.2.1).

The last digits. With one free slot `y`, the sum `S = t + w(y)` is known
for each `y` with the right residue, and its last digits must be digits of
the unknown positions: copies of decided digits `x >= k` that the prefix
does not hold yet, or `y`. This is the bottom check of section 27.4, at the
one place in the top-down tree where the low digits are known. It removes
another 17% (one digit) or 24% (two digits) of the nodes, and finds the same
solutions. But a node with one free slot costs only its two interval
evaluations, and the check costs a loop over the candidate `y` with digit
counts in the prefix. Corollary 27.9 says that a bottom check never prunes a
top-down tree above its single vectors. Here it prunes, but where the tree
is already cheap.

Correction (chapter 37, 2026-10-19). The last digits do pay in another
form. A 64-bit mask of the digits that the unknown positions still hold
costs one `or` per child and one compare per new prefix digit, and a table
of `w(y) mod b` per level and residue class makes one digit a shift and an
`and` (section 37.1.3). Three last digits then save 3% to 8% of the cycles
in bases 24 to 31, and with the last two digits of a pair on the nodes
with two free slots 5% to 13% (Tables 37.1.2 and 37.2.3). Both tests are
on by default. The committed test leaves 3,224,507 and 2,958,329 nodes for
one and two digits, a little more than the rows above (section 37.5).

### 31.4.3 Results that give no rule

- Self-paying digits (Propositions 2.2 and 2.3) need `a^(a-1) = b^k`. In
  bases up to 127 this happens only in perfect powers such as 8 and 64.
  They build solutions under `0^0 = 0`; they say nothing about which
  multisets fail.
- Blocks and exact splits (chapter 22): section 22.5.3 shows that a search
  by blocks returns only a share of about `1/b` of the solutions and costs
  as much as the tree.
- The leading digit of section 1.7 is a statement about the top digits of
  `S`, which the interval computes exactly.
- The 3-adic and 5-adic laws of chapter 20 describe which residues
  `x^x - x` reaches. They enter through Table 31.2.1, not as separate rules:
  every residue of the multiset modulo a divisor of `b - 1` is a part of
  the residue modulo `b - 1` (Proposition 10.2).
- Bottom digits in bases with a small radical (section 27.4): no node above
  the single vectors knows them.

## 31.5 Splitting a base into jobs

Section 27.5 found that the work units have a heavy-tailed size law, that
every `n`-th unit is a poor split for many shards, and that the type of a
unit (free slots `rf`, unknown digits `L`) explains 93% to 97% of the
variance of `ln(nodes)`. The new option `--shard-by size` uses that fit.

The rule. Weigh each unit by `2^((15 rf - 10 L) / 16)`, about
`e^(0.656 rf - 0.44 L)`, scaled so that the units of each digit count
`d = b - j` carry the measured share of `d` (the weights of the progress
estimate). Sort the units by weight, largest first, ties by index. Give
each unit to the shard with the least weight so far, ties to the lowest
shard. The arithmetic is in integers (a 16-entry table of `2^(j/16)` and
shifts), so every machine computes the same split. The shard line of the
output and the journal header name the rule, and `merge` refuses shards
split by different rules.

Table 31.5.1. Largest shard over the mean, base 30 with the residue rule,
from the measured unit sizes (`analysis/r6s_shards.py`). `best` is the
same greedy split with the true sizes.

| unit depth | units | shards | `index` | `size` | best |
|---:|---:|---:|---:|---:|---:|
| 4 | 45,955 | 16 | 1.33 | 1.15 | 1.00 |
| 4 | 45,955 | 64 | 2.12 | 1.35 | 1.00 |
| 4 | 45,955 | 256 | 4.46 | 3.50 | 3.50 |
| 6 | 523,095 | 16 | 1.07 | 1.04 | 1.00 |
| 6 | 523,095 | 64 | 1.21 | 1.14 | 1.00 |
| 6 | 523,095 | 256 | 1.57 | 1.36 | 1.00 |

On the units of chapter 27 (old engine, depth 4, bases 28 to 34), 64 shards
go from 1.85 to 2.56 times the mean to 1.37 to 1.54. For 256 shards at
depth 4 the largest unit alone is 3.5 times a shard, and no split helps; at
depth 6 the predicted split gives 1.36. Section 27.5 recommended a deeper
unit depth for many shards. The two changes add up: depth 6 and the size
rule give 1.14 for 64 shards, where depth 4 and the index rule give 2.12.

The prediction error is the limit. Within a type the standard deviation of
`ln(nodes)` is 0.5 (section 27.5), so a unit predicted as large can be 1.6
times larger. The greedy split with the true sizes is perfect at 64 shards.
A better predictor, for example the node count of each unit two levels
down, would close part of the gap at the cost of a pass over the units
(question 126).

## 31.6 The inexact search

The residue rule is exact, and it runs on the generic path of the inexact
rules too. So `--zscore` keeps its miss rate, and the calibration of
chapter 28 (the z-score of a planted path) does not change: the rule
removes no node above a solution. Node counts of
`fast search b --zscore 3.4 --zlaw cond`:

| b | without the rule | with the rule | ratio |
|---:|---:|---:|---:|
| 28 | 4,138,756 | 3,617,649 | 0.874 |
| 30 | 12,657,118 | 11,519,928 | 0.910 |
| 32 | 30,533,202 | 27,907,568 | 0.914 |

User-mode cycles on one P-core: base 30, 6.89 G against 6.42 G (0.932,
median of 2); base 32, 19.74 G against 18.25 G (0.924, one run each).

The gain is smaller than in the exact search, because the z-score rule has
already removed many of the nodes that the residue rule removes: a node
with one free slot and an unlikely prefix.

Heuristic 31.6. The theory gives no better threshold. The z-score uses the
probability `E` of the suffix counts. A residue factor `q P_f(R)`, the
chance that `f` free digits complete the residue, could join `E`. It
differs from 1 only for `f <= 2` (Table 31.2.1), where the subtrees hold one
to three nodes, and the exact rule already removes the nodes where it is 0.
A threshold that changes with the level or with the cost of a subtree was
tried in section 28.1.6 and gave no gain.

## 31.7 What this means for the runs of round 6

Question 104 asks for an exact census of bases 42 to 46, both conventions.
Run them together: one run with both conventions visits 0.75 to 0.87 of
the old tree, while two runs with `-m 0` and `-m 1` visit 1.4 to 1.7 times
it. For many machines, use `--unit-depth 6 --shard-by size` (section 31.5).

Question 105 asks for a `b`-digit solution under `0^0 = 1` with
`--min-digits b --zscore 3.4 --zlaw cond`. Add `-m 1`: the residue rule then
tests only that convention.

Nodes of `fast search b --min-digits b -m 1 --zscore 3.4 --zlaw cond`:

| b | old | new | ratio | evaluations, ratio |
|---:|---:|---:|---:|---:|
| 30 | 1,702,244 | 1,532,500 | 0.900 | 0.957 |
| 33 | 11,441,160 | 10,347,616 | 0.904 | 0.959 |
| 36 | 34,836,328 | 31,231,673 | 0.897 | 0.958 |

So about 10% fewer nodes and 4% fewer evaluations: a small gain for the
`b`-digit runs, where the z-score rule already removes most nodes with one
free slot.

Section A7 of `questions-round6.md` says that what is left for the exact
search is the middle digits of `S`, constant factors and quantum search.
This chapter adds one constant factor, from the one residue the multiset
fixes, and shows that the low digits pay only where the tree is already
cheap. It does not touch question 109.

Correction (chapter 37, 2026-10-19). The low digits pay a second constant
factor. With the last-digit tests on the nodes with one and two free slots
the search visits 0.52 to 0.57 of the nodes of the residue rule and saves
5.5% to 13.3% of the cycles with both conventions, 10% to 19% with one
(Tables 37.2.3 to 37.2.5).

## Files

- Engine: `fast/src/search.rs` (`res_ok`, `res_add`, `node_res`, the
  residue fields of `Params` and `Node`), `fast/src/search/gpu.rs` and
  `fast/shaders/search.comp` (the same test on the GPU), `fast/src/main.rs`
  (`--no-residue`, `-m`, `--shard-by`, tests), `fast/src/merge.rs` and
  `fast/src/journal.rs` (the shard rule and the convention in the headers).
- Scripts: `analysis/r6s_residue.py`, `analysis/r6s_nodes.py`,
  `analysis/r6s_shards.py`, `analysis/r6s_cyc.c`, `analysis/r6s_cycbench.py`.
- Data: `analysis/data/r6s_nodes_*.txt` (stderr of the runs of Tables 31.2.2
  and 31.3.1; bases 34 and 35 in `r6s_nodes_old_34_35.txt` and
  `r6s_nodes_res_34_35.txt`), `analysis/data/r6s_rf_b28_*.txt` (Table 31.1.1),
  `analysis/data/r6s_units_b30_u4.txt.gz` (Table 31.5.1).
- Test builds that are not committed: the table by `rf` (Table 31.1.1), the
  first-round-only forcing loop (section 31.3.2), the bottom checks and the
  other variants of section 31.4.2. Each is a few lines in `next_child` or
  `settle`.

## New questions

These are questions 124 to 128 of `questions.md`.

1. (Answered in chapter 37: with the residue, the interval removes 0.0% to
7% of these nodes, too few to pay; the last digit of the pair removes 10%
to 28% of them and pays, section 37.2.) The residue rule needs one free
slot. Is there a cheap exact test for two free slots? The congruence alone reaches almost every class. The pair
`(y_1, y_2)` must also make `S = t + w(y_1) + w(y_2)` fall in the interval
of the prefix; with the residue this is a 2-sum problem over `k` values.
How often does no pair satisfy both, and can a sorted table per level
answer it in a few instructions?

2. (Answered in chapter 37: the extra instructions are moves that run in
idle issue slots and cost no cycles, section 37.3.) Where do the extra
cycles of the residue go? Two residues per node
cost 6% to 13% more instructions. A child that computes its residue only
after its forced digits saves 2.3% of the instructions and no cycles
(section 31.4.2), so the cost is not the arithmetic. A profile of the loop
over `e` with and without the rule would say whether the larger node, the
extra branch, or the pre-test before the interval costs the time.

3. A better size predictor for `--shard-by size`. The node count of each
unit after one or two more levels, times the type fit, should cut the
within-type error of 0.5 in `ln(nodes)`. What is the best balance for 64 and
256 shards at depth 4, and what does the probe cost?

4. Table 31.1.1 says that each free slot multiplies the subtree by about 1.8,
and that the tree is 43% nodes with one free slot. Is the law of `rf` over
the nodes of the exact tree a fixed geometric law, as the branching process
of section 27.5 suggests? If so, the share of the nodes that any test on
`f` free slots can reach is known in advance for every base.

5. (Answered in chapter 37: yes, the mask is one `or` per child and one
compare per new prefix digit, and three digits save 3% to 8% of the
cycles, section 37.1.) Do the last digits pay in some other form? A check of the last digit
removes 17% of the nodes at base 26 but costs 2% more cycles. A table of
`w(y) mod b` per residue class, and a bit mask of the digits that the
unknown positions still hold, would make it a few instructions. Is the mask
cheap to keep up to date as the prefix grows?
