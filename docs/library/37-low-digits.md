# 37. The last digits and two free slots

This chapter answers questions 128, 124 and 125 of chapter 31. Question
128 asks whether the last digits of a node with one free slot can be
tested in a few instructions. Question 124 asks for a cheap exact test on
nodes with two free slots. Question 125 asks where the extra instructions
of the residue rule go. Two tests come out of it, and both are on by
default in `fast` (`--low-digits 3 --low-pairs 2`). With both, the exact
search visits 0.52 to 0.57 of the nodes of the residue rule and saves 5%
to 13% of the cycles with both conventions, 10% to 19% with one.

Labels: proven (a proof is here), computed (a measurement, with its
range), heuristic (a judgment from data). Scripts are `analysis/r6s2_*`,
data `analysis/data/r6s2_*`.

Refereeing. The chapter began as a draft. Before it entered the library
Lemma 37.1 and Proposition 37.2 were checked line by line, and the engine
code that implements them (`low_ok`, `pair_ok`, `node_avail`, the `avail`
updates in `next_child` and `settle`) was read against the statements.
The tests are exact as implemented. The draft stated the two-slot test
without its own proposition; Proposition 37.4 and Corollary 37.5 now
state it. The tables were recomputed from the data files (section 37.5).
One pair of data files had swapped names; they are renamed. The Lean
version of the exact search now runs both tests, with a soundness lemma
for each (section 37.5).

## Summary

| section | question | result | status |
|---|---|---|---|
| 37.1 | 128: the last digits with one free slot | The last `j` digits of the sum lie in unknown positions, so they are digits that the unknown positions hold (Lemma 37.1, Proposition 37.2). A 64-bit mask of these digits costs one `or` per child and one compare per new prefix digit. With tables of `w(y) mod b` per level, convention and residue class, one digit is a shift and an `and`. At base 26 the test removes 17% (one digit) to 26% (three digits) of the nodes. One digit about breaks even. Three digits save 3% to 8% of the cycles in bases 24 to 31 with both conventions. | proven; computed |
| 37.2 | 124: two free slots | "`S` in the interval of the prefix" adds nothing but the ends of the `d`-digit range (Proposition 37.3). With the residue it fails 0.0% to 7% of these nodes, too few to pay. The last digit of `t + w(y1) + w(y2)` fails 10% to 28% of them (Proposition 37.4), and is the same shift and `and` over the pairs. With two digits, and three digits for one free slot, the default visits 0.52 to 0.57 of the nodes of the residue rule and takes 0.87 to 0.95 of the cycles in bases 24 to 31 (0.81 to 0.90 with one convention). | proven; computed |
| 37.3 | 125: the instructions of the residue rule | On the same tree, the residue engine with its rule off runs 35% more instructions than the engine before it and 2% fewer cycles. The 68 extra instructions per interval evaluation are mostly register and stack moves of the two byte residues. They fill idle issue slots. The loop waits on its dependent vector additions and on mispredicts. The cycles track the interval evaluations, not the nodes. | computed; heuristic |
| 37.4 | defaults, the GPU | `--low-digits 3 --low-pairs 2` is the default. The GPU search is unchanged and runs without the tests. | computed |
| 37.5 | checks | The tables agree with the data files. The search with the tests finds every solution (Corollary 37.5). A separate functional implementation of the algorithm in Lean has a formal proof of this; the Rust engine is not verified, and its tree with `--unit-depth 0` has the Lean node counts in bases 2 to 12. | proven; computed |

Scripts: `analysis/r6s2_bench.py` (cycle counts, with `analysis/r6s_cyc.c`),
`analysis/r6s2_tables.py` (Tables 37.1.2, 37.2.3 and 37.2.4),
`analysis/r6s2_pair.py` (Table 37.2.1) with the instrumented build
`analysis/r6s2_pair_probe.py`, `analysis/r6s_nodes.py` (Table 37.2.5),
`analysis/r6s2_bykind.py` (Table 37.3.2). Engine: `fast/src/search.rs`
(`low_ok`, `pair_ok`, `node_avail`, the `avail` field), `fast/src/digits.rs`
(`low4`), `fast/src/main.rs` (`--low-digits`, `--low-pairs`, tests).

Machine. The test laptop (4 P-cores, 4 E-cores). Other jobs kept the
1-minute load at 9 to 15. So the tables give node counts, which do not
depend on the load, and user-mode cycles of `fast search b -j 1` on one
P-core, counted with `perf_event_open`. Each cycle count is the median of
3 alternating runs of all builds and flag sets of a base. The largest
spread of the 3 runs of a median is 2.3%, and most are below 1%. Each
measurement used at most 4 threads. Wall times are a secondary check.

Checks (computed). `fast search 2 33` with `-m 0`, `-m 1` and both gives
the lines of `output/b2-41-0.txt` and `output/b2-41-1.txt`. Every run of
the cycle tables gave the output of the old build. `cargo test --release`
passes. The test of chapter 31 that runs every residue mask against the
reference in bases 2 to 20 now also runs every level of both new tests. In
test builds an assertion checks that the mask of each node equals the mask
recomputed from its counts and prefix. The weight options of chapter 17
run against a brute force with the tests on and off. With the tests off
the node counts are those of the residue rule in every base measured. The
GPU tests (`--features gpu`) pass. The GPU and the CPU visit the same
nodes and evaluations with the tests off.

## 37.1 The last digits with one free slot (question 128)

### 37.1.1 Notation

As in section 31.1.1. A node of level `k` has fixed the counts `c_x` of the
digits `x >= k`. Its known prefix holds the top `d - pp` digits of the sum,
lanes `pp` to `d - 1`; lane `i` is the digit of `b^i`. Every prefix digit
below `k` was forced and took a free slot. The node has `rf` free slots,
each holding a digit below `k`. Write `o_x` for the copies of `x` in the
prefix, and

    A = { x >= k : c_x > o_x },

the decided digits with copies outside the prefix. Under `0^0 = m` a
completion with free digits `y_1, ..., y_rf` has the sum

    S_m = t + m (z + #{i : y_i = 0}) + w(y_1) + ... + w(y_rf),

with `w(0)` taken as 0 inside `t` and `z` the zeros of the prefix. (With
the weights of chapter 17 the term `m` is the weight of 0, and `t` holds
the offset; with a negative weight of 0 the engine also shifts `t` and
adds the shift back in the test.)

### 37.1.2 The test

Lemma 37.1 (proven). Let a node of level `k` have `rf` free slots, and let
a completion with free digits `y_1, ..., y_rf` be a solution `n` under
some convention. Then the digits of `n` in the lanes `0` to `pp - 1` are,
as a multiset, the `c_x - o_x` copies of each `x >= k` together with
`y_1, ..., y_rf`.

Proof. The number `n` equals its sum `S` and has `d` digits, so it lies in
the clipped interval of the node. Every number of that interval has the
known prefix in the lanes `pp` to `d - 1`, so `n` has it too. The digits of
`n` are the multiset of the completion: `c_x` copies of each `x >= k`, the
forced digits, and `y_1, ..., y_rf`. The prefix holds `o_x` copies of each
`x >= k`, and its digits below `k` are exactly the forced digits: a prefix
digit below `k` was forced when it appeared, and a forced digit is a
prefix digit. Removing the prefix from the digits of `n` leaves the lanes
below `pp`. It removes `o_x` copies of each `x >= k` and every forced
digit, which leaves the claim.

Proposition 37.2 (proven). Let `rf = 1` and `1 <= j <= pp`. Suppose that
for every reported convention `m` and every `y < k` that completes the
residue of Theorem 31.1 under `m`, some digit of `S_m` in the lanes `0` to
`j - 1` lies outside `A + {y}`. Then no completion of the node is a
solution of a reported convention.

Proof. Let a completion with free digit `y` be a solution `n` under a
reported convention `m`. By Theorem 31.1, `y` completes the residue. By
Lemma 37.1 every digit of `n` in the lanes below `pp` is a copy of some
`x >= k` with `c_x - o_x > 0`, so in `A`, or it is `y`. Since `j <= pp`,
this holds for the lanes `0` to `j - 1`, and `n = S_m`.

The test ignores the multiplicities. A digit that appears twice in the
last `j` lanes needs only one copy outside the prefix. So the test is
weaker than it could be, and still exact.

The search tests a node at the two points of the residue rule
(section 31.2.1): after the forced digits of a child with one free slot
left, and before the interval of child `e = rf - 1`. At the second point
the child has not been settled, so it uses the prefix of its parent, and
`A` of its parent plus `k` if `e > 0`. This is the `A` of the child for the
parent's prefix: the child has `c_k = o_k + e`. Every completion of the
child is a completion of the parent, so its sum has the parent's prefix,
and Lemma 37.1 holds with that prefix. A forced digit of the child only
names `y`. There `pp >= rf >= 1`.

### 37.1.3 The mask and the tables

`A` is a 64-bit mask in each node (the test needs `b <= 64`). It changes
in two places only:

- child `e` of a node adds `k` if `e > 0`, since then `c_k = o_k + e`;
- `settle` counts the copies of each new prefix digit `x >= k` for the
  count test anyway. When the count reaches `c_x` it clears bit `x`.

So the mask costs one `or` per child and one compare and clear per new
decided digit in the prefix. Question 128 asked whether it is cheap to
keep up to date. It is, and with the tests off the search does not keep it.

The test of one digit. Let `a = (t + m z) mod b`, read from lane 0 of `t`
and a table of `m z mod b`. A table per level `k`, convention `m` and
residue class `R` holds `V = { w_m(y) mod b }` over the `y < k` that
complete `R`, as bits `v` and `v + b` of a 128-bit word. A right shift by
`b - a` then gives `{ (v + a) mod b }` in the low `b` bits. A second word
holds `{ (y - w_m(y)) mod b }`, the shifts `a` at which some `y` ends in
itself. The test is

    ((V2 >> (b - a)) & A) != 0  or  bit a of the second word,

for each reported convention. It holds exactly when some `y` of the class
has its last digit in `A + {y}`. With more digits the search loops over
the one to three candidates `y` of the class, computes
`(t + m z + w_m(y)) mod b^j` from lanes 0 to 2 of `t` and tables of
`w_m(y) mod b^3`, and splits it into digits with a table of `b^2` entries.
For three digits it uses one multiplication, `s / b^2 = (s M) >> 40` with
`M = ceil(2^40 / b^2)`. This is exact for `s < b^3` and `b <= 64`, since
`s (M b^2 - 2^40) < 2^18 2^12 < 2^40`; a test checks every case. With
`pp = 2` the third lane is known, and three digits test two. So the
engine tests `min(j, pp)` digits.

### 37.1.4 Nodes and cycles (computed)

Table 37.1.1. Base 26, both conventions, against the residue rule alone
(3,894,520 nodes, 14,192,574 evaluations). Test builds, not committed.

| digits | nodes | ratio | evaluations, ratio | cycles, ratio |
|---:|---:|---:|---:|---:|
| 1 | 3,224,507 | 0.828 | 0.906 | 0.97 to 0.99 |
| 2 | 2,958,329 | 0.760 | 0.868 | 0.94 to 0.97 |
| 3 | 2,880,850 | 0.740 | 0.857 | 0.93 to 0.95 |

The cycle ratios are the range over three builds of the same code with
small differences in layout, each a median of 3 runs. One digit removes
the 17% of section 31.4.2 and now about breaks even, where the loop of
chapter 31 cost 2% more cycles. The first build kept `A` in 128 bits. Its
variable shifts of 128-bit words made one digit cost 2% more cycles again;
64 bits fixed that.

Table 37.1.2. Bases 24 to 31, cycles and nodes against the residue rule
alone. `off`: the new build with both tests off; `L2`, `L3`: two and three
digits; `L3P1`: three digits and the test of section 37.2 on one digit.
One earlier build (`analysis/data/r6s2_cycles_steps.json`).

| b | `off` | `L2` | `L3` | `L3P1` | nodes `L2` | nodes `L3` | nodes `L3P1` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 24 | 1.005 | 0.956 | 0.942 | 0.923 | 0.751 | 0.732 | 0.670 |
| 25 | 1.006 | 0.986 | 0.969 | 0.937 | 0.768 | 0.743 | 0.643 |
| 26 | 1.005 | 0.972 | 0.949 | 0.935 | 0.760 | 0.740 | 0.678 |
| 27 | 1.009 | 0.985 | 0.962 | 0.953 | 0.739 | 0.712 | 0.666 |
| 28 | 1.006 | 0.984 | 0.962 | 0.934 | 0.780 | 0.760 | 0.662 |
| 29 | 1.008 | 0.992 | 0.964 | 0.958 | 0.752 | 0.723 | 0.680 |
| 30 | 1.007 | 0.937 | 0.919 | 0.903 | 0.739 | 0.721 | 0.659 |
| 31 | 1.002 | 0.962 | 0.954 | 0.920 | 0.803 | 0.778 | 0.669 |

With `-m 0` and `-m 1` the same tests give 0.92 to 0.98 (`L2`) and 0.91
to 0.97 (`L3`) of the cycles. Each digit removes fewer nodes than the one
before: 17%, then 7%, then 2% at base 26. The third digit still pays,
because its loop runs only for the nodes that pass the first two.

The tests cost 0% to 1.4% when they are off (`off`). Neither a node nor a
cursor is larger (the mask and the count of prefix zeros fit in their
padding), but the compiler lays out the loop differently. Section 37.3
shows that such instruction counts say little about cycles here.

## 37.2 Two free slots (question 124)

### 37.2.1 What the interval adds

Question 124 asks for a pair `(y1, y2)` that satisfies the residue and puts
`S = t + w(y1) + w(y2)` in the interval of the prefix.

Proposition 37.3 (proven). Let a node have `rf = 2`, and let `S` be the
sum of one of its completions under `0^0 = m` (nonnegative weights). Then
`S` lies in the clipped interval of the node, and so starts with its
prefix, exactly when `b^(d-1) <= S < b^d`.

Proof. `t <= S <= t + z W(0) + 2 W(k-1) = hi`, since a free digit weighs
at least 0 and at most `W(k-1)`, and a known zero at most `W(0)`. The
clipped interval is `[max(t, b^(d-1)), min(hi, b^d - 1)]`.

So the interval part of the 2-sum problem asks only whether some pair with
the right residue reaches `b^(d-1)`, when `t < b^(d-1)`, or stays below
`b^d`. Section 31.4.2 found that the residues of the pairs reach almost
every class, so the pair test with the interval should remove little. It
does.

### 37.2.2 How often no pair passes (computed)

An instrumented build (`analysis/r6s2_pair_probe.py`) enumerates the pairs
`y1 <= y2 < k` of every node with two free slots, after its forced
digits, and tests five conditions:

1. the residue mod `b - 1` and `S` in the clipped interval (Proposition 37.3);
2. 1, and the digit of `S` in lane `pp - 1`, the first unknown position, is
   in `A + {y1, y2}`;
3. 1, and the last digit of `S` is in `A + {y1, y2}`;
4. 1, 2 and 3;
5. `S` is a solution.

Condition 5 is exact. A node passes only if a solution lies below it, so
it bounds what any test on two free slots can do. Tests 2 to 4 are exact
by Lemma 37.1.

Table 37.2.1. Both conventions, residue rule only. `fail`: share of the
nodes with two free slots that no pair passes, in the build of that
condition. `nodes`: nodes of the whole search with the test, over the
nodes without it.

| b | nodes | two-slot nodes | fail 1 | fail 2 | fail 3 | fail 4 | nodes 1 | nodes 2 | nodes 3 | nodes 4 | nodes 5 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 20 | 82,463 | 27,055 | 0.033 | 0.406 | 0.236 | 0.678 | 0.987 | 0.858 | 0.895 | 0.720 | 0.574 |
| 21 | 163,033 | 48,557 | 0.001 | 0.243 | 0.101 | 0.574 | 1.000 | 0.922 | 0.953 | 0.759 | 0.572 |
| 22 | 302,261 | 97,450 | 0.031 | 0.411 | 0.245 | 0.685 | 0.988 | 0.857 | 0.894 | 0.718 | 0.575 |
| 23 | 579,030 | 183,514 | 0.001 | 0.362 | 0.110 | 0.601 | 1.000 | 0.877 | 0.950 | 0.756 | 0.575 |
| 24 | 1,166,554 | 362,883 | 0.003 | 0.363 | 0.171 | 0.667 | 0.999 | 0.878 | 0.920 | 0.722 | 0.574 |
| 25 | 1,993,518 | 622,626 | 0.066 | 0.404 | 0.276 | 0.678 | 0.975 | 0.862 | 0.886 | 0.718 | 0.567 |
| 26 | 3,894,520 | 1,245,619 | 0.003 | 0.408 | 0.163 | 0.682 | 0.999 | 0.861 | 0.924 | 0.711 | 0.563 |
| 27 | 7,720,378 | 2,388,100 | 0.000 | 0.354 | 0.127 | 0.627 | 1.000 | 0.883 | 0.943 | 0.735 | 0.558 |
| 28 | 13,596,926 | 4,484,191 | 0.071 | 0.470 | 0.252 | 0.707 | 0.971 | 0.833 | 0.890 | 0.697 | 0.554 |
| 29 | 26,908,928 | 8,596,052 | 0.009 | 0.373 | 0.114 | 0.625 | 0.996 | 0.874 | 0.948 | 0.735 | 0.554 |
| 30 | 53,636,804 | 17,328,474 | 0.002 | 0.369 | 0.161 | 0.682 | 0.999 | 0.875 | 0.922 | 0.699 | 0.549 |

The answer to question 124. With the residue and the interval, no pair
passes in 0.0% to 7% of the nodes with two free slots, and the search
loses 0.0% to 2.9% of its nodes. The large values come at bases 20, 22,
25 and 28. A sorted table or a min and max of `w` per residue class could
answer it in a few instructions. But it would save less than 1% of the
nodes in most bases, and the test runs on a third of the nodes. I did not
build it.

The digits are another matter. The first unknown digit fails 24% to 47%
of these nodes, the last digit 10% to 28%, both together 57% to 71%. An
exact test on two free slots could remove up to 43% to 45% of all nodes
(column `nodes 5`).

### 37.2.3 The last digit of a pair

Proposition 37.4 (proven). Let `rf = 2` and `1 <= j <= pp`. Suppose that
for every reported convention `m` and every pair `y1 <= y2 < k` with
`R_m + r_m(y1) + r_m(y2) == 0 (mod b - 1)`, some digit of
`S_m = t + m (z + #{i : y_i = 0}) + w(y1) + w(y2)` in the lanes `0` to
`j - 1` lies outside `A + {y1, y2}`. Then no completion of the node is a
solution of a reported convention.

Proof. Let a completion with free digits `y1 <= y2` be a solution `n`
under a reported `m`. Its residue is `R_m + r_m(y1) + r_m(y2)`, which is 0
modulo `b - 1` by Proposition 1.5. By Lemma 37.1 every digit of `n` below
lane `pp` is in `A` or is `y1` or `y2`. The sum and the residue do not
depend on the order of `y1, y2`, so the pairs with `y1 <= y2` cover every
completion.

The last digit needs no full sum, and the mask of section 37.1.3 serves
again. A table per level, convention and residue class holds
`{ (w_m(y1) + w_m(y2)) mod b }` over the pairs `y1 <= y2 < k` that
complete the class, doubled as before, and the bits `(y1 - v)` and
`(y2 - v)`. Two digits loop over the pairs of the class that pass; the
pairs below `k` come first in each list, so a table of end indices gives
them. The test runs after the forced digits of a child with two free slots
left. Run also before them, as the one-slot test is, it cost 0.8% more
cycles at base 26 and removed no further node. A child whose forced digits
fill a slot meets the one-slot test instead.

Corollary 37.5 (proven). The search with `--low-digits L --low-pairs P`
(`L <= 3`, `P <= 2`) finds every solution of the conventions it reports.

Proof. The search removes a node only by the rules of the old search, by
Theorem 31.1, by Proposition 37.2 with `j = min(L, pp)`, or by
Proposition 37.4 with `j = min(P, pp)`. Section 37.1.2 shows that the test
before the interval of a child uses a valid prefix and mask. The old
search misses nothing (Corollary 31.2).

Table 37.2.2. Base 26, both conventions, three digits for one free slot.
The last row is from two other series, against the residue rule alone.
Test builds, not committed.

| two-slot test | nodes | cycles, ratio to no two-slot test |
|---|---:|---:|
| none | 2,880,850 | 1.000 |
| one digit, before and after the forced digits | 2,641,779 | 0.998 |
| one digit, before | 2,785,697 | 0.989 |
| one digit, after | 2,641,779 | 0.990 |
| two digits, after | 2,134,691 | about 0.96 |

### 37.2.4 Cycles (computed)

Table 37.2.3. Cycles of the residue rule alone (`base`, commit 9756e6b)
and ratios to it. `L3P1`: three digits, pairs on one digit. `L2P2`,
`L3P2`: two or three digits, pairs on two digits (`L3P2` is the default).
Both conventions.

| b | `base` | `off` | `L3P1` | `L2P2` | `L3P2` | nodes, `L3P2` |
|---:|---:|---:|---:|---:|---:|---:|
| 24 | 0.384 G | 1.000 | 0.915 | 0.903 | 0.891 | 0.543 |
| 25 | 0.634 G | 1.006 | 0.922 | 0.941 | 0.926 | 0.552 |
| 26 | 1.211 G | 1.001 | 0.926 | 0.921 | 0.911 | 0.548 |
| 27 | 2.302 G | 1.001 | 0.935 | 0.959 | 0.938 | 0.550 |
| 28 | 4.079 G | 1.007 | 0.933 | 0.934 | 0.919 | 0.548 |
| 29 | 8.022 G | 1.010 | 0.938 | 0.967 | 0.945 | 0.568 |
| 30 | 16.13 G | 1.008 | 0.888 | 0.877 | 0.867 | 0.526 |
| 31 | 34.28 G | 1.003 | 0.907 | 0.920 | 0.895 | 0.573 |

Table 37.2.4. The same with one convention. `base` is the residue rule for
that convention alone.

| b | `-m 0`: `off` | `L3P2` | nodes | `-m 1`: `off` | `L3P2` | nodes |
|---:|---:|---:|---:|---:|---:|---:|
| 24 | 1.010 | 0.841 | 0.536 | 1.000 | 0.838 | 0.544 |
| 25 | 1.008 | 0.882 | 0.550 | 1.014 | 0.871 | 0.557 |
| 26 | 0.998 | 0.859 | 0.555 | 1.000 | 0.843 | 0.549 |
| 27 | 1.002 | 0.885 | 0.550 | 1.005 | 0.875 | 0.550 |
| 28 | 1.010 | 0.869 | 0.552 | 1.003 | 0.858 | 0.548 |
| 29 | 1.009 | 0.896 | 0.564 | 1.006 | 0.869 | 0.559 |
| 30 | 1.007 | 0.820 | 0.526 | 1.008 | 0.807 | 0.521 |
| 31 | 1.002 | 0.857 | 0.571 | 1.003 | 0.838 | 0.565 |

`L3P2` is the fastest in every base and mode but 25, 27 and 29 with both
conventions, where `L3P1` is ahead by 0.3% to 0.7%, inside the scatter.
It saves 5.5% to 13.3% of the cycles with both conventions, 10% to 18%
with `-m 0` and 12.5% to 19.3% with `-m 1`. With one convention the
residue classes of the pairs are fewer, so the masks are sparser and the
test removes more.

The cycles fall less than the evaluations. `L3P2` evaluates 0.68 to 0.72
of the intervals of `base`. The cycles per evaluation rise from 82 to 101
(bases 24 to 31, both conventions) to 107 to 127. The tests cost their
own work, and the evaluations they remove are among the cheaper ones.

Wall time (secondary). Base 32 on 8 threads: 7.75 s against 9.40 s, median
of 3 alternating runs, load about 12.

Table 37.2.5. Nodes of `fast search b` with the default against the
residue rule alone, and the old engine of chapter 31 (before the residue
rule). Output identical in every base.

| b | old | residue | default | ratio to residue | ratio to old | `-m 0`, ratio | `-m 1`, ratio |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 15 | 4,985 | 4,178 | 2,757 | 0.660 | 0.553 | 0.657 | 0.650 |
| 18 | 32,886 | 26,681 | 15,102 | 0.566 | 0.459 | 0.572 | 0.567 |
| 21 | 184,506 | 163,033 | 91,395 | 0.561 | 0.495 | 0.558 | 0.561 |
| 24 | 1,430,261 | 1,166,554 | 633,928 | 0.543 | 0.443 | 0.536 | 0.544 |
| 26 | 4,955,060 | 3,894,520 | 2,134,691 | 0.548 | 0.431 | 0.555 | 0.549 |
| 28 | 18,025,432 | 13,596,926 | 7,452,542 | 0.548 | 0.413 | 0.552 | 0.548 |
| 30 | 66,246,690 | 53,636,804 | 28,191,150 | 0.526 | 0.426 | 0.526 | 0.521 |
| 31 | 121,387,604 | 92,205,006 | 52,876,747 | 0.573 | 0.436 | 0.571 | 0.565 |
| 32 | 214,709,067 | 178,023,228 | 93,847,947 | 0.527 | 0.437 | 0.533 | 0.531 |
| 33 | 464,274,849 | 404,543,412 | 224,320,623 | 0.555 | 0.483 | 0.551 | 0.552 |

The `-m` columns compare with the residue rule for the same convention
(Table 31.2.2). From base 20 on the ratio lies between 0.52 and 0.60 and
shows no trend with the base (computed). Unlike the residue rule alone, it
depends little on the factors of `b - 1`, since the last digits do not
depend on them.

Heuristic 37.6. The share of the tree the tests remove stays near 0.45 in
larger bases. So the census runs of bases 42 to 46 on the CPU should take
0.85 to 0.95 of their time with the residue rule alone. The share of nodes
with one and two free slots, the inputs of both tests, changes little with
the base (Table 31.1.1, section 31.2.2). Both tests depend on the level
`k / b` and the share of digits left more than on `b` itself.

## 37.3 Where the residue rule's instructions go (question 125)

Chapter 31 measured 6% to 13% more instructions with the residue rule.
It asked whether the larger node, the extra branch or the test before the
interval costs the time. Comparisons on the same tree answer it:

- `old`: the engine before the residue rule (commit `ba24b14~1`);
- `fields`: the residue engine (commit 9756e6b) with `res_add` and
  `res_ok` replaced by no-ops, run with `--no-residue`. It carries the
  residues in every node and cursor, but never changes or tests them;
- `nores`: the residue engine with `--no-residue`. It computes both
  residues of every child and runs both tests, which never fail;
- `res`: the residue engine with its rule.

The first three visit the same 4,955,060 nodes and 16,313,626 evaluations
at base 26.

Table 37.3.1. Base 26, both conventions, one P-core, median of 3 (two
alternating series; `old` and `nores` are in both, and agree within 0.7%).

| build | cycles | instructions | IPC | branch misses | cycles per evaluation |
|---|---:|---:|---:|---:|---:|
| `old` | 1.376 G | 3.323 G | 2.42 | 16.1 M | 84.3 |
| `fields` | 1.393 G | 3.383 G | 2.43 | 16.2 M | 85.4 |
| `nores` | 1.345 G | 4.501 G | 3.35 | 15.0 M | 82.5 |
| `res` | 1.210 G | 3.675 G | 3.04 | 15.1 M | 85.3 |

So the residues cost 35% more instructions on the same tree and no
cycles: `nores` is 2% faster than `old`. The fields alone cost 1.8% of the
instructions and 1.1% of the cycles. The rule then removes 13% of the
evaluations and 10% of the cycles of `nores`.

Table 37.3.2. Base 24, instructions by kind from callgrind (dynamic
counts, `analysis/data/r6s2_residue_kinds.txt`), `fields` to `nores`,
4,773,112 evaluations.

| kind | added | per evaluation |
|---|---:|---:|
| moves to or from the stack | 87.9 M | 18.4 |
| scalar arithmetic | 87.0 M | 18.2 |
| moves between registers | 80.1 M | 16.8 |
| conditional moves | 18.3 M | 3.8 |
| arithmetic on memory | 16.9 M | 3.5 |
| other moves from memory | 14.0 M | 2.9 |
| vector | 12.7 M | 2.7 |
| branches | 11.2 M | 2.3 |
| vector moves to or from the stack | -1.1 M | -0.2 |
| total | 326.9 M | 68.5 |

The residues are two bytes per node. Each child adds `r(k)` to both, with
a conditional subtraction of `q`. The compiler packs and unpacks the two
bytes, and spills them around the vector additions. Half of the added
instructions are moves. None of them is on the critical path. The loop
waits on chains of dependent vector additions (each about 20 cycles,
`fast/README.md`) and on about one mispredict per child, and the residue
work fits in the slots those leave idle. The IPC rises from 2.42 to 3.35
at the same cycle count.

Answer to question 125 (computed; heuristic for the cause). Neither the
larger node, nor the branch, nor the test before the interval costs
measurable time. The instructions are moves and arithmetic that run in
the shadow of the vector chain. The cycles track the interval
evaluations, about 82 to 85 per evaluation in all four builds. Chapter 31
saw the cycles fall less than the nodes because the nodes it removes are
cheap: a node with one free slot costs two evaluations. A leaner residue
(one `u16`, or residues only for the nodes near the bottom) would save
instructions, not cycles. The same holds for the new tests: they lower
the instructions by 12% to 25% (`L3P2`) and the cycles by less.

The method. Line attributions of callgrind differ between builds, because
the inlined code maps to different lines. The table counts instructions by
their kind (from `objdump`) at each address that callgrind counted, which
does not depend on the line map. `perf` is not installed. Valgrind 3.25
does not decode GFNI, so the profiled builds use
`-C target-feature=-gfni`.

## 37.4 Defaults and the GPU

Both tests are on by default (`--low-digits 3 --low-pairs 2`), since they
win in every base and mode of Tables 37.2.3 and 37.2.4. `--low-digits 0
--low-pairs 0` restores the tree of chapter 31, and `--no-residue` turns
both tests off with the rule. The tests need `b <= 64`; above that the
search runs without them.

The tests do not act while the program builds the work units. So the
units, the unit counts in the journals and the shards are the same with
and without them, and a journal of chapter 31 resumes with the new build.

The GPU search is unchanged. Each node of the shader would need the
64-bit mask and the clear in its forced-digit loop, and the tables of
section 37.1.3 per level. The subgroup work is bound by its dependent
chains (`fast/README.md`), where the gain of the residue rule was 1.18x.
I did not port it. `--gpu` and `--hybrid` turn the tests off, so their CPU
threads visit the nodes of the GPU, and the GPU tests still check equal
node and evaluation counts.

## 37.5 Independent checks

The engine against the statements. The code of `low_ok` and `pair_ok`
(`fast/src/search.rs`) computes, for each reported convention, the test
"some `y` (or pair) of the residue class has its last `min(j, pp)` digits
in `A` plus the free digits". The precheck of one digit with the shifted
masks is the union of the per-candidate checks, so it fails only when
every candidate fails. `t` is a carry-normalized digit vector modulo
`b^(32N)`, so its low lanes give `t mod b^3` even when `t` is shifted
below 0. The zero term `zlow` holds the shift and `z` times the weight of
0, and the weight of a free 0 is in the tables. The mask: child `e` sets
bit `k` when `e > 0` (`ck = occk + e`), `settle` clears bit `x` when the
copies of `x` in the known lanes reach `c_x`, and `run_units` starts each
unit from `node_avail`. The prefix zeros `z` come from the known lanes of
the clipped `lo`, which are the prefix. The reading found no case where a
test removes a node with a solution below it. A rerun of the test
`residue_rule_keeps_solutions` (`cargo test --release`; bases 2 to 20,
every residue mask and every level of both tests, with the mask assertion
on) passes.

The tables against the data. Table 37.2.1 was recomputed from
`analysis/data/r6s2_pair_b20_30.txt` and agrees in every entry. Tables
37.1.2, 37.2.3 and 37.2.4, and the ranges quoted with them (evaluations,
cycles per evaluation, instructions), agree with
`analysis/data/r6s2_cycles_steps.json` and `r6s2_cycles.json`. Tables
37.3.1 and 37.3.2 agree with `r6s2_residue_cycles.json` and
`r6s2_residue_kinds.txt`. Table 37.2.5 agrees with `r6s2_nodes_both.txt`
and Table 31.2.2. The files of the `-m 0` and `-m 1` runs had swapped
names: the file named `m0` held the runs of `-m 1`. The cycle data, which
record their arguments, and a rerun of base 15 (2,725 nodes with `-m 0`,
2,531 with `-m 1`) settle it. The files are renamed; the table was right.
Tables 37.1.1 and 37.2.2 come from test builds that are not committed.

Lean. The verified search of `lean/Munchausen/Search/` now runs both
tests, with any numbers of digits (`searchWith b ms low pair`; `search` uses
3 and 2). `foundWith_eq_solutions` and `found_eq_solutions` hold with the
tests on. `lowDigit_avail_or_free` is Lemma 37.1 in the form the search
uses: a digit of a completion in an unknown position is in `A` or is a free
digit. `lowOk_of_isCompletion` and `pairOk_of_isCompletion` are
Propositions 37.2 and 37.4 for the nodes of the Lean search, and
`avail_childAt` is the update of the mask by a child. The Lean code
recomputes `A` from the counts and the prefix, as it does `t`, `hi` and the
residue. Its tree has the node counts of `fast search 2 12 --unit-depth 0`
for the residue rule alone, the default, `-m 0`, `-m 1`, and the digit
counts 1, 0 and 2, 1 (`#guard` in `Examples.lean`). The option matters:
the Rust code builds its work units, by default 4 levels deep, without the
tests, so the node counts of section 37.2.4 are those of that mixed tree.
The theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

One difference with chapter 31 is unexplained. Section 31.4.2 reports
3,222,980 nodes at base 26 for the check of one last digit, and 2,947,567
for two. The committed test leaves 3,224,507 and 2,958,329. The two-digit
gap fits a check that counted copies, as question 156 proposes. The
one-digit gap of 1,527 nodes (0.05%) needs a check at some other point,
for example after forced digits that fill the last slot. The build of
chapter 31 is not committed, so this cannot be traced. Both versions keep
every solution.

## Library corrections

Each item now has a note in the chapter or question file it corrects.

1. Section 31.4.2, the rows "one free slot: last digit of `S` must be in
   the unknown positions" (1.020 cycles) and "last two digits" (1.073),
   and the paragraph "But a node with one free slot costs only its two
   interval evaluations, and the check costs a loop over the candidate
   `y` with digit counts in the prefix." With the mask and the tables of
   section 37.1.3 the check pays: three digits save 3% to 8% of the cycles
   (Table 37.1.2), and with the pair test 5% to 13% (Table 37.2.3). The
   summary row 31.4 says the same.
2. Section 31.7: "shows that the low digits pay only where the tree is
   already cheap." They pay a constant factor of 1.06 to 1.15 in cycles
   with both conventions.
3. Section 31.2.4: "Every evaluation now updates two residues, and the
   instructions grow by 6% to 13%." The added instructions cost no cycles
   (Table 37.3.1). The cycles fall less than the nodes because the removed
   nodes are cheap, as that section says.
4. Questions 124, 125 and 128 are answered (section 37.2.2, section 37.3,
   section 37.1).

## Files

| file | contents |
|---|---|
| `fast/src/search.rs` | `low_ok`, `pair_ok`, `node_avail`, `magic_b2`, the tables `ltab`, `ltab2`, `lcand`, `pcand`, the `avail` field of `Node` and `Head`, the count of prefix zeros in `Cursor` |
| `fast/src/digits.rs`, `fast/src/main.rs` | `low4`; the options and tests |
| `fast/src/search/gpu.rs` | the CPU side of `--hybrid` runs without the tests |
| `analysis/r6s2_bench.py`, `analysis/r6s2_tables.py` | cycle counts and Tables 37.1.2, 37.2.3, 37.2.4 |
| `analysis/r6s2_pair.py`, `analysis/r6s2_pair_probe.py` | Table 37.2.1 and its instrumented build |
| `analysis/r6s2_bykind.py` | Table 37.3.2 |
| `analysis/data/r6s2_cycles.json` | Tables 37.2.3 and 37.2.4 |
| `analysis/data/r6s2_cycles_steps.json` | Table 37.1.2 |
| `analysis/data/r6s2_pair_b20_30.txt` | Table 37.2.1 |
| `analysis/data/r6s2_nodes_{both,m0,m1}.txt` | Table 37.2.5, stderr of `fast search 2 33` |
| `analysis/data/r6s2_residue_cycles.json`, `r6s2_residue_kinds.txt` | Tables 37.3.1 and 37.3.2 |
| `lean/Munchausen/Search/` | the verified search with both tests (section 37.5) |

Test builds that are not committed: the variants of Tables 37.1.1 and
37.2.2, and `fields` of section 37.3 (two functions made no-ops).

## New questions

These are questions 154 to 158 of `questions.md`.

1. The first unknown digit of a pair. It fails 24% to 47% of the nodes
   with two free slots (Table 37.2.1), more than the last digit, but needs
   the carry of `t + w(y1) + w(y2)` into lane `pp - 1`. Most pairs have
   `w(y2)` far below `b^(pp-1)`, so the digit is that of `t` or one more.
   Can a test on the top lanes of `t` and a table of `w(y) / b^(pp-1)` per
   level decide it for most pairs, and the rest by a full sum?
2. The GPU. With the tests, the CPU visits 0.53 to 0.57 of the nodes of
   the GPU. Does a port to `shaders/search.comp` pay on the subgroup
   engine, where the residue rule gave 1.18x?
3. Copies. The tests ignore the multiplicity of a digit in the last lanes.
   A second mask of the digits with two copies left would make them exact
   for two and three digits. How many more nodes would that remove?
4. Three free slots. The sums of three weights reach most classes and most
   last digits, so the mask would be dense. Does the last digit of a
   triple still remove a useful share of those nodes (14% of the tree,
   Table 31.1.1)?
5. (Answered in this chapter, section 37.5.) Lean. Lemma 37.1 and
   Propositions 37.2 and 37.4 are statements about multisets and digits,
   close to those of chapter 1. Can the verified search of
   `lean/Munchausen/Search/` run both tests, with a soundness lemma for
   each?
