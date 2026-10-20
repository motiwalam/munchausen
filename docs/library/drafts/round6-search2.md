# Round 6: the last digits and two free slots

DRAFT. This file answers questions 128, 124 and 125 of `questions.md`
(new questions 5, 1 and 2 of chapter 31). Question 128 asks whether the
last digits of a node with one free slot can be tested in a few
instructions. Question 124 asks for a cheap exact test on nodes with two
free slots. Question 125 asks where the extra instructions of the residue
rule go. Two tests come out of it, and both are on by default in `fast`.
Each statement is marked proven (a proof is here), computed (a
measurement, with its range) or heuristic (a judgment from data).

## Summary

| section | question | result | status |
|---|---|---|---|
| 1 | 128: the last digits with one free slot | The last `j` digits of the sum lie in unknown positions, so they must be digits that the unknown positions hold (Proposition 1.2). A 64-bit mask of these digits costs one `or` per child and one compare per new prefix digit. With tables of `w(y) mod b` per level, convention and residue class, one digit is a shift and an `and`. At base 26 the test removes 17% (one digit) to 26% (three digits) of the nodes. One digit about breaks even. Three digits save 3% to 8% of the cycles in bases 24 to 31 with both conventions. | proven; computed |
| 2 | 124: two free slots | "S in the interval of the prefix" adds nothing but the ends of the `d`-digit range (Proposition 2.1). With the residue it fails 0.0% to 7% of these nodes, too few to pay. The last digit of `t + w(y1) + w(y2)` fails 10% to 28% of them, and is the same shift and `and` over the pairs. On two digits, with the test of section 1, the default visits 0.52 to 0.57 of the nodes of the residue rule and takes 0.87 to 0.95 of the cycles in bases 24 to 31 (0.81 to 0.90 with one convention). | proven; computed |
| 3 | 125: the instructions of the residue rule | On the same tree, the residue engine with its rule off runs 35% more instructions than the engine before it and 2% fewer cycles. The 68 extra instructions per interval evaluation are mostly register and stack moves of the two byte residues. They fill idle issue slots. The loop waits on its dependent vector additions and on mispredicts. The cycles track the interval evaluations, not the nodes. | computed; heuristic |
| 4 | defaults, the GPU | `--low-digits 3 --low-pairs 2` is the default. The GPU search is unchanged and runs without the tests. | computed |

Scripts: `analysis/r6s2_bench.py` (cycle counts, with `analysis/r6s_cyc.c`),
`analysis/r6s2_tables.py` (Tables 1.2, 2.3 and 2.4), `analysis/r6s2_pair.py`
(Table 2.1) with the instrumented build `analysis/r6s2_pair_probe.py`,
`analysis/r6s_nodes.py` (Table 2.5), `analysis/r6s2_bykind.py` (Table 3.2).
Data: `analysis/data/r6s2_*`. Engine: `fast/src/search.rs` (`low_ok`,
`pair_ok`, `node_avail`, the `avail` field), `fast/src/digits.rs` (`low4`),
`fast/src/main.rs` (`--low-digits`, `--low-pairs`, tests).

Machine. The test laptop (4 P-cores, 4 E-cores). Other jobs kept the
1-minute load at 9 to 15. So the tables give node counts, which do not
depend on the load, and user-mode cycles of `fast search b -j 1` on one
P-core, counted with `perf_event_open`. Each cycle count is the median of 3
alternating runs of all builds and flag sets of a base. The largest spread of the 3 runs
of a median is 2.3%, and most are below 1%. Each measurement used at most
4 threads. Wall times are a secondary check.

Checks (computed). `fast search 2 33` with `-m 0`, `-m 1` and both gives
the lines of `output/b2-41-0.txt` and `output/b2-41-1.txt`. Every run of
the cycle tables gave the output of the old build. `cargo test --release`
passes. The test of chapter 31 that runs every residue mask against the
reference in bases 2 to 20 now also runs every level of both new tests. In
test builds an assertion checks that the mask of each node equals the mask
recomputed from its counts and prefix. The weight options of chapter
17 run against a brute force with the tests on and off. With the tests
off the node counts are those of the residue rule in every base measured.
The GPU tests (`--features gpu`) pass. The GPU and the CPU visit the same
nodes and evaluations with the tests off.

## 1. The last digits with one free slot (question 128)

### 1.1 Notation

As in section 31.1.1. A node of level `k` has fixed the counts `c_x` of the
digits `x >= k`. Its known prefix holds the top `d - pp` digits of the sum,
lanes `pp` to `d - 1`. Every prefix digit below `k` was forced and took a
free slot. The node has `rf` free slots, each holding a digit below `k`.
Write `o_x` for the copies of `x` in the prefix, and

    A = { x >= k : c_x > o_x },

the decided digits with copies outside the prefix. Under `0^0 = m` a
completion with free digits `y_1, ..., y_rf` has the sum

    S_m = t + m (z + #{i : y_i = 0}) + w(y_1) + ... + w(y_rf),

with `w(0)` taken as 0 inside `t` and `z` the zeros of the prefix. (With
the weights of chapter 17 the term `m` is the weight of 0, and `t` holds the
offset and the shift of a negative weight.)

### 1.2 The test

Lemma 1.1 (proven). Let a completion of the node be a solution under some
convention. Then the digits of `S` in the lanes `0` to `pp - 1` are, as a
multiset, the `c_x - o_x` copies of each `x >= k` together with
`y_1, ..., y_rf`.

Proof. A solution has the digits of its multiset. The lanes `pp` and up of
`S` are the prefix, because `S` lies in the interval of the node and every
number of that interval has the prefix. The prefix holds `o_x` copies of
each `x >= k`, and its digits below `k` are the forced digits, which the
multiset contains exactly once each beyond the free slots. Removing the
prefix from the multiset leaves the copies outside the prefix and the free
slots.

Proposition 1.2 (proven). Let `rf = 1` and `1 <= j <= pp`. If for every
`y < k` that completes the residue of Theorem 31.1 under a reported
convention `m`, some digit of `S_m` in the lanes `0` to `j - 1` lies outside
`A + {y}`, then no completion of the node is a solution of a reported
convention.

Proof. By Lemma 1.1 every digit of a solution in the lanes below `pp` is in
`A` or is `y`. The residue rule already excludes the other `y`.

The test ignores the multiplicities. A digit that appears twice in the
last `j` lanes needs only one copy. It is weaker than it could be, and
still exact.

The search tests a node at the two points of the residue rule
(section 31.2.1): after the forced digits of a child with one free slot
left, and before the interval of child `e = rf - 1`. At the second point
the child has not been settled, so it uses the prefix of its parent and
`A` of its parent plus `k` if `e > 0`. A forced digit of that child only
names `y`, so Lemma 1.1 holds with the parent's prefix too, and `pp >= 1`
there.

### 1.3 The mask and the tables

`A` is a 64-bit mask in each node (the test needs `b <= 64`). It changes
in two places only:

- child `e` of a node adds `k` if `e > 0`, since then `c_k = o_k + e`;
- `settle` counts the copies of each new prefix digit `x >= k` for the
  count test anyway. When the count reaches `c_x` it clears bit `x`.

So the mask costs one `or` per child and one compare and clear per new
decided digit in the prefix. Question 128 asked whether it is cheap to keep
up to date. It is, and with the tests off the search does not keep it.

The test of one digit. Let `a = (t + m z) mod b`, read from lane 0 of `t`
and a table of `m z mod b`. A table per level `k`, convention `m` and
residue class `R` holds `V = { w_m(y) mod b }` over the `y < k` that
complete `R`, as bits `v` and `v + b` of a 128-bit word, so that a shift by
`b - a` gives `{ (v + a) mod b }` in the low `b` bits. A second word holds
`{ (y - w_m(y)) mod b }`, the shifts `a` at which some `y` ends in itself.
The test is

    ((V2 >> (b - a)) & A) != 0  or  bit a of the second word,

for each reported convention. With more digits the search loops over the
one to three candidates `y` of the class, computes
`(t + m z + w_m(y)) mod b^j` from lanes 0 to 2 of `t` and tables of
`w_m(y) mod b^3`, and splits it into digits with a table of `b^2` entries
and, for three digits, one multiplication (`s / b^2 = (s M) >> 40`, exact
for `s < b^3` and `b <= 64`; a test checks every case).

### 1.4 Nodes and cycles (computed)

Table 1.1. Base 26, both conventions, against the residue rule alone
(3,894,520 nodes, 14,192,574 evaluations).

| digits | nodes | ratio | evaluations, ratio | cycles, ratio |
|---:|---:|---:|---:|---:|
| 1 | 3,224,507 | 0.828 | 0.906 | 0.97 to 0.99 |
| 2 | 2,958,329 | 0.760 | 0.868 | 0.94 to 0.97 |
| 3 | 2,880,850 | 0.740 | 0.857 | 0.93 to 0.95 |

The cycle ratios are the range over three builds of the same code with
small differences in layout, each a median of 3 runs. One digit removes
the 17% of section 31.4.2 and now about breaks even, where the loop of
chapter 31 cost 2% more cycles. The first build kept `A` in 128 bits, and
its variable shifts of 128-bit words made one digit cost 2% more cycles
again; 64 bits fixed that.

Table 1.2. Bases 24 to 31, cycles and nodes against the residue rule
alone. `off`: the new build with both tests off; `L2`, `L3`: two and three
digits; `L3P1`: three digits and the test of section 2 on one digit. One
earlier build (`analysis/data/r6s2_cycles_steps.json`).

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
padding), but the compiler lays out the loop differently.
Section 3 shows that such instruction counts say little about cycles here.

## 2. Two free slots (question 124)

### 2.1 What the interval adds

Question 124 asks for a pair `(y1, y2)` that satisfies the residue and puts
`S = t + w(y1) + w(y2)` in the interval of the prefix.

Proposition 2.1 (proven). Let a node have `rf = 2`, and let `S` be the
sum of one of its completions under `0^0 = m` (nonnegative weights). Then
`S` lies in the clipped interval of the node, and so starts with its
prefix, exactly when `b^(d-1) <= S < b^d`.

Proof. `t <= S <= t + z W(0) + 2 W(k-1) = hi`, since the free digits weigh
at least 0 and at most `W(k-1)`. The clipped interval is
`[max(t, b^(d-1)), min(hi, b^d - 1)]`.

So the interval part of the 2-sum problem asks only whether some pair with
the right residue reaches `b^(d-1)`, when `t < b^(d-1)`, or stays below
`b^d`. Section 31.4.2 found that the residues of the pairs reach almost
every class, so the pair test with the interval should remove little. It
does.

### 2.2 How often no pair passes (computed)

An instrumented build (`analysis/r6s2_pair_probe.py`) enumerates the pairs
`y1 <= y2 < k` of every node with two free slots, after its forced
digits, and tests five conditions:

1. the residue mod `b - 1` and `S` in the clipped interval (Proposition 2.1);
2. 1, and the digit of `S` in lane `pp - 1`, the first unknown position, is
   in `A + {y1, y2}`;
3. 1, and the last digit of `S` is in `A + {y1, y2}`;
4. 1, 2 and 3;
5. `S` is a solution.

Condition 5 is exact. A node passes only if a solution lies below it. So
it bounds what any test on two free slots can do. Tests 2 to 4 are exact by
Lemma 1.1.

Table 2.1. Both conventions, residue rule only. `fail`: share of the nodes
with two free slots that no pair passes. `nodes`: nodes of the whole
search with the test, over the nodes without it.

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
25 and 28. A sorted table or a min and max of `w` per
residue class could answer it in a few instructions, but it would save
less than 1% of the nodes in most bases, and the test runs on a third of
the nodes. I did not build it.

The digits are another matter. The first unknown digit fails 24% to 47% of
these nodes, the last digit 10% to 28%, both together 57% to 71%. An exact
test on two free slots could remove up to 43% to 45% of all nodes (column
5).

### 2.3 The last digit of a pair

The last digit needs no full sum, and the mask of section 1.3 serves again.
A table per level, convention and residue class holds
`{ (w_m(y1) + w_m(y2)) mod b }` over the pairs `y1 <= y2 < k` that complete
the class, doubled as before, and the bits `(y1 - v)` and `(y2 - v)`. Two
digits loop over the pairs of the class that pass; the pairs below `k` come
first in each list, so a table of end indices gives them. The test runs
after the forced digits of a child with two free slots left. Run also
before them, as the one-slot test is, it cost 0.8% more cycles at base 26
and removed no further node. A child whose forced digits fill a slot meets
the one-slot test instead.

Table 2.2. Base 26, both conventions, three digits for one free slot. The
last row is from two other series, against the residue rule alone.

| two-slot test | nodes | cycles, ratio to no two-slot test |
|---|---:|---:|
| none | 2,880,850 | 1.000 |
| one digit, before and after the forced digits | 2,641,779 | 0.998 |
| one digit, before | 2,785,697 | 0.989 |
| one digit, after | 2,641,779 | 0.990 |
| two digits, after | 2,134,691 | about 0.96 |

### 2.4 Cycles (computed)

Table 2.3. Cycles of the residue rule alone (`base`, commit 9756e6b) and
ratios to it. `L3P1`: three digits, pairs on one digit. `L2P2`, `L3P2`:
two or three digits, pairs on two digits (`L3P2` is the default). Both
conventions.

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

Table 2.4. The same with one convention. `base` is the residue rule for
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
with `-m 0` and 12.5% to 19.3% with `-m 1`. With one convention the residue
classes of the pairs are fewer, so the masks are sparser and the test
removes more.

The cycles fall less than the evaluations. `L3P2` evaluates 0.68 to 0.72
of the intervals of `base`, and the cycles per evaluation rise from 82 to
101 (bases 24 to 31, both conventions) to 107 to 127. The tests cost
their own work, and the evaluations they remove are among the cheaper ones.

Wall time (secondary). Base 32 on 8 threads: 7.75 s against 9.40 s, median
of 3 alternating runs, load about 12.

Table 2.5. Nodes of `fast search b` with the default against the residue
rule alone, and the old engine of chapter 31 (before the residue rule).
Output identical in every base.

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

The `-m` columns compare with the residue rule for the same convention.
From base 20 on the ratio lies between 0.52 and 0.60 and shows no trend
with the base (computed). Unlike the residue rule alone, it depends little
on the factors of `b - 1`, since the last digits do not depend on them.

Heuristic 2.2. The share of the tree the tests remove stays near 0.45 in
larger bases, so the census runs of bases 42 to 46 on the CPU should take
0.85 to 0.95 of their time with the residue rule alone. The share of nodes
with one and two free slots, the inputs of both tests, changes little with
the base (Table 31.1.1, section 31.2.2), and both tests depend on the level
`k / b` and the share of digits left more than on `b` itself.

## 3. Where the residue rule's instructions go (question 125)

Chapter 31 measured 6% to 13% more instructions with the residue rule
and asked whether the larger node, the extra branch or the test before the
interval costs the time. Two comparisons on the same tree answer it:

- `old`: the engine before the residue rule (commit `ba24b14~1`);
- `fields`: the residue engine (commit 9756e6b) with `res_add` and
  `res_ok` replaced by no-ops, run with `--no-residue`. It carries the
  residues in every node and cursor, but never changes or tests them;
- `nores`: the residue engine with `--no-residue`. It computes both
  residues of every child and runs both tests, which never fail;
- `res`: the residue engine with its rule.

The first three visit the same 4,955,060 nodes and 16,313,626 evaluations
at base 26.

Table 3.1. Base 26, both conventions, one P-core, median of 3 (two
alternating series; `old` and `nores` are in both, and agree within 0.7%).

| build | cycles | instructions | IPC | branch misses | cycles per evaluation |
|---|---:|---:|---:|---:|---:|
| `old` | 1.376 G | 3.323 G | 2.42 | 16.1 M | 84.3 |
| `fields` | 1.393 G | 3.383 G | 2.43 | 16.2 M | 85.4 |
| `nores` | 1.345 G | 4.501 G | 3.35 | 15.0 M | 82.5 |
| `res` | 1.210 G | 3.675 G | 3.04 | 15.1 M | 85.3 |

So the residues cost 35% more instructions on the same tree and no cycles:
`nores` is 2% faster than `old`. The fields alone cost 1.8% of the
instructions and 1.1% of the cycles. The rule then removes 13% of the
evaluations and 10% of the cycles of `nores`.

Table 3.2. Base 24, instructions by kind from callgrind (dynamic counts,
`analysis/data/r6s2_residue_kinds.txt`), `fields` to `nores`, 4,773,112
evaluations.

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

The residues are two bytes per node. Each child adds `r(k)` to both, with a
conditional subtraction of `q`, and the compiler packs and unpacks the two
bytes, and spills them around the vector additions. Half of the added
instructions are moves. None of them is on the critical path. The loop
waits on chains of dependent vector additions (each about 20 cycles,
`fast/README.md`) and on about one mispredict per child, and the residue
work fits in the slots those leave idle. The IPC rises from 2.42 to 3.35
at the same cycle count.

Answer to question 125 (computed; heuristic for the cause): neither the
larger node, nor the branch, nor the test before the interval costs
measurable time. The instructions are moves and arithmetic that run in
the shadow of the vector chain. The cycles track the interval evaluations,
about 82 to 85 per evaluation in all four builds. Chapter 31 saw the
cycles fall less than the nodes because the nodes it removes are cheap: a
node with one free slot costs two evaluations. A leaner residue (one `u16`,
or residues only for the nodes near the bottom) would save instructions,
not cycles. The same holds for the new tests: they lower the instructions
by 12% to 25% (`L3P2`) and the cycles by less.

The method. Line attributions of callgrind differ between builds, because
the inlined code maps to different lines. The table counts instructions by
their kind (from `objdump`) at each address that callgrind counted, which
does not depend on the line map. `perf` is not installed. Valgrind 3.25
does not decode GFNI, so the profiled builds use
`-C target-feature=-gfni`.

## 4. Defaults and the GPU

Both tests are on by default (`--low-digits 3 --low-pairs 2`), since they
win in every base and mode of Tables 2.3 and 2.4. `--low-digits 0
--low-pairs 0` restores the tree of chapter 31, and `--no-residue` turns
both tests off with the rule.

The tests do not act while the program builds the work units. So the
units, the unit counts in the journals and the shards are the same with
and without them, and a journal of chapter 31 resumes with the new build.

The GPU search is unchanged. Each node of the shader would need the
64-bit mask and the clear in its forced-digit loop, and the tables of
section 1.3 per level; the subgroup work is bound by its dependent chains
(`fast/README.md`), where the gain of the residue rule was 1.18x. I did not
port it. `--gpu` and `--hybrid` turn the tests off, so their CPU threads
visit the nodes of the GPU, and the GPU tests still check equal node and
evaluation counts.

## Files

- Engine: `fast/src/search.rs` (`low_ok`, `pair_ok`, `node_avail`,
  `magic_b2`, the tables `ltab`, `ltab2`, `lcand`, `pcand`, the `avail`
  field of `Node` and `Head`, the count of prefix zeros in `Cursor`),
  `fast/src/digits.rs` (`low4`), `fast/src/main.rs` (options and tests),
  `fast/src/search/gpu.rs` (the CPU side of `--hybrid` runs without the
  tests).
- Scripts: `analysis/r6s2_bench.py`, `analysis/r6s2_tables.py`,
  `analysis/r6s2_pair.py`, `analysis/r6s2_pair_probe.py`,
  `analysis/r6s2_bykind.py`.
- Data: `analysis/data/r6s2_cycles.json` (Tables 2.3, 2.4),
  `analysis/data/r6s2_cycles_steps.json` (Table 1.2),
  `analysis/data/r6s2_pair_b20_30.txt` (Table 2.1),
  `analysis/data/r6s2_nodes_{both,m0,m1}.txt` (Table 2.5, stderr of
  `fast search 2 33`), `analysis/data/r6s2_residue_cycles.json` and
  `analysis/data/r6s2_residue_kinds.txt` (Tables 3.1, 3.2).
- Test builds that are not committed: the variants of Tables 1.1 and 2.2,
  and `fields` of section 3 (two functions made no-ops).

## New questions

1. The first unknown digit of a pair. It fails 24% to 47% of the nodes
with two free slots (Table 2.1), more than the last digit, but needs the
carry of `t + w(y1) + w(y2)` into lane `pp - 1`. Most pairs have
`w(y2)` far below `b^(pp-1)`, so the digit is that of `t` or one more. Can
a test on the top lanes of `t` and a table of `w(y) / b^(pp-1)` per level
decide it for most pairs, and the rest by a full sum?
2. Copies. The tests ignore the multiplicity of a digit in the last lanes.
A second mask of the digits with two copies left would make them exact for
two and three digits. How many more nodes would that remove?
3. Three free slots. The sums of three weights reach most classes and most
last digits, so the mask would be dense. Does the last digit of a triple
still remove a useful share of those nodes (14% of the tree, Table 31.1.1)?
4. The GPU. With the tests, the CPU visits 0.53 to 0.57 of the nodes of the
GPU. Does a port to `shaders/search.comp` pay on the subgroup engine, where
the residue rule gave 1.18x?
5. Lean. Lemma 1.1 and Proposition 1.2 are statements about multisets and
digits, close to those of chapter 1. They should be easy to formalize
next to Proposition 1.5.
