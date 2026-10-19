# 26. Near-solutions as evidence

This chapter answers questions 73, 72, 74, 85 and 86 of
`questions-round5.md`. Questions 73 and 72 test the tool that the library
uses for every "chance" verdict: the count of near-solutions
`n = F(n) + D` at offsets `D` in the class of 0. Question 74 looks at the
largest positive deviation, in the Pisot bases. Questions 85 and 86 test
the model in two new ways. Each statement is marked proven (a proof is
here), computed (an exact computation, with its range) or heuristic (the
model, or a judgment from data).

## Summary

| question | answer | status |
|---|---|---|
| 73, offsets are not independent | A rearrangement of the digits keeps `F` and moves `D` by `n' - n`, a multiple of `b-1` (Lemma 26.1). So the near-solutions of one multiset form a cluster across offsets. In bases 12 to 26, 43% to 88% of the near-solutions share their multiset with another offset; the variance of a sum over offsets is 1.5 to 3.5 times the Poisson value, and 60 offsets are worth 26 to 29 independent ones. The swap lemma predicts the design effect within a few percent (Heuristic 26.6). Offsets with no two a transposition apart cut the sharing to 15% (Table 26.2.2). The P values of `D = 0` against the offsets barely move, because the noise of the single count `N_0` dominates. The per-base precision of the offset means changes a lot: the chi-square of `lambda / model` drops from 97 to 41 on 21 bases, and base 19 goes from 4.6 to 2.9 standard errors. | proven (lemma); computed |
| 72, a pooled test | 284 solutions against 297 to 304 expected in eight worlds. The worlds disagree more than chance allows: heterogeneity `Q = 23.3` on 7 degrees of freedom with the library's Pisot calibration (P = 0.002), and 17.2 (P = 0.016) with the Pisot offsets in the class of 0 modulo `2x`. Two worlds drive it: the odd-base factorions (ratio 0.33) and the Pisot bases (1.34 to 1.56). Without these two, the other six fit one common ratio, 0.91 (P = 0.60 for heterogeneity). | computed, heuristic |
| 74, the Pisot excess | No pairing move other than the twins links solutions; twins are as common among near-solutions. Two calibration faults explain part of the excess: for even `x` the offsets `j x` with odd `j` carry 1.5 to 2.4 times fewer near-solutions under `0^0 = 0` than those with even `j` (corrected in chapter 34 from "1.4"; see section 26.6.2), and the defect spectrum is higher near `D = 0` than at the far offsets (14.8 against 9.7 per offset). Against a local calibration in the class of 0 modulo `2x`, the even bases have 25 solutions against 14.8 (P = 0.05 with the calibration error). | computed; the class effect is unexplained |
| 85, image and in-degrees | The image shares are 0.21 (base 10) to 0.14 (base 16), against 0.50 for the formula of question 85 and 0.31 to 0.38 for the weighted random mapping. Exact coincidences of the sums `S(c)` explain part of the gap (Proposition 26.10), and the forced top digits of `S` explain about two thirds of the rest (Table 26.7.3). The in-degrees of distinct sums are overdispersed: variance / mean 3.6 to 6.3 against 2.3 to 3.8. | proven; computed |
| 86, a mixing statistic | The low digits of `F(c)` agree with `c` at the rate of random digits within 1.6% in the integers, base -20, the factorions and the factorial system, and within 3.7% in the Pisot base 6. `F_q[T]` is the one world with a clear excess, 2.2% to 3.4% per value over 125 values. The statistic does not follow the model error: it flags `F_q[T]` with the same sign under both conventions, where the model error changes sign, and it misses the factorial failure, which sits in the top digits. A top-digit factor is lowest in the factorial system (0.53 to 0.55), but also below 1 in the Pisot base, where the count is 3 times the model. | computed; negative answer |

## 26.1 The swap lemma (question 73)

### 26.1.1 Setting

Fix a world with digits, a weight `w` and a convention for `w(0)`. For a
digit multiset `c`, let `S(c)` be the sum of its weights. For an offset `D`,
a near-solution is a number `n` with `n = F(n) + D`, where `F(n) = S(c(n))`
and `c(n)` is the digit multiset of `n`. Let `N_D` be their number, with the
length restriction of the section that uses them. An offset set `O` holds
`J` offsets in the class of 0: `D = 2j(b-1)` in sections 11.1 and 11.2
(`j = 1..60`), `D = j(b-1)` and `D = j b (b-1)` for factorions (`j = 1..30`),
and so on.

The library compares `N_0` with the mean `lambda = (1/J) sum over D in O of
N_D`. It treats the `J` counts as independent draws.

### 26.1.2 The lemma

Lemma 26.1 (proven, the swap lemma). Let `n` and `n'` have the same digit
multiset in base `b`, both without a leading zero. Then `F(n') = F(n)` and

    n' - F(n') = (n - F(n)) + (n' - n),   n' - n == 0 (mod b - 1).

If `n'` is `n` with the digit `x` at position `i` and the digit `y` at
position `j > i` exchanged, then

    n' - n = (x - y)(b^j - b^i) = (x - y) b^i (b - 1) R_(j-i),

with the repunit `R_s = 1 + b + ... + b^(s-1)`. For the last two digits
this is `(x - y)(b - 1)`.

Proof. `F` depends only on the multiset, so `F(n') = F(n)`. Every power of
`b` is 1 modulo `b - 1`, so a number is congruent to its digit sum, and
the two digit sums are equal. For the transposition, only positions `i`
and `j` change: `n' - n = y b^i + x b^j - x b^i - y b^j`.

Corollary 26.2 (proven, the class). The transposition of Lemma 26.1 keeps
`D` in its class modulo `2(b-1)` exactly when `(x - y) b^i R_(j-i)` is
even. In an odd base this means `(x - y)(j - i)` even, since `b^i` is odd
and `R_s == s (mod 2)`. In an even base it means `i >= 1` or `x == y
(mod 2)`, since `R_s` is odd.

Lemma 26.3 (proven, the fibre). Let `O` be a set of offsets. The
near-solutions with multiset `c` at offsets in `O` are exactly the
rearrangements `n'` of `c` without a leading zero and with
`n' - S(c)` in `O`. Their number `K_c` is fixed by `c` and `O`. Each pair
`(c, D)` gives at most one near-solution, `n = S(c) + D`.

Proof. `n` has multiset `c` and `n = S(c) + D` with `D` in `O`. Conversely,
such a rearrangement is a near-solution at `D = n' - S(c)` by Lemma 26.1.

So a near-solution comes with all its rearrangements whose offsets fall
in `O`. In a window of offsets below `b^t`, these are
rearrangements of the bottom few digits. One coincidence, a multiset whose
sum lies close to one of its own arrangements, is counted at several
offsets.

Lemma 26.4 (proven, other systems). The same holds in every positional
world where `F` depends on the multiset:

- Base `-b`: `n' - n == 0 (mod b + 1)`. Exchanging the digits `x` at
  position 1 and `y` at position 0 moves `D` by `(x - y)(b + 1)`.
- Factorions, weight `x!`: as Lemma 26.1, with the same class `b - 1`.
- The factorial system: positions `i < j` move `n` by `(x - y)(j! - i!)`,
  if both digits are allowed at both positions. Positions 1 and 2 give
  steps of 1, so the offsets `D = 1..100` of section 21.5.3 are linked.
- The Pisot base `eps_x`: write `eps^i = F_(i-1) + F_i eps` with
  `F_i = x F_(i-1) + F_(i-2)`, `F_0 = 0`, `F_1 = 1` and
  `F_(-i) = (-1)^(i+1) F_i`. A rearrangement with digit changes `e_i` keeps
  `n` an integer exactly when `sum e_i F_i = 0`, if the new string is
  admissible. Positions `k` and `-k` with `k` odd have equal `F`, so their
  exchange moves `n` by `(d_(-k) - d_k)(F_(k-1) - F_(-k-1))`; for `k = 1`
  this is `(d_(-1) - d_1) x`. The class `j x` of section 21.4 is therefore
  linked.
- `F_q[T]`: Lemmas 24.9 and 24.10 are stronger forms. There the offsets
  `(B-1) g` with small `g` map the solutions one to one onto
  near-solutions.

Proof. In each case the place values `beta_i` are fixed integers (or, for
the Pisot base, elements of `Z[eps]`), and `n' - n = sum e_i beta_i`. For
`-b`, `(-b)^i == 1 (mod b+1)`. For the Pisot base, `n' - n` is
`sum e_i F_(i-1) + eps sum e_i F_i`, which is an integer exactly when
`sum e_i F_i = 0`. The values of `F_i` follow from `eps^(-1) = eps - x`.

### 26.1.3 What the dependence changes

Proposition 26.5 (proven, under the usual independence of distinct
multisets). Let `X_(c,D)` be the indicator that `c` is a near-solution at
`D`, and assume that distinct multisets are independent. Then:

1. For each offset, `N_D = sum over c of X_(c,D)` is a sum of independent
   indicators, so its law is Poisson, up to the clumps at one offset
   (twins, triples), which multiply its variance by
   `psi = E[clump^2] / E[clump]`.
2. The mean `lambda` is unbiased whatever the clusters.
3. The total `T = sum over D in O of N_D` has variance close to
   `sum over c of E[K_c^2]`, since each multiset is a near-solution with
   small probability. So `Var T = phi E T` with the design effect
   `phi = E[K^2] / E[K]`, measured on near-solutions. The mean of `J`
   offsets is worth `J_eff = J psi / phi` independent offsets.
4. `N_0` keeps its own law. A solution and its rearrangements in `O` are
   in one cluster, so `N_0` and `T` are positively correlated.
5. The rank of `N_0` among the offset counts is uniform if the joint law
   of `(N_0, N_D for D in O)` is exchangeable, whatever the dependence.

Proof. Parts 1 and 2 hold because each pair `(c, D)` gives at most one
near-solution (Lemma 26.3) and the means are equal by assumption. For part
3, `T = sum over c of K_c`, and the `K_c` are independent. Part 4 is
Lemma 26.3 at `D = 0`. Part 5 is the usual permutation argument.

So the statement of question 73 needs one correction. The spread of a
single offset count is Poisson; the spread of sums and means over offsets
is not. Every test that uses only `lambda` and the Poisson noise of `N_0`
changes little, since `Var lambda = phi lambda / J` is small next to
`lambda` when `J` is 20 or more. Tests that use the precision of `lambda`
itself change a lot: per-base comparisons of `lambda` with the model,
comparisons between two offset families, and z-scores of one base.

### 26.1.4 The design effect predicted

Heuristic 26.6. For a near-solution picked at random, `phi = 1 + E[number
of partners]`, where a partner is a rearrangement whose offset lies in `O`
(Lemma 26.3). If the bottom digits are uniform (Table 24.6.1) and `D` is
uniform in `O`, the expected number of partners is a finite sum over the
rearrangements of the bottom 4 or 5 digits. `analysis/r5e_swap_model.py`
computes it by sampling (20,000 strings per base). For `O = {2j(b-1):
j = 1..60}` it gives 2.60 in base 12, 2.17 in base 16, 1.93 in base 20,
1.71 in base 26 and 1.62 in base 32. It falls slowly with `b`. For a
window of fixed size it tends to 1, because the chance that a swap of the
last two digits lands in the window falls like `1/b` once `b` exceeds the
window.

Table 26.2.1 compares this with the measurement. Under `0^0 = 1` the mean
measured design effect is 1.045 times the prediction over bases 12 to 26.
Under `0^0 = 0` it is 1.21 times, because the twins of Proposition 26.7
join two clusters.

## 26.2 Measurements (computed)

### 26.2.1 Integer bases 12 to 26

`analysis/r5e_int_offsets.py` reran `fast search b --offset D --min-digits
b-6` for `D = 2j(b-1)`, `j = 0..60`, bases 12 to 26, with every string
kept (`analysis/data/r5e_int_std.txt`). `analysis/r5e_int_report.py`
groups the events by multiset and by twins (`analysis/r5e_cluster.py`).

Table 26.2.1 (computed). Near-solutions under `0^0 = 1`, at least `b-6`
digits, 60 offsets. "Shared" is the share of near-solutions whose multiset
is also a near-solution at another offset. The free family is that of
section 26.2.2.

| b | events | shared | phi | free: events | shared | phi | Heuristic 26.6: phi | free phi |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 12 | 53 | 0.74 | 2.51 | 80 | 0.26 | 1.30 | 2.60 | 1.36 |
| 13 | 130 | 0.88 | 2.89 | 127 | 0.31 | 1.36 | 2.46 | 1.29 |
| 14 | 55 | 0.71 | 2.38 | 60 | 0.22 | 1.27 | 2.34 | 1.25 |
| 15 | 80 | 0.64 | 1.95 | 73 | 0.16 | 1.16 | 2.25 | 1.20 |
| 16 | 105 | 0.64 | 2.16 | 94 | 0.26 | 1.32 | 2.17 | 1.19 |
| 17 | 101 | 0.69 | 2.33 | 103 | 0.10 | 1.10 | 2.07 | 1.16 |
| 18 | 82 | 0.66 | 2.00 | 60 | 0.00 | 1.00 | 2.02 | 1.16 |
| 19 | 61 | 0.57 | 1.95 | 73 | 0.16 | 1.16 | 1.97 | 1.14 |
| 20 | 92 | 0.71 | 2.37 | 66 | 0.12 | 1.12 | 1.93 | 1.13 |
| 21 | 66 | 0.65 | 2.06 | 52 | 0.12 | 1.12 | 1.87 | 1.10 |
| 22 | 56 | 0.43 | 1.54 | 84 | 0.10 | 1.10 | 1.84 | 1.11 |
| 23 | 99 | 0.69 | 2.03 | 80 | 0.05 | 1.05 | 1.80 | 1.08 |
| 24 | 54 | 0.56 | 1.67 | 85 | 0.07 | 1.07 | 1.77 | 1.09 |
| 25 | 75 | 0.51 | 1.59 | 78 | 0.08 | 1.08 | 1.74 | 1.08 |
| 26 | 59 | 0.58 | 1.92 | 70 | 0.11 | 1.11 | 1.71 | 1.08 |

Under `0^0 = 0` the shares are similar (0.43 to 0.85) and the design
effects higher (1.71 to 3.50), with `psi` = 1.03 to 1.16 from the twins.
Pooled over bases 12 to 26: shared 0.67 and 0.66, `phi` = 2.48 and 2.14,
`J_eff` = 26.8 and 28.0 of 60 (`0^0 = 0` and 1). This confirms the lead of
the question (41% to 65% shared in bases 14 to 18).

The partner pairs sit at the moves of Lemma 26.1: 43% at a swap of the last
two digits (`|j - j'| <= b - 1`), 20% at positions 0 and 2, 18% at
positions 1 and 2, and 19% at longer rearrangements. Of the 52 solutions in
these bases, 29 have a rearrangement that is a near-solution in the window.

The counts per offset stay Poisson, as Proposition 26.5 says: the group
totals per offset have variance / mean 0.68 to 0.93. A sum over offsets
does not: its clustered variance is 2.1 times the naive one (median over
42 cases; range 1.3 to 3.5).

### 26.2.2 Offsets with no transposition between them

Definition 26.7. For base `b`, let `Tr(b)` be the set of values
`t b^i R_s` with `1 <= t <= b-1`, `i >= 0`, `s >= 1`: the moves
`|n' - n| / (b-1)` of single transpositions (Lemma 26.1). The transposition
free family takes `k_0 = 0` and adds the next even `k` whose distance to
every chosen `k` is not in `Tr(b)`, until 61 values are chosen. The offsets
are `D = k (b-1)`, in the class of 0 modulo `2(b-1)`.
(`r5e_lib.swap_free_ks`; for base 12 the values are 0, 14, 28, 42, 56,
70, 168, ..., 2070.)

Table 26.2.2 (computed, `analysis/data/r5e_int_free.txt`, bases 12 to 26). The
two families against `D = 0`.

| family | convention | `N_0` | mean per offset | shared | phi | `J_eff` of 60 | P(at least `N_0`), clustered |
|---|---|---:|---:|---:|---:|---:|---:|
| `2j(b-1)` | `0^0 = 0` | 27 | 24.30 | 0.67 | 2.48 | 26.8 | 0.33 |
| transposition free | `0^0 = 0` | 27 | 25.37 | 0.16 | 1.33 | 50.5 | 0.40 |
| `2j(b-1)` | `0^0 = 1` | 25 | 19.47 | 0.66 | 2.14 | 28.0 | 0.13 |
| transposition free | `0^0 = 1` | 25 | 19.75 | 0.15 | 1.17 | 51.5 | 0.15 |

The two families agree on the mean within 4%. The free family keeps 15% of
shared near-solutions; all of them come from rearrangements of three or
more digits, which Definition 26.7 does not exclude. Heuristic 26.6 predicts
its design effect as well (Table 26.2.1, last column).

### 26.2.3 The other worlds

Table 26.2.3 (computed). Design effects of every offset family of the
library that has strings or that I reran with them.

| world, family | section | data | shared | phi | psi | `J_eff` |
|---|---|---|---:|---:|---:|---:|
| integers, `2j(b-1)`, bases 12 to 26 | 11.1 | `r5e_int_std.txt` | 0.66 to 0.67 | 2.14 to 2.48 | 1.00 to 1.11 | 27 to 28 of 60 |
| factorions, `j(b-1)`, odd bases 15 to 35 | 17.4 | `r5e_fact_b1.txt` (new) | 0.71 to 0.72 | 2.01 to 2.66 | 1.07 to 1.25 | 14 to 16 of 30 |
| factorions, `j b (b-1)` | 19.5 | `r2c_fact_offsets_bb1.txt` | 0.71 to 0.72 | 1.87 to 2.02 | 1.07 to 1.15 | 17 of 30 |
| factorions, `j b^2 (b-1)`, `j b^3 (b-1)` | 23.1.3 | `r2c_fact_offsets_b2b1.txt`, `_b3b1.txt` | 0.70 to 0.73 | 1.97 to 2.28 | 1.09 to 1.27 | 16 to 17 of 30 |
| factorions, `j b^2 lcm(1..b+1)` | 23.1.3 | `r2c_fact_offsets_lcm.txt` | 0.00 | 1.08 to 1.17 | 1.08 to 1.17 | 30 of 30 |
| negative bases -10 to -24, `j step`, `j step b` | 23.2 | `r5e_nega_offsets.txt` (new) | 0.53 to 0.70 | 1.68 to 2.41 | 1.00 to 1.19 | 10 to 12 of 20 |
| near-2-cycles, bases 4 to 16 | 23.3 | `r5e_cycles2_hits.txt` (new) | 0.76 to 0.90 | 2.45 to 2.90 | 1.00 | 10 to 12 of 30 |
| Pisot `eps_x`, `j x`, `x = 2..10` | 21.4 | `r5e_pisot_list_*.txt` (new) | 0.52 to 0.89 | 1.60 to 6.35 | 1.00 to 1.76 | 8 to 19 of 30 |
| 4-digit strings, `D = j` | 19.2.2 | `r3c_offsets_k4_j.txt` | 0.88 | 5.27 | 1.00 | 38 of 200 |
| 5-digit strings, `D = j` | 19.2.3 | `r3c_offsets_k5_j.txt` | 0.83 | 5.42 | 1.00 | 37 of 200 |
| 4- and 5-digit strings, `D = j L` | 19.2 | `r3c_offsets_k*_jL.txt` | 0.00 | 1.00 | 1.00 | 200 of 200 |
| 5-digit strings, window, bases 13 to 99 | 22.4 | `r5e_short_spectrum.txt` (new) | 0.93 | 2.33 | 1.00 | |

Three remarks.

- Far offsets have no clusters. The factorion family `j b^2 lcm(1..b+1)`
  and the kdigit family `D = j * 75600` share no multiset. Their steps are
  divisible by many small numbers, and no rearrangement of a few low digits
  reaches them.
- Short strings cluster in a second way. Strings with a common prefix of
  `k - 2` digits and different last digits fill runs of consecutive
  offsets, as section 19.2.3 noted (177 hits in 44 clusters). With prefix
  links added, the design effect of the offsets `D = j` grows to 49 to 85.
- For the 5-digit window of section 22.4, 93% of the 257 hits share their
  multiset with another hit.

## 26.3 A correct calibration

### 26.3.1 The clustered P value

Definition 26.8. Let `T` be the offset total over `J` offsets, `phi` the
design effect and `p_k` the law of the clump size at one offset (twins give
`k = 2`, factorion triples `k = 3`). The clustered P value of `N_0` is

    P(N_0 <= n) = E over lambda of  CP(n; lambda, p),
    lambda ~ Gamma(shape T / phi + 1/2, rate J / phi),

with `CP` the compound Poisson law with mean `lambda` and clump law `p`
(Panjer recursion). With `phi = 1` and no clumps this is the usual
predictive P value with a Jeffreys prior; with `J` large it is the Poisson
P value. `analysis/r5e_lib.py` implements it (`p_low_c`, `p_high_c`).

The gamma law has variance `phi lambda / J`, the clustered variance of
Proposition 26.5. The clumps matter more than `phi` for small `N_0`: three
factorions against 10.8 per offset give 0.0056 as a Poisson count, 0.0077
as a compound count with the measured triples, and 0.0089 with the
calibration error added.

### 26.3.2 Which tool to use

- To compare one count `N_0` with its offsets, use Definition 26.8 with the
  measured `phi` and clump law. Report the rank P value
  `(1 + #{D : N_D <= N_0}) / (J + 1)` as well. It is exact under
  exchangeability (Proposition 26.5, part 5), but it cannot go below
  `1/(J+1)`.
- To compare offset means between bases or families, use the clustered
  variance `sum over clusters of K_c^2`, not the sample variance of the
  counts. The sample variance estimates the variance of one offset count,
  which is about `psi lambda`, and misses the factor `phi / psi`.
- For new runs, choose offsets with no transposition between them
  (Definition 26.7) or with steps divisible by many small numbers (the
  `lcm` family). Both keep the mean (Table 26.2.2) and double `J_eff`.
- Keep the strings. Every rerun in this file needed them.

## 26.4 Every chance verdict revisited

Table 26.4.1 lists every P value and every z-score of the library that rests
on near-solutions at offsets, with the value recomputed by Definition 26.8
or by the clustered variance. "Fixed" means the old method (Poisson with
`lambda` known, or the sample variance of the counts). Scripts:
`r5e_int_report.py`, `r5e_scatter.py`, `r5e_fact_report.py`,
`r5e_nega_report.py`, `r5e_kdigit_report.py`, `r5e_short_spectrum.py`,
`r5e_cycles2_report.py`, `r5e_pooled.py`.

Table 26.4.1 (computed).

| statement | section | old | new | verdict |
|---|---|---:|---:|---|
| integers, `0^0 = 0`, even bases 12-32, 13 against 10.9 | 11.1 | P(>=) 0.30 | 0.31 | unchanged |
| integers, `0^0 = 0`, odd, 20 against 22.2 | 11.1 | P(<=) 0.37 | 0.38 | unchanged |
| integers, `0^0 = 1`, even, 15 against 12.8 | 11.1 | P(>=) 0.31 | 0.31 | unchanged |
| integers, `0^0 = 1`, odd, 15 against 14.0 | 11.1 | P(>=) 0.43 | 0.43 | unchanged |
| dispersion of `N_0` around `lambda(b)`, 42 cases | 11.1 | 48.8, P 0.22 | 44.6, P 0.36 | unchanged: Poisson |
| empty base 19, union mean 1.9 | 11.1 | 0.15 | 0.15 | unchanged |
| empty bases 12-32, expected (even/odd, `0^0 = 0`/1) | 11.2 | 4.1, 1.3, 3.6, 2.6 | 4.2, 1.3, 3.6, 2.7 | unchanged |
| no `b`-digit solution under `0^0 = 1`, 0 against 1.30 | 11.2 | 0.27 | 0.27 | unchanged |
| chi-square of `lambda / model`, 21 bases, `t = 0` (`0^0 = 0`, 1); section 11.2a had 108 and 85 with an earlier model run | 11.2a, 23.5 | 97.0, 95.7 (P `10^-11`) | 41.4, 43.3 (P 0.005, 0.003) | changes: the excess scatter is half as large |
| the same with the top 3 digits forced, `t = 3` | 23.5 | 68.2, 75.7 (P `10^-6`, `10^-8`) | 30.2, 34.7 (P 0.09, 0.03) | changes: no clear excess under `0^0 = 0` |
| the same, `t = 4` | 23.5 | 59.6, 72.4 | 28.0, 34.5 (P 0.14, 0.03) | changes |
| base 19, `0^0 = 0`, `lambda` 1.35 against 2.02 | 23.5 | z = -4.6 | z = -2.9 | weaker; one of 42 cases |
| `0^0 = 1`, mean `lambda / model` 1.12 | 23.5 | z = 4.4 | z = 3.0 | weaker, survives |
| factorions, odd, `j(b-1)`: 3 and 4 against 11.8 and 11.1 | 17.4 | P 0.0026, 0.014 | 0.0060, 0.019; rank 0.032 | unchanged: open, likely chance |
| factorions, odd, `j b (b-1)`: 3 and 4 against 10.8 and 10.6 | 19.5 | 0.006, 0.020 | 0.0089, 0.025; rank 0.032 | unchanged |
| the same after 16 groups | 19.5 | about 0.1 | 0.13 | unchanged |
| families `j b^2 (b-1)`, `j b^3 (b-1)`, `lcm` | 23.1.3 | about 0.005 | 0.004 to 0.007 (`0^0 = 0`), 0.020 (`0^0 = 1`) | unchanged |
| in-sample after selection, with fresh bases (Fisher) | 23.1.3 | about 0.05 | about 0.09 | weaker |
| 4-digit strings, calibrated by `D = j` and `D = j L` | 19.2.2 | 0.37, 0.17, 0.42, 0.13 (`0^0 = 1`); 0.10, 0.06, 0.15, 0.03 (`0^0 = 0`) | 0.39, 0.19, 0.45, 0.17; 0.14, 0.10, 0.24, 0.08 | unchanged; the 0.03 goes to 0.08 |
| 5-digit strings, calibrated by `D = j` (primes, p-adic) | 19.2.3 | 0.08, 0.15 | 0.12, 0.19 | unchanged |
| 5-digit strings, calibrated by `D = j L` | 19.2.3 | 0.005, 0.011 | 0.012, 0.023 | weaker; superseded by 22.4 |
| 5-digit, bases 13-99, by `D = j L` | 19.2.3 | 0.0008 | 0.0012 | unchanged; superseded by 22.4 |
| 5-digit, bases 13-99, window calibration, 3 against 0.33 | 22.4 | 0.0047 | 0.0055 | unchanged |
| the same after the choice of 10 cells | 22.4 | 0.015 | about 0.018 | unchanged |
| 4-digit, bases 13-99, window, 1 against 1.40 | 22.4 | 0.75 | 0.74 | unchanged |
| negative bases -10 to -27, keeping the last digit, 42 against 52.0 | 23.2 | 0.09 | 0.11 | unchanged |
| multiples of 3 against their offsets, 10 against 17.3 | 23.2 | 0.044 | 0.056 | unchanged |
| offsets `j step b` against `j step`, other bases, `0^0 = 0` | 23.2 | about 4 SD | 2.9 SD (2.3 SD on bases -10 to -24) | weaker, survives as a lean |
| 2-cycles, even bases, `0^0 = 0`, 2 against 5.25 | 23.3 | 0.10 | 0.11 | unchanged |
| rational bases, `p, q` odd, 14 against 19.9 near | 21.2 | 0.11 (model) | 0.12 | unchanged |
| Pisot, even `x`, near-solutions "match the model" | 21.4 | none | see section 26.6 | changes: the class `j x` is wrong for even `x` |
| `F_q[T]` near-solutions as independent draws | 21.1.6 | none | Lemma 24.9 | already withdrawn in chapter 24 |
| integer near-solutions as "a genuine second draw" | 24.6.3 | none | 66% share a multiset | changes: the sentence is wrong |
| factorial system, clusters of 10 to 50 offsets | 21.5.3 | none | Lemma 26.4 | explains the clusters |

What changes:

- The precision of the offset means was overstated by a factor 1.4 in
  standard deviation (`sqrt(phi / psi)`, median). The "excess per-base
  scatter" of sections 11.2a and 23.5 is half an artefact. With the
  clustered variance, the refined model leaves a chi-square of 41 to 43 on
  21 bases. With the top 3 or 4 digits forced (section 23.5) it is 28 to
  30 under `0^0 = 0`, which is noise (P 0.09 to 0.14), and 35 under
  `0^0 = 1` (P 0.03).
- Base 19 is no longer a separate anomaly. Its near-solution rate under
  `0^0 = 0` is 2.9 standard errors below the top-digit model, one case of
  42. Question R2.b of chapter 23 loses most of its basis.
- The near-solution side result of section 23.2 (the family that keeps the
  last digit gives fewer near-solutions) drops from about 4 to about 2.9
  standard deviations. A part of the difference is real; the claim "4
  standard deviations" is not.
- The sentence of section 24.6.3 that an integer near-solution "is a
  different multiset, a genuine second draw" is false for two thirds of
  the near-solutions. The conclusion drawn from it, that the integer
  near-solution rate is within a few percent of the model, stands with the
  wider error bars of this section.
- The 12% excess of the refined model under `0^0 = 1` survives at 3.0
  standard deviations.

Update (chapter 34). Perturbed worlds show that a world-level ratio
scatters 1.3 to 1.5 times more than the clustered standard error allows,
even with the top digits forced (section 34.1.5). With that factor the 12%
excess falls to about 2.0 to 2.3 standard deviations. It does not sit in
the zeros (Heuristic 34.4). The P values of the tests named before the data
were seen look uniform (Heuristic 34.14).

What does not change: every verdict about `D = 0` itself. The factorion
shortfall (P 0.006 to 0.025 per family and convention, 0.13 after the
choice among 16 groups), the 5-digit excess (0.0055), the negative bases,
the 2-cycles and the empty bases keep their verdicts. The calibration
error is small next to the Poisson noise of a count of 3 to 60. The clumps
at one offset (twins, triples) move the small P values more than the
clusters across offsets do.

## 26.5 A pooled test (question 72)

### 26.5.1 Data

`analysis/r5e_pooled.py` collects `N_0` and the offset total per base and
convention in eight worlds, from the files of chapters 11, 17, 19, 21 and
23. The design effects come from section 26.2 where strings exist. For the
rational and Eisenstein bases, which have no strings, `phi = 2` is
assumed; with `J = 30` the results do not depend on it.

The questioner's lead removed the 7 Pisot twin pairs from the solutions
but not from the near-solutions, which also contain twins (Table 26.6.2).
Here both sides keep their twins, and `psi` carries the clumping.

Table 26.5.1 (computed; model heuristic). `O` solutions, `E` offset means
summed over the bases. z corrected uses
`Var(O - E) = psi E + phi E / J`.

| world | bases | `O` | `E` | z naive | z corrected | `phi` | `psi` |
|---|---|---:|---:|---:|---:|---:|---:|
| integers | 12 to 32, both conventions | 63 | 59.9 | +0.40 | +0.38 | 2.31 | 1.06 |
| factorions, odd | 15 to 35, `j b (b-1)` | 7 | 21.4 | -3.12 | -2.88 | 1.95 | 1.11 |
| factorions, even | 14 to 36, `j (b-1)` | 21 | 21.4 | -0.08 | -0.07 | 2.34 | 1.16 |
| negative | -10 to -27, `j step b` | 42 | 52.0 | -1.38 | -1.29 | 1.84 | 1.06 |
| rational | `p <= 11`, `q > 1` | 67 | 75.9 | -1.02 | -0.99 | 2.0 | 1.0 |
| Pisot, library offsets `j x` | `x = 2..12` | 62 | 39.7 | +3.54 | +3.11 | 2.6 | 1.2 |
| Pisot, even `j` for even `x` | `x = 2..12` | 62 | 46.1 | +2.34 | +2.03 | 2.6 | 1.2 |
| Eisenstein | -2+w, -3+w | 6 | 4.5 | +0.71 | +0.68 | 2.0 | 1.0 |
| 2-cycles | 4 to 18 | 16 | 22.4 | -1.36 | -1.33 | 1.4 | 1.0 |

Correction (chapter 34). The row "integers, 12 to 32, both conventions"
adds the two conventions as independent counts. Their residuals in one base
correlate at +0.78 (Table 34.5.1.1), because the zero-free near-solutions
count under both (Lemma 34.2). The `z` of that row is too large by a factor
of about 1.3. The conclusion of section 26.5 does not change.

### 26.5.2 Results

Proposition 26.9 (computed, heuristic in its reading). With the library's
Pisot offsets: 284 solutions against 297.2, common ratio 0.956. The
heterogeneity statistic is `Q = 23.3` on 7 degrees of freedom (P = 0.001
by chi-square, 0.002 by a parametric bootstrap of 20,000 draws). A random
effect per world on `log theta` has standard deviation `tau = 0.29`; the
likelihood ratio test of `tau = 0` gives P = 0.007.

With the Pisot offsets in the class of 0 modulo `2x` (section 26.6.2): 284
against 303.6, common ratio 0.935, `Q = 17.2` (P = 0.016 by chi-square,
0.018 by bootstrap), `tau = 0.22`, P = 0.06 for `tau = 0`.

Leave one world out (class calibration): without the odd factorions
`Q = 9.1` on 6 degrees of freedom (P = 0.17); without the Pisot bases
`Q = 10.5` (P = 0.10); without any other world `Q` stays between 15.7
and 17.2 (P 0.009 to 0.015). The shrunken ratios per world are 0.67
(odd factorions), 0.81 (2-cycles), 0.84 (negative), 0.89 (rational),
0.94 (even factorions), 0.98 (Eisenstein), 1.01 (integers) and 1.18
(Pisot).

Answer. The worlds disagree more than Poisson noise and calibration error
allow, and the corrected variance does not remove it: it lowers the sum of
squared z-scores from 27.7 to 23.0 (library Pisot offsets) or from 20.6 to
17.4 (class offsets). Two worlds drive it. The odd-base factorions are the
shortfall of question 41, found after looking at 16 groups; after that
choice its P value is about 0.13 (Table 26.4.1). The Pisot
bases are the subject of question 74. Without these two worlds the other
six fit one common ratio, 0.91, with `Q = 3.6` on 5 degrees of freedom
(P = 0.60). That ratio is 1.3 standard deviations below 1, and it comes
mostly from the negative, rational and 2-cycle worlds, each about one
standard deviation low. So outside the two named worlds there is no sign
that `D = 0` is special.

## 26.6 The Pisot excess (question 74)

### 26.6.1 Pairs of solutions

`analysis/r5e_pisot_pairs.py` lists the 62 solutions with `x >= 2`
(`r3t_pisot_search*.txt`) and every pair at distance at most `2x`.

Table 26.6.1 (computed). All pairs of solutions with `|N - N'| <= 2x`.

| `x` | `0^0` | pair | change | kind |
|---:|---:|---|---|---|
| 2 | 0 | 3 = `1,0.1,1` and 4 = `1,1.1,1` | position 0: 0 to 1 | twin |
| 2 | 0 | 3 and 5 = `2,0.0,1` | positions 1 and -1 | other |
| 2 | 0 | 4 and 5 | positions 1, 0, -1 | other |
| 2 | 1 | 4, 8, 11, 14 in a chain | three or four positions each | other |
| 4 | 0 | 9 / 10, 54 / 55 | position 0 | twin |
| 6 | 0 | 6615 / 6616 | position 0 | twin |
| 7 | 0 | 917942 / 917943 | position 0 | twin |
| 8 | 0 | 96959 / 96960 | position 0 | twin |
| 10 | 0 | 1956350341 / 1956350342 | position 0 | twin |

Apart from the twins of Proposition 21.13, only the tiny solutions of
`x = 2` (`N <= 14`) pair up. One pair at a larger distance has a visible
structure: 3423 and 3475 in base `eps_6` differ at positions 2, 1, -1 and
-2. The digits at 1 and -1 swap (5 and 1), which moves `N` by `-4 x =
-24` (Lemma 26.4), and the digits at 2 and -2 both go from 1 to 3, which
adds `2(x^2 + 2) = 76` to `N` and `2(3^3 - 1) = 52` to `F`. The sum of the
two moves changes `N` and `F` by 52 each. I found no second such pair.

Table 26.6.2 (computed, offsets `j x`, `j = 1..30`, `x = 2..10`,
`r5e_pisot_list_*.txt`). Pairs within one offset.

| group | twin pairs per offset | other pairs within `2x`, per offset | twin pairs at `D = 0` | other pairs at `D = 0` |
|---|---:|---:|---:|---:|
| even `x`, `0^0 = 0` | 2.67 | 2.70 | 6 | 2 |
| even `x`, `0^0 = 1` | 0 | 0.80 | 0 | 3 |
| odd `x`, `0^0 = 0` | 0.73 | 0.00 | 1 | 0 |
| odd `x`, `0^0 = 1` | 0 | 0.13 | 0 | 0 |

Under `0^0 = 0` in even bases, 42% of the near-solutions and 39% of the
solutions lie in twin pairs. The other pairs come from `x = 2` and `x = 4`
among the near-solutions (1.80 and 0.83 per offset) and from `x = 2` among
the solutions. So the near-solutions pair at least as often as the
solutions. No move other than the twins pairs solutions with solutions
and not near-solutions with near-solutions.

### 26.6.2 The calibration

Two faults of the offsets `j x` appear in the data.

The class. For even `x`, offsets with even and odd `j` differ (computed,
`r5e_pisot_list_*.txt`, mean per offset):

| `x` | `0^0 = 0`: even `j` | odd `j` | `0^0 = 1`: even `j` | odd `j` |
|---:|---:|---:|---:|---:|
| 4 | 3.47 | 2.07 | 1.67 | 1.53 |
| 6 | 3.07 | 2.07 | 2.93 | 1.27 |
| 8 | 3.67 | 2.47 | 2.00 | 1.07 |
| 10 | 3.00 | 1.27 | 1.87 | 2.00 |

For odd `x` the two halves agree within noise. So for even `x` the class of
0 is (in part) modulo `2x`, as the class of 0 is modulo `2(b-1)` for odd
integer bases. The offsets `j x` mix both halves and underestimate `D = 0`
by a factor of about 1.2 to 1.4 under `0^0 = 0`. I have not found the
identity behind it. Writing `eps^i` modulo `2x` gives
`(N - sum d_i) / x == A_2 + A_3 (mod 2)`, with `A_r` the digit sum over
positions `== r (mod 4)` (proven for even `x`; the proof expands
`eps^2 = 1 + x eps`, `eps^4 == 1 (mod 2x)` and uses that `N` is rational).
A direct check of every `N <= 3000` for `x = 2, 4, 6, 8` agrees. The
identity ties the parity of `j` to the arrangement, not to the multiset
alone, so it does not by itself give the factor.

The peak at 0. `r3t_pisot defects` counts `N - F(N)` for every
`N <= N_max` (`N_max` = `10^5` to `3 * 10^7`, which holds every solution
for `x <= 8`). The spectrum is higher near 0 than far from it.

Table 26.6.3 (computed, `analysis/data/r5e_pisot_defects.txt`, `x = 2..8`,
lengths `T >= 2`). Solutions against five calibrations, mean per offset.
"Local" is `D = +-2jx`, `j = 1..3`; "far" is `D = +-2jx`, `j = 11..20`.

| group | `N_0` | all `j`, `j x > 0` | even `j` | both signs, even `j` | local | far |
|---|---:|---:|---:|---:|---:|---:|
| even `x`, `0^0 = 0` | 25 | 10.60 | 12.53 | 10.70 | 14.83 | 9.70 |
| even `x`, `0^0 = 1` | 11 | 6.33 | 7.67 | 6.10 | 6.83 | 5.90 |
| odd `x`, `0^0 = 0` | 6 | 3.33 | 3.00 | 2.70 | 2.67 | 2.70 |
| odd `x`, `0^0 = 1` | 7 | 3.27 | 3.40 | 2.88 | 2.17 | 2.90 |

The clustered P values of `N_0` for even `x` under `0^0 = 0` (Definition
26.8 with `phi = 2.5` and twins) are 0.0016 (all `j`), 0.0095 (even `j`)
and 0.049 (local). The peak sits in a few lengths. For `x = 6` at length
`T = 9` under `0^0 = 0`, the 11 even offsets with `-14 <= j <= 8`,
`j != 0`, hold 3.4 near-solutions each, and the even offsets with
`10 <= |j| <= 40` hold 0.7. The 5 solutions of `x = 6` with `T = 9` sit
in this peak.

Answer (heuristic). Twins explain the size of the clumps, not the excess.
No other exact move pairs solutions only. Most of the excess of the even
bases is in the calibration: the offsets `j x` mix two classes modulo
`2x`, and at the short lengths that hold most solutions the defect
spectrum peaks at `D = 0`, so far offsets miss the peak. Against the local
calibration in the right class, 25 against 14.8 has P = 0.05 including its
error. Under `0^0 = 1` and for odd `x` the remaining excesses (11 against
6.8, 7 against 2.2) have P = 0.14 and 0.03 with the local calibration.
They rest on the tiny solutions of `x <= 5`, where every calibration is
crude. The class factor modulo `2x` is a new structure, and its cause is
open.

## 26.7 The image and the in-degrees of F (question 85)

### 26.7.1 The run

`dyn_cycles --image` (new) visits every multiset `c` of 1 to `b` digits
with a nonzero digit, as the cycle pass does, and counts the in-degree of
the multiset of `S(c)`. A second pass groups the multisets by class
(length and digit sum modulo `b-1`) and adds the model predictions. It
runs on one thread.

Proposition 26.10 (proven). (1) The image is the same under both
conventions. (2) Under `0^0 = 0`, multisets that differ only in their
zeros have the same `S`; under `0^0 = 1`, multisets that differ only in the
split of `c_0 + c_1` have the same `S`.

Proof. (2) `w(0) = 0` in the first case; `w(0) = w(1) = 1` in the second.
(1) Under `0^0 = 0` the image is the set of multisets of `S_0(e)`, `e` the
nonzero part of `c`, a zero-free multiset of at most `b` digits. Under
`0^0 = 1`, `S_1(c) = S_0(c')` with `c'` equal to `c` with every 0 replaced
by 1, again a zero-free multiset of at most `b` digits. Both sets of `e`
are all zero-free multisets of 1 to `b` digits.

So the random mapping must act on the distinct values of `S`, not on the
multisets. There are other exact coincidences, such as `w(2) = 4 w(1)`.
The program collects the distinct values of `S` (bases up to 16, where
`S < 2^64`). It needs 2 bytes per multiset and 8 bytes per zero-free
multiset.

### 26.7.2 The image

Table 26.7.2 (computed, `analysis/data/r5e_image_summary.txt`,
`r5e_image_report.txt`). Image share: the multisets with in-degree at
least 1, divided by all multisets. "Uniform" is the formula of question
85. "Weighted" draws the image inside its class with probability
proportional to the number of strings with that multiset. "Distinct sums"
is the weighted model with `m_K` replaced by the number of distinct values
of `S` in class `K`.

| b | multisets | distinct sums | image | share | uniform | weighted | distinct sums |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 184,745 | 87,143 | 37,974 | 0.206 | 0.498 | 0.379 | 0.264 |
| 11 | 705,420 | 332,211 | 136,054 | 0.193 | 0.500 | 0.366 | 0.255 |
| 12 | 2,704,143 | 1,271,841 | 487,882 | 0.180 | 0.502 | 0.355 | 0.247 |
| 13 | 10,400,586 | 4,886,437 | 1,724,860 | 0.166 | 0.504 | 0.343 | 0.239 |
| 14 | 40,116,585 | 18,830,486 | 6,513,561 | 0.162 | 0.507 | 0.333 | 0.231 |
| 15 | 155,117,504 | 72,754,141 | 22,826,109 | 0.147 | 0.505 | 0.320 | 0.222 |
| 16 | 601,080,373 | 281,730,496 | 82,804,468 | 0.138 | 0.508 | 0.310 | 0.215 |

The uniform formula is far off, because most multisets map into a few
crowded classes and the image inside a class is not uniform. The weighted
model is still about twice the truth. Counting distinct sums closes more
than half of that gap (66% in base 10, 55% in base 16). The rest is 22%
to 36% of the prediction, and it grows with the length: in base 16 the
image is 0.98 of the distinct-sums prediction at 4 digits, 0.68 to 0.72
at 8 or 9 digits and 0.56 to 0.69 at 11 to 16 digits.

### 26.7.3 The forced top digits

`analysis/r5e_image_sim.py` keeps every distinct value of `S`, replaces
its digits below the top `t` by random digits with the same length and
digit sum modulo `b-1`, and counts the distinct multisets.

Table 26.7.3 (computed, 5 seeds each).

| b | true image | `t = 0` | `t = 1` | `t = 2` | `t = 3` | gap closed by `t = 3` |
|---:|---:|---:|---:|---:|---:|---:|
| 10 | 37,974 | 48,872 | 45,832 | 43,950 | 41,968 | 0.63 |
| 11 | 136,054 | 180,145 | 163,944 | 158,374 | 150,446 | 0.67 |
| 12 | 487,882 | 667,215 | 616,364 | 578,805 | 555,889 | 0.62 |

At `t = 0` the simulation reproduces the distinct-sums model (48,872
against 48,842). Keeping the top 3 digits closes about two thirds of the
gap. So the values of `S` share their leading digits far more than random
integers do, which makes their multisets collide. This is the forced top
digits of section 11.2, seen on all multisets at once.

### 26.7.4 The in-degrees

The in-degree of a multiset counted over distinct sums is overdispersed.
Its variance / mean is 3.60, 4.06, 4.52, 5.24, 5.33, 6.02, 6.33 for bases
10 to 16, against 2.29 to 3.81 for the Poisson mixture of the model; the
share with in-degree at least 4 is 0.036 to 0.039 against 0.025 to 0.032.

Answer (computed). The class-lumped random mapping does not predict the
image. The formula of question 85 overestimates it by a factor 2.4 to 3.7.
Two structures explain most of the gap: exact coincidences of the sums
(Proposition 26.10 and others, a factor 1.44) and the forced top digits
(about two thirds of the remaining factor 1.3 to 1.6). The test confirms the picture
of chapters 11, 23 and 24: the top digits of `S` are not random, the rest
nearly is. It does not show a new correlation between `c` and `S(c)`.

## 26.8 A mixing statistic for every world (question 86)

### 26.8.1 The statistic

`analysis/r5e_mixing.py`. In each world, draw random strings `c` of the
dominant length whose sum `F(c)` has the same length and meets the identity
of the world. Let `r` be `c` minus the top 3 digits of `F(c)`, the digits
that the low part of `F(c)` must supply for a solution. For each digit
value `v`, record whether the low histogram of `F(c)` has exactly `r_v`
copies of `v`. Do the same for a comparator `U`, which keeps the top 3
digits of `F(c)` and the class of the identity and draws its low digits
at random. The agreement ratio is the mean agreement of `F` over that of
`U`; the model assumes 1. A second number, the top factor, is the share of
samples whose top 3 digits of `F(c)` lie inside `c`, over the same share
for the top 3 digits of an independent string of the world.

### 26.8.2 Results

Table 26.8.1 (computed; 20,000 samples per world, 2,000 for `F_q[T]` per base,
4,000 for Pisot). Model ratio: observed over model, from the chapters.

| world | agreement ratio `F / U` | `R`, product over values | top factor | model ratio: solutions | near-solutions |
|---|---:|---:|---:|---:|---:|
| integers, `b = 20`, 19 digits, `0^0 = 0` | 0.989 | 0.79 | 0.83 | 1.0 (11.2a) | 0.99 |
| integers, `0^0 = 1` | 0.990 | 0.80 | 0.86 | 1.0 | 1.12 |
| base -20, 19 digits, `0^0 = 0` | 1.008 | 1.18 | 1.18 | 0.83 (-10 to -27) | 0.93 |
| base -20, `0^0 = 1` | 1.000 | 0.99 | 1.13 | 0.71 | 1.01 |
| factorions, `b = 20`, 14 digits, `w(0) = 0` | 1.002 | 1.05 | 1.07 | 0.69 (even bases) | 0.73 |
| factorions, `w(0) = 1` | 0.995 | 0.91 | 1.01 | 0.93 | 0.92 |
| factorial system, `L = 12`, `0^0 = 0` | 0.986 | 0.78 | 0.53 | 0 of 4.5 | about 1, in clusters |
| factorial system, `0^0 = 1` | 0.984 | 0.78 | 0.55 | 0 of 4.5 | about 1, in clusters |
| `F_5[T]`, `e = 3`, three bases, 17 digits, `0^0 = 0` | 1.023 to 1.034 | 0.001 to 24 | (too few) | 1.31 | 1.33 |
| `F_5[T]`, `0^0 = 1` | 1.022 to 1.033 | 0.88 to 42 | (too few) | 0.51 | 0.49 |
| Pisot `x = 6`, `T = 12`, `0^0 = 0` | 0.965 | 0.51 | 0.67 | 3.2 | 1.16 |
| Pisot `x = 6`, `0^0 = 1` | 1.037 | 1.04 | 0.78 | 2.9 | 1.23 |

The product `R` is dominated by noise and by single values: its standard
error on the log scale is 0.04 to 0.06 for the integer-like worlds and 0.2
to 1.0 for `F_q[T]`, where it swings from 0.001 to 42 between bases. The
agreement ratio is the stable number. In `F_5[T]` the top 3 digits of
`F(c)` almost never lie inside `c` (0.3% of samples), so the top factor
is not measured there.

Answer (computed, negative). The low digits of `F(c)` are random to within
1.6% per value in the integers, base -20, the factorions and the factorial
system, and within 3.7% in the Pisot base 6. `F_q[T]` stands out with 2.2%
to 3.4% per value over 125 values, which matches chapter 24. But the
statistic does not follow the model error. It has the same sign in
`F_q[T]` under both conventions, where the model error goes from 1.3 to
0.5. It is near 1 in the factorial system, where the model fails
completely, because that failure sits in the top digits; the top factor
is lowest there (0.53 to 0.55). In the Pisot base both numbers are near or
below 1 while the count is 3 times the model. One low-digit number cannot predict the model's error.
The two places where the model fails sit in the top digits (factorial
system) and in a single channel, the zero count (`F_q[T]` under
`0^0 = 1`, section 24.4.4), and a per-value average dilutes both.

## Files

- Engines: `fast/src/bin/r3t_pisot.rs` (`search x J list`, `defects`),
  `fast/src/bin/dyn_cycles.rs` (`--image`). Default outputs are unchanged;
  `cargo test --release` passes and `fast search 2 30` matches
  `output/b2-41-*.txt`.
- Library: `analysis/r5e_lib.py` (design effects, clustered P values,
  transposition free offsets), `analysis/r5e_cluster.py` (clusters).
- Runs: `r5e_int_offsets.py`, `r5e_nega_offsets.py`, `r5e_cycles2_run.sh`,
  `r5e_pisot_run.sh`, `r5e_pisot_defects.sh`, `r5e_image_run.sh`.
- Reports: `r5e_int_report.py`, `r5e_swap_model.py`, `r5e_scatter.py`,
  `r5e_fact_report.py`, `r5e_nega_report.py`, `r5e_cycles2_report.py`,
  `r5e_kdigit_report.py`, `r5e_short_spectrum.py`, `r5e_pooled.py`,
  `r5e_pisot_pairs.py`, `r5e_pisot_defects.py`, `r5e_image_report.py`,
  `r5e_image_sim.py`, `r5e_mixing.py`.
- Data: `analysis/data/r5e_*`.

## Open ends

- The class factor modulo `2x` in even Pisot bases (section 26.6.2): which
  identity makes even `j` carry more near-solutions under `0^0 = 0`?
- Heuristic 26.6 for the other worlds: a closed form of `phi` for
  factorions, negative bases and Pisot bases.
- A model of the image (section 26.7) with the top digits forced and the
  coincidences of `S` counted exactly.
- Rerun the rational and Eisenstein offsets with strings, to replace the
  assumed `phi = 2` of Table 26.5.1.
