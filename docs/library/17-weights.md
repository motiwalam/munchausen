# 17. Other weights: a sharp test of the model

Draft for questions 26, 19, 9 and 10. The engine now searches exactly with
other weights than `x^x`. Four experiments use it: weights with forced
residues, the convention `0^0 = m`, the weights `x^(x+t)`, and `x!`.
Every statement is marked as proven, computed, or heuristic (the refined
model of chapter 5). In the tables, "model" always means the refined model,
run by sampling with the exact weights of the experiment.

## Summary

| question | answer | basis |
|---|---|---|
| 26 | `fast search` takes `--zero m`, `--shift t`, `--factorial` and `--set-residue r`. The default search is unchanged. | computed |
| 19 | Forced residues `w(x) == x` multiply the count of long solutions by 18.9 against 17.0 = mean `b-1`. Residues `x + 1` leave only `(b-1)`-digit solutions, 0.583 `(b-1)` per base against 0.557 predicted. | proven and computed |
| 9 | The odd-base factor is 2.0 for even `m` and 1.2 for odd `m`. The data agree within 1.4 standard deviations once the shared zero-free solutions are split off. | model and computed |
| 10 | `x^(x+t)` keeps the length law and the parity factor. `x!` keeps about one solution per base, has no parity factor, and has a different length law. | model and computed |

The surprise: factorions are rare in odd bases. Bases 14 to 36 have 3
long factorions under `w(0) = 0` where the model expects 11.9 (P = 0.002 for
a Poisson count with the model's mean, before any correction for the choice
of the group). The near-factorions at 30 offsets in the same bases match the
model. So the shortfall belongs to the offset 0 alone, and I have no
explanation. Sections 19.5 and 23.1 test it further. The latest assessment,
in section 23.1, is a combined P of about 0.05.

## 17.1 The engine (question 26)

`fast search` accepts four new options (`fast/README.md`):

| option | weights |
|---|---|
| `--zero m` | the digit 0 weighs `m` under convention 1; convention 0 keeps 0 |
| `--shift t` | `x^(x+t)` for `x >= 1`, `t >= -1` |
| `--factorial` | `x!` for `x >= 1` |
| `--set-residue r` | each `w(x)`, `x >= 1`, raised by less than `b-1` to `x + r` modulo `b-1`, after `--perturb` |

The search assumed `x^x` in five places. Each one now takes any weights:

- The interval. `hi` bounded a free position below `k` by `w(k-1)` and a
  known zero by 1. It now uses `W(k-1)`, the largest weight among digits 0
  to `k-1`, and the larger of the two weights of 0. This bound holds for
  any weights at least 0. They need not increase, so `--zero 3` works,
  although then `w(0) = 3 > w(1) = 1`.
- `lo = t` needs weights at least 0. A negative `m` makes a sum smaller
  than `t` by up to `|m| d`. The root then starts at `t = -|m| d`, stored
  modulo `b^(32N)`, and the top lane marks a negative `t`. Only the generic
  path of the inexact rules runs this test, so the exact search keeps its
  machine code.
- The leaf assumed `w(1) = 1` and `w(0)` in {0, 1}. It now adds
  `e w(1) + c_0 w(0)` per convention.
- `kmax` is the largest digit with `w(j) < b^d`. Every digit above it weighs
  at least `b^d`, for any weights, so this rule stays.
- The lengths ran from 2 to `b`. They now run up to the largest `d` with
  `d max w >= b^(d-1)` (proven bound). That is `b` for `x^x`, `b + t` or
  `b + t + 1` for `x^(x+t)`, and `b - b/ln b` for `x!`.

The program also derives the one-digit solutions and its arbitrary
precision check from the same weight table. So it now verifies the results
of `--perturb` as well.

Checks (computed):

- The default search prints the same solutions as `output/b2-41-*.txt` for
  bases 2 to 36 and visits the same number of nodes in every base.
- A new test compares 24 weight options with a brute force over all digit
  multisets, in bases 2 to 8, for both vector widths. The options are
  `--zero` -3, -2, -1, 0, 2, 3, 7, `--shift` -1 to 3, `--factorial`,
  combinations, and `--set-residue` 0 to 2 with and without `--perturb`.
- `analysis/wgt_model.py` recomputes the weights in Python. Every solution
  of 9 options in bases 10 to 16 satisfies `n = F(n)` with them.
- `--factorial` finds every factorion of OEIS A193163 for bases 2 to 20,
  and nothing else. Base 21 adds `(1,4)` = 25.

Cost in base 30, 3 threads (computed):

| weights | nodes | relative to `x^x` |
|---|---:|---:|
| `x^(x-1)` | 38,331,821 | 0.58 |
| `x^x` | 66,246,690 | 1 |
| `x^(x+1)` | 112,772,217 | 1.70 |
| `x^(x+2)` | 186,685,777 | 2.82 |
| `x!` | 3,611,454 | 0.055 |

The `x!` tree grows about 1.75 times per base. Base 42 takes 2.97 billion
nodes and 158 s on 3 threads.

## 17.2 Forced residues (question 19)

### The identity (proven)

Let `w(x) == x + r (mod b-1)` for every digit `x >= 1`, and let 0 weigh
`z`. Every integer satisfies `n == digit sum (mod b-1)`. So a solution
with `d` digits, `c_0` of them zero, must satisfy

    r (d - c_0) + z c_0 == 0   (mod b-1).

The four cases with `r, z` in {0, 1} give:

| `r` | `z` | condition on a solution | allowed lengths |
|---:|---:|---|---|
| 0 | 0 | none | all |
| 0 | 1 | `c_0 == 0 (mod b-1)` | all, with no zero (or `b-1` zeros) |
| 1 | 1 | `d == 0 (mod b-1)` | only `d = b-1` |
| 1 | 0 | `d - c_0 == 0 (mod b-1)` | `d = b-1` with no zero, or `d = b` with one zero |

`--set-residue r` gives `w(1) = 1 + r`, and the convention gives `z`. No
solution has more than `b` digits here, because the weights stay below
`1.25 (b-1)^(b-1) + b`, and `(b+1)` times that is below `b^b` for `b >= 4`.

### The predictions (model)

The refined model counts every multiset that meets the condition `b-1`
times. In the large-base limit, the digit counts are independent Poisson(1)
variables, and the length shares are those of section 5.2:

| `r` | `z` | limit per base | value |
|---:|---:|---|---:|
| random | | 1 | 1 |
| 0 | 0 | `(b-1) * 1` | `1.00 (b-1)` |
| 0 | 1 | `(b-1) P(c_0 = 0)` | `0.368 (b-1)` |
| 1 | 1 | `(b-1) * 0.552` | `0.552 (b-1)` |
| 1 | 0 | `(b-1) (0.552 + 0.080) / e` | `0.233 (b-1)` |

### The measurement (computed)

`analysis/wgt_residue.py` searches bases 12 to 24 with seeds 1 to 8, 104
runs per weight set, with `sum (b-1) = 1768`. The model uses the exact
weights of each run. Long means `d >= b-6`.

| weights | convention | long solutions | model, same weights | per `b-1`: observed | model | limit |
|---|---|---:|---:|---:|---:|---:|
| `--perturb` | `0^0 = 0` | 98 | 111.8 | | | |
| `--perturb` | `0^0 = 1` | 109 | 111.8 | | | |
| `--set-residue 0` | `0^0 = 0` | 1955 | 1891.4 | 1.106 | 1.070 | 1.000 |
| `--set-residue 0` | `0^0 = 1` | 845 | 789.8 | 0.478 | 0.447 | 0.368 |
| `--set-residue 1` | `0^0 = 1` | 1030 | 984.7 | 0.583 | 0.557 | 0.552 |
| `--set-residue 1` | `0^0 = 0` | 454 | 453.1 | 0.257 | 0.256 | 0.233 |

Forcing `w(x) == x` multiplies the count by 1955 / 103.5 = 18.9. The model
predicts 1891.4 / 111.8 = 16.9, and the mean of `b-1` is 17.0. With
`w(x) == x + 1` and `0^0 = 1`, all 1030 solutions have exactly `b-1`
digits, as the identity demands. Their number is 0.583 `(b-1)` per base,
against 0.557 from the model and 0.552 in the limit. All four forced cases
lie within 7% of the model. That is a 17-fold change in the count,
predicted to a few percent.

Two details differ from a Poisson law:

- The counts per run scatter twice as much as Poisson counts:
  `sum (N - lambda)^2 / lambda` is 192 to 261 over 104 runs, against 98 and
  101 for random residues. The cause is families. A forced residue fixes the
  small weights. For example, `--set-residue 1` in base 21 gives `w(1) = 2`,
  `w(2) = 23`, `w(3) = 44`, so `w(2) - w(1) = w(3) - w(2) = b`. A digit 1,
  2 or 3 in the second-to-last place then gives three solutions at once.
  Seed 2 in base 21 has 26 solutions where the model expects 11.1.
- Short solutions are 4 times too common under `--set-residue 0`: 336
  two-digit solutions under `0^0 = 0` against 78.5. This is algebra, not
  chance (proven). Write `w(x) = x + k_x (b-1)`. Then `n = F(n)` holds
  exactly when `sum x_i (b^i - 1)/(b-1) = sum k_x`. For 2 digits `(a, c)`
  this says `a = k_a + k_c`. Since `k_1 = 0` and `k_2 = 1` for every
  `b >= 4`, the numbers `(1,2)` and `(2,2)` are solutions in every base and
  for every seed.

## 17.3 The convention `0^0 = m` (question 9)

### The prediction (model)

In an odd base, `b-1` is even, and `x^x == x (mod 2)` for `x >= 1`. So the
identity modulo 2 reads `m c_0 == 0 (mod 2)`. For even `m` it always holds,
and the expected count doubles. For odd `m` it needs an even number of
zeros, which has probability `(1 + e^(-2))/2`, so the factor is
`1 + e^(-2) = 1.135` in the limit. The finite-base model gives 2.00 to 2.02
for even `m` and 1.19 to 1.22 for odd `m` in bases 10 to 30.

### The measurement (computed)

`analysis/wgt_zero.py`, bases 10 to 30, nontrivial solutions (`m = 0` and
`m = 1` are the true conventions):

| `m` | even bases: observed | model | odd bases: observed | model | odd-base factor of the model |
|---:|---:|---:|---:|---:|---:|
| -2 | 17 | 13.07 | 30 | 23.89 | 2.01 |
| -1 | 16 | 12.99 | 17 | 14.38 | 1.22 |
| 0 | 15 | 13.08 | 29 | 23.95 | 2.02 |
| 1 | 21 | 13.02 | 19 | 14.21 | 1.20 |
| 2 | 14 | 13.03 | 25 | 23.60 | 1.99 |
| 3 | 21 | 13.16 | 17 | 14.24 | 1.19 |

The columns are not independent. A solution without the digit 0 is a
solution for every `m`. There are 24 of them, against 16.5 expected: 10
against 5.8 in even bases and 14 against 10.6 in odd bases. Every row
carries this excess. The solutions with zeros are separate draws for each
`m`. Pooled by the parity of `m`:

| `m` | bases | solutions with zeros: observed | model | P(at least observed) |
|---|---|---:|---:|---:|
| even (-2, 0, 2) | even | 16 | 21.7 | 0.91 |
| even (-2, 0, 2) | odd | 42 | 39.5 | 0.37 |
| odd (-1, 1, 3) | even | 28 | 21.7 | 0.11 |
| odd (-1, 1, 3) | odd | 11 | 10.9 | 0.53 |

So the parity factor follows the parity of `m`, as predicted. Odd bases
with odd `m` have 11 solutions with zeros against 10.9, while odd bases with
even `m` have 42 against 39.5. The values `m = -2, 2, 3` have no twins or
self-paying families, and they fit as well as `m = 0, 1`.

## 17.4 Universality (question 10)

### Predictions (model)

- `x^(x+t)`. A digit `b-y` weighs about `e^(-y) b^(b-y+t)`. So the length
  law of section 5.2 holds with every length moved up by `t`: 8.0% at
  `b+t`, 55.2% at `b+t-1`, 23.2% at `b+t-2`. Since `x^(x+t) == x (mod 2)`,
  the parity factors stay 2 and 1.135.
- `x!`. A digit `b-y` weighs about `(b-1)! / b^(y-1)`, one base-`b` digit
  less per step. Let `D` be the number of digits of `(b-1)!`. If the largest
  digit present is `b-y`, the sum has about `D - y + 1` digits. The counts
  are Poisson with mean `lambda = D/b`, which tends to 1 like `1 - 1/ln b`.
  So the shares are geometric: `(1-q) q^y` at `D - y`, with
  `q = e^(-lambda)`. For `b = 30`, `D = 21` and the shares are 50%, 25%,
  12%. In the limit they are 63.2%, 23.3%, 8.6%: the law of `x^x` with its
  top two lengths merged. The total stays about 1 per base.
- `x!` has no parity factor. For `x >= 2`, `x!` is even, so `x! - x` is
  odd for odd `x`. The identity modulo 2 then depends on the number of odd
  digits, which is even or odd with equal chance.

### Measurements (computed)

`analysis/wgt_family.py` and `analysis/wgt_summary.py`. Totals of
nontrivial solutions, observed against the model, and the factor of the
model in odd bases:

| weights | bases | `0^0 = 0`: even | odd | factor | `0^0 = 1`: even | odd | factor |
|---|---|---:|---:|---:|---:|---:|---:|
| `x^(x-1)` | 10-32 | 21 / 15.1 | 28 / 27.6 | 2.12 | 21 / 14.7 | 16 / 17.0 | 1.31 |
| `x^x` | 10-30 | 15 / 13.0 | 29 / 24.0 | 2.04 | 21 / 13.0 | 19 / 14.1 | 1.20 |
| `x^(x+1)` | 10-32 | 18 / 14.3 | 34 / 25.4 | 2.03 | 14 / 14.0 | 16 / 14.9 | 1.19 |
| `x^(x+2)` | 10-32 | 18 / 13.4 | 33 / 25.1 | 2.04 | 19 / 13.5 | 17 / 14.2 | 1.16 |
| `x!` | 10-42 | 23 / 20.2 | 14 / 19.6 | 1.03 | 23 / 20.1 | 15 / 19.2 | 1.00 |

Length law, both conventions together, `j` = reference length minus `d`
(reference `b + t`, or `D` for `x!`). Observed / model (share of the model):

| weights | `j = -1` | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `x^(x-1)` | | 3 / 4.0 (6%) | 32 / 32.2 (52%) | 11 / 15.1 (24%) | 7 / 6.9 (11%) | 1 / 1.2 | 4 / 2.8 |
| `x^x` | | 2 / 4.1 (7%) | 35 / 29.7 (53%) | 13 / 13.1 (23%) | 11 / 4.9 (9%) | 0 / 1.8 | 1 / 2.2 |
| `x^(x+1)` | | 5 / 5.1 (8%) | 38 / 33.6 (54%) | 10 / 14.2 (23%) | 6 / 4.4 (7%) | 0 / 2.1 | 2 / 2.4 |
| `x^(x+2)` | | 8 / 4.7 (8%) | 40 / 34.3 (57%) | 22 / 13.7 (23%) | 1 / 3.5 (6%) | 1 / 2.3 | 0 / 2.1 |
| `x!` | 3 / 2.7 (4%) | 18 / 32.6 (45%) | 21 / 16.6 (23%) | 5 / 9.3 (13%) | 2 / 5.4 (7%) | 3 / 3.1 | 4 / 2.9 |

The Poisson law, for the long solutions (`j <= 5`) per base and convention:

| weights | `0^0 = 0`: observed | model | dispersion | empty bases: observed | model | `0^0 = 1`: observed | model | dispersion | empty | model |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `x^(x-1)` (23 bases) | 31 | 35.9 | 19.8 | 6 | 5.5 | 27 | 26.3 | 21.8 | 6 | 7.4 |
| `x^x` (21 bases) | 32 | 32.3 | 31.2 | 5 | 5.1 | 30 | 23.5 | 29.1 | 6 | 6.9 |
| `x^(x+1)` (23 bases) | 36 | 35.8 | 21.5 | 7 | 5.5 | 25 | 25.9 | 24.0 | 7 | 7.5 |
| `x^(x+2)` (23 bases) | 40 | 35.2 | 23.4 | 4 | 5.6 | 32 | 25.3 | 29.3 | 5 | 7.7 |
| `x!` (33 bases) | 27 | 36.5 | 46.9 | 19 | 11.0 | 29 | 36.1 | 38.2 | 16 | 11.1 |

"Dispersion" is `sum (N - lambda)^2 / lambda` over the bases. For a Poisson
law it is near the number of bases.

What this shows:

- `x^(x+t)` is universal in every test. Totals, parity factors, the
  shift of the length law by `t`, the dispersion and the number of empty
  bases all match. For `t = -1` the weights `w(1) = 1` and `w(2) = 2` give
  twins `(..., 1)` and `(..., 2)` under both conventions; this adds 3 twin
  pairs under `0^0 = 1`.
- Short solutions (`j >= 6`) exceed the model for every weight: 18 against
  6.7 for `x^(x-1)` under `0^0 = 0`. This matches the local factors of
  section 11.4, which this model leaves out.
- `x!` keeps the total near the model's 1.2 per base: 75 against 79.1
  over all lengths and both conventions. It loses the parity factor, as predicted: the model's factor is 1.00 to
  1.03, and odd bases have no surplus. The length law is a different one,
  as predicted. But long factorions fall short: 56 against 72.6. The
  shortfall sits in odd bases at the top length `D`: 4 against 15.8.

### The factorion shortfall in odd bases

Bases 14 to 36, long solutions:

| bases | convention | observed | model | P(at most observed) | near-solutions per offset / model |
|---|---|---:|---:|---:|---:|
| even | `0^0 = 0` | 9 | 13.0 | | 0.73 |
| even | `0^0 = 1` | 12 | 12.9 | | 0.92 |
| odd | `0^0 = 0` | 3 | 11.9 | 0.002 | 0.94 to 1.04 |
| odd | `0^0 = 1` | 4 | 11.8 | 0.009 | 0.92 to 0.97 |

The last column comes from `analysis/wgt_offsets.py`. It counts the
solutions of `n = F(n) + j (b-1)` for `j = 1` to 30, which are draws of the
same coincidence (section 11.1). In odd bases they match the model. The 30
offsets give totals over the 11 odd bases from 6 to 18 under `0^0 = 0` and
from 5 to 21 under `0^0 = 1`. The offset 0 gives 3 and 4, below every one
of them.

Two explanations fail:

- The last digits. For `x!`, `b^K` divides `x!` for all but the small
  digits, so the last `K` digits of the sum are a fixed function of the
  small counts. `analysis/wgt_lowdigits.py` puts the last 1, 2 or 3 digits
  into the model exactly. The expected count in odd bases moves from 17.8
  to between 16.5 and 19.6. No shortfall.
- The base. The near-solutions show that odd bases have the normal number
  of coincidences. Only `D = 0` is short.

So the shortfall is either a fluctuation or a property of the exact equation
`n = F(n)` that the offsets do not share. The two conventions share their
zero-free solutions, so the two P values are not independent. The P values
in the table are `P(X <= observed)` for a Poisson count with the refined
model's mean. I looked at about 16 groups before I saw this one, which makes a
P of 0.002 worth about 0.03. Section 19.5 calibrates the count with
near-factorions instead of the model (P = 0.006 and 0.02, about 0.1 after the
same correction). Section 23.1 adds fresh bases and gives the latest
assessment: a combined P of about 0.05.

Fresh odd bases, searched after the shortfall was found (computed, 290 s
and 1148 s on 3 threads): base 43 has one long factorion, 30 digits long and
zero-free, so it counts under both conventions. Base 45 has none. The model
expects 2.05 per convention in the two bases, and the shortfall at its
observed rate (about 0.3 times the model) predicts 0.6. One observed fits
both. Status: open. Bases 47 and 49 take about 1 and 3 hours.

## 17.5 Status

| question | status |
|---|---|
| 26 | done: `--zero`, `--shift`, `--factorial`, `--set-residue`, tested against brute force |
| 19 | the identity is proven; the counts match the model within 7% for a 17-fold change |
| 9 | the parity factor follows the parity of `m`, as predicted |
| 10 | `x^(x+t)` is universal; `x!` keeps the count and loses the parity factor, with a new length law; the odd-base shortfall of factorions is open |

## Files

- `analysis/wgt_model.py`: the weights in Python and the refined model for
  any weights.
- `analysis/wgt_residue.py`: question 19; data in
  `analysis/data/wgt_residue.txt`.
- `analysis/wgt_family.py`, `analysis/wgt_summary.py`: questions 9 and 10;
  data in `analysis/data/wgt_true.txt`, `wgt_zero_*.txt`, `wgt_shift_*.txt`,
  `wgt_factorial.txt` and `wgt_factorial_odd_43_45.txt`.
- `analysis/wgt_zero.py`: the split by zeros for question 9; data in
  `analysis/data/wgt_zero_summary.txt`.
- `analysis/wgt_lowdigits.py`, `analysis/wgt_offsets.py`: the factorion
  tests; data in `analysis/data/wgt_lowdigits_*.txt` and
  `analysis/data/wgt_offsets_factorial.txt`.
