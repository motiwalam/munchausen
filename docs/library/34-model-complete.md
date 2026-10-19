# 34. Is the refined model complete?

This chapter answers questions 90, 93, 94, 103 and 106 of `questions.md`
(workload 1 of `questions-round6.md`). All five ask whether the refined model
of section 5.3, with the forced top digits of section 23.5, accounts for
everything apart from identities. Question 93 looks for a third kind of
correction in the 12% excess under `0^0 = 1`. Question 94 asks whether the
zero deficit of question 71 shows in the near-solutions. Question 90 turns
the model's main laws into a statement about the trace of a stochastic
matrix. Question 103 collects every P value of the library. Question 106
tests the independence of neighbouring bases.

Each statement carries one label: Theorem, Proposition, Lemma or Corollary
(proved here, or proved with a stated computation), Heuristic, Conjecture,
or computed (an exact computation or a measurement, with its range).
Scripts are `analysis/r6q_*.py`, data `analysis/data/r6q_*`. Every run used
one or two threads.

Notation. `w(x) = x^x` for `x >= 1` and `w(0) = m`. `F(n)` is the sum of
`w` over the digits of `n`. A near-solution at offset `D` is an `n` with
`n = F(n) + D`. Unless said otherwise the offsets are `D = 2j(b-1)`,
`j = 1..60`, the lengths are `b-6` to `b`, and `lambda` is the mean number
of near-solutions per offset (section 11.2a). "Model" means the refined
model: the digits of `F` are uniform among the strings that meet the
identity modulo `b - 1`. "Model, t = 3" also forces the top 3 digits of `F`
(section 23.5). `phi` is the design effect of chapter 26. `z` counts the
zero digits of a string, `c_0` the zeros of a multiset.

## Summary

| question | result | status |
|---|---|---|
| 93 | The refined model can now be computed exactly, split by the number of zeros (Proposition 34.1). The 12% excess under `0^0 = 1` has two parts. In odd bases it is the zero-free near-solutions: 1.26 times the model (`z = +3.4`), the same strings under both conventions. They carry 72% of the expectation under `0^0 = 1` and 42% under `0^0 = 0`, so the same surplus lifts the `0^0 = 1` ratio more. In even bases it is the near-solutions with one zero under `0^0 = 1`: 1.30 times the model (`z = +2.9`), while `0^0 = 0` has 0.93. | computed |
| 93 | At the shifted offsets `2j(b-1) + 1` and `+ 2` the even bases show surpluses of 7% to 15% in both conventions and other zero classes. In five perturbed worlds the two conventions agree: the gap `R1 - R0` is -0.02 to -0.04 in every seed, against +0.09 +/- 0.04 for the true weights. The perturbed worlds also show that world-level ratios scatter 1.3 to 1.5 times more than the clustered error allows, which brings `z = 3.0` down to about 2. Verdict: not established. The excess does not sit in the zeros, and no third kind of correction is needed at the present precision. | computed; Heuristic 34.4 |
| 94 | Solutions under `0^0 = 0`, bases 12 to 43: 29 zeros against 43.1 in the exact model (`z = -2.2`). The forced top digits do not lower this expectation: they raise the zeros per near-solution by 5% in even bases and lower them by 1% in odd bases, against the 10% of the lead. Near-solutions: no deficit in even bases (0.82 zeros per near-solution against 0.84), a deficit in odd bases (0.72 against 0.85, `z = -3.1`), which is the zero-free surplus of question 93 seen from the other side. | computed |
| 90 | The basic expected count over the lengths 2 to `b` is the trace of the length matrix without its first row and column. Every row `b - j` tends to one law `(s_j')` (Theorem 34.6). The trace is `1 + C/b + o(1/b)` with `C = -d E[J'] / d mu = e/(e-1)^2 + 1/(2e) + 2.2 * 10^-5 = 1.10464` (Proposition 34.8; proved for the partial trace, the tail computed). `C/b` is one eigenvalue: `b lambda_2` is 1.34, 1.20, 1.14 at `b` = 40, 100, 300. Length 1 adds `E_1 = N_1(b)/(b-1)` with `N_1(b) = #{x : x^x < b}`, which grows like `ln b / ln ln b`, so with length 1 the excess has no limit. The "second eigenvalue about `3/b`" of the lead is this length-1 state. | Theorem 34.6, Propositions 34.5 and 34.8, Corollary 34.7, Heuristic 34.9; computed |
| 90 | The refined count is a sum over the characters `t` of `Z/(b-1)` (Proposition 34.10). For odd `b` and `0^0 = 0` the character of order 2 gives exactly the basic count again (Theorem 15.2); for `0^0 = 1` it tends to `e^-2` times it (Theorem 34.12). The other characters add between -0.23 and +0.36 at `b <= 25` and at most 0.11 in absolute value for `25 < b <= 128`. | Proposition 34.10, Theorem 34.12; computed; Conjecture 34.13 |
| 103 | 241 rows, 133 current tests with a P value, 56 data groups. Taken together the P values are far from uniform: 14 of 56 groups below 0.05 (2.8 expected), Fisher P `10^-9`. The 12 groups named before the data were seen look uniform: none below 0.1, median 0.59, Fisher P = 0.74. Every group below 0.05 is an anomaly the library already names, or a world where the model is known to fail. No lean toward deficits: 17 excesses against 8 deficits among the groups with P < 0.2. | computed; Heuristic 34.14 |
| 106 | Residuals `lambda / model` of neighbouring bases 12 to 32: lag-1 correlation -0.09 and -0.17 with the top-digit model (permutation P 0.65 and 0.46); -0.31 and -0.41 without it (P 0.06, 0.07). No multiset is a near-solution in two bases (0.02 expected). The top-digit factors of one multiset in bases `b` and `b + 1` are uncorrelated (`|r| <= 0.044`). But the two conventions in one base correlate at +0.78: pooled tests must not treat them as independent. | computed; Heuristic 34.15 |
| library | Two stale combined P values (chapters 17 and 19), a range misquoted in section 21.4, an unsupported claim in section 24.6.2, a pooled test in Table 26.5.1 that adds correlated counts as independent, and three problems with the leads of `questions-round6.md` | section "Library corrections" |

## 34.1 Where the 12% excess sits (question 93)

### 34.1.1 An exact refined model

The library computes the refined model by sampling. It can be computed
exactly, and split by any statistic of the low digits.

Proposition 34.1 (proved). Let `w(1) < ... < w(b-1)` and `w(0) <= w(1)`.
Walk over the digit values from `b - 1` down to 0. Given that no digit above
`x` is present, the free digits that remain are independent and uniform on
`{0, ..., x}`, and a pending leading digit is uniform on `{1, ..., x}`. So
the count of `x` is binomial, and the leading digit equals `x` with chance
`1/x`. Stop as soon as the partial sum `s` and `s + (r + l) w(x)` have the
same number of digits, where `r` free digits and `l` leading digits remain.
At a stopped node the length of `F` is fixed, the remaining digits are
uniform, and

    P(F == n (mod b-1), z zeros | node) = (1/(b-1)) sum over t of e(t U / (b-1)) psi_x(t)^l C(r, z) B_x(t)^z A_x(t)^(r - z),

with `U` the sum of `w - x` over the placed digits, `A_x(t)` the mean of
`e(t (w(y) - y) / (b-1))` times `x/(x+1)` over `1 <= y <= x`, `B_x(t)` the
term of `y = 0` divided by `x + 1`, and `psi_x` the mean over `1..x`.

Proof. The law of the remaining digits given the placed ones is as stated
because the digits are independent and uniform. The residue condition is
the orthogonality of the characters of `Z/(b-1)`. The stopping rule is
exact because all later terms are at most `w(x)` each.

`analysis/r6q_lib.py` implements it with exact integer sums. Branches below
`10^-15` are dropped; the dropped mass is below `2 * 10^-11` up to
`b = 300`. It agrees with the sampled model of `r2c_top_model.py` within
its standard error in all 30 cases checked (bases 12 to 26, both
conventions; for example 1.1462 against 1.1488 +/- 0.0056 in base 12). A
base takes about 0.05 seconds. The same walk gives the whole length matrix
of section 34.3 and accepts the perturbed weights of `fast --perturb`
(`r6q_lib.weights` reproduces them; checked on three near-solutions).

### 34.1.2 The excess

Table 34.1.2.1 (computed, `r6q_neighbors.py residuals`,
`data/defects_bulk_b1.txt`, bases 12 to 32). `lambda / model` per parity
and convention. "Mean" is the mean of the per-base ratios, as in section
23.5; `z` is that of the pooled ratio, with the clustered standard errors of
chapter 26.

| model | `0^0` | even bases | odd bases | mean, all bases | `z`, all |
|---|---:|---:|---:|---:|---:|
| exact, `t = 0` | 0 | 0.933 | 1.054 | 0.991 | +0.33 |
| exact, `t = 0` | 1 | 1.095 | 1.145 | 1.119 | +2.96 |
| `t = 3` | 0 | 0.941 | 1.036 | 0.986 | +0.23 |
| `t = 3` | 1 | 1.110 | 1.133 | 1.121 | +3.09 |

This reproduces the 12% and `z = 3.0` of Table 26.4.1.

### 34.1.3 The split by zeros

Two exact facts organize the data.

Lemma 34.2 (proved). A string without the digit 0 has the same `F` under both
conventions. So the zero-free near-solutions are the same events under
both conventions, and so is their model expectation.

Lemma 34.3 (proved). `F_1(n) = F_0(n) + c_0(n)`. So `n` is a near-solution
at `D` under `0^0 = 1` with `c` zeros exactly when it is a near-solution at
`D + c` under `0^0 = 0` with `c` zeros.

Table 34.1.3.1 (computed, `r6q_zeros.py comparetop`, `data/r5e_int_std.txt`,
bases 12 to 26, 60 offsets each, model `t = 3`). Near-solutions per offset
summed over the bases of each parity, by the number of zeros, against the
model. `z` uses the variance `phi E / J` with the measured `phi` (1.9 to
2.2).

| parity | `0^0` | zero-free | 1 zero | 2 zeros | 3 or more | all |
|---|---:|---|---|---|---|---|
| even | 0 | 3.43 / 3.46 (0.99) | 2.93 / 3.17 (0.93) | 1.12 / 1.40 (0.80) | 0.43 / 0.48 (0.90) | 7.92 / 8.51 (0.93, `z` -1.1) |
| even | 1 | 3.43 / 3.44 (1.00) | 4.13 / 3.17 (1.30, `z` +2.9) | 1.50 / 1.41 (1.07) | 0.20 / 0.51 (0.39, `z` -2.4) | 9.27 / 8.53 (1.09, `z` +1.4) |
| odd | 0 | 7.97 / 6.34 (1.26, `z` +3.4) | 5.85 / 5.50 (1.06) | 1.85 / 2.35 (0.79) | 0.72 / 0.71 (1.01) | 16.38 / 14.90 (1.10, `z` +2.0) |
| odd | 1 | 7.97 / 6.35 (1.26, `z` +3.4) | (none possible) | 2.17 / 2.31 (0.94) | 0.07 / 0.10 (0.64) | 10.20 / 8.76 (1.16, `z` +2.5) |

The model without forced digits gives the same picture (`r6q_zeros.py
compare`): zero-free 0.95 (even) and 1.29 (odd), one zero under `0^0 = 1`
in even bases 1.28.

So the excess is not one effect.

- Odd bases. Under `0^0 = 1` an odd number of zeros breaks the parity
  doubling, and 72% of the expectation is zero-free; under `0^0 = 0` it is
  42%. The zero-free near-solutions run 26% above the model, and they are
  the same events in both conventions (Lemma 34.2). So the same surplus
  raises the `0^0 = 1` ratio to 1.16 and the `0^0 = 0` ratio to 1.10. The
  classes with zeros fit (0.93 to 1.06, apart from two zeros under
  `0^0 = 0`, 0.79). Base 13 carries 0.70 of the 1.63 surplus per offset
  (1.85 against 1.15); without it the zero-free ratio is 1.17 (`z = +2.1`).
  Section 23.5 already noted that base 13 has short lengths, where the local
  factors of section 11.4 raise the count.
- Even bases. The zero-free class fits (0.99 and 1.00). The convention gap
  sits in the strings with one zero: 1.30 under `0^0 = 1` against 0.93
  under `0^0 = 0`. By Lemma 34.3 the first are the `0^0 = 0` near-solutions
  with one zero at the offsets `2j(b-1) + 1`.

### 34.1.4 The shifted offsets

`analysis/r6q_offsets.py` reran the search at `D = 2j(b-1) + c`, `c = 1, 2`,
`j = 1..60`, bases 12 to 26 (`data/r6q_shift_c1.txt`, `r6q_shift_c2.txt`).
The model takes the residue condition of `D == c (mod b-1)` (the argument
`shift` of `refined_by_zeros`). In odd bases `0^0 = 0` has no near-solution
at odd `D`, since `x^x - x` is even; the model agrees.

Table 34.1.4.1 (computed, `r6q_zeros.py compare`, model `t = 0`, even bases
12 to 26). Ratio observed / model; `z` as in Table 34.1.3.1.

| offsets | `0^0` | zero-free | 1 zero | 2 zeros | 3 or more | all |
|---|---:|---:|---:|---:|---:|---|
| `2j(b-1)` | 0 | 0.95 | 0.92 | 0.84 | 1.03 | 0.92 (`z` -1.3) |
| `2j(b-1)` | 1 | 0.95 | 1.28 | 1.12 | 0.47 | 1.08 (`z` +1.2) |
| `2j(b-1) + 1` | 0 | 0.94 | 1.28 | 0.97 | 1.47 | 1.10 (`z` +1.5) |
| `2j(b-1) + 1` | 1 | 0.94 | 1.16 | 1.12 | 1.31 | 1.07 (`z` +1.1) |
| `2j(b-1) + 2` | 0 | 1.22 | 1.16 | 1.12 | 0.68 | 1.15 (`z` +2.4) |
| `2j(b-1) + 2` | 1 | 1.22 | 0.96 | 1.26 | 1.63 | 1.15 (`z` +2.3) |

The one-zero cell of `0^0 = 0` at `+1` repeats the one-zero cell of
`0^0 = 1` at 0 (4.133 per offset in both), as Lemma 34.3 requires; this
checks the runs. In odd bases the offsets `+ 2` give 1.02 (`0^0 = 0`) and
0.98 (`0^0 = 1`).

What this shows (computed). The even bases run above the model at every
offset family except `2j(b-1)` under `0^0 = 0`: the six rows have mean 1.08.
Surpluses of 1.2 to 1.6 appear in the zero-free class (`+2`), in two or
more zeros (`+1`, `+2`) and in one zero (`+1`). No zero class and no
convention is high in all three families. So the one-zero surplus of Table
1.3.1 is one cell of a scatter that the other cells share; it is not a
property of the zeros.

### 34.1.5 Perturbed worlds

`analysis/r5e_int_offsets.py std 12 26 60 1 --perturb s`, `s = 1..5`
(`data/r6q_pert_s*.txt`). The engine replaces each `w(x)`, `x >= 2`, by
`w(x)` plus a random amount below `w(x)/4`, which keeps the lengths and
destroys every residue structure. The model is the exact refined model on
the same weights (`t = 0`).

Table 34.1.5.1 (computed, `r6q_zeros.py summary`, `data/r6q_zero_summary.txt`).
Ratio observed / model. `R0`, `R1`: all bases 12 to 26 pooled, per
convention. The gap `R1 - R0` has standard error from the events with
zeros only, since the zero-free events are common (Lemma 34.2).

| world | even, `0^0 = 0` | even, 1 | odd, 0 | odd, 1 | odd, zero-free | `R0` | `R1` | gap |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| true, `t = 3` | 0.930 | 1.087 | 1.100 | 1.164 | 1.257 | 1.038 | 1.126 | +0.088 +/- 0.042 |
| true, `t = 0` | 0.923 | 1.076 | 1.105 | 1.181 | 1.288 | 1.038 | 1.129 | +0.090 +/- 0.042 |
| seed 1 | 0.999 | 0.980 | 1.073 | 1.010 | 1.056 | 1.033 | 0.994 | -0.039 +/- 0.049 |
| seed 2 | 1.069 | 1.049 | 1.064 | 1.039 | 1.228 | 1.067 | 1.044 | -0.022 +/- 0.051 |
| seed 3 | 1.013 | 1.003 | 1.057 | 1.024 | 1.153 | 1.033 | 1.013 | -0.021 +/- 0.050 |
| seed 4 | 1.148 | 1.080 | 0.775 | 0.783 | 0.785 | 0.974 | 0.942 | -0.032 +/- 0.048 |
| seed 5 | 0.953 | 0.914 | 0.952 | 0.913 | 0.863 | 0.953 | 0.914 | -0.039 +/- 0.049 |

What this shows (computed).

- The perturbed worlds have no convention gap. In all five the gap is
  slightly negative, -0.031 on average (+/- 0.022 for the mean). The true
  weights have +0.09, which is 2.5 standard errors above the perturbed
  mean. In this sense the gap is arithmetic of `x^x`, as the question
  framed it.
- The perturbed worlds scatter more than the clustered errors allow. The
  cells of one parity and convention have a sampling error of about 0.06
  to 0.07. Against the model with `t = 0` they range from 0.78 to 1.15
  between seeds; seed 4 has 0.78 in odd bases (`z` about -3.3). The odd
  zero-free cell, whose true value 1.26 drives the excess, takes 0.79 to
  1.23 (standard deviation 0.18 against a sampling error of about 0.10).
- Forcing the top digits of the perturbed weights (Table 34.1.5.2) removes
  part of this scatter, not all of it.

Table 34.1.5.2 (computed, the same runs against the model with `t = 3` on the
perturbed weights, 200,000 strings per length).

| seed | even, 0 | even, 1 | odd, 0 | odd, 1 | odd, zero-free | `R0` | `R1` | gap |
|---:|---:|---:|---:|---:|---:|---:|---:|---|
| 1 | 0.965 | 0.943 | 1.049 | 0.989 | 1.029 | 1.004 | 0.964 | -0.039 |
| 2 | 1.001 | 0.976 | 1.054 | 1.057 | 1.195 | 1.025 | 1.012 | -0.013 |
| 3 | 1.019 | 1.003 | 1.016 | 0.971 | 1.082 | 1.018 | 0.988 | -0.030 |
| 4 | 1.160 | 1.082 | 0.837 | 0.856 | 0.825 | 1.015 | 0.981 | -0.034 |
| 5 | 0.970 | 0.910 | 0.979 | 0.936 | 0.889 | 0.974 | 0.922 | -0.052 |

The standard deviation over seeds of one cell is now 0.08 to 0.09 against a
sampling error of 0.065, and 0.15 for the odd zero-free cell against 0.10.
So the clustered variance of chapter 26 understates the spread of a
world-level ratio by a factor of about 1.3 to 1.5 in standard deviation,
even with the top digits forced. The pooled ratios `R0` and `R1` stay
within 0.92 to 1.03, and the gap stays negative in every seed.

### 34.1.6 Verdict

Heuristic 34.4. The 12% excess under `0^0 = 1` is not a third kind of
correction tied to the zeros.

- In odd bases it is a surplus of zero-free near-solutions (1.26, base 13
  carrying almost half), common to both conventions. Under `0^0 = 1` it
  weighs more because the parity rule removes the strings with an odd
  number of zeros.
- In even bases the gap between the conventions sits in one cell (one zero
  under `0^0 = 1`), and the shifted offsets show cells of the same size in
  other zero classes and in both conventions.
- Perturbed worlds show no gap between the conventions, so the model
  treats the zeros correctly. The true weights have a gap 2.5 standard
  errors above theirs. That part is specific to `x^x`, but it lands in
  different zero classes in odd and even bases.
- Perturbed worlds also show cell-to-cell deviations of 15% to 20%, and the
  clustered variance understates the spread of a world-level ratio by a
  factor of about 1.3 to 1.5.

With that factor, the `z = 3.0` of the excess becomes about 2.0 to 2.3,
and the convention gap about 1.7 to 2. So the answer to direction A1 is:
not established. The data do not need a third kind of correction, and the
excess does not sit in the zeros. A modest effect of `x^x` that separates
the conventions is not excluded; fresh bases (odd bases 27 to 41 with
strings) would decide it (question 140). The extra between-world
variance is a real finding and needs a cause (question 139).

## 34.2 Do near-solutions share the zero deficit? (question 94)

### 34.2.1 The expected zeros

Section 24.6.2 compared the zeros of the long solutions with a binomial law
`Bin(d-1, 1/b)`. The exact model of Proposition 34.1 gives the law of the
zero count of a solution of given base, length and convention, with the
length and the residue conditions in place.

Table 34.2.1.1 (computed, `r6q_zeros.py solutions`,
`data/r6q_zero_solutions.txt`). Solutions with at least `b - 6` digits,
bases 12 to 43 (`output/b2-41-*.txt`, `b43-*.txt`).

| `0^0` | bases | solutions | zeros | exact model | binomial | zero-free | model |
|---:|---|---:|---:|---|---|---:|---:|
| 0 | even | 19 | 10 | 16.7 +/- 4.0 | 16.8 | 11 | 7.7 |
| 0 | odd | 30 | 19 | 26.4 +/- 5.0 | 26.7 | 16 | 12.2 |
| 1 | even | 21 | 17 | 18.6 +/- 4.2 | 18.5 | 11 | 8.5 |
| 1 | odd | 25 | 18 | 15.7 +/- 5.0 | 16.0 | 16 | 17.6 |

Under `0^0 = 0`: 29 zeros against 43.1 +/- 6.4, `z = -2.2`. Base 43 adds
one odd solution. The exact law and the binomial agree within 0.3 digits.

The forced top digits. The lead of question 94 expected the forced top
digits to lower the binomial expectation by about 10%, since they are
rarely 0. The model with `t = 3` (`r6q_zeros.py top`, 400,000 strings per
length) says otherwise. Per near-solution, the expected zeros are 0.893
against 0.847 at `t = 0` in even bases under `0^0 = 0` (+5%), and 0.847
against 0.859 in odd bases (-1%). Section 24.6.2's "the forced top
digits account for 2 to 4 of the 13.5" is not supported by this
computation (section "Library corrections", item 3).

### 34.2.2 The near-solutions

Table 34.2.2.1 (computed, `r6q_zeros.py near`, `data/r6q_zero_near.txt`,
bases 12 to 26). Per near-solution event. The residual is the sum over
events of their zeros minus the model's mean zeros per near-solution in
their base, per offset; `z` uses the clustered variance of the residuals
(clusters of chapter 26).

| `0^0` | bases | near-solutions per offset | model | zeros per near-solution | model | residual `z` |
|---:|---|---:|---:|---:|---:|---:|
| 0 | even | 7.92 | 8.58 | 0.823 | 0.840 | -0.33 |
| 0 | odd | 16.38 | 14.83 | 0.720 | 0.849 | -3.11 |
| 1 | even | 9.27 | 8.61 | 0.842 | 0.842 | -0.09 |
| 1 | odd | 10.20 | 8.63 | 0.451 | 0.594 | -2.62 |

Without base 13 the odd rows give 0.757 against 0.860 (`z = -2.2`) and
0.494 against 0.609 (`z = -2.0`).

Answer (computed). The near-solutions have the zero rate of the model in
even bases, where the solutions under `0^0 = 0` have their larger shortfall
(10 against 16.7). In odd bases the near-solutions are short of zeros under
both conventions, but this is the zero-free surplus of Table 34.1.3.1 seen
from the other side: there are too many zero-free near-solutions, not too
few zeros in the others (the classes with zeros fit, 0.93 to 1.06). The
solutions under `0^0 = 1` in odd bases have no shortfall (18 against 15.7).
So the near-solutions do not confirm question 71 as a law of the zeros of
`F`. The even-base part of question 71 is chance (`z` about -1.7, with no
counterpart in thousands of near-solution digits). The odd-base part
(19 against 26.4, `z = -1.5`) has the same sign as the zero-free surplus,
which is itself within the between-world scatter of section 34.1.5.

## 34.3 The expected count is a trace (question 90)

### 34.3.1 The length matrix

Let `M_b` be the `b x b` matrix with `M_b[d, d'] = P(F(n) has d' digits)`
for `n` a uniform `d`-digit string (leading digit uniform on `1..b-1`).
`F(n) < b^b`, so `M_b` is stochastic (Proposition 15.1).

Proposition 34.5 (proved). (1) The basic model's expected count over the
lengths 2 to `b` (the count of `analysis/model.py`, which starts at length
2) is `tr M_b - M_b[1, 1]`. (2) `M_b[1, 1] = E_1 = N_1(b) / (b - 1)` with
`N_1(b) = #{x >= 1 : x^x < b}`. So `N_1(b) = 2` for `5 <= b <= 27`, 3 for
`28 <= b <= 256`, 4 for `257 <= b <= 3125`, and
`N_1(b) ~ ln b / ln ln b`.

Proof. (1) The diagonal entry `d` is `E_d` of section 5.1. (2) A 1-digit
string `x` has `F = x^x`, which has one digit exactly when `x^x < b`.

Length 1 is an artefact of the model: only `n = 1` is a 1-digit solution,
whatever `E_1` says. Its column is almost empty off the diagonal: a string
of length `d >= 2` has `F < b` only if every digit has `x^x < b`, which has
chance at most `((N_1(b) + 1)/b)^(d-1)`. So `E_1` is almost an eigenvalue of `M_b`: 0.0312 against
`E_1 = 0.0303` at `b = 100`, 0.0135 against 0.0134 at `b = 300`. This is
the "second eigenvalue about `3/b`" of the lead: it is `N_1(b)/(b-1)`, and
`N_1 = 3` for `28 <= b <= 256`.

### 34.3.2 The rows converge

Theorem 34.6 (proved). Fix `j, j' >= 0`. For `b >= b_0(j')` (the constant of
Theorem 29.1),

    | M_b[b - j, b - j'] - s_j' |  <=  ((j+1)(j'+1) + 1) / b  +  (j'+2) / floor(sqrt b)!.

So for each fixed `J` the `J x J` corner of `M_b` at the longest lengths
tends to the rank-one matrix whose rows all equal `(s_0, ..., s_(J-1))`.

Proof. The proof of Theorem 29.1 with the row and the column separated.
Lemma 29.4 localizes the event "F has `b - j'` digits" to the event
`A_j'` on `H`; its proof uses the length of the string only through the
bound `d <= b`. Lemma 29.3, applied to the `K = j' + 1` top counts of a
string of `b - j` digits, gives the total variation bound
`(1 + K + K j)/b = (1 + (j'+1)(j+1))/b`. Under the Poisson law `Q` the
chance of `A_j'` is `s_j'` whatever `j` is.

Corollary 34.7 (proved; question 81). The law of the length of `F` for a
string of `b - j` digits has the limit `(s_j')`, independent of `j`. The
length shares of section 5.2 are the diagonal of this limit, and the shares
add to 1 because the limit is a probability law. This is the reason behind
"one solution per base" that section 14.6.3 states in words.

### 34.3.3 The first correction is one eigenvalue

Proposition 34.8 (proved at the level of Proposition 29.7, whose expansion it
uses). (1) For fixed `j, j'`,

    M_b[b - j, b - j'] = s_j' + ( (j + 1) sigma_j' + a_j' ) / b + O(1/b^2),

where, with `A_j'` the set of `(y, k)` of section 29.1.1,

    sigma_j' = sum over (y, k) in A_j' of (e^-y / k!) (y - k),
    a_j'     = sum over (y, k) in A_j' of (e^-y / k!) (y k + k - k(k-1)/2 - y^2/2 - y).

(2) `sum sigma_j = sum a_j = 0`. (3) For every fixed `J`,

    sum over j < J of M_b[b - j, b - j] = sum over j < J of s_j + (1/b) sum over j < J of ((j+1) sigma_j + a_j) + O_J(1/b^2),

and the full sum of the coefficients is

    C = sum over j of j sigma_j = - d/dmu E_mu[J'] at mu = 1 = e/(e-1)^2 + 1/(2e) + sum over y >= 2 of e^-y sum over k > e^y of (k - y)/k!,

with `C = 1.104636`. Here `E_mu[J']` is the mean distance from `b` of the
length of `F` when the top counts are independent Poisson(`mu`)
variables: `J' = y_0 - [N_(b - y_0) > e^(y_0)]`, and `E_1[J'] = 1.5017`.

Proof. (1) The expansion in the sketch of Proposition 29.7 has
`delta_j(y, k) = (j+1)(y - k) + (y k + k - k(k-1)/2 - y^2/2 - y)`. The first
part comes from the length `n = b - j - 1` of the free part, the second
from the leading digit, the binomial-to-Poisson step and the weight
correction of Lemma 29.2, which do not depend on `j`. The column enters
only through the set `A_j'`. (2) Under the Poisson(`mu`) law the
probability of `(y_0, N) = (y, k)` is `e^(-mu y) mu^k / k!`, whose
derivative at `mu = 1` is `(e^-y / k!)(k - y)`. The `A_j` partition the
outcomes (proof of Corollary 29.6), so `sum s_j(mu) = 1` and
`sum sigma_j = -d/dmu 1 = 0`. The rows of `M_b` sum to 1, so the `1/b`
terms of each row sum to 0: `(j+1) sum sigma + sum a = 0`, hence
`sum a = 0`. (3) Sum (1) over the diagonal; `sum (j+1) sigma_j + a_j =
sum j sigma_j` by (2), and `sum j sigma_j = -d/dmu sum j s_j(mu)`. For the
closed form, `E_mu[y_0] = 1/(1 - e^-mu)`, whose derivative at 1 is
`-e/(e-1)^2`; the correction term is
`T(mu) = sum over y of e^(-mu y) sum over k > e^y of mu^k / k!`, and
`T'(1)` is the last two terms (for `y = 1`, `e^-1 sum over k >= 3 of
(k-1)/k! = e^-1 / 2`).

The uniformity in `j` needed to let `J` grow with `b` is not proved here.
Theorem 29.5 bounds the tail sum of `E_(b-j)` by `5.6 e^(-J/3)`, not by
`o(1/b)`. The exact computation closes the gap numerically:

Table 34.3.3.1 (computed, `r6q_trace.py table` and `rows`,
`data/r6q_trace_table.txt`, `r6q_trace_rows.txt`; exact up to a dropped
mass below `2 * 10^-11`; both conventions agree to 6 digits).

| `b` | `tr M_b` | `E_1` | `b (tr M_b - E_1 - 1)` | `b lambda_2`, lengths `>= 2` |
|---:|---:|---:|---:|---:|
| 10 | 1.5417 | 0.2222 | 3.195 | 2.30 |
| 20 | 1.2676 | 0.1053 | 3.246 | 1.52 |
| 40 | 1.1236 | 0.0769 | 1.869 | 1.34 |
| 100 | 1.0448 | 0.0303 | 1.446 | 1.20 |
| 200 | 1.0214 | 0.0151 | 1.260 | 1.14 |
| 300 | 1.0175 | 0.0134 | 1.229 | 1.14 |

Limit: `C = 1.105`. At small `b` the length-2 row adds about `(N_2/b)^2 b`.

Heuristic 34.9 (why one eigenvalue; checked by the last column of Table
34.3.3.1). To first order the corner of `M_b` is `1 u^T + (1/b) v sigma^T` with
`u = s + a/b` and `v_j = j + 1`. A rank-two matrix of this form has the
eigenvalues `u . 1 = 1` and `(sigma . v)/b = C/b`. So the whole first-order
excess of the trace is one eigenvalue, `C/b`, and it measures how much the
length of `F` follows the length of the string: a string with fewer digits
has fewer large digits, so `F` is a little shorter too. With length 1 the
trace is `1 + (N_1(b) b/(b-1) + C)/b + o(1/b)`, and `b (tr M_b - 1)` has no
limit.

### 34.3.4 The refined model: a sum over characters

Let `q = b - 1`, `e(x) = exp(2 pi i x)`, and for a character `t` of `Z/q`

    tau_t(b) = sum over d = 2..b of E[ 1{F(n) has d digits} e(t (F(n) - n)/q) ],

`n` a uniform `d`-digit string.

Proposition 34.10 (proved). The refined model's expected count over the
lengths 2 to `b` is `sum over t of tau_t(b)`. It is also the trace of the
class matrix of section 15.1.5 restricted to these lengths, and
`tau_0 = tr M_b - E_1`.

Proof. The `d`-digit numbers are `q b^(d-1)` consecutive integers, so
`n mod q` is exactly uniform. The refined count of length `d` is
`q P(F has d digits and F == n (mod q))`, which is the diagonal mass of
the class matrix in the `q` classes of length `d`, and orthogonality of
the characters writes it as the sum of the `tau_t`.

Corollary 34.11 (proved). For odd `b` and `0^0 = 0`, `tau_(q/2) = tau_0`
exactly, and the class matrix has two closed classes (the parities). This is
the only case where a nontrivial character is constant on `F(n) - n`
(Theorem 15.2). So the eigenvalue 1 has multiplicity 2 exactly in that
case, and the refined count is `2 tau_0` plus the other characters.

Theorem 34.12 (proved). For odd `b` and `0^0 = 1`, `tau_(q/2)(b) -> e^-2` as
`b -> infinity`.

Proof. For odd `b`, `n` is congruent to its digit sum modulo 2, and
`x^x == x (mod 2)` for `x >= 1`, so `F(n) - n == c_0(n) (mod 2)` and
`tau_(q/2) = sum over d of E[1{F has d digits} (-1)^(c_0)]`. For `d = b - j`
with `j` fixed, Lemma 29.4 localizes the length event to `A_j` on `H`, and
Lemma 29.3 with one more coordinate (the count of the digit 0, among the
`d - 1` free digits) couples the `K + 1` counts with independent Poisson(1)
variables within `(1 + (K+1)(j+1))/b`. Under the Poisson law `c_0` is
independent of `A_j`, and `E[(-1)^(c_0)] = e^-2`. So the term of length
`b - j` tends to `e^-2 s_j`. The terms with `j >= J` are bounded in
absolute value by the tail bound of Theorem 29.5, which tends to 0 as `J`
grows. Sum over `j` and use `sum s_j = 1`.

Conjecture 34.13. The other characters vanish in the limit:
`sum over t not in {0, q/2} of tau_t(b) -> 0`. Then the refined count tends
to 1 (even `b`), 2 (odd `b`, `0^0 = 0`) and `1 + e^-2` (odd `b`,
`0^0 = 1`), the table of section 5.3.

This needs equidistribution of `sum (w(x) - x)` modulo `q` with a relative
error, the strong form of Assumption R (Conjecture 29.18). The
anti-concentration of Theorem 30.5 is not enough.

Table 34.3.4.1 (computed, `r6q_trace.py refined`,
`data/r6q_refined_trace.txt`, bases 10 to 64, 80, 100, 128). The
decomposition of the refined count, lengths 2 to `b`.

| `b` | `0^0` | refined | `tau_0` | `tau_(q/2)` | other characters |
|---:|---:|---:|---:|---:|---:|
| 13 | 0 | 2.892 | 1.265 | 1.265 | +0.362 |
| 13 | 1 | 1.731 | 1.265 | 0.267 | +0.200 |
| 25 | 0 | 2.404 | 1.107 | 1.107 | +0.191 |
| 31 | 1 | 1.228 | 1.071 | 0.172 | -0.015 |
| 43 | 0 | 2.173 | 1.042 | 1.042 | +0.089 |
| 63 | 1 | 1.166 | 1.026 | 0.149 | -0.009 |
| 64 | 0 | 1.087 | 1.025 | | +0.062 |
| 100 | 0 | 1.014 | 1.015 | | -0.001 |
| 128 | 1 | 1.025 | 1.011 | | +0.014 |

Over all bases 10 to 64 the other characters add -0.23 to +0.36, and at
most 0.11 in absolute value for `b > 25`. The ratio `tau_(q/2) / tau_0`
under `0^0 = 1` is 0.211 at `b = 13`, 0.145 at `b = 63`, against
`(1 - 2/b)^(b-2)`, which tends to `e^-2 = 0.135`. The largest values of
the other characters occur at `b` = 13, 11, 25, 22, 29, 14, 37 and 43. I
found no simple rule for them (question 142).

The lead's other claims, in this language. The parity doubling is the
multiplicity 2 of Corollary 34.11, and `1 + e^-2` is Theorem 34.12. The factor
`q^k(B)` of Theorem 21.6 should be the multiplicity of the eigenvalue 1 in
`F_q[T]` in the same way; I have not written that proof.

## 34.4 A ledger of P values (question 103)

### 34.4.1 The ledger

`data/r6q_ledger_raw.tsv` lists 241 statements of chapters 3 to 32 that
compare data with the model: the section, the world, the test, the counts,
the statistic as printed, a two-sided P value (a one-sided P doubled, a
`z` converted), the direction (excess, deficit, fit), a key for the data it
uses, whether the hypothesis was named before the data were seen, and
whether a later chapter superseded it. 221 rows are current; 133 of them
have a P value. For tests named in advance that print only a count and a
mean, `r6q_ledger.py` adds a two-sided Poisson P (14 rows). A reading
agent built the ledger; the rows marked "unclear" in the column `prereg`
(33 of 56 groups) are judgment calls.

Tests that share data are merged into 56 groups, in two ways: the smallest
P of the group with the Sidak correction `1 - (1 - p)^k`, and the first
test listed in the group.

### 34.4.2 Results

Table 34.4.2.1 (computed, `r6q_ledger.py`, `data/r6q_ledger_report.txt`; the
Sidak merge, the primary merge in brackets).

| set | groups | below 0.01 | below 0.05 | expected below 0.05 | median | Fisher P |
|---|---:|---:|---:|---:|---:|---:|
| all | 56 | 3 (4) | 14 (14) | 2.8 | 0.23 | `2 * 10^-9` |
| named in advance | 12 | 0 (0) | 0 (0) | 0.6 | 0.59 | 0.74 (0.66) |
| not named in advance, or unclear | 44 | 3 (4) | 14 (14) | 2.2 | 0.18 | `3 * 10^-11` |
| without `F_q[T]` and the factorial system | 40 | 1 (2) | 8 (8) | 2.0 | 0.24 | `2 * 10^-4` |
| integers only | 9 | 1 (1) | 3 (3) | 0.45 | 0.23 | 0.005 |

The 14 groups below 0.05: the `F_q[T]` census (6 groups; the model fails
there, chapter 24); the empty bases `== 3 (mod 8)` (a pattern chosen after
the data, broken by base 43); the negative-base offsets that keep the last
digit (section 23.2); the narcissistic 6-digit excess in even bases
(19.4.3); the 5-digit window (22.4); the odd-base factorions (17.4); the
zero digits of question 71 (24.6.2); the `b-1`-digit excess of section 5.5;
the Pisot class (26.6); the 12% excess (23.5). Each is already named in the
library as an anomaly, a selected pattern or a known failure.

Heuristic 34.14. The P values of the library are not uniform, and the cause
is selection, not a hidden flaw.

- The 12 groups named in advance (fresh bases 39 to 44 and -36 to -38,
  the forced and shifted weights of chapter 17, fresh factorion bases 37 to
  47, base 18 for 2-cycles) look like uniform draws: KS P = 0.56, none
  below 0.1. With 12 groups this rules out only gross flaws, such as a
  model that is 30% off in every world.
- If each reported group were the smallest of `k` looks, the share below
  0.05 (14 of 56) needs `k` about 6, and the median (0.23) needs `k` about
  3. The lower tail is heavier than any single `k` gives: a few groups are
  real failures (`F_q[T]`, factorial system), the rest look like modest
  selection.
- There is no lean toward deficits at `D = 0`. Among the 25 groups with
  P < 0.2, 17 are excesses and 8 deficits; among all 44 directional
  groups, 27 and 17. The common ratio 0.91 of section 26.5 comes from the
  negative, rational and 2-cycle worlds, each about one standard deviation
  low, and does not show in the ledger as a whole.
- Dependence. The integer groups share data across the two conventions
  (Table 34.5.1.1: correlation +0.78 in one base), and several groups reuse
  the same bases. The Fisher P values above treat the groups as
  independent and so overstate the evidence; the conclusion does not
  depend on them, since the named-in-advance set is clean and the rest is
  explained by selection.

So the answer to the question: the "chance" verdicts of the library cannot
be closed all at once by a uniformity test, because the ledger is
dominated by tests chosen after the data. The tests that were named in
advance agree with the model. The cheapest way to strengthen this is more
of them (question 104).

## 34.5 Are neighbouring bases independent? (question 106)

### 34.5.1 Correlation of the residuals

`r6q_neighbors.py residuals`. For each base 12 to 32 and convention, the
standardized residual `(lambda - model) / se`, with the clustered standard
error (bases 12 to 26) or the sample one times `sqrt(2.1)` (bases 27 to
32). The parity means are removed, since the parities alternate. The null
law permutes the residuals within each parity class (20,000 draws).

Table 34.5.1.1 (computed, `data/r6q_neighbors.txt`).

| model | `0^0` | lag-1 correlation | permutation P | lag 2 |
|---|---:|---:|---:|---:|
| `t = 0` | 0 | -0.31 | 0.060 | +0.05 |
| `t = 0` | 1 | -0.41 | 0.067 | -0.02 |
| `t = 3` | 0 | -0.09 | 0.65 | -0.10 |
| `t = 3` | 1 | -0.17 | 0.46 | -0.09 |
| | same base, `0^0 = 0` against `0^0 = 1` | +0.85 (`t = 0`), +0.78 (`t = 3`) | | |

The negative lag-1 correlation without the forced digits goes away with
them: it was the top-digit factor, which varies smoothly with `b` and which
the model now carries. With 20 pairs the null standard deviation is 0.19 to
0.22, so the test excludes only correlations above about 0.4.

The two conventions in one base are strongly correlated, because the
zero-free near-solutions are common to both (Lemma 34.2). Any pooled test
that adds the two conventions as independent counts overstates its
precision; Table 26.5.1 does this for the integers ("both conventions").

### 34.5.2 Shared multisets

`S(c)` does not depend on the base. A multiset with largest digit `X` is a
candidate in every base above `X`, so dependence between bases could come
from one multiset that is a near-solution in two of them.

Computed (`r6q_neighbors.py shared`). Among 906 (`0^0 = 0`) and 716
(`0^0 = 1`) distinct near-solution multisets of bases 12 to 26, none is a
near-solution (at any of the 61 offsets) in a second base. Under
independence the expected number is 0.020 and 0.007 for neighbours, 0.028
and 0.013 for any two bases. Among the solutions of bases 2 to 43 the only
multisets that solve two bases are `(1, 3)` (bases 9 and 25) and
`(0, 1, 3)` (bases 4 and 5, `0^0 = 0`).

The joint law of the top digits. For random multisets of `b - 1` and `b - 2`
digits whose sum has the same length in bases `b` and `b + 1` (13% to 56%
of the candidates in base `b`), the forced-top factors of section 23.5
(`t = 3`) in the two bases have correlation between -0.033 and +0.044
(`b` = 12, 16, 20, 24, 30, 20,000 multisets each), and the ratio
`E[f_b f_(b+1)] / (E f_b E f_(b+1))` is 0.70 to 1.43 with no consistent
sign (`r6q_neighbors.py top`).

Heuristic 34.15. For the second Borel-Cantelli lemma in the form of
Kochen and Stone, it is enough that
`sum over b != b' <= B of P(A_b and A_b')` is at most
`(1 + o(1)) (sum over b <= B of P(A_b))^2`. Within the model, the only
link between two bases is a multiset that is a candidate in both. Its
contribution is at most `kappa max_c p_(b')(c) E_b`, where `kappa` is the
largest joint top-digit factor (below `b^3`). Each single multiset has a
chance of at most about `d! / b^(d-1)`, of order `b^(3/2) e^-b` for
`d = b`, so this term is negligible against `E_b E_(b')`. So the
second half of Conjecture 10.3 needs no more independence than the model
already has, and the data show no dependence: no shared multisets, no
correlated top digits, no neighbour correlation once the top digits are
modelled. This is a test of the model's assumption, not a proof for the
true weights.

## Library corrections

Items 1 to 7 now have a note in the chapter or question they correct.

1. The summary and section 17.4 of `17-weights.md`, and the summary row of
   question 57 and section 19.5.3 of `19-sieve-spectra.md`, still give the
   factorion shortfall "a combined P of about 0.05". Section 23.5 (update) and Table
   26.4.1 revise it to about 0.09. Found by the ledger agent; checked.
2. Section 21.4 (update) and the summary of chapter 26 (question 74): "even `j` carry 1.4 to 2.4 times as many near-solutions as odd `j`".
   The table of section 26.6.2 gives ratios 1.68, 1.48, 1.49 and 2.36, so
   1.5 to 2.4.
3. `24-ffield-gap.md`, section 24.6.2: "The forced top digits account for 2
   to 4 of the 13.5" missing zeros. With the top three digits forced, the
   expected zeros per near-solution rise by 5% in even bases and fall by
   1% in odd bases (section 34.2.1), so they account for none of it. The text
   seems to have used Heuristic 24.17 (zeros of `S(c)` for random `c`),
   which is a different quantity from the zeros of `c` given that `c` is a
   solution.
4. `questions-round6.md`, question 90 and direction A1: "the second
   eigenvalue near `3/b`" and "`b (tr M - 1)` is 5.5, 5.6, 5.0 and 4.7" use
   the trace over lengths 1 to `b`. The length-1 entry is `N_1(b)/(b-1)`
   (Proposition 34.5), which is the second eigenvalue and makes
   `b (tr M - 1)` grow like `ln b / ln ln b`. Over lengths 2 to `b`, the
   count the library uses, `b (tr - 1)` tends to `C = 1.105`.
5. `questions-round6.md`, question 94 (lead): the forced top digits do not
   lower the expected zeros by about 10% (section 34.2.1).
6. `questions-round6.md`, question 93 (lead): "even bases have 177 distinct
   multisets with zeros ... 217 under `0^0 = 1`" counts multisets in each
   convention separately; by Lemma 34.3 those of `0^0 = 1` are `0^0 = 0`
   near-solutions at other offsets, so the two numbers are not counts of
   the same events. The comparison needs the model per zero class, as in
   Table 34.1.3.1.
7. Table 26.5.1, row "integers, 12 to 32, both conventions": the two
   conventions are added as independent, but their residuals correlate at
   +0.78 (Table 34.5.1.1). The `z` of that row is too large by a factor of
   about 1.3; the conclusion of section 26.5 does not change.
8. The ledger agent reported smaller inconsistencies, not checked one by
   one: the old P values of the factorion row of Table 26.4.1 (0.0026,
   0.014) are not those of section 17.4 (0.002, 0.009, which are against
   model means, not offset means); section 23.5 says base 19 is "about 4.5
   standard errors low" where Table 26.4.1 gives 4.6 and the printed
   numbers give 4.8; section 11.2a uses 20 degrees of freedom for the
   chi-square that chapters 23 and 26 give on 21 bases; the 8-digit
   expectation of section 22.4.4 (1.35) differs from the table of 22.4.1
   (1.13).

## Files

| file | contents |
|---|---|
| `analysis/r6q_lib.py` | exact refined model by zero class (Proposition 34.1), the weights of `fast --perturb`, the reader of near-solution files |
| `analysis/r6q_trace.py` | exact length matrix, trace, spectrum, `c_j` and `C`, the character decomposition (section 34.3) |
| `analysis/data/r6q_trace_table.txt`, `r6q_trace_rows.txt`, `r6q_refined_trace.txt` | its outputs (Tables 34.3.3.1, 34.3.4.1) |
| `analysis/r6q_offsets.py` | near-solutions at `D = 2j(b-1) + c` |
| `analysis/data/r6q_shift_c1.txt`, `r6q_shift_c2.txt` | its runs, bases 12 to 26, 60 offsets |
| `analysis/data/r6q_pert_s1.txt` .. `r6q_pert_s5.txt` | near-solutions in perturbed worlds (`r5e_int_offsets.py ... --perturb s`) |
| `analysis/r6q_zeros.py` | zero classes: exact and forced-top models, comparisons, the zero tests of question 94, the summary |
| `analysis/data/r6q_zero_model.txt`, `r6q_zero_top.txt` | model by zero class (exact; `t = 0..3` sampled) |
| `analysis/data/r6q_zero_classes.txt`, `r6q_zero_summary.txt`, `r6q_zero_near.txt`, `r6q_zero_solutions.txt` | comparisons (Tables 34.1.3.1 to 34.2.2.1) |
| `analysis/r6q_neighbors.py` | residual correlations, shared multisets, joint top digits (section 34.5) |
| `analysis/data/r6q_neighbors.txt` | its output |
| `analysis/r6q_ledger.py` | merging, uniformity and Fisher tests of the ledger |
| `analysis/data/r6q_ledger_raw.tsv`, `r6q_ledger_report.txt` | the ledger and the report (Table 34.4.2.1) |

## New questions

These are questions 139 to 143 of `questions.md`.

1. Between-world variance. In perturbed worlds the ratio `lambda / model`
   of one parity and convention ranges from 0.84 to 1.16 across seeds even
   with the top digits forced, 1.3 to 1.5 times the clustered sampling
   error. What carries this variance? Candidates: the short lengths of
   small bases (base 13 alone moves the odd zero-free cell by 0.1), the
   fourth and later top digits, and the low digits of `F` modulo `b`. Once known, it fixes the error bar of
   every world-level ratio in the library.
2. The zero-free surplus in odd bases. Zero-free near-solutions in odd bases
   12 to 26 are 1.26 times the model (1.17 without base 13). Does it hold
   in odd bases 27 to 41 (a rerun of `r5e_int_offsets.py` with strings),
   and is it a local factor of short lengths, as section 11.4 has for short
   solutions?
3. Uniform first-order trace. Prove `tr M_b - E_1 = 1 + C/b + o(1/b)` by
   bounding `|E_(b-j) - s_j - c_j/b|` uniformly for `j <= C' ln b`, which
   with Theorem 29.5 would finish Proposition 34.8.
4. The other characters. Which property of `b - 1` makes
   `sum over t not in {0, q/2} of tau_t(b)` large (0.36 at `b = 13`, 0.19 at
   25, 0.06 at 64)? Is it bounded by a function of the largest power of 2
   and 3 dividing `b - 1`?
5. A pre-registered ledger. Write down, before the runs of question 104,
   the model's prediction and a two-sided test for every group of Table
   4.2.1 that can be extended to fresh bases, and add the results to the
   named-in-advance set.
