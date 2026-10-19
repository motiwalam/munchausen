# Round 6 census: fresh data in bases 42 to 46

DRAFT. This file answers questions 104, 105, 95, 107 and 110 of
`questions-round6.md`. Section 1 holds the predictions. I wrote it and
committed it before any search of bases 42, 45 and 46, and before the
exact search of base 44, so that the git history dates the predictions
before the data. The later sections hold the runs, the comparison and the
smaller questions. Each statement is marked proven (a proof is here),
computed (an exact computation, with its range) or heuristic (the model,
or a judgment from data).

## 1. Predictions (written before the runs)

### 1.1 What was known before

- Bases 2 to 41 and 43 are searched exactly (`output/`).
- Base 44 was searched with `--deficit 2 --band 2.5` (section 9.3,
  `analysis/data/b44-inexact.txt`). That run found one solution under
  `0^0 = 1`, with 43 digits and two zeros, and none under `0^0 = 0`. The
  rules miss about 15% of solutions at this size. So base 44 is not empty,
  and its counts are not fresh data. Section 1.5 separates them.
- Bases 42, 45 and 46 have never been searched, exactly or not. I ran no
  search of them before this commit.

### 1.2 The model

`analysis/r6c_predict.py` draws, for every length `d` from `b - 14` to `b`,
one million random `d`-digit multisets (seed 104). A multiset counts under
convention `m` if its sum has `d` digits and meets the identity modulo
`b - 1` (the refined model, section 5.3). Each counted multiset then gets
the weight of `analysis/r2c_top_model.py`: the chance that it holds the top
three digits of its own sum, over the uniform chance (the forced top
digits, sections 11.2 and 23.5). This is "t = 3" below; "t = 0" is the
refined model. The output is `analysis/data/r6c_predict_census.txt`, and
`analysis/r6c_summary.py` turns it into the tables. The sampling error of
each total is about 0.02.

The model leaves out lengths below `b - 14` (below `10^-4` per length in
the model) and the identity families of chapters 2, 22 and 25. None of the
families of chapter 2 applies: 42, 44, 45 and 46 are not perfect powers.
Bases 39 to 43 had no solution shorter than `b - 3` digits.

The calibrated variant multiplies the counts under `0^0 = 1` by 1.12, the
ratio of the near-solution rate to the model in bases 12 to 32
(section 11.2a). Under `0^0 = 0` that ratio is 0.98, and I keep the model.

### 1.3 Expected counts

Table 1.3 (heuristic, the model with t = 3). Expected nontrivial
solutions by length class. "Zero-free" counts the solutions without a
zero, which are solutions under both conventions.

| base | `0^0` | `b` | `b-1` | `b-2` | `b-3` | `<= b-4` | total | calibrated | zero-free | mean zeros | P(none) |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 42 | 0 | 0.065 | 0.566 | 0.213 | 0.077 | 0.051 | 0.97 | | 0.36 | 0.97 | 0.38 |
| 42 | 1 | 0.071 | 0.557 | 0.216 | 0.075 | 0.056 | 0.98 | 1.09 | 0.36 | 0.99 | 0.38 |
| 44 | 0 | 0.066 | 0.566 | 0.248 | 0.091 | 0.051 | 1.02 | | 0.39 | 0.94 | 0.36 |
| 44 | 1 | 0.066 | 0.548 | 0.239 | 0.085 | 0.062 | 1.00 | 1.12 | 0.39 | 0.93 | 0.37 |
| 45 | 0 | 0.140 | 1.085 | 0.493 | 0.172 | 0.082 | 1.97 | | 0.79 | 0.90 | 0.14 |
| 45 | 1 | 0.077 | 0.636 | 0.288 | 0.102 | 0.037 | 1.14 | 1.28 | 0.79 | 0.66 | 0.32 |
| 46 | 0 | 0.071 | 0.572 | 0.249 | 0.096 | 0.073 | 1.06 | | 0.36 | 1.05 | 0.35 |
| 46 | 1 | 0.068 | 0.566 | 0.248 | 0.096 | 0.081 | 1.06 | 1.19 | 0.36 | 1.03 | 0.35 |

The refined model without the top digits (t = 0) gives totals 1.03, 1.03,
1.05, 1.05, 2.07, 1.19, 1.05 and 1.08 in the same order. The top digits
lower the totals by 1% to 6%, and the `b`-digit class by 10% to 20%.

Base 45 is the only odd base. Its expectation under `0^0 = 0` is twice
the others, from the parity factor of section 5.3, and under `0^0 = 1` it
is 1.14 times, the factor `1 + e^-2`. The most likely length is `b - 1` in
every base and convention (55% to 56% of the total).

Totals over the four bases (heuristic, Poisson, 90% interval):

| `0^0` | expected | 90% interval | calibrated |
|---:|---:|---:|---:|
| 0 | 5.03 | 2 to 9 | 5.03 |
| 1 | 4.18 | 1 to 8 | 4.68 |

### 1.4 Empty bases

A base is empty if it has no nontrivial solution under either convention.
With `E_s` the zero-free part, `P(empty) = exp(-(E_0 + E_1 - E_s))`
(section 9.7).

| base | `E_0 + E_1 - E_s` | P(empty) | calibrated |
|---:|---:|---:|---:|
| 42 | 1.59 | 0.21 | 0.18 |
| 44 | 1.63 | 0.20, but 0 after section 9.3 | |
| 45 | 2.32 | 0.10 | 0.09 |
| 46 | 1.76 | 0.17 | 0.15 |

Expected number of empty bases among 42, 45 and 46: 0.48 (calibrated
0.42). Section 9.7 found no empty even base in 10 to 41 (P = 0.057). If
the even-base deficit is real, 42 and 46 are both non-empty; the model
gives that chance `0.79 * 0.83 = 0.66`.

Base 44 under `0^0 = 0`: given that the inexact run found nothing, the
chance of no solution is `exp(-1.02) / exp(-0.85 * 1.02) = 0.86`.

### 1.5 Lengths `b` and `b - 1`

Sums over bases 42, 44, 45 and 46 (heuristic):

| class | `0^0` | expected | P(none) |
|---|---:|---:|---:|
| `b` digits | 0 | 0.34 | 0.71 |
| `b` digits | 1 | 0.28 | 0.75 |
| `b - 1` digits | 0 | 2.79 | 0.06 |
| `b - 1` digits | 1 | 2.31 | 0.10 |

A `b`-digit solution under `0^0 = 1` in one of these bases would refute
the conjecture of section 7.1. The model gives this a chance of 25%.

Section 5.5 found more `(b-1)`-digit solutions under `0^0 = 1` than the
model expects: 27 against 17.3 in bases 10 to 38 (ratio 1.56), and 5
against 2.45 in bases 39 to 43. If that excess is a real effect of about
1.5 to 2 times, the four bases hold 3.5 to 4.6 such solutions instead of
2.3.

Fresh data only (base 44 counts with its share missed by the inexact run,
0.15 of the model):

| `0^0` | fresh expected | 90% interval | calibrated |
|---:|---:|---:|---:|
| 0 | 4.16 | 1 to 8 | 4.16 |
| 1 | 3.33 | 1 to 7 | 3.73 |

### 1.6 Zeros

The model gives a solution about one zero on average (0.66 to 1.05 by
base and convention). The zero-free share is 34% to 38% of the expected count
under `0^0 = 0` in the even bases and 40% in base 45. Question 71 found
too few zeros in the long solutions under `0^0 = 0`. The fresh solutions
add a few data points to it.

### 1.7 The tests, fixed in advance

1. The total per convention against Table 1.3, over the fresh data, with a
   Poisson P value in each direction.
2. The `(b-1)`-digit class under `0^0 = 1` against 2.31 (one-sided, for an
   excess, as section 5.5 asks).
3. The number of empty bases among 42, 45 and 46 against 0.48.
4. The 12% excess under `0^0 = 1`: the likelihood ratio of the calibrated
   variant against the model. With about 3.5 expected events this test is
   weak. A ratio of 1.12 changes the expected count by 0.4, so no result of
   this census can decide it alone.
5. The mean number of zeros against section 1.6.

The near-solution rate of question 104 is not part of this census. The GPU
path does not take `--offset`, and each offset costs a full CPU search of
the base.

### 1.8 Question 105: `b`-digit solutions under `0^0 = 1`

`analysis/r6c_predict.py bdigit 42 60` (two million multisets per base,
seed 105) gives the expected number of `b`-digit solutions, model with
t = 3:

| base | 46 | 47 | 48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `0^0 = 1` | 0.063 | 0.083 | 0.083 | 0.093 | 0.067 | 0.120 | 0.068 | 0.076 | 0.070 | 0.085 | 0.078 |
| `0^0 = 0` | 0.061 | 0.142 | 0.076 | 0.166 | 0.064 | 0.215 | 0.070 | 0.131 | 0.070 | 0.147 | 0.072 |

The census covers base 46 exactly. The runs of question 105 use
`--min-digits b -m 1 --zscore 3.4 --zlaw cond`, which misses about 2% of
the model's solutions over all lengths, maybe more at length `b`.
Bases 47 to 52 expect 0.51 under `0^0 = 1` (P(at least one) = 0.40), and
bases 47 to 55 expect 0.74 (P = 0.52). Base 51 has the largest expectation:
`b - 1 = 50` is even, and the top-digit factor is 1.33 there.

### 1.9 Plan and time

On the test laptop, under a load of about 11 from other jobs, `fast search
34 --hybrid -j 6` took 12.4 s, `--gpu` 18.5 s and the CPU alone on 6
threads 48.2 s. So I use `--hybrid -j 6`. At 1.89 per base this gives about
0.6, 2.0, 3.8 and 7.2 hours for bases 42, 44, 45 and 46, 14 hours in all.
The node estimate of section 9.3 for base 44 (`5.5 * 10^11` before the
residue rule) suggests up to 1.3 times more. The GPU path does not take
`--journal`, so `analysis/r6c_census.sh` splits each base into shards
(`--shard i/n --shard-by size`) and runs them one after another. A shard
that finished is skipped on a restart.
