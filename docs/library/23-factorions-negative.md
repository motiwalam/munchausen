# 23. Factorions, empty negative bases, cycles and scatter

This chapter answers questions 41, 42, 35, 43 and 44. Each claim is marked proven (a proof is here), computed (an
exhaustive computation, with its range) or heuristic (the probabilistic
model, or a judgment from data).

## Summary

| question | answer | status |
|---|---|---|
| 41, factorions in odd bases | Base 47 has one long factorion per convention against 1.05 expected. Fresh odd bases 37 to 47 have 3 per convention against 6.2. Near-factorions at offsets that keep every residue up to `b+1` and mod `b^3` are normal (7.8 to 8.3 against 8.5 in bases 21 to 35), while `D = 0` has 1 and 2. No mechanism found; the census is confirmed by a second engine and by brute force. | computed; verdict open, likely chance |
| 42, empty negative bases | -36 and -37 have solutions, -38 is empty. Multiples of 3 from -12 to -36: 3 empty of 9 against 1.15 expected (P = 0.095); other bases 3 of 20 against 2.44. Near-solution rates of the multiples of 3 are normal, also at offsets that keep `n mod 3`, and the last-digit factor mod 3 is 1.000. | computed, heuristic: chance |
| 35, 2-cycles in even bases | Base 18 has one 2-cycle under `0^0 = 0`. Even bases 4 to 18: 2 against 4.0. Near-2-cycles `F(F(n)) = n - j(b-1)` give 5.3 per offset, so these bases have the normal rate of the coincidence. No second invariant. | computed, heuristic: chance |
| 43, lengths in base -1+i | Positive integers have exactly the lengths `== 1, 4 (mod 8)`: integers are base -4 numbers written in blocks of four digits. The census of base -1+i is complete. | proven |
| 44, per-base scatter | Forcing the top 3 or 4 digits of `F` lowers the chi-square of `lambda / model` from 97 to 60 (`0^0 = 0`) and from 96 to 72 (`0^0 = 1`) on 21 bases. The rest sits in a few bases (13, 19, 16, 20) and in a uniform 12% excess under `0^0 = 1`. | computed, heuristic |

## 23.1 Long factorions in odd bases (question 41)

Setting. `F(n)` is the sum of `x!` over the base-`b` digits, with `w(0) = 0`
(`m = 0`) or `w(0) = 0! = 1` (`m = 1`). `L(b)` is the length of `(b-1)!`,
and a factorion is long if it has at least `L(b) - 5` digits. The engine is
`fast search --factorial` of branch q-weights (commit 2e67477), built in
`fast/target/qweights` and run with `--journal`. The model is the refined
model of that branch (`analysis/r2c_wgt_model.py`, a copy).

### 23.1.1 New bases (computed)

Bases 10 to 45 were done on branch q-weights
(`analysis/data/r2c_qw_factorial*.txt`). Base 47 is new:

| base | time | nodes | long factorions, `m = 0` | `m = 1` | model, `m = 0`, `m = 1` |
|---:|---:|---:|---|---|---:|
| 43 | 290 s, 3 threads | `5.2 * 10^9` | one, 30 digits, zero-free | the same | 0.98, 1.01 |
| 45 | 1148 s, 3 threads | | none | none | 1.07, 1.07 |
| 47 | 6292 s, 2 threads | `5.4 * 10^10` | one, 34 digits | another, 34 digits | 1.05, 1.06 |

The two 34-digit factorions of base 47 (`analysis/data/r2c_fact47_raw.txt`):

    m = 0: (7,43,14,26,45,17,6,35,16,16,6,1,38,18,38,6,38,36,22,0,3,40,28,25,34,19,37,42,35,35,1,35,38,20)
    m = 1: (8,12,30,39,40,11,0,11,34,18,18,22,18,45,10,7,24,2,5,16,4,10,22,34,2,0,14,44,23,34,40,28,31,44)

`L(47) = 35`, so both are one digit short of the top length. Base 49 was
not run: at the rate of base 47 it needs about 6 hours on 2 threads. Its
journal setup is in `fast/target/r2c/queue_b.sh`.

The odd bases after the range 14 to 36 in which the shortfall was seen
(37, 39, 41, 43, 45, 47) have 3 long factorions per convention against 6.2
in the model (computed). `P(X <= 3) = 0.13` for a Poisson count with mean
6.2 (heuristic). The fresh data lean toward the shortfall (0.5 times the
model) but do not decide between it and chance.

### 23.1.2 The census is right (computed)

- `worlds lanes B fact0`, a new weight table in the independent engine
  `fast/src/bin/worlds.rs`, finds the same `m = 0` factorions as
  `fast search` in every base 10 to 35. `worlds brute` agrees for 10 to 20
  (`analysis/data/r2c_fact0_check.txt`).
- For `m = 1`, the census of chapter 14 (`worlds lanes fact`) and that of
  `fast search` agree in every base 10 to 41, and `worlds brute fact`
  agrees for 16 to 20.

So the shortfall is not an engine error.

### 23.1.3 Offsets that keep more residues (computed)

Section 11.1 calibrates each base with near-solutions `n = F(n) + D`. The
offsets `D = j (b-1)` keep only the residue mod `b-1`. If the shortfall came
from a congruence, offsets that keep that residue too should share it.
`analysis/r2c_fact_offsets.py` counts long near-factorions for `j = 1..30`
in five families. Mean count per offset, summed over the odd bases 21 to
35, against `D = 0` (`analysis/r2c_fact_compare.py`):

| family | keeps `n - F(n) == 0` modulo | `m = 0` | `m = 1` |
|---|---|---:|---:|
| `D = 0` (the solutions) | everything | 1 | 2 |
| model | | 8.52 | 8.37 |
| `j (b-1)` | `b-1` | 8.33 | 8.37 |
| `j b (b-1)` | `b-1`, `b` | 8.17 | 8.13 |
| `j b^2 (b-1)` | `b-1`, `b^2` | 8.13 | 8.20 |
| `j b^3 (b-1)` | `b-1`, `b^3` | 7.80 | 8.20 |
| `j b^2 lcm(1..b+1)` | every integer up to `b+1`, and `b^3` | 8.23 | 7.83 |

Over the odd bases 15 to 35 the first four families give 10.6 to 11.8 per
offset for both conventions (model 11.9 and 11.8), while `D = 0` gives 3
and 4. The group total over the bases, per offset, has variance close to its
mean (7.9 to 16.8 for means 10.6 to 11.7), so it behaves like a Poisson
count. Of 240 offset draws (4 families, 30 offsets, 2 conventions), one is
at most as low as `D = 0`.

What this rules out (computed, with the reasoning heuristic):

- The residue mod `b`, the last digit, and the low digits mod `b^2` and
  `b^3`. For `x!` the last digits of `F` depend only on the small digits,
  and the offsets that keep them show no shortfall.
- Any congruence to a modulus up to `b+1`: the `lcm` family keeps all of
  them at once.
- The forced top digits of section 11.2. At the lengths that carry the
  count (`L(b) - 1` and up) every offset is below `10^-3 n`, so all offsets
  share the top digits of `D = 0`.
- Twins. For `x!`, `w(x) = x` for `x = 0, 1, 2` under `m = 0`, so solutions
  ending in 0, 1, 2 come in triples, and in pairs (1, 2) under `m = 1`. This
  holds for every offset alike. It makes counts clump, but the offset totals
  show little overdispersion.

The deficit sits mostly at the top length `L(b)`, in both parities. Bases
14 to 36, solutions with `L(b)` digits: `D = 0` has 0, 1 (odd, `m = 0, 1`)
and 2, 3 (even); the offsets `j b (b-1)` give 4.1, 3.7, 4.5 and 5.0 per
offset. Even bases make up for it with 11 solutions at `L(b) - 1` against
6.2 at the offsets, so their total is normal.

Verdict (heuristic). A mechanism would have to separate `D = 0` from every
small offset that keeps all residues up to `b+1` and mod `b^3`. By Proposition
10.2 the only residue of `n` that the digit multiset fixes is `n mod (b-1)`;
any other modulus acts through the low digits (powers of `b`, covered up to
`b^3`) or through the arrangement, which a fixed multiset does not control. I
see no candidate. The in-sample shortfall has P about 0.005 per convention
against the offsets' calibration, between the 0.002 of section 17.4 (against
the refined model) and the 0.006 of section 19.5 (against the narrow offsets).
After the choice among about 16 groups it is about 0.05 to 0.1, and the fresh
bases add P = 0.13. Fisher's combination gives about 0.05. This supersedes the
values of sections 17.4 and 19.5. I count it as an unexplained fluctuation.
Base 49 (expected 1.1 per convention) would add little; ten more odd bases
would.

Update (chapter 33). Chapter 33 excludes factorions by local arguments:
`x!` is divisible by every prime up to `x`, so a 3-digit string with one
large digit `x` must make a fixed quadratic expression a square modulo all
these primes (Lemma 33.2). This works for a string with one dominant digit,
across all bases. A long factorion has many digits of comparable size, and
section 33.3.3 notes that such strings are outside every method there. So
chapter 33 does not explain the shortfall of this section.

## 23.2 Empty negative bases (question 42)

### 23.2.1 Census of -36 and -37 (computed)

`worlds lanes` gets `--shard i/n`, which searches the `i`-th of `n` parts
of the parallel front; output is unchanged without it. The script
`analysis/r2c_nega_run.py` runs one base in units (one per length, the long
lengths cut into 48 shards) and appends each finished unit to a file, so a
run survives interruptions. Shards were checked against full runs for -20,
-24, -27 and -28.

| base | `0^0 = 1` | lengths | `E_1` | `0^0 = 0` | lengths | `E_0` | time (2 threads, per convention) |
|---:|---:|---|---:|---:|---|---:|---:|
| -36 | 3 | 33, 35, 35 | 1.06 | 1 | 35 | 1.06 | 1087 s |
| -37 | 1 | 37 | 1.18 | 1 | 37 | 2.08 | 1679 s |
| -38 | 0 | | 1.04 | 0 | | 1.04 | 4498 s; 4932 s (2 and 1 to 3 threads) |

(`analysis/data/r2c_negabase_census_36_41.txt`; models for -37 to -41 in
`analysis/data/r2c_negamodel_37_41.txt`.) The 37-digit solution of -37 has
no zero, so it counts in both conventions. In base -36 the solution
`(27,0,6,...,1,7,2)` under `0^0 = 0` and `(27,0,6,...,1,7,1)` under
`0^0 = 1` are partners:

Remark (proven). If `n` is a solution under `0^0 = 0`, ends in the digit 2
and has exactly two zeros, then `n - 1` (last digit 1) is a solution under
`0^0 = 1`, in any base `b` or `-b`. Indeed `F_1(n-1) = F_0(n) + 2 - 4 + 1 =
n - 1`.

### 23.2.2 Multiples of 3 (computed, then heuristic)

`analysis/r2c_nega_compare.py`. Base -38 is empty in both conventions, so
bases -2 to -38 have 9 empty bases against 4.63 expected (P = 0.033).
Leaving out the named bases -3, -6, -9: the multiples of 3 from -12 to -36
have 3 empty bases of 9 (-15, -18, -30) against 1.15 expected, P = 0.095.
The other bases from -10 have 3 of 20 (-20, -34, -38) against 2.44,
P = 0.45. So the new bases weaken the multiples-of-3 cluster (-36 is not
empty, -38 is) and leave a general excess of empty negative bases. Over
bases -10 to -38 the solutions number 72 against 83.2 in the refined
model (P = 0.12). For bases -10 to -27 the offsets that keep the last digit
(below) give 52.0 against the model's 53.9, while `D = 0` has 42 (P = 0.09).
The shortfall is mild and is shared by all bases, not by the multiples of 3.

Mechanisms tested:

- The residue mod 3. For `3 | b`, `-b == 0 (mod 3)`, so `n == s_0 (mod 3)`:
  the last digit is fixed mod 3 by `F`. The refined model treats the last
  digit as uniform. The exact factor, the mean of `3 c_r / d` over random
  multisets with `r = F mod 3` and `c_r` the number of digits `== r (mod 3)`,
  is 0.9985 to 1.0006 for `b` = 12 to 39, both conventions (computed by
  sampling, 200,000 multisets each; heuristic as a model factor). So mod 3
  has no effect.
- The identity mod `b+1` (Proposition 14.5). For `3 | b`, `b + 1 == 1
  (mod 3)`, so it carries no factor 3, and the refined model includes it
  exactly.
- Near-solutions. `analysis/r2c_nega_offsets.py` counts `n = F(n) + D` for
  20 offsets in two families, `j step` (step `b+1`, or `2(b+1)` for even
  `b`) and `j step b`, which also keeps `n - F(n)` mod `b`, hence mod 3.
  Bases -10 to -27, sums of the mean counts:

| group | `m` | `D = 0` | model | `j step` | `j step b` |
|---|---:|---:|---:|---:|---:|
| multiples of 3 | 0 | 6 | 10.25 | 11.45 | 9.85 |
| multiples of 3 | 1 | 4 | 7.38 | 7.90 | 7.40 |
| others | 0 | 20 | 21.07 | 24.90 | 19.15 |
| others | 1 | 12 | 15.24 | 18.25 | 15.55 |

The multiples of 3 have the model's rate of near-solutions in both
families. So nothing about these bases lowers the chance of a solution, and
their low count at `D = 0` (10 against 17.6) is a draw (P = 0.04 for the
sum, chosen after the fact). Verdict: chance, as in section 14.3.3.

A side result (computed, 20 offsets per base). The family that keeps the
last digit gives fewer near-solutions in every group: 19.15 against 24.90
for the other bases under `0^0 = 0` (about 4 standard deviations), and
9.85 against 11.45 for the multiples of 3. In positive bases the offsets
`2 j b (b-1)` also predicted slightly fewer solutions than `j (b-1)`
(section 11.2). It is the better calibration for `D = 0`, and against it
the totals at `D = 0` are 42 against 52 (all bases) and 10 against 17.3
(multiples of 3). The last digit is not the cause of the empty multiples
of 3: it acts on all bases alike.

Update (chapter 26). With the clustered calibration of section 26.3 the
P values of this section become 0.11 (negative bases, 42 against 52) and
0.056 (multiples of 3), and the fewer near-solutions at offsets with step `b`
are about 2.9 standard deviations, not 4. The verdicts do not change.

## 23.3 2-cycles in even bases under `0^0 = 0` (question 35)

### 23.3.1 Near-2-cycles (computed)

`fast/src/bin/r2c_cycles2.rs` visits every digit multiset `c` of 1 to `b`
digits once (as `dyn_cycles.rs`). With `c'` the multiset of `S(c)` and
`G(c) = S(c')`, it counts

    A_j = #{ c : the digits of G(c) + j (b-1) form c, and c' != c },

so `A_0` is twice the number of 2-cycles, and for `j >= 1` it counts the
near-2-cycles `F(F(n)) = n - j(b-1)`. These keep the residue mod `b-1` (and
mod 2 in odd bases), so each `j` is a fresh draw of the same coincidence,
as the offsets of section 11.1 are for fixed points. The same pass builds
the class matrix of section 15.1.5, so the model `E_2` of base 18 comes from
`analysis/dyn_cycle_model.py`. Its values for bases 12, 16 and 17 match
`analysis/data/dyn_cycle_model.txt`. The run is journaled in batches. Base
18 took about 3200 s per convention on one thread. The 2-cycle counts agree with
the census of chapter 15 for bases 4 to 17.

Base 18 under `0^0 = 0` has one 2-cycle (computed):

    (2,13,4,8,1,3,17,8,10,0,12,6,2,0,12,12) <-> (6,14,11,1,5,13,13,1,3,12,5,6,4,12,10,16,10)

Base 18 under `0^0 = 1` also has one 2-cycle (computed):

    (13,11,5,7,4,5,9,15,17,10,2,1,6,7,4,2,10) <-> (6,14,12,4,6,4,14,17,5,1,15,14,7,7,8,17,0)

It has a zero, so it is not shared with `0^0 = 0`. The model expects 0.51
2-cycles per convention in base 18.

Groups, bases 4 to 18 (`analysis/r2c_cycles2_compare.py`,
`analysis/data/r2c_cycles2.txt`):

| group | 2-cycles | model `E_2` | P(X <= obs) | near-2-cycles per offset |
|---|---:|---:|---:|---:|
| even, `0^0 = 0` | 2 | 4.02 | 0.24 | 5.25 |
| even, `0^0 = 1` | 4 | 4.30 | 0.57 | 4.97 |
| odd, `0^0 = 0` | 6 | 7.23 | 0.42 | 8.32 |
| odd, `0^0 = 1` | 4 | 3.88 | 0.65 | 3.92 |

The even bases under `0^0 = 0` have 5.25 near-2-cycles per offset, above
the model's 4.02. So these bases do not lack the coincidence that makes a
2-cycle. A second invariant would lower every offset that keeps the
residues, and it does not. The deficit at `D = 0` is 2 against 5.25, P =
0.10 for a Poisson count (heuristic). With base 18 it is no longer
striking.

Why no invariant can exist (proven for residues): Theorem 15.2 shows that
`n mod q` is invariant under `F` only for `q = 2`, odd `b` and `0^0 = 0`.
The offsets test the non-congruence kind of invariant and find none
(heuristic).

Verdict: chance. The model underestimates near-2-cycles slightly in even
bases (5.25 against 4.02), as it underestimates fixed points (the offsets
give 10.4 against 9.4).

## 23.4 Lengths in base -1+i (question 43)

Theorem 23.1 (proven). In base `beta = -1+i` (digits 0 and 1), the
representation of a rational integer `n` is its base -4 representation with
each base -4 digit `B` written as the block `(B mod 2, 0, [B >= 2], [B >= 2])`
at positions `4j` to `4j+3` (least significant first). So a positive integer
has `8m + 1` digits if its leading base -4 digit is 1, and `8m + 4` digits if
it is 2 or 3. Both residues occur for every `m`: `16^m` and `2 * 16^m`.

Proof. `beta^4 = -4`. Cut a representation of `z` into blocks of four digits,
so that `z = sum_j C_j (-4)^j` with `C_j = a_0 + a_1 beta + a_2 beta^2 + a_3
beta^3` and `a_k` in {0, 1}. Since `beta^2 = -2i` and `beta^3 = 2 + 2i`,

    C = (a_0 - a_1 + 2 a_3) + i (a_1 - 2 a_2 + 2 a_3).

Let `y_j` be the imaginary part of `C_j`. It lies in {-2, ..., 3}. If `z` is
real, `sum_j y_j (-4)^j = 0`. Reducing mod 4 gives `y_0 == 0`, so `y_0 = 0`,
because 0 is the only multiple of 4 in that range. Divide by -4 and repeat:
every `y_j` is 0. Now `a_1 - 2 a_2 + 2 a_3 = 0` forces `a_1 = 0` and
`a_2 = a_3`. Then `C_j = a_0 + 2 a_2` is a base -4 digit `B_j` in {0, 1, 2, 3},
and `z = sum B_j (-4)^j` is the base -4 representation of `z`, which is unique.
A positive integer has an odd number `2m + 1` of base -4 digits
(Proposition 12.2). Its top block ends at position `8m` when `B = 1` and at
`8m + 3` when `B` is 2 or 3.

This answers question 43 and the first open question of section 14.7.
`analysis/r2c_gauss_m1i.py` checks the block form for every `|n| <= 10^6`
and 100,000 random integers below `10^60` (computed,
`analysis/data/r2c_gauss_m1i.txt`).

Corollary 23.2 (proven). The ones of a positive `n` number the base -4 digit
sum `s(n)`, and its digits number `8m + 1` or `8m + 4`. So the Munchausen
numbers of base -1+i are:

- under `0^0 = 0` (`F` counts ones), the `n` with `n = s(n)`: exactly 1, 2,
  3, 4, 5, 6 and 7;
- under `0^0 = 1` (`F` counts digits), the `n` equal to their length:
  exactly 1 and 9.

Proof. With `2m + 1` base -4 digits, `n > (4^(2m) - 1)/5` (Corollary 14.2),
while `s(n) <= 3 (2m + 1)` and the length is at most `8m + 4`. For `m >= 2`
both bounds are below 51, so `m <= 1` and `n <= 19`. For `m = 1`,
`n = 16 - 4 B_1 + B_0` and `s = 1 + B_1 + B_0` (the top digit must be 1,
since `n <= 19`), so `n = s` means `B_1 = 3`: n = 4 to 7. The length is 9,
so `n = 9` is the only one of length type. For `m = 0`, n = 1, 2, 3 with
lengths 1, 4, 4.

This is the census of section 14.5 (computed there to 18 digits), now
proven complete. The argument needs a power of `beta` that is a rational
integer. For `-n+i` with `n >= 2` no power is real, because the argument
`pi - arctan(1/n)` is not a rational multiple of `pi`; so the runs of
section 14.5.1 need another proof.

## 23.5 The per-base scatter of `lambda` (question 44)

`analysis/r2c_top_model.py`. For each base 12 to 32 and length `b-6` to `b`,
400,000 random multisets are drawn as in the refined model. For those whose
`F` has the right length and meets the identity mod `b-1`, the top `t` digits
of `F` are read off `F`, and the chance that the other digits complete the
multiset replaces the uniform chance (the ratio of `forced_top.py`). All `t`
share one sample. The target is the measured `lambda_m(b)` of section 11.2a
(`defects_bulk_b1.txt`, 60 offsets each), with its own standard error
(computed; `analysis/data/r2c_top_model.txt`).

| `t` | `0^0 = 0`: chi-square | correlation | `0^0 = 1`: chi-square | correlation | mean `lambda / model`, `0^0 = 1` |
|---:|---:|---:|---:|---:|---:|
| 0 (refined model) | 97.0 | 0.84 | 95.7 | 0.34 | 1.12 |
| 1 | 98.3 | 0.82 | 94.0 | 0.32 | 1.13 |
| 2 | 76.3 | 0.86 | 81.9 | 0.56 | 1.13 |
| 3 | 68.2 | 0.91 | 75.7 | 0.66 | 1.12 |
| 4 | 59.6 | 0.89 | 72.4 | 0.62 | 1.12 |

Chi-square on 21 bases; it includes the sampling error of the model.

What this shows (heuristic):

- The forced top digits explain about half of the excess scatter under
  `0^0 = 0` (excess chi-square 76 down to 39) and a third under `0^0 = 1`
  (75 down to 51). Each further digit helps less; `t = 4` is at the noise of
  400,000 samples.
- The rest is concentrated. At `t = 3`, under `0^0 = 0`, base 19
  (1.35 +- 0.14 against 2.02) and base 13 (3.50 against 2.52) carry 34 of
  the 68. Base 13 has short lengths (7 to 13), where the local factors of
  section 11.4 raise the count. Base 19, the empty base, has 0.67 times
  the model's rate of near-solutions, about 4.5 standard errors low;
  section 11.1 compared it only to the range of the other bases.
- Under `0^0 = 1` the model is 12% low on average, in even and odd bases
  alike (1.11 and 1.13). Bases 16, 13 and 20 carry 38 of the 76 at `t = 3`:
  base 16 has 1.75 against 1.04, base 20 has 1.53 against 1.06.

So the second-order effects found so far are the top digits. The next
candidates are the low digits: for `x^x`, `F mod b` is a function of the
counts, and the offsets `j (b-1)` move it, so `lambda` averages the
last-digit factor over residues. A model with forced top and bottom digits
together, and local factors for the short lengths, is the natural next step.

Update (chapter 26). Section 23.5 used the sample variance of the offset
means, which near-solution clusters inflate (Lemma 26.1). With the corrected
variance the chi-squares become 41 and 43 (P 0.005, 0.003) at `t = 0` and
28 to 35 (P 0.03 to 0.14) with the top digits forced. Base 19 drops to
`z = -2.9`, one case of 42, so it is no longer a separate anomaly. The 12%
excess under `0^0 = 1` survives at `z = 3.0`. The factorion P values of
section 23.1 move from about 0.05 to about 0.09 combined. See section 26.4.

## New questions

- 23.a. Is there any arithmetic difference between `n = F(n)` and
  `n = F(n) + D` for small `D` that keeps every residue up to `b+1`? For
  factorions in odd bases the solutions run at 0.3 to 0.5 times their
  near-solutions in two disjoint base ranges.
- 23.b. Why is base 19 low under `0^0 = 0` in its near-solutions, not just
  in its solutions? The top-digit model does not explain it.
- 23.c. Prove the length runs of positive integers in base `-n+i`, `n >= 2`.
- 23.d. In negative bases, keeping the last digit (offsets `j step b`)
  lowers the near-solution rate by 10 to 25%. Which digits of `F mod b`
  cause it, and does the refined model need a last-digit factor?
- 23.e. Under `0^0 = 1` the per-base rate is 12% above the refined model in
  both parities. Is this the short lengths, the zeros, or something else?

## Files

- Engines: `fast/src/bin/worlds.rs` (`--shard i/n`, weights `fact0`),
  `fast/src/bin/r2c_cycles2.rs`.
- Scripts: `analysis/r2c_fact_offsets.py`, `r2c_fact_compare.py`,
  `r2c_fact_family.py`, `r2c_fact0_check.py`, `r2c_wgt_model.py` (copy of
  q-weights `wgt_model.py`), `r2c_nega_run.py`, `r2c_nega_compare.py`,
  `r2c_nega_offsets.py`, `r2c_nega_offsets_compare.py`,
  `r2c_cycles2_compare.py`, `r2c_gauss_m1i.py`, `r2c_top_model.py`.
- Data: `analysis/data/r2c_*`. The files `r2c_qw_*` are copies of the
  factorion data of branch q-weights.
