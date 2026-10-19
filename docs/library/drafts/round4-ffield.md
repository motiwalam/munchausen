# Round 4 draft: why the model misses in F_q[T]

Section 21.1 left one problem open. In `F_q[T]` with the weight
`w(d) = d^(q^deg d)` the refined model of chapter 5 is off for odd `q`:
about 1.3 times too low under `0^0 = 0` and about 2 times too high under
`0^0 = 1`. Near-solutions with offsets `(B-1) g` agreed with the actual
counts, so the solutions looked like ordinary draws. This draft finds the
cause, proves the structure behind it, gives exact counts where it can,
extends the census, and asks what the toy world says about the integers.

Each statement carries one mark:

- proven: a proof is in this draft;
- cited: a result of an earlier chapter, with its number;
- computed: an exact enumeration, with its range;
- heuristic: an estimate with a stated assumption.

## Summary

| section | statement | result | status |
|---|---|---|---|
| 2 | Frobenius blocks (Lemma 2.1, Proposition 2.2) | `n(T^q)` sends each base-`B` digit to its own block of `q` digits, without carries. So the digits of `F(x)` at positions `[q^(j-1), q^j)` are the digits of `Phi^j(p_j)` for one single digit `p_j`. | proven |
| 2 | Forced zeros and rank one (Corollary 2.4, Propositions 2.5, 2.6) | a digit whose position has a base-`q` digit above `R = floor((e-1)q/e)` is zero. About `1/e` of the positions carry multiples of one fixed digit, and their class sums are one number `c(x)` times a fixed vector. | proven |
| 3 | Census (Table 3.1) | 28 cases, all bases, both conventions, up to `(q, e) = (17, 3)`, `(5, 4)`, `(3, 5)`, `(2, 7)`, with a new engine (`(7, 3)` in 0.2 s against 69 s). The exact `e = 3` averages are erratic in `q`; I found no closed formula. | computed |
| 4.1, 4.2 | digit law of `F(x)` | the digits are far from uniform: 4 to 700 times more zeros than the model, and whole positions that are always zero or always of one degree | computed |
| 4.3 | near-solutions (Lemmas 4.1, 4.2) | the offsets of the round 3 check map most solutions to near-solutions one to one: constant offsets always, offsets of degree below `deg d_0 = deg d_1` too. So that check repeated the census. Offsets that perturb 5 low digits bring the count down to the model. | proven; computed |
| 4.4 | `0^0 = 1` (Proposition 4.3) | if `B - 1` has an irreducible factor of degree prime to `p`, the solutions under `0^0 = 1` are exactly the solutions under `0^0 = 0` whose number of zero digits is divisible by `p`. The model puts this share at 0.72 to 0.95; it is 0.02 to 0.67. This explains the whole `0^0 = 1` gap. | proven; computed |
| 4.4 | `e = 2` (Corollary 4.4) | under `0^0 = 1` a base with two roots of `B - 1` has 0 or `q(q-1)` solutions, never `q(q-2)`; it has none when `B = lambda (T - c)^2`. This corrects a line of section 21.1.5. | proven (squares); computed (the rest, `q <= 19`) |
| 4.5 | `0^0 = 0` (Proposition 4.5) | the solutions sit where the lower class sums are forced, for example 43% have `D_1 = 0` for `q = 13` against 2.5% in the model. Where the identity is freer on that sector, the model is low. The mean excess is 3% to 47% for odd `q`, about 5 standard deviations in all; for `q = 2` there is none. | proven (structure); computed; heuristic (mechanism) |
| 4.6 | which assumption fails | independence and uniformity of the digits of `F`. The identity modulo `B - 1` is exact. The zero-count term is the channel under `0^0 = 1`. The cause is that `F` is additive. | computed; heuristic |
| 5 | short solutions (Theorem 5.1) | for every `e`: a base has exactly `q(q-1)` or no solutions with `D_j` constant for `j >= 2`, by an explicit test on `(T^q - T)/(B - 1)`. Binomial bases `lambda T^e + mu` pass when `e | q - 1`. This extends Theorem 21.7 to all `e`. | proven; computed |
| 6 | integers | the analog is the forced top digits of section 11.2. Below the top 3 positions the integer digits of `F` are uniform. The effect on the integer model is a few percent. | computed |

## 1. Setting and notation

Let `q` be prime, `e >= 2`, and `B` in `F_q[T]` of degree `e` with leading
coefficient `lambda`. The digits are the polynomials of degree below `e`.
A digit of degree `j` weighs `d(T^(q^j))`, and `0` weighs `m`
(Proposition 21.1, cited). For a number `n` with class sums
`x = (D_0, ..., D_(e-1), z)`,

    F(x) = sum_j D_j(T^(q^j)) + m z,

and `n` is a solution when `n = F(x)` and the class sums of `n` are `x`
(Corollary 21.2, cited). Write further:

- `Phi(n) = n(T^q) = n^q`, the Frobenius map. It is additive and fixes
  `F_q`.
- For a digit `d`, `beta_0(d), ..., beta_(q-1)(d)` are the base-`B` digits of
  `d(T^q)`. This works because `deg d(T^q) <= (e-1) q < q e`.
- `R = floor((e-1) q / e)`. Then `beta_r = 0` for `r > R`.
- `sigma = beta_0` is the Frobenius map modulo `B`, and `sigma'` is the
  Frobenius map modulo `B - 1`, both on digits.
- `tau_r = beta_r(T^(e-1))`, the digits of `T^((e-1) q)`.
- `k(B)` is the free residue dimension of section 21.1.4.
- "Refined" is the refined model of section 21.1.6, an exact sum. "Census"
  means all bases of degree `e` with any leading coefficient.

## 2. The Frobenius blocks

### 2.1 Blocks and the Horner form

Lemma 2.1 (proven). For every `n = sum_i d_i B^i`, the base-`B` expansion of
`n(T^q)` is

    n(T^q) = sum_i sum_{r <= R} beta_r(d_i) B^(q i + r).

So the digit at position `q i + r` of `n(T^q)` is `beta_r(d_i)`, and the
digits at positions `q i + r` with `r > R` are zero.

Proof. The coefficients of `n`, `d_i` and `B` lie in `F_q`, so
`n(T^q) = n^q = sum_i d_i^q (B^q)^i = sum_i d_i(T^q) B^(q i)`. Substitute
`d_i(T^q) = sum_r beta_r(d_i) B^r`. The exponents `q i + r` with `r < q` are
distinct, and every `beta_r(d_i)` is a digit, so this is the expansion by
uniqueness. Since `deg d(T^q) <= (e-1) q < e (R + 1)`, the digits with
`r > R` vanish.

So Frobenius never carries. It replaces each digit by a block of `q` digits.

Proposition 2.2 (Horner form, proven).

    F(x) = D_0 + m z + Phi(D_1 + Phi(D_2 + ... + Phi(D_(e-1)) ...)).

Proof. `Phi^j(D_j) = D_j(T^(q^j))`, and `Phi` is additive.

Corollary 2.3 (proven). Put `p_(e-1) = D_(e-1)`, `p_j = sigma(p_(j+1)) + D_j`
for `1 <= j <= e-2`, and `p_0 = sigma(p_1) + D_0 + m z`. Then the base-`B`
digits of `F(x)` are `p_0` at position 0 and, for each `1 <= j <= e-1`, the
digits of `Phi^j(p_j)` at the positions `q^(j-1) <= i < q^j`.

Proof. Let `y^(e-1) = D_(e-1)` and `y^(j) = D_j + Phi(y^(j+1))`, so that
`F(x) = y^(0)` with `D_0 + m z` in place of `D_0`. By Lemma 2.1 the digit at
position 0 of `y^(j)` is `sigma` of the digit at position 0 of `y^(j+1)`, plus
`D_j`; that is `p_j`. The digits of `y^(j)` at positions `1 .. R` are
`beta_r(p_(j+1))`, and its digits at positions `>= q` are the blocks of the
digits of `y^(j+1)` at positions `>= 1`. Induction on `j` puts the digits
created from `p_j` at positions `[q^(j-1), (R+1) q^(j-1))` of `F(x)`, and
there they are the digits of `Phi^(j-1)(Phi(p_j) - sigma(p_j))`, that is of
`Phi^j(p_j)`. The ranges for different `j` are disjoint because `R + 1 <= q`.

So the whole digit string of `F(x)`, up to `L` digits, is assembled from
`e` single digits `p_0, ..., p_(e-1)`. The class sums of `F(x)` are
`class(p_0) + sum_{j >= 1} K_j(p_j)`, where `K_j` is a table over the `q^e`
digits. The engine `fast/src/bin/r4f_ffield.rs` uses exactly this. It walks
`x` level by level and needs only table lookups. It also reduces the bases to
orbits under `T -> aT + b` (Lemma 2.7). It reproduces every count and every
model sum of section 21.1.6 and of `analysis/data/r3t_ffield_frob.txt`
(computed, the six cases with `e >= 3` of section 21.1.6, both conventions,
and the old engine's `(7, 3)`).

### 2.2 Zeros and rank one

Corollary 2.4 (forced zeros, proven). The digit of `F(x)` at a position
`i >= 1` is zero whenever some base-`q` digit of `i` exceeds `R`.

Proof. By Corollary 2.3 and Lemma 2.1 applied `j` times, the digit at
`i = sum_k i_k q^k` in `[q^(j-1), q^j)` is
`beta_(i_0)(beta_(i_1)(... beta_(i_(j-1))(p_j)))`.

There are forced zeros exactly when `q > e`, since then `R <= q - 2`. For
`e = 3` the positions below `L` have two base-`q` digits, the upper one at
most `R`, so the share of forced zeros is `(q - 1 - R)/q`, about `1/3`. More
zeros come from low degrees.

Lemma 2.5 (proven). For a digit `d` of degree `j`, `beta_r(d) = 0` for
`r > floor(j q / e)`. A zero digit at position `s` of `y^(1)` gives `q`
zero digits at positions `q s .. q s + q - 1` of `F(x)`.

Proof. `deg d(T^q) = j q`. The second statement is Lemma 2.1 with
`beta_r(0) = 0`.

Proposition 2.6 (rank one, proven). Let `floor((e-2) q / e) < r <= R`.

1. For every digit `d`, `beta_r(d) = d_(e-1) tau_r`, where `d_(e-1)` is the
   coefficient of `T^(e-1)` in `d`.
2. The digits of `F(x)` at the positions `i >= 1` with `i == r (mod q)` add
   up to `c(x) tau_r`, with

       c(x) = coefficient of T^(e-1) in  sum_{j >= 1} sigma'^(j-1)(D_j),

   and all of them lie in the class of `tau_r`.

Proof. (1) `d(T^q) = sum_t d_t T^(t q)`, and base-`B` expansion is
`F_q`-linear. `T^(t q)` has no digit above position `floor(t q / e)`, which
is below `r` for `t <= e - 2`. (2) Write `F(x) = D_0 + m z + Phi(y)` with
`y = y^(1)`. By Lemma 2.1 the digits in question are `beta_r(y_s)`, which by
(1) are `(y_s)_(e-1) tau_r`. Their sum is `tau_r` times the `T^(e-1)`
coefficient of the digit sum of `y`. The digit sum has degree below `e` and is
congruent to `y` modulo `B - 1`, and `y == sum_{j >= 1} sigma'^(j-1)(D_j)`
because `Phi` acts as `sigma'` modulo `B - 1`.

For `e = 3` the positions `floor(q/3) < r <= R` form about one third of each
block. In the model they are about `L/3` independent uniform digits. In truth
their total contribution to the class sums is one number `c(x)` times a fixed
vector of the base.

Lemma 2.7 (symmetry, proven). For `a != 0`, the map `psi(f)(T) = f(aT + b)`
sends the solutions in base `B` to the solutions in base `psi(B)`.

Proof. `psi` is an `F_q`-algebra automorphism that keeps degrees, so it maps
digits to digits of the same degree and expansions to expansions. Since
`psi(d)^(q^j) = psi(d^(q^j))`, it commutes with the weight.

Lemma 2.8 (proven). Under `0^0 = 0`, if `n` is a solution, so is `c n + a`
for all `c != 0` and `a` in `F_q`. These `q (q-1)` solutions are distinct.

Proof. The digits of `c n` are `c d_i`, of the same degrees, so its class
sums are `c x` and `F(c x) = c F(x)`. The translates are Proposition 21.3
(cited). If `c n + a = n` with `c != 1`, then `n` is a constant, which has
one digit.

## 3. The census

### 3.1 All cases

Table 3.1 (computed, all bases of degree `e`, both conventions,
`analysis/data/r4f_census_q*e*m*.txt`). Per base: solutions with at least 2
digits and the refined model. `z` is the difference in units of its own
scatter (`analysis/r4f_dispersion.py`): each orbit of Lemma 2.7 counts as one
draw, with the variance of the counts among the orbits of the same `k(B)`.
The share `p | z` is the share of `0^0 = 0` solutions whose number of zero
digits is divisible by `p`; Proposition 4.3 explains why it matters.

| `q` | `e` | bases | `0^0 = 0` census | refined | ratio | `z` | `0^0 = 1` census | refined | ratio | share `p | z` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 3 | 8 | 1.500 | 1.786 | 0.84 | -0.6 | 1.000 | 1.464 | 0.68 | 0.67 |
| 2 | 4 | 16 | 2.375 | 3.196 | 0.74 | -1.3 | 1.875 | 2.668 | 0.70 | 0.65 |
| 2 | 5 | 32 | 3.750 | 4.071 | 0.92 | -0.9 | 2.125 | 3.183 | 0.67 | 0.57 |
| 2 | 6 | 64 | 6.594 | 4.575 | 1.44 | 2.1 | 4.094 | 3.635 | 1.13 | 0.62 |
| 2 | 7 | 128 | 5.031 | 5.026 | 1.00 | 0.0 | 3.000 | 3.768 | 0.80 | 0.60 |
| 3 | 3 | 54 | 8.222 | 6.479 | 1.27 | 0.9 | 4.111 | 5.477 | 0.75 | 0.49 |
| 3 | 4 | 162 | 14.444 | 9.858 | 1.47 | 2.5 | 3.778 | 8.025 | 0.47 | 0.26 |
| 3 | 5 | 486 | 14.296 | 12.924 | 1.11 | 1.3 | 5.111 | 10.315 | 0.50 | 0.36 |
| 5 | 3 | 500 | 34.400 | 26.230 | 1.31 | 2.3 | 11.840 | 23.338 | 0.51 | 0.34 |
| 5 | 4 | 2500 | 60.480 | 45.414 | 1.33 | 2.9 | 19.664 | 39.674 | 0.50 | 0.33 |
| 7 | 3 | 2058 | 76.286 | 64.810 | 1.18 | 2.2 | 2.286 | 59.438 | 0.038 | 0.030 |
| 11 | 3 | 13310 | 240.000 | 233.004 | 1.03 | 0.5 | 17.273 | 220.000 | 0.079 | 0.072 |
| 13 | 3 | 26364 | 407.077 | 379.118 | 1.07 | 1.8 | 8.923 | 360.982 | 0.025 | 0.022 |
| 17 | 3 | 78608 | 857.412 | 835.518 | 1.03 | 0.8 | P173M1 |

The share `p | z` counts only bases where Proposition 4.3 applies: all bases
except 4 of 16 for `(2, 4)`, 13 of 64 for `(2, 6)` and 16 of 54 for
`(3, 3)`.

New cases against chapter 21: `(2,6)`, `(2,7)`, `(3,5)`, `(5,4)`, `(7,3)`,
`(11,3)`, `(13,3)`, `(17,3)`. The largest, `(17, 3)` under `0^0 = 0`, takes
2 minutes on 4 threads; `(2, 7)` takes 6.

Statement 3.1 (computed). Under `0^0 = 0` the ratio is 1.03 to 1.47 for odd
`q`, and every odd case has `z > 0`; together the nine odd cases give a
combined `z` of about 5 (the sum of the `z` divided by 3). For `q = 2` the
ratios scatter on both sides of 1.
Under `0^0 = 1` the census is far below the model for every odd `q`, and the
gap grows with `q`: the ratio is 0.025 for `q = 13`.

### 3.2 Degree 3 by free residues

Table 3.2 (computed). `e = 3`, `0^0 = 0`, per base and divided by `q(q-1)`,
the size of the families of Lemma 2.8.

| `q` | `k = 1` census | refined | `k = 2` census | refined | `k = 3` census | refined | all, census | all, refined |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 0.333 | 0.193 | 1.857 | 1.333 | 7.00 | 6.19 | 43/25 | 1.312 |
| 7 | 0.176 | 0.139 | 1.630 | 1.218 | 8.40 | 8.07 | 89/49 | 1.543 |
| 11 | 0.049 | 0.091 | 1.262 | 1.110 | 12.00 | 12.03 | 24/11 | 2.118 |
| 13 | 0.105 | 0.077 | 1.467 | 1.086 | 13.77 | 14.03 | 441/169 | 2.430 |
| 17 | 0.062 | 0.059 | 1.197 | 1.061 | 18.08 | 18.02 | 911/289 | 3.072 |

For `q = 3` the average is `37/27`. The bases with `k = 3` follow the model
within 2%. The excess sits in `k = 2`, and `k = 1` scatters on both sides.

Statement 3.2 (computed). The exact average for `e = 3`, divided by
`q(q-1)`, is `37/27, 43/25, 89/49, 24/11, 441/169, 911/289` for
`q = 3, 5, 7, 11, 13, 17`. Its ratio to the model moves up and down with `q`
(1.31, 1.18, 1.03, 1.07, 1.03 for `q >= 5`), and the column `k = 1` is not
even monotone. The short part alone depends on the arithmetic of `q`
(section 5.2). So I found no closed formula for the average over all bases
of degree 3, and I do not expect a simple one.

## 4. Which assumption fails

### 4.1 The digits of F are not uniform

Table 4.1 (computed, `q = 5`, `e = 3`, all bases and all full-length `x`,
`analysis/data/r4f_positions_q5e3.txt`). The share of each digit degree by
position. The model gives every position below the top the same row.

| position | zero | degree 0 | degree 1 | degree 2 |
|---|---:|---:|---:|---:|
| model | 0.008 | 0.032 | 0.160 | 0.800 |
| 0 | 0.020 | 0.078 | 0.102 | 0.800 |
| 1 | 0.066 | 0 | 0.134 | 0.800 |
| 2 | 0.200 | 0 | 0.128 | 0.672 |
| 3 | 0.200 | 0 | 0.800 | 0 |
| 4, 9, 14 | 1 | 0 | 0 | 0 |
| 8, 13 | 0.200 | 0 | 0.800 | 0 |
| 16 (top) | 0 | 0 | 0 | 1 |

Here `R = 3`. Positions `== 4 (mod 5)` are forced zeros (Corollary 2.4).
Positions `== 3 (mod 5)` hold the block tops `(y_s)_2 tau_3`, of degree
exactly 1 or zero (Proposition 2.6). The other positions lie between these
rows. No digit of degree 0 ever occurs above position 0, while the model
expects about 0.5 such digits per string. So `D_0` is the last digit or 0.

Table 4.2 (computed, `analysis/data/r4f_zeros.txt`, 4,000 random full-length
`x` per base orbit). Zero digits of `F(x)` against the model, and the share
of `x` whose zero count is divisible by `p`.

| `q` | `e` | `L` | forced zeros | mean zeros | model | share `p | z` | model |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 7 | 0 | 1.49 | 0.375 | 0.549 | 0.724 |
| 2 | 5 | 13 | 0 | 4.82 | 0.375 | 0.487 | 0.730 |
| 2 | 6 | 27 | 0 | 10.88 | 0.406 | 0.515 | 0.719 |
| 3 | 3 | 7 | 0 | 1.08 | 0.222 | 0.494 | 0.798 |
| 3 | 4 | 21 | 0 | 7.89 | 0.247 | 0.299 | 0.782 |
| 3 | 5 | 65 | 0 | 28.51 | 0.263 | 0.337 | 0.770 |
| 5 | 3 | 17 | 3 | 4.91 | 0.128 | 0.446 | 0.879 |
| 5 | 4 | 94 | 30 | 37.97 | 0.149 | 0.286 | 0.862 |
| 7 | 3 | 33 | 8 | 9.92 | 0.093 | 0.000 | 0.911 |
| 11 | 3 | 81 | 21 | 25.70 | 0.060 | 0.090 | 0.942 |
| 13 | 3 | 113 | 32 | 36.26 | 0.051 | 0.000 | 0.950 |

The model takes zeros to be rare, `(L-1)/q^e` of them. In truth 15% to 45%
of the digits are zero. Where `q <= e` no position is forced, but Lemma 2.5
still makes zeros common: a digit of `y^(1)` of low degree gives a short
block, and a zero digit gives `q` zeros.

### 4.2 A test with the true count law

`analysis/r4f_profile.py` keeps the model's assumption that digit values are
uniform within their class, but replaces the law of the class counts (how
many zeros, how many digits of each degree) by the true joint law in each
base and length.

Table 4.3 (computed, per base).

| `q` | `e` | `m` | census | refined | true count law |
|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 0 | 2.375 | 3.196 | 3.375 |
| 2 | 4 | 1 | 1.875 | 2.668 | 2.188 |
| 2 | 5 | 0 | 3.750 | 4.071 | 3.809 |
| 2 | 5 | 1 | 2.125 | 3.183 | 2.105 |
| 3 | 3 | 0 | 8.222 | 6.479 | 9.750 |
| 3 | 3 | 1 | 4.111 | 5.477 | 5.870 |
| 5 | 3 | 0 | 34.400 | 26.230 | 26.287 |
| 5 | 3 | 1 | 11.840 | 23.338 | 9.144 |

Under `0^0 = 1` the true count law moves the prediction most of the way to
the census for `q = 2` and `q = 5`. Under `0^0 = 0` with `q = 5` it changes
nothing. So two different things fail: the zero count under `0^0 = 1`, and
something beyond the counts under `0^0 = 0`. Sections 4.4 and 4.5 identify
them.

### 4.3 Why the near-solutions agreed

Lemma 4.1 (proven). Let `c` be a nonzero constant and let `n` be a solution
under `0^0 = 0` whose digits `d_0`, `d_1` both have degree at least 1. Then
`n' = n + (B - 1) c` has the digits `d_0 - c`, `d_1 + c` and the same other
digits, and `n' = F(x') + (B-1) c` for its class sums `x'`. This is a
bijection between such solutions and such near-solutions with offset
`(B-1) c`.

Proof. Adding a constant keeps the degree of `d_0` and `d_1`, so `x'`
differs from `x` only in the constant terms of two class sums, by `-c` and
`+c`. Since `D(T^(q^j))` changes by the same constant as `D`,
`F(x') = F(x) = n`. The inverse subtracts `(B - 1) c`.

Lemma 4.2 (proven). Let `n` be a solution under `0^0 = 0` with
`deg d_0 = deg d_1 = j`, and let `g` be a digit with `deg g < j`. Then
`n + (B - 1) g` has the same class sums `x` as `n`, so it is the
near-solution `F(x) + (B - 1) g`. This is a bijection between such solutions
and such near-solutions with offset `(B-1) g`.

Proof. `(B - 1) g` has the digits `-g` and `g` at positions 0 and 1. The
digits `d_0 - g` and `d_1 + g` keep degree `j`, and the class `j` sum changes
by `-g + g = 0`.

Most solutions have `deg d_0 = deg d_1 = e - 1` (Table 4.1: 80% of the digits
at positions 0 and 1 have full degree). The round 3 check of section 21.1.6
used constant offsets for `q = 5` and offsets of degree below 2 for `q = 3`.
By the two lemmas these near-solutions were mostly the solutions again: for
`q = 5`, `e = 3` the near count 17,200 equals the solution count exactly.
So the check was not an independent draw. In the integers no such bijection
exists, because `x^x` is not additive (section 6.3).

Table 4.4 (computed, `analysis/r4f_offsets.py`, every base orbit, 20 random
`g` per orbit and degree bound for `q = 5`, 8 for `q = 3`). Near-solutions
of the same length as `F(x)`, per base and offset, for offsets `(B-1) g`
with `deg g < K`. The second row gives how many low digits the offsets can
change.

| `q = 5`, `e = 3`, `K` | 0 | 1 | 3 | 6 | 12 | 18 | 24 | 30 | 36 | 45 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| digits changed, of 17 | 0 | 2 | 2 | 3 | 5 | 7 | 9 | 11 | 13 | 16 |
| near-solutions | 34.4 | 34.4 | 28.9 | 28.3 | 25.8 | 24.5 | 25.4 | 20.9 | 20.1 | 21.6 |

| `q = 3`, `e = 4`, `K` | 0 | 1 | 4 | 8 | 16 | 32 | 48 | 64 | 76 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| digits changed, of 21 | 0 | 2 | 2 | 3 | 5 | 9 | 13 | 17 | 20 |
| near-solutions | 14.4 | 14.4 | 11.7 | 11.6 | 10.6 | 8.9 | 8.7 | 5.9 | 6.6 |

The refined model is 26.2 and 9.9. Constant offsets (`K = 1`) give the census
again, by Lemma 4.1. Offsets by a general digit (`K = e`) break the bijection
for the solutions whose last two digits differ in degree, and remove 40% of
the excess for `q = 5`. Randomizing 5 low digits removes all of it. With only
the top digit kept the count falls below the model, by factors 0.82 and 0.67.
That factor is the top digit alone: it is `D_(e-1)` times a fixed digit of a
fixed degree, where the model draws it uniformly. Section 11.2 found the same
kind of factor for forced top digits in the integers. So the structure that
makes the `0^0 = 0` excess sits in the low and middle digits, where the
lower class sums are made (section 4.5), and the top digit pulls the other
way.

### 4.4 The channel under 0^0 = 1: the zero count

Proposition 4.3 (proven). Let `p` be the characteristic. If `B - 1` has an
irreducible factor whose degree is prime to `p`, then the solutions in base
`B` under `0^0 = 1` are exactly the solutions under `0^0 = 0` whose number
of zero digits is divisible by `p`.

Proof. Write `F_m` for the map under `0^0 = m`, and `z(n)` for the number of
zero digits. Then `F_1(n) = F_0(n) + z(n)`, a constant. Let `n` be a
solution under `0^0 = 1`. Section 21.1.4 shows that the trace of the identity
at a factor `P` of `B - 1` is `z deg P = 0` in `F_q` (cited, from the proof of
Theorem 21.6). With `p` prime to `deg P` this gives `p | z(n)`. So
`F_0(n) = F_1(n) = n`. Conversely, if `F_0(n) = n` and `p | z(n)`, then
`F_1(n) = n`.

The census confirms it in every base where the hypothesis holds: 45,649
bases in 13 cases (computed, `analysis/r4f_conventions.py`). For `e = 3` and
`q >= 5` every base qualifies, so the `0^0 = 1` count of `(17, 3)` follows
from the `0^0 = 0` census: P173DERIVED.

So the ratio between the conventions is the share of `0^0 = 0` solutions
with `p | z`. The refined model gets this share from rare zeros, and its
ratio of the two conventions is close to its own `P(p | z)`: 0.89 against
0.88 for `q = 5`, 0.92 against 0.91 for `q = 7`, 0.94 against 0.94 for
`q = 11`. The true share is the last column of Table 3.1. So

    (census / model under 0^0 = 1) = (census / model under 0^0 = 0) * (true share p | z) / (model share p | z),

which is an exact identity once the model ratio equals its own share. For
`q = 5`, `e = 3`: `1.31 * 0.344 / 0.890 = 0.507`, the observed ratio.

The true share is small because the zero count is mostly forced. For `e = 3`
and full length, Corollary 2.4 gives `Z` forced zeros, and a solution needs
`-Z mod p` further zeros. These come only from Lemma 2.5 and from
coincidences:

| `q` | 5 | 7 | 11 | 13 | 17 | 19 | 23 |
|---|---:|---:|---:|---:|---:|---:|---:|
| forced zeros `Z` | 3 | 8 | 21 | 32 | 55 | 72 | 105 |
| further zeros needed, `-Z mod p` | 2 | 6 | 1 | 7 | 13 | 4 | 10 |
| full-length solutions under `0^0 = 1` | yes | none | yes | none | Q17FULL | | |

(computed for `q <= 17`). So the `0^0 = 1` count is governed by `Z mod p`, a
quantity the model cannot see.

Corollary 4.4 (`e = 2` under `0^0 = 1`). Let `q >= 5` and let `B - 1` have
two distinct roots in `F_q`.

1. (proven) If `B = lambda (T - c)^2`, base `B` has no solution under
   `0^0 = 1`, while it has `q(q-1)` under `0^0 = 0`.
2. (computed, `q <= 19`, all such bases) Otherwise it has `q(q-1)` solutions
   under both conventions.

The bases of (1) are `q (q-1)/2` of the `q (q-1)^2 / 2` bases with two
roots, so the average is `q (q-2)`. Section 21.1.5 states `q (q-2)` for
every such base; the census shows 0 or `q(q-1)` per base, with average
`q (q-2)` (computed, `analysis/data/r3t_ffield_frob.txt`, `q = 5, 7`).

Proof of (1). Put `S = T - c`. Then `T^q = c + S^q`, and
`S^q = S (S^2)^((q-1)/2) = lambda^(-(q-1)/2) S B^((q-1)/2)`. So the solution
`C + b T^q` of Theorem 21.7 has the digit `C + b c` at position 0, the digit
`b lambda^(-(q-1)/2) S` at position `(q-1)/2`, and zeros at the `(q-3)/2`
positions between. Its zero count is `(q-3)/2` or `(q-1)/2`, both between 1
and `p - 1`. By Proposition 4.3 it is not a solution under `0^0 = 1`.

### 4.5 The channel under 0^0 = 0: forced lower classes

Under `0^0 = 0` the zeros do not matter, and the count law alone does not
explain the gap (Table 4.3). What does is where the solutions sit.

Table 4.5 (computed, `q = 13`, `e = 3`, all bases,
`analysis/data/r4f_types_q13e3m0.txt`). Solutions per base by the type of
their class sums: per class, `0`, `low` (nonzero, top coefficient 0) or `top`
(top coefficient nonzero).

| `D_0, D_1, D_2` | census | refined |
|---|---:|---:|
| `0, 0, top` | 170.8 | 4.1 |
| `0, top, top` | 197.9 | 141.2 |
| `0, top, low` | 16.3 | 15.2 |
| `0, low, top` | 3.4 | 47.1 |
| `top, top, top` | 4.3 | 116.0 |
| `top, low, top` | 0 | 38.7 |
| all with `D_0 != 0` | 6.5 (1.6%) | 165.6 (44%) |
| all with `D_1 = 0` | 176.0 (43%) | 9.3 (2.5%) |
| total | 407.1 | 379.1 |

The totals differ by 7%, but the solutions are a different population.
Almost none has `D_0 != 0`, because constants never occur above position 0
(Table 4.1). Almost half has `D_1 = 0`. The reason is Proposition 2.6 and the
next statement.

Proposition 4.5 (generic cell, proven). Let `0^0 = 0`, `q >= e`, and
`rho = (e-1) q mod e`. Call `x` generic in base `B` if every digit of `F(x)`
that is neither a forced zero (Corollary 2.4) nor at a position
`== R (mod q)` has degree `e - 1`.

1. If `q == 1 (mod e)`, then `rho = e - 1`, and a generic `x` is a solution
   if and only if `D_j = 0` for all `j < e - 1` and
   `sigma'^(e-1)(D_(e-1)) = D_(e-1)`.
2. If `q != 1 (mod e)`, then `rho < e - 1`, and a generic `x` is a solution
   if and only if `D_j = 0` for `j` not in `{rho, e - 1}`,
   `D_rho = c(x) tau_R`, and the identity of Proposition 21.5 holds.

Proof. By Proposition 2.6 with `r = R`, the digits at the positions
`== R (mod q)` are multiples of `tau_R`, the top digit of `T^((e-1) q)`,
which has degree `rho`. They add up to `c(x) tau_R`. All other nonzero digits
of a generic `x` lie in class `e - 1`. The digit sum is
`F(x) mod (B - 1) = sum_j sigma'^j(D_j)`. In case 1 every nonzero digit is
in class `e - 1`, so the lower class sums are 0 and the top one is the digit
sum; with `D_j = 0` below `e - 1` the digit sum is `sigma'^(e-1)(D_(e-1))`.
In case 2 the class `rho` sum is `c(x) tau_R`, the others below `e - 1` are
0, and the top one is the digit sum minus `c(x) tau_R`; it equals `D_(e-1)`
exactly when the identity holds.

In both cases the lower classes are forced: zero, or one multiple of a fixed
digit.

So in case 1 the fixed-point system on the generic cell collapses to
`D_j = 0` and the identity restricted to `D_(e-1)`. Its solution space is the kernel of
`sigma'^(e-1) - 1` on `F_q[T]/(B - 1)`, of dimension `kappa(B)`. For
squarefree `B - 1` this is `sum gcd(e - 1, deg P)` over its irreducible
factors `P`, while `k(B)` is the number of factors. So `kappa > k` exactly
when some factor has degree sharing a divisor with `e - 1`, for `e = 3` a
quadratic factor.

Table 4.6 (computed, `q = 7`, `e = 3`, `analysis/data/r4f_generic_q7e3.txt`).
Per base: the full-length `x` with `D_0 = D_1 = 0` that satisfy the identity,
the generic ones among them, the solutions among them, and all solutions.

| type of `B - 1` | `x` with `D_0 = D_1 = 0` and identity | generic | solutions among them | all solutions |
|---|---:|---:|---:|---:|
| three roots | 294 | 140 | 157.2 | 352.8 |
| root and quadratic | 294 | 42 | 74.3 | 78.0 |
| double root and root | 42 | 7 | 7.0 | 35.0 |
| irreducible cubic | 0 | 0 | 0 | 7.9 |
| triple root | 0 | 0 | 0 | 0 |

Every generic `x` of the proposition is a solution (140 of 140, 42 of 42, 7
of 7). In the bases with a quadratic factor, `sigma'^2 = 1` on
`F_q[T]/(B - 1)`, so all 294 such `x` satisfy the identity, and 95% of the
solutions of these bases have `D_0 = D_1 = 0`. The model gives these bases
52.2 solutions; they have 78.

Table 4.7 (computed, `analysis/r4f_bytype.py`). Census against the refined
model by the type of `B - 1`, for the types where `kappa > k` and the split
types.

| `q` | `e` | type of `B - 1` | `k` | `kappa` | census/base | refined | ratio |
|---:|---:|---|---:|---:|---:|---:|---:|
| 11 | 3 | root and quadratic | 2 | 3 | 140.0 | 122.5 | 1.14 |
| 13 | 3 | root and quadratic | 2 | 3 | 242.0 | 169.7 | 1.43 |
| 3 | 4 | root and cubic | 2 | 4 | 15.0 | 9.3 | 1.61 |
| 5 | 4 | root and cubic | 2 | 4 | 41.5 | 24.9 | 1.67 |
| 11 | 3 | three roots | 3 | 3 | 1320.0 | 1323.2 | 1.00 |
| 13 | 3 | three roots | 3 | 3 | 2148.6 | 2188.0 | 0.98 |
| 5 | 4 | four roots | 4 | 4 | 620.0 | 624.8 | 0.99 |

Heuristic 4.6. The `0^0 = 0` excess comes from the sector of class sums
that the Frobenius blocks force (lower classes zero or a multiple of `c(x)`).
The solutions concentrate there, and the model, which spreads them over all
class sums, assigns that sector the free residue factor `q^k`. Where the
identity restricted to the sector has the larger kernel `q^kappa`, the model
is low. Where `B - 1` splits, `sigma' = 1` and `kappa = k`, and the model is
right within 2%. Other types also deviate (for example `(5, 4)` with an
irreducible quartic, ratio 2.0), so this is the main mechanism, not the only
one.

### 4.6 Verdict

The model of chapter 5 assumes that the digits of `F(c)` behave like
independent uniform digits, subject only to the identity. In `F_q[T]` that
assumption fails at its root:

- Independence across positions fails. `F(x)` has `e(e+1)/2` parameters, and
  Corollary 2.3 builds its `L` digits from `e` single digits. About `1/e` of
  the positions are multiples of one fixed digit (Proposition 2.6).
- Uniformity fails. Whole positions are always zero or always of one degree
  (Table 4.1), and zeros are 4 to 700 times too common (Table 4.2).
- The identity modulo `B - 1` is exact and the model uses it correctly. The
  model's error is not in `F mod (B - 1)` but in which class sums the
  solutions have, which changes the free residue factor that applies to them
  (section 4.5).
- The zero-count term is the channel under `0^0 = 1`: Proposition 4.3 turns
  the whole gap into the share of solutions with `p | z`.
- The root is the Frobenius structure: `F` is additive, so `F(x)` is a
  Frobenius image, and Frobenius acts on base-`B` digits blockwise.

The round 3 evidence that "solutions are ordinary draws" came from a control
that maps most solutions to near-solutions one to one (Lemmas 4.1 and 4.2).
As the control randomizes more digits it moves to the model (Table 4.4).

## 5. Exact counts

### 5.1 Short solutions for every e

Call a solution short if `D_j` is a constant for every `j >= 2`. Then
`F = C + b T^q` with `b` the `T`-coefficient of `D_1`. For `e = 2` every
solution is short.

Theorem 5.1 (proven). Let `0^0 = 0` and `e >= 2`.

1. If base `B` has a short solution, then `B - 1` has `e` distinct roots in
   `F_q`.
2. Let `B - 1` have `e` distinct roots in `F_q`. Write
   `Q = (T^q - T)/(B - 1) = sum_i q_i B^i` in base `B`, put
   `delta_i = q_(i-1) - q_i` for `i >= 1`, let `E_j` be the sum of the
   `delta_i` of degree `j`, and let `j_0 = deg(T - q_0)`, with `j_0 = 0` when
   `T - q_0` is a constant. Base `B` has exactly `q (q-1)` short solutions,
   the numbers `C + b T^q` with `C` in `F_q` and `b != 0`, if
   - `E_j` is a constant for every `j >= 2` with `j != j_0`, and
   - in case `j_0 >= 2`, the `T`-coefficient of `E_1` is 1.

   Otherwise it has none.

Proof. Let `n` be short with class sums `D`. Then
`F = C + b T^q` with `C = sum_j D_j(0)`. If `b = 0`, `F` has one digit. (1)
The identity (Proposition 21.5, cited) gives `n == sum_j D_j = C + b T`
modulo `B - 1`, so `(B-1) | b (T^q - T)`. Since `T^q - T` is the product of
the `T - a`, `a` in `F_q`, `B - 1` has `e` distinct roots.

(2) Since `q >= e`, the monomials `T^(t q^j)` with `1 <= t <= j < e` are
distinct, so `F(D) = C + b T^q` holds exactly when `D_j` is constant for
`j >= 2`, the `T`-coefficient of `D_1` is `b`, and `sum_j D_j(0) = C`. Now
`C + b T^q = C + b T + b (B - 1) Q`, and
`(B - 1) Q = sum_i delta_i B^i` with `delta_0 = -q_0`. All these are digits,
so the base-`B` digits of `n = C + b T^q` are `d_0 = C + b (T - q_0)` and
`b delta_i` for `i >= 1`. The `delta_i` telescope: `sum_{i>=1} delta_i = q_0`,
so `sum_j E_j = q_0` and the digit sum is `C + b T`. Hence
`sum_j D_j(0) = C` always holds.

The digits `b delta_i` add `b E_j` to class `j`. If `j_0 >= 1`, `d_0` has
degree `j_0` for every `C` and `b`; if `j_0 = 0`, `d_0` is a constant or
zero. Consider the cases.

- `j_0 >= 2`. For `j >= 2`, `j != j_0`, `D_j = b E_j` must be constant. The
  class `j_0` sum is `C + b T - b sum_{j != j_0} E_j`; it is constant exactly
  when the `T`-coefficient of `E_1` is 1, which is also the condition on
  `D_1 = b E_1`.
- `j_0 = 1`. `D_j = b E_j` must be constant for `j >= 2`. Then
  `D_1 = C + b T - b sum_{j != 1} E_j` has `T`-coefficient `b`.
- `j_0 = 0`. `D_j = b E_j` must be constant for `j >= 2`. Then
  `sum_j E_j = q_0 = T - const` gives the `T`-coefficient 1 for `E_1`, so
  `D_1 = b E_1` is right.

The conditions do not involve `C` or `b`, so either all `q (q-1)` numbers are
solutions or none is. They have degree `q >= e`, so at least 2 digits.

For `e = 2` there is no `j >= 2`, and `j_0 <= 1`, so the test always passes:
this is Theorem 21.7 (cited) again.

Check (computed, `analysis/r4f_short.py`, `analysis/data/r4f_short_direct.txt`).
The test agrees with a direct enumeration of all short class sums in every
base for `(q, e) = (3,2), (5,2), (5,3), (7,3), (5,4)`, and with the census
lengths `floor(q/e) + 1` in every base for `(3,3), (7,3), (11,3), (13,3),
(17,3), (5,4)`.

Corollary 5.2 (proven). Let `e | q - 1` and `B = lambda T^e + mu`, where
`(1 - mu)/lambda` is a nonzero `e`-th power. Then `B` and every
`B(aT + b)` have exactly `q (q-1)` short solutions.

Proof. Put `u = T^e`, `k = (q-1)/e`, `c = (1 - mu)/lambda`. Then
`B - 1 = lambda (u - c)` has `e` distinct roots, and `c^k = 1`. So
`Q = T (u^k - 1) / (lambda (u - c)) = (T/lambda) sum_{i<k} c^(k-1-i) u^i`
with `u = (B - mu)/lambda`. This is `T` times a polynomial in `B` with
constant coefficients, so every digit of `Q` is a constant times `T`. All
`delta_i` have degree at most 1, so `E_j = 0` for `j >= 2`, and
`j_0 <= 1`. The test passes. Lemma 2.7 gives the images.

For `(5, 4)` the 20 bases with short solutions are exactly these binomial
bases and their translates (computed). For `e = 3` and `q == 1 (mod 3)` they
are the bases whose `B - 1` has its roots on a coset of the cube roots of
unity; in the normalized family `B = 1 + lambda T (T - 1)(T - gamma)` these
are the `gamma` with `gamma^2 - gamma + 1 = 0`, which pass for every
`lambda` (computed, `q = 7, 13, 19`).

### 5.2 Short solutions on average

Table 5.1 (computed). Short solutions per base, `e = 3`, with the number of
normalized pairs `(gamma, lambda)` that pass, out of `(q-1)(q-2)`.

| `q` | 5 | 7 | 11 | 13 | 17 | 19 | 23 |
|---|---:|---:|---:|---:|---:|---:|---:|
| short solutions per base | 0 | 2.571 | 1.818 | 9.231 | 4.706 | 17.05 | 7.65 |
| passing pairs | 0 of 12 | 18 of 30 | 12 of 90 | 60 of 132 | 30 of 240 | 108 of 306 | 48 of 462 |

For `q == 2 (mod 3)` about 2 pairs pass per `gamma`; for `q == 1 (mod 3)`
the binomial cosets add a whole row. The average is erratic in `q`, which is
one reason why Statement 3.2 finds no formula.

### 5.3 What is exact and what is not

Exact: the structure (section 2), the relation between the conventions
(Proposition 4.3), the short solutions (Theorem 5.1), and every census value
in Table 3.1, which is the exact average over all bases of degree `e`. Not
found: a closed formula for the average of the full-length solutions for
`e >= 3`. On each cell of fixed digit degrees the problem is a linear system
of `e(e+1)/2` equations, but the cells are many. For `e = 3` about `2q^2/9`
digits depend on the ratio of the two top coefficients of `D_2`, and each
drops its degree at one value of that ratio. With `2q^2/9` drops among `q`
values, almost every ratio is exceptional for some digit, so the cells are
small and do not share one system.

## 6. The integer case

The failing assumption is the same in the integers: the digits of
`S(c) = sum c_x x^x` are taken as independent and uniform. The question is
how much structure the integer digits have.

### 6.1 Only the top digits are forced

In `F_q[T]` additivity makes every block structured. `x -> x^x` is not
additive, and nothing like Lemma 2.1 holds. What remains is the top: the
largest digits fix the leading digits of `S(c)` (section 11.2, cited).

Table 6.1 (computed, `analysis/r4f_integer_zeros.py`, 100,000 random
`(b-1)`-digit strings per base with a `(b-1)`-digit sum, `0^0 = 1`,
`analysis/data/r4f_integer_zeros_m1.txt`). Zero digits of `S(c)` against
`c`, and the rate of zero digits at the top 3 and bottom 3 positions of
`S(c)`, times `b`.

| `b` | zeros of `c` | zeros of `S(c)` | `P(z_S = z_c)` | model | parity factor, true | model | top 3 positions | bottom 3 |
|---:|---:|---:|---:|---:|---:|---:|---|---|
| 11 | 0.785 | 0.759 | 0.366 | 0.359 | 1.218 | 1.184 | 0.00 0.01 0.27 | 1.01 1.00 1.03 |
| 15 | 0.841 | 0.891 | 0.334 | 0.344 | 1.113 | 1.156 | 0.00 1.85 1.83 | 1.00 1.01 1.00 |
| 21 | 0.885 | 0.809 | 0.338 | 0.333 | 1.181 | 1.142 | 0.00 0.00 0.04 | 1.02 1.01 0.99 |
| 25 | 0.903 | 0.879 | 0.328 | 0.329 | 1.186 | 1.137 | 0.00 0.00 0.76 | 0.98 1.00 0.99 |
| 31 | 0.925 | 0.891 | 0.327 | 0.325 | 1.139 | 1.109 | 0.00 1.16 0.11 | 0.98 1.02 1.01 |
| 41 | 0.940 | 0.879 | 0.325 | 0.321 | 1.150 | 1.125 | 0.00 0.00 0.05 | 1.01 1.00 0.99 |

The top 2 or 3 positions of `S(c)` are forced: they are almost never zero, or
zero far more often than `1/b`. Below them the zero rate is `1/b` within 3%.
So the integer digits of `S(c)` carry the forced top digits and nothing like
the block structure. Section 5.5 found the same for the fit of the top 10 and
bottom 8 digits (cited).

### 6.2 Estimates for the integer model

Heuristic 6.1. The forced top digits move the integer predictions by a few
percent:

- the zero count of `S(c)` is lower than that of `c` by 0.03 to 0.08 digits,
  and the chance that the zero counts match changes by less than 2%
  (Table 6.1);
- the parity factor under `0^0 = 1` in odd bases, computed with the true zero
  law of `S(c)`, is 2% to 4% above the model's for 5 of the 6 bases (Table
  6.1; the sampling error is about 1%);
- the forced-top correction of section 11.2 is 0.86 to 0.91 for `b`-digit
  solutions and near 1 for `b-1` and `b-2` digits (cited). With the 8% share
  of `b` digits this lowers the total by about 1%.

The `F_q[T]` mechanism of section 4.5 would need integer solutions to
concentrate on special multisets. A check of the zero digits of the actual
long solutions (`analysis/r4f_integer_types.py`, at least `b-6` digits,
bases 12 to 41):

| | long solutions | zero digits | model | solutions without zeros | model |
|---|---:|---:|---:|---:|---:|
| `0^0 = 0`, even bases | 19 | 10 | 16.8 +/- 4.0 | 11 | 7.7 |
| `0^0 = 0`, odd bases | 29 | 19 | 25.7 +/- 5.0 | 15 | 11.7 |
| `0^0 = 1`, even bases | 21 | 17 | 18.5 +/- 4.2 | 11 | 8.6 |
| `0^0 = 1`, odd bases | 23 | 16 | 14.6 +/- 4.8 | 15 | 16.1 |

Under `0^0 = 1` the solutions follow the model. Under `0^0 = 0` they have
fewer zeros, 29 against 42.5 (2.1 standard deviations). The forced top digits
account for 2 to 4 of the 13.5. I count the rest as chance, but it is the one
place where the integer data lean the way the toy world does.

### 6.3 The lesson for chapter 11

The near-solution test of section 11.1 uses offsets `D = j (b-1)` with even
`j <= 120`. Adding `j (b - 1) = j b - j` changes the two lowest digits by
`-j` and `+j`, but it changes `F` by `w(d_0 - j) - w(d_0) + w(d_1 + j) -
w(d_1)`, which is not 0. So the integer offsets have no analog of Lemmas 4.1
and 4.2: an integer near-solution is a different multiset, a genuine second
draw.

Each integer near-solution event asks whether the digits of `F(c) + D` form
`c`. For small `D` these share all but the bottom 2 or 3 digits with
`F(c)`. So the near-solution rate keeps any structure of the high digits of
`F` and randomizes only the bottom. Section 11.2a found that rate within
2% of the refined model under `0^0 = 0` and within 12% under `0^0 = 1`
(cited). Read with this draft, that says the high digits of the integer `F`
carry no structure that changes the count, beyond what those percentages
allow. The bottom digits are uniform by Table 6.1. In `F_q[T]` the same
reading fails twice: the round 3 offsets were not second draws (Lemmas 4.1,
4.2), and the low digits are structured (Table 4.4).

So the integer model survives this test, with an error budget of a few
percent from the forced top digits and about 10% unexplained under
`0^0 = 1` (section 11.2a, cited).

## 7. Open ends

- A formula, or a good heuristic, for the full-length count for `e >= 3`
  that uses the block structure: for example a model that keeps Corollary 2.3
  exactly and draws only the digits `tau_r` of `T^(tq)`.
- The test of Theorem 5.1 for `e = 3`, `q == 2 (mod 3)`: about 2 values of
  `lambda` pass per `gamma`. Which ones?
- Corollary 4.4 (2): a proof that `T^q` has no zero digit in a non-square base
  with two roots of `B - 1`.
- Whether the `0^0 = 0` zero deficit of the integer solutions (section 6.2)
  persists in bases above 41.

## Scripts and data

| file | contents |
|---|---|
| `fast/src/bin/r4f_ffield.rs` | census by the Horner form, orbits under `T -> aT + b`, exact model sums; `--types` splits by type |
| `analysis/r4f_lib.py` | polynomials, digit matrices, class sums and the model in numpy |
| `analysis/r4f_byk.py`, `r4f_bytype.py`, `r4f_dispersion.py` | census by `k(B)`, by type of `B - 1`, and `z`-scores |
| `analysis/r4f_conventions.py` | Proposition 4.3 against the census |
| `analysis/r4f_positions.py`, `r4f_zeros.py`, `r4f_profile.py` | digit law, zeros, and the true count law |
| `analysis/r4f_offsets.py` | near-solutions against the offset degree |
| `analysis/r4f_generic.py` | Proposition 4.5 in the census |
| `analysis/r4f_short.py` | Theorem 5.1 against direct counts and the census |
| `analysis/r4f_integer_zeros.py`, `r4f_integer_types.py` | the integer checks of section 6 |
| `analysis/data/r4f_*` | all outputs |
