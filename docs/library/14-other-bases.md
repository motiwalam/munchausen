# 14. Other number systems: negative, imaginary and Gaussian bases, and factorions

DRAFT. Answers questions 5, 6, 7 and 10 of `questions.md`.

Each statement is marked as in the library: proven (a proof is here),
computed (an exhaustive search, with its range), or model (the probabilistic
model of chapter 5, adapted).

## 14.1 Negative bases: structure

In base `-b`, with `b >= 2`, every integer has exactly one representation
`n = sum s_i (-b)^i` with digits `0 <= s_i <= b-1` and no sign. A
Munchausen number is a string with `n = F(n)`, where `F` is the sum of
`w(s_i)` as in chapter 1. Section 12.3 found the first examples.

Write `max_j` and `-negmin_j` for the largest and smallest values of strings
with `j` digits, leading zeros allowed:

    max_j    = (b-1) (1 + b^2 + b^4 + ...)      (even positions below j)
    negmin_j = (b-1) (b + b^3 + b^5 + ...)      (odd positions below j)

Proposition 14.1 (prefix intervals, proven). The integers with at most `j`
digits in base `-b` are exactly the interval `[-negmin_j, max_j]`. The
integers whose digits at positions `>= j` are fixed form a translate of this
interval by a multiple of `b^j`.

Proof. The `b^j` strings have distinct values, by uniqueness, and all lie in
the interval. The interval has `max_j + negmin_j + 1 = (b-1)(1 + b + ... +
b^(j-1)) + 1 = b^j` integers, so the strings fill it. Fixing the top part to
the value `m` gives the set `m (-b)^j + [-negmin_j, max_j]`.

So `n` and `n'` share all digits at positions `>= j` exactly when
`floor((n + negmin_j) / b^j) = floor((n' + negmin_j) / b^j)`. This is the
fact the search of chapter 6 needs, and section 14.2 uses it.

Corollary 14.2 (proven). For odd `d`, the integers with exactly `d` digits are
the interval

    L_d < n <= U_d,    L_d = (b^(d-1) - 1)/(b+1),   U_d = (b^(d+1) - 1)/(b+1).

For even `d` they are all negative. So `U_d / L_d` is about `b^2`: a window
twice as wide, in digits, as in a positive base, and only odd lengths.

Proposition 14.3 (proven). `n + negmin_d` has the base-`b` digits `s_i` at even
positions and `b-1-s_i` at odd positions.

Proof. `n + negmin_d = sum over even i of s_i b^i + sum over odd i of
(b-1-s_i) b^i`, and every coefficient is a base-`b` digit.

So base `-b` arithmetic is base `b` arithmetic after one shift. The `lanes`
engine of section 14.2 stores `n + negmin_d` in the digit vectors of
`fast/src/digits.rs`.

### 14.1.1 The only invariant residue

Proposition 14.4 (analog of Proposition 10.2, proven). Let `M >= 2`. The
residue `n mod M` depends only on the digit multiset of `n`, for all `n` with
at least 3 digits in base `-b`, exactly when `M` divides `b+1`.

Proof. Since `-b == 1 (mod b+1)`, every `n` satisfies
`n == s_0 + s_1 + ... (mod b+1)`, which depends only on the multiset. So every
divisor of `b+1` works. Conversely, take a number with at least 3 digits and
last two digits `x, y` with `x - y = 1`, and swap them. The leading digit does
not move, so both strings are valid numbers with the same multiset. The value
changes by `(x - y)(-b) + (y - x) = -(b+1)`. So `M` divides `b+1`.

For a solution, `n = F(n)`, so:

Proposition 14.5 (digit-sum identity, proven). Every solution in base `-b`
satisfies

    sum over digits x of ( w(x) - x ) == 0   (mod b+1).

This is the identity of section 1.6 with `b-1` replaced by `b+1`. The
consequences move with it:

- Odd `b`, `0^0 = 1`: a solution has an even number of zeros. Odd `b`,
  `0^0 = 0`: the identity holds modulo 2 for free, because `x^x == x (mod 2)`.
- `b == 3 (mod 4)`, `0^0 = 0`: the number of digits `== 2 (mod 4)` is even.
- `b == 2 (mod 3)`, `0^0 = 0`: the number of digits `== 2 (mod 6)` is a
  multiple of 3.

The proofs are those of section 1.6. The census of section 14.3 obeys all three
rules (`analysis/wld_negacompare.py` checks them).

So the parity doubling of section 5.3 happens in odd negative bases, the bases
`-b` with `b + 1` even. In positive bases it happens for odd `b`, where `b - 1`
is even. Both moduli are even exactly when `b` is odd, so the same `|b|` double
in both signs.

### 14.1.2 Length

Proposition 14.6 (proven). A solution in base `-b` has an odd number `d` of
digits with `d <= b+1`. So `d <= b+1` for even `b` and `d <= b` for odd `b`.

Proof. Odd length is Proposition 12.2. Let `d >= b+2` be odd. Then
`F(n) <= d (b-1)^(b-1)`, and `n > L_d`. It suffices that
`d (b+1) (b-1)^(b-1) + 1 <= b^(d-1)`. For `b = 2` the smallest such odd
`d` is 5, and `5 * 3 + 1 = 16 = 2^4`. For `b = 3` and `d = 5`,
`5 * 4 * 4 + 1 = 81 = 3^4`. For `b >= 4` and `d = b+2` the ratio of the left
side to `b^(b+1)` is at most `(1 + 2/b)(1 + 1/b)(1 - 1/b)^(b-1) + b^-(b+1)`,
and `(1 - 1/b)^(b-1)` decreases in `b`, so the ratio is at most
`1.875 * 0.422 + 0.001 < 1`. Going from `d` to `d+2` multiplies the left side
by less than 2 and the right side by `b^2 >= 4`.

The bound is reached. Base -10 has the 11-digit solution
`(1,9,2,1,7,4,5,8,9,8,9)` and base -14 the 15-digit solution
`(1,13,3,12,9,13,4,5,8,8,5,13,5,7,8)`, both with `b+1` digits.

### 14.1.3 The large-base limit

The basic model of section 5.1 carries over unchanged: `E_d` is the chance
that a random `d`-digit string has a sum with exactly `d` digits, now
`L_d < F <= U_d`. Each window holds `(b-1) b^(d-1)` integers, one per string,
so the argument of section 5.1 applies.

Let `b` grow. The digit counts become independent Poisson variables with mean
`d / b`, close to 1. A digit `b - y` weighs about `e^-y b^(b-y)`, so the
largest digit present fixes the size of `F`. With `c` copies of the largest
digit `b-1`, `F` is about `(c/e) b^(b-1)`; with largest digit `b-y`, about
`c e^-y b^(b-y)`. The window boundaries sit at even powers of `b` apart:

Proposition 14.7 (model). In the limit the expected number of solutions in base
`-b` with each length is:

| even `b` | share | odd `b` | share |
|---|---:|---|---:|
| `b+1` digits: 3 or more copies of `b-1` | 8.0% | `b` digits: at least one `b-1` | 63.2% |
| `b-1`: 1 or 2 copies of `b-1`, or none and some `b-2` | 78.4% | `b-2`: no `b-1`, some `b-2` or `b-3` | 31.8% |
| `b-3`: largest digit `b-3` or `b-4` | 11.7% | `b-4`: largest digit `b-4` or `b-5` | 4.3% |
| `b-5` | 1.6% | `b-6` | 0.6% |
| fewer | 0.3% | fewer | 0.1% |

Derivation. Even `b`, `d = b+1`: `L_d` is about `b^(b-1)`, so `F > L_d` needs
`c/e > 1`, that is `c >= 3`: `1 - (5/2) e^-1 = 0.080`. `d = b-1`: the window
is `(b^(b-3), b^(b-1))`, which holds `F` for `c` in {1, 2}, chance
`(3/2) e^-1 = 0.552`, and for `c = 0` with some `b-2`, chance
`e^-1 (1 - e^-1) = 0.233`. A largest digit `b-3` would need
`c e^-3 > 1`, 21 copies. Each further window drops two digit values:
`e^-2k (1 - e^-2)`. Odd `b`, `d = b`: the window `(b^(b-2), b^b)` holds `F`
for every `c >= 1` of the digit `b-1` (`1 - e^-1`), and for the digit `b-2`
only with 8 or more copies (`c e^-2 > 1`). Then `d = b-2` takes a largest
digit `b-2` or `b-3`: `e^-1 (1 - e^-2) = 0.318`, and so on with ratio `e^-2`.
Both columns sum to 1.

So a large negative base, like a large positive one, expects about one
solution per convention before the identity. The lengths differ: in an even
negative base 78% of the solutions have `b-1` digits, and the rare `b+1`-digit
solutions have the same 8% share as the `b`-digit solutions of positive
bases. In an odd negative base most solutions have `b` digits.

The refined model of section 5.3, with the identity of Proposition 14.5:

| | even `b` | odd `b` |
|---|---:|---:|
| `0^0 = 0` | 1 | 2 |
| `0^0 = 1` | 1 | `1 + e^-2 = 1.135` |

## 14.2 A search engine for negative bases (question 6)

`fast/src/bin/worlds.rs` has three engines. All three print the same
solutions on every base they share, under both conventions.

- `brute` enumerates every digit multiset whose partial sums can still land
  in the window `(L_d, U_d]`, filters by Proposition 14.5 and checks the rest
  exactly. It also sums the model of section 14.1.3 exactly. Bases -2 to -18;
  base -18 takes 86 seconds per convention on 3 threads.
- `tree` decides the counts from the largest digit down, like
  `fast/src/search.rs`. The range `[lo, hi]` of the final sum is an interval,
  and by Proposition 14.1 the digits that `lo` and `hi` share at the top are
  digits of every number in between. A known top digit `x` must fit the count
  already decided for `x`, or, if `x` is still undecided, it forces one copy
  of `x` into the sum, which narrows the range again. Arithmetic is `u128`,
  enough up to base -26.
- `lanes` is the same tree on the digit vectors of `fast/src/digits.rs`. By
  Proposition 14.3 it stores `n + negmin_d`, whose base-`b` digits are the
  base `-b` digits with the odd positions complemented. So a negative base
  costs the same as a positive one. It reaches base -35.

Speed (computed, `0^0 = 1`, 3 threads):

| base | tree nodes | seconds |
|---:|---:|---:|
| -20 | `1.3 * 10^5` | 0.06 |
| -25 | `2.6 * 10^6` | 0.38 |
| -30 | `8.2 * 10^7` | 9.0 |
| -35 | `1.6 * 10^9` | 235 |

The tree grows about 1.9x per base, the rate of the positive-base search
(section 14.6.1). The Python reference `analysis/negabase.py` stops near base
-12, and `brute` grows about 3.5x per base.

## 14.3 The census of negative bases (computed)

All solutions in bases -2 to -35 under both conventions
(`analysis/data/wld_negabase_census.txt`). `E_m` is the refined model,
summed exactly for bases up to -18 and sampled with 400,000 strings per
length above (`analysis/wld_negamodel.py`). The lengths are listed per
solution.

| base | `0^0 = 1` | lengths | `E_1` | `0^0 = 0` | lengths | `E_0` |
|---:|---:|---|---:|---:|---|---:|
| -2 | 1 | 3 | 0.75 | 2 | 3, 3 | 2.25 |
| -3 | 0 | | 1.11 | 0 | | 1.33 |
| -4 | 0 | | 1.05 | 1 | 5 | 0.63 |
| -5 | 1 | 5 | 1.16 | 2 | 3, 5 | 2.54 |
| -6 | 0 | | 1.20 | 0 | | 1.17 |
| -7 | 3 | 3, 7, 7 | 1.48 | 4 | 3, 3, 7, 7 | 2.55 |
| -8 | 1 | 7 | 1.36 | 2 | 3, 3 | 1.58 |
| -9 | 0 | | 1.40 | 0 | | 2.31 |
| -10 | 3 | 9, 9, 11 | 1.30 | 4 | 9, 9, 9, 11 | 1.24 |
| -11 | 2 | 9, 11 | 1.61 | 2 | 11, 11 | 2.80 |
| -12 | 1 | 11 | 1.23 | 0 | | 1.27 |
| -13 | 1 | 13 | 1.44 | 4 | 7, 13, 13, 13 | 2.48 |
| -14 | 2 | 13, 15 | 1.20 | 1 | 15 | 1.12 |
| -15 | 0 | | 1.38 | 0 | | 2.37 |
| -16 | 0 | | 1.18 | 1 | 15 | 1.13 |
| -17 | 1 | 17 | 1.34 | 2 | 17, 17 | 2.29 |
| -18 | 0 | | 1.12 | 0 | | 1.12 |
| -19 | 1 | 19 | 1.30 | 1 | 19 | 2.27 |
| -20 | 0 | | 1.12 | 0 | | 1.12 |
| -21 | 2 | 21, 21 | 1.31 | 1 | 21 | 2.25 |
| -22 | 0 | | 1.11 | 1 | 21 | 1.11 |
| -23 | 1 | 23 | 1.30 | 2 | 21, 23 | 2.27 |
| -24 | 0 | | 1.10 | 3 | 23, 23, 23 | 1.09 |
| -25 | 0 | | 1.27 | 2 | 3, 3 | 2.18 |
| -26 | 1 | 27 | 1.08 | 0 | | 1.07 |
| -27 | 1 | 25 | 1.24 | 2 | 25, 27 | 2.15 |
| -28 | 2 | 23, 27 | 1.06 | 1 | 23 | 1.05 |
| -29 | 0 | | 1.21 | 1 | 27 | 2.13 |
| -30 | 0 | | 1.05 | 0 | | 1.05 |
| -31 | 4 | 31, 31, 31, 31 | 1.19 | 5 | 29, 29, 31, 31, 31 | 2.10 |
| -32 | 2 | 31, 31 | 1.05 | 4 | 13, 13, 31, 31 | 1.06 |
| -33 | 1 | 33 | 1.21 | 3 | 33, 33, 33 | 2.09 |
| -34 | 0 | | 1.05 | 0 | | 1.04 |
| -35 | 0 | | 1.23 | 1 | 33 | 2.14 |

Algebraic solutions show up as in positive bases. Under `0^0 = 0` the twins
`(...,0)` and `(...,1)` of section 2.1 appear in bases -2, -7, -8, -10,
-25 and -32. `(4,0,0)` in base -8 and `(5,0,0)` in base -25 are the family
`(x,0,0)` in base `-x^((x-1)/2)` of section 12.3, which needs `x` odd or a
square. The 13-digit pair in base
-32 is `(16,0,...,0)` and `(16,0,...,0,1)`: the digit 16 pays for itself at
position 12, because `16 * 32^12 = 2^64 = 16^16` and `(-32)^12 > 0`.

The `(b+1)`-digit solutions, in bases -10, -14 and -26, all start with the
digit 1 and continue with the digit `b-1`: `(1,9,2,...)`, `(1,13,3,...)`,
`(1,25,13,...)`. With `c >= 3` copies of `b-1` the sum is about
`(c/e) b^(b-1)`, and in base `-b` that is `1 * b^b - s * b^(b-1) + ...` with
`s` about `b - c/e`, so `s = b-1` for `c` = 3 or 4.

### 14.3.1 Counts against the model

Bases -10 to -35 (`analysis/wld_negacompare.py`):

| convention | bases | observed | refined model | basic model | `P(X <= observed)` |
|---|---|---:|---:|---:|---:|
| `0^0 = 0` | even | 15 | 14.5 | 14.6 | 0.62 |
| `0^0 = 0` | odd | 26 | 29.5 | 14.5 | 0.30 |
| `0^0 = 1` | even | 11 | 14.6 | 14.6 | 0.21 |
| `0^0 = 1` | odd | 14 | 17.0 | 14.5 | 0.28 |

The refined model fits. The parity doubling is plain: odd bases have 26
solutions under `0^0 = 0` against 15 in even bases. The basic model, without
the identity, predicts the same for both. Unlike positive bases (section
5.4) there is no surplus: the counts sit slightly below the model in all four
groups, by 1 standard deviation or less.

At finite `b` the model expects more than its limit: 1.25 per convention in
base -10 and 1.15 in base -18 (basic model, exact), 1.05 in base -34. The surplus comes
from short lengths, where a few large digits suffice. Lengths 3 to 7 carry
0.35 of the 1.25 in base -10 and 0.05 in base -18.

### 14.3.2 Length shares

Bases -10 to -35, both conventions. "top" is `b+1` for even `b` and `b` for
odd `b`:

| length | even `b`, observed | model (finite `b`) | limit | odd `b`, observed | model (finite `b`) | limit |
|---|---:|---:|---:|---:|---:|---:|
| top | 5 (19%) | 2.2 (8%) | 8.0% | 29 (72%) | 26.1 (56%) | 63.2% |
| top - 2 | 17 (65%) | 20.7 (71%) | 78.4% | 8 (20%) | 13.9 (30%) | 31.8% |
| top - 4 | 0 | 3.1 (11%) | 11.7% | 0 | 2.1 (5%) | 4.3% |
| top - 6 | 2 | 1.5 | 1.6% | 1 | 1.7 | 0.6% |
| shorter | 2 | 0.8 | | 2 | 2.6 | |

The two laws of Proposition 14.7 are visible: in even bases most solutions
have `b-1` digits, in odd bases `b` digits. The top length is over-represented
in both columns, 5 against 2.2 and 29 against 26.1. Together that is 34
against 28.3, a surplus of about 1 standard deviation. It echoes the excess of
`(b-1)`-digit solutions of section 5.5 and is not significant on its own.
The 5 at the top length of even bases are 3 strings: the zero-free ones of
bases -10 and -14 count in both conventions, and base -26 adds one.

### 14.3.3 Empty bases, and bases -3, -6, -9

Eight bases from -2 to -35 have no solution in either convention: -3, -6,
-9, -15, -18, -20, -30 and -34. The model gives each base a chance
`exp(-E_union)` to be empty, with `E_union = E_0 + E_1 - E_zerofree`,
because a solution without zeros counts in both conventions. That chance is
about 17% for even and 7% for odd bases. The expected number of empty bases is
4.2; 8 or more happens with probability 0.046.

Six of the eight are multiples of 3. Bases -3, -6 and -9 were named before
this census, so the fair test uses the later multiples of 3: -12 to -33.
Three of these eight bases are empty (-15, -18, -30) against 0.97 expected;
3 or more happens with probability 0.06.

No congruence explains it. A multiple of 3 has `b + 1 == 1 (mod 3)`, so
Proposition 14.4 gives it no condition at 3, and -21, -24, -27 and -33 have
solutions. The defect spectrum of section 11.1 tests the rest
(`analysis/wld_negadefects.py`, `analysis/data/wld_negadefects.txt`): for
30 offsets `D` in the class of 0 (multiples of `b+1`, of `2(b+1)` in even
bases), count the `n` with `n = F(n) + D`.

| base | mean count per offset, `0^0 = 1` | model `E_1` | mean, `0^0 = 0` | model `E_0` |
|---:|---:|---:|---:|---:|
| -12 | 1.43 | 1.23 | 1.70 | 1.27 |
| -15 | 1.37 | 1.38 | 2.67 | 2.37 |
| -18 | 1.13 | 1.12 | 1.17 | 1.12 |
| -21 | 1.43 | 1.31 | 2.20 | 2.25 |
| -24 | 1.13 | 1.10 | 1.13 | 1.09 |
| -16 (for comparison) | 1.13 | 1.18 | 1.60 | 1.13 |

The empty bases -15 and -18 have normal spectra. Over all 30 cases (bases
-10 to -24, both conventions), the variance/mean ratio of the counts has
median 0.90 (range 0.51 to 1.61), a Poisson law as in positive bases. So a
base does not "know" that it is empty, and -15 and -18 are empty by chance.
Bases -3, -6 and -9 are too small for a spectrum; the model gives them
chances 0.21, 0.17 and 0.07 to be empty, and the product 0.0026 is not small
among 34 bases with 8 empty. The cluster at multiples of 3 is a 6% event once
the three named bases are set aside. Verdict: chance (computed for -15 and
-18, model for -3, -6, -9).

## 14.4 Imaginary bases `ci`

Proposition 14.8 (proven). Let `c >= 2`. A string `S` is a Munchausen number in
base `ci` (digits 0 to `c^2 - 1`) exactly when its digits at odd positions are
all 0 and its digits at even positions form a string `t` of odd length `d`
with

    value of t in base -c^2  =  F_m(t) + m (d - 1).

In particular `S` has `2d - 1 == 1 (mod 4)` digits, and under `0^0 = 0` the
Munchausen numbers of base `ci` and base `-c^2` correspond one to one.

Proof. `(ci)^(2k) = (-c^2)^k` and `(ci)^(2k+1) = ci (-c^2)^k`. So the value of
`S` is `A + ci B`, where `A` is the value of the even-position digits in base
`-c^2` and `B` that of the odd-position digits. `F(S)` is a positive integer,
so `B = 0`, and by uniqueness in base `-c^2` all odd-position digits are 0.
The top digit of `S` sits at an even position, so `S` has `2d - 1` digits,
and `d` is odd by Proposition 12.2. The `d - 1` zeros at odd positions add
`m (d - 1)` to `F`.

`worlds lanes -c^2 pow1 --offset-per-digit 1` lists the `0^0 = 1` case
(`analysis/data/wld_imaginary.txt`); `analysis/wld_imaginary.py` confirms base
`2i` by brute force over all strings up to 9 digits.

| base | `0^0 = 1` | `0^0 = 0` (from base `-c^2`) |
|---|---|---|
| `2i` | `(1,0,2,0,0)`: `16 - 8 = 8 = 1+1+4+1+1` | `(1,0,3,0,0,0,2,0,3)` |
| `3i` | `(1,0,3,0,3)`, `(1,0,5,0,3,0,0,0,0)`, one with 13 digits | none |
| `4i` | `(1,0,0,0,4)`, one with 29 digits | one with 29 digits |
| `5i` | none | `(5,0,0,0,0)`, `(5,0,0,0,1)` |

## 14.5 Gaussian bases `-n+i` (question 7)

In base `beta = -n + i`, with digits 0 to `n^2`, every Gaussian integer has
exactly one representation (Katai and Szabo). The last digit of `a + bi` is
`(a + n b) mod (n^2 + 1)`, because `i == n (mod beta)`.
`fast/src/bin/gauss.rs` enumerates digit multisets, writes `F` in base `beta`
and compares, and sums the model exactly.

Proposition 14.9 (identity, proven). Every Gaussian integer satisfies
`z == digit sum (mod beta - 1)`. A rational integer is divisible by the
primitive Gaussian integer `beta - 1 = -(n+1) + i` exactly when it is
divisible by its norm `M = (n+1)^2 + 1`. So a solution satisfies
`sum (w(x) - x) == 0 (mod M)`. As in Proposition 14.4, swapping the last two
digits changes the value by `(x - y)(beta - 1)`, so no other Gaussian modulus
is a function of the multiset.

`M` is even exactly when `n` is even. So the parity doubling under `0^0 = 0`
holds in the bases -2+i and -4+i and not in -1+i and -3+i.

Proposition 14.10 (length bound, proven with a finite computation). Let
`R0 = n^2 / (|beta| - 1)` and let `L0` be the largest length of a Gaussian
integer with `|z| < 1 + R0`. Then every `z != 0` has at most
`ceil(log |z| / log |beta|) + L0` digits, and a solution has at most `D`
digits:

| base | `L0` | `D` | identity modulus `M` |
|---|---:|---:|---:|
| -1+i | 9 | 18 | 5 |
| -2+i | 5 | 16 | 10 |
| -3+i | 4 | 24 | 17 |
| -4+i | 4 | 38 | 26 |

Proof. With `z_0 = z` and `z_(k+1) = (z_k - a_k)/beta`,
`|z_(k+1)| <= (|z_k| + n^2) / |beta|`, so
`|z_k| < |z| / |beta|^k + R0`. After `k = ceil(log_|beta| |z|)` steps
`|z_k| < 1 + R0`, and `z_k` has at most `L0` more digits. A `d`-digit
solution has `F <= d n^(2 n^2)`; `D` is the largest `d` with
`d <= ceil(log_|beta|(d n^(2n^2))) + L0`.

The census (complete up to `D` digits for `n` = 1, 2, 3;
`analysis/data/wld_gauss_census.txt`):

| base | `0^0 = 1` | model `E_1` | `0^0 = 0` | model `E_0` |
|---|---|---:|---|---:|
| -1+i | `(1,1,1,0,0,0,0,0,1)` = 9 | | `(1,1,0,0)` = 2, `(1,1,0,1)` = 3, and four with 9 digits = 4 to 7 | |
| -2+i | none | 1.05 | `(4,2,4,0,4,1,0,4)` = 1029 | 2.22 |
| -3+i | three with 19 digits, one with 21 | 1.11 | the same 21-digit string (no zeros) | 1.10 |
| -4+i | none up to 22 digits | 1.06 | not searched | 2.08 |

Base -1+i is degenerate: both weights are 1, so `F` is the number of ones
(or of digits), and the solutions are the integers whose representation has
that many ones. The model does not apply to it.

The 21-digit solution of base -3+i is
`(1,5,9,2,5,4,9,7,1,3,9,1,9,2,9,1,7,8,2,8,8)` = 1,989,087,728. Its three
19-digit companions under `0^0 = 1` have values 404,344,784 to 454,535,682.
`analysis/wld_gauss_census.txt` holds them all; each was rechecked in exact
Gaussian arithmetic.

Base -4+i is out of reach for this enumeration. Length 22 alone has
`5 * 10^8` multisets in the window and took 458 seconds, and the model puts
99% of its expectation above 22 digits, mostly at 34 digits (83%). A prefix
tree like that of section 14.2 would need the top digits of a real interval,
which in base `-n+i` are not an interval but the points of a fractal tile on
a line.

### 14.5.1 Lengths of positive integers

Positive integers do not use every length (computed for all integers up to
`10^6` and samples up to `10^30`, `analysis/wld_gauss_lengths.py`):

| base | lengths up to 40 that never occur |
|---|---|
| -1+i | all but 1, 4, 9, 12, 17, 20, 25, 28 |
| -2+i | 2, 3, 5, 7, 10, 12, 14, 17, 19, 21, 24, 26, 31, 33, 38, 40 |
| -3+i | 2, 3, 5, 7, 9, 14, 16, 18, 23, 25, 27, 32, 34, 36, 38 |
| -4+i | 2, 3, 5, 7, 9, 16, 18, 20, 22, 29, 31, 33, 35 |

This is the analog of the odd lengths of negative bases (Proposition 12.2). A
positive `N` with `D` digits is `beta^(D-1)` times a point of the tile
`s + T0` near the top digit `s`, so `(D-1) arg(beta)` must point into that
tile (heuristic). `arg(beta) = pi - arctan(1/n)`, so two more digits turn
the direction by `-2 arctan(1/n)`. The lengths come in runs of one parity,
and the parity switches about every `pi / arctan(1/n)` digits: 6.8 for
-2+i, 9.8 for -3+i, 12.8 for -4+i, as in the table. For base -1+i,
`beta^8 = 16`, so `ell(16 N) = ell(N) + 8` and the set of lengths is closed
under adding 8 (proven). The model has `E_d = 0` exactly at the missing
lengths, and the Munchausen numbers found have lengths 4, 8, 9, 19 and 21,
all allowed.

### 14.5.2 The model for Gaussian bases

`E_d` is the chance that a random `d`-digit string has a sum `F` with `d`
digits, refined by the factor `M` on the identity. For `n` = 2, 3, 4 the
expected count per convention is 1.05, 1.11 and 1.06, and doubles under
`0^0 = 0` for even `n` (2.22 and 2.08). The census matches it: 1 solution
against 2.22 and none against 1.05 for -2+i, 1 against 1.10 under
`0^0 = 0` for -3+i. The exception is -3+i under `0^0 = 1`, with 4
against 1.11 (`P = 0.026`).

The reason the count is again about 1 is general (model). Near the length
where `F` and the strings have the same size, the length `ell(F)` of the sum
of a random `d`-string barely depends on `d`: `F` is dominated by the copies
of the largest digit. Then `sum_d P(ell(F_d) = d)` is close to
`sum_l P(ell(F) = l) = 1`. Sections 5.2 and 1.3 are the cases where this sum
can be done in closed form. One length takes most of the mass: 19 digits
(75%) for -3+i, 34 digits (83%) for -4+i. `F` is about `c n^(2n^2)`, with
`c` the number of copies of the top digit `n^2`, and two more digits multiply
the size of a number by `|beta|^2 = n^2 + 1`. So the typical values of `c`
(1 to 4) move `F` by less than two lengths, and the gaps of section 14.5.1 leave
one or two allowed lengths in that range.

## 14.6 Universality: factorions (question 10)

A factorion is an `n` equal to the sum of `x!` over its base-`b` digits, with
`0! = 1` (OEIS A014080 for base 10, A193163 for the counts). `worlds` handles
the weights `x!` with the same engines (`analysis/data/wld_factorion_census.txt`,
bases 2 to 41; `brute` and `lanes` agree on bases 2 to 16). Base 10 gives
145 and 40585, base 11 gives 26, 48 and 40472, as known.

### 14.6.1 What changes

The 8/55/23% law of section 5.2 rests on two facts about `w(x) = x^x`:

- the top weight sits at a fixed height: `(b-1)^(b-1) = b^(b-1) / e` in the
  limit, so `c` copies cross a power of `b` at `c = e`;
- one digit value lower costs a factor `e b`: `(b-1)^(b-1) / (b-2)^(b-2)` is
  about `e (b-1)`.

For `x^(x+t)` with fixed `t`, both facts hold unchanged, with the lengths
shifted by `t`. So the law is the same (model). The census of `x^(x+1)` under
`0^0 = 1`, bases 10 to 28 (`analysis/data/wld_powt1_census.txt`), has 26
solutions: 3 with `b+1` digits, 15 with `b`, 2 with `b-1`, 6 shorter. The
model says 8%, 55% and 23% for `b+1`, `b`, `b-1`.

For `x!` both facts fail. One digit value lower costs only a factor `b-1`,
and the height of the top weight, `theta(b) = frac(log_b (b-1)!)`, moves with
`b`. Let `L(b) = floor(log_b (b-1)!) + 1`, the length of `(b-1)!`.

Proposition 14.11 (model). For factorions, a `d`-digit string has digit counts
of mean `lambda = d / b`, and lengths near `L(b)` have `lambda` about
`L(b)/b = 1 - 1/ln b + o(1/ln b)`. With `c` copies of the largest digit
`b-1-k`, `F` is about `c (b-1)! / b^k`, so it has `L(b) - k` digits unless
`theta + log_b c >= 1`, when it has one more. Since `log_b c -> 0`, for
almost all large `b` the shares are

    P(length L(b) - k) = (1 - e^-lambda) e^(-k lambda),   k = 0, 1, 2, ...

which tends to 63.2%, 23.3%, 8.6%, 3.2%. The top share equals that of odd
negative bases (Proposition 14.7), but the shares fall by `e^-1` per length,
not `e^-2`. It is not the 8/55/23% law. The expected total is still 1 per base.

Derivation. The weights `(b-1-k)!` fall by a factor about `b` per step, so the
largest digit present fixes the power of `b`, and the number of its copies only
fixes the leading digit. The top digit `b-1-k` is the largest present with
chance `e^(-k lambda) (1 - e^-lambda)`.

The convergence is slow, because `lambda - 1` is about `-1/ln b` and
`log_b c` is about `ln c / ln b`. Sampled model (`analysis/wld_factmodel.py`):

| base | `L(b)/b` | `L-2` | `L-1` | `L` | `L+1` | total |
|---:|---:|---:|---:|---:|---:|---:|
| 100 | 0.780 | 11.1% | 20.1% | 43.9% | 18.5% | 1.02 |
| 300 | 0.827 | 10.8% | 24.4% | 56.2% | 0 | 1.01 |
| 1,000 | 0.855 | 9.5% | 23.1% | 54.6% | 5.6% | 1.00 |
| 10,000 | 0.891 | 11.3% | 24.4% | 57.0% | 0.8% | 1.00 |

The `L+1` share is the leak through `theta`. `theta(100) = 0.985`, so 2
copies of the digit 99 already reach the next power of 100.
`theta(1000) = 0.868` needs 3 copies and `theta(10^4) = 0.864` needs 4.
`theta(300) = 0.064` leaves no leak.

### 14.6.2 The census against the model

Bases 10 to 41 (`analysis/wld_factcompare.py`):

| | observed | model |
|---|---:|---:|
| factorions | 37 | 37.1 |
| bases with none | 11 | 10.1 |
| lengths `L-5` to `L+1` | 28 | 34.8 |
| lengths `L-6` and shorter | 9 | 2.3 |

| length | `L-4` | `L-3` | `L-2` | `L-1` | `L` | `L+1` |
|---|---:|---:|---:|---:|---:|---:|
| observed | 3 | 1 | 2 | 9 | 9 | 2 |
| model | 1.6 | 2.6 | 4.5 | 8.0 | 15.8 | 1.3 |

The count per base and the share of empty bases follow the model. The long
factorions follow its length law loosely; the top length is short of the
model (9 against 15.8). Short factorions, most of them with 2 digits, are four
times too common, as are the short Munchausen numbers of section 10.5. They
are roots of a low-degree polynomial in `b`, where the per-base model does not
apply. The two `L+1` factorions sit in bases 17 and 5, where `theta` is 0.83
and 0.97, as Proposition 14.11 requires.

There is no parity effect: `x! == 0 (mod 2)` for `x >= 2`, so the identity
modulo `b-1` gives no free factor. The census agrees: 15 factorions in the 16
odd bases from 11 to 41, 22 in the 16 even bases from 10 to 40.

Update (chapter 33). For short factorions the polynomial view now gives
theorems. Every `x >= 3` gives the 2-digit factorion `(1, x)` in base
`x! - x + 1` (Proposition 33.9), so 2-digit factorions are infinitely many.
A 3-digit factorion with one large digit `x` has `x` below an explicit
bound when `x` is last or in the middle (Theorems 33.4 and 33.5), because
`x!` is divisible by every prime up to `x`. With the two other digits at
most 10 the 3-digit factorions are the 7 known ones (8 under `w(0) = 0`),
except a leading `x > 4,103,641` with `4x x! + s^2` a square, a problem of
Brocard type (Theorem 33.6).

### 14.6.3 What is universal

- Universal (model, confirmed in all four systems): about one solution per
  base and convention, a Poisson count, and empty bases at rate
  `exp(-E)`. Section 5.2 explains why: the length of the sum barely depends on
  the length of the string, so the expectations over all lengths add to 1.

  Update (chapter 34): for `x^x` this is now a theorem in the model. The
  law of the length of `F` for a string of `b - j` digits tends to the same
  limit for every fixed `j` (Theorem 34.6, Corollary 34.7).
- Universal: the identity modulo the "digit-sum modulus" (`b-1`, `b+1`,
  `(n+1)^2 + 1`) and the parity factor 2 whenever that modulus is even and
  `w(x) == x (mod 2)`.
- Not universal: the length shares. They depend on the height of the top
  weight between powers of the base and on the cost of one digit value less.
  `x^x` and `x^(x+t)` give 8/55/23%; even negative bases give 8/78/12%; odd
  negative bases and factorions give geometric laws, with ratio `e^-2` and
  `e^-1` respectively.

## 14.7 Status

| question | answer | status |
|---|---|---|
| 5. invariant residues in base `-b` | only the divisors of `b+1` (Proposition 14.4) | proven |
| 5. identity, parity, length | `sum (w(x) - x) == 0 (mod b+1)`; parity doubling in odd `b`; odd lengths up to `b+1` (Propositions 14.5, 14.6) | proven |
| 5. length shares | even `b`: 8.0/78.4/11.7%; odd `b`: 63.2/31.8/4.3% (Proposition 14.7) | model |
| 5. census | bases -2 to -35, both conventions (section 14.3) | computed |
| 5. census against model | counts within 1 standard deviation; parity doubling confirmed | computed |
| 5. bases -3, -6, -9 | empty by chance: normal defect spectra; the multiples of 3 cluster is a 6% event after selection | computed and model |
| 6. engine | prefix intervals (Proposition 14.1) and a shifted digit vector (Proposition 14.3); 1.9x per base, base -35 in 4 minutes | computed |
| 7. imaginary bases `ci` | reduce to base `-c^2` with offset `m (d-1)`; lengths `== 1 (mod 4)` (Proposition 14.8) | proven |
| 7. Gaussian bases | census for -1+i, -2+i, -3+i; -4+i only to 22 digits; length bound (Proposition 14.10); about 1 per convention | computed, model |
| 7. lengths in Gaussian bases | positive integers skip some lengths, in runs (section 14.5.1) | computed |
| 10. universality | count law universal; length shares not: factorions follow `(1 - e^-lambda) e^(-k lambda)` (Proposition 14.11) | model, computed to base 41 |

Open questions raised here:

- A proof of the set of lengths that positive integers take in base -n+i.
  For -1+i the data say lengths `== 1` or `4 (mod 8)`. (Proved for -1+i
  in chapter 23: Theorem 23.1 gives exactly the lengths `8m + 1` and
  `8m + 4`, both for every `m`. The bases -n+i with `n >= 2` remain open.)
- A search for base -4+i past 22 digits needs the top digits of a real
  interval, which are not an interval. A tile-based prefix test might work.
- Base -3+i has 4 solutions under `0^0 = 1` against 1.11 expected, three of
  them with 19 digits. Is it chance (`P = 0.026`)?
- Short factorions and short negative-base solutions are much more common
  than the per-base model says, as for short Munchausen numbers. The
  polynomial heuristic of section 11.4 is the natural tool for them.
  (For factorions, chapter 33 proves more: 2-digit factorions are
  infinitely many (Proposition 33.9), and the 3-digit ones with one large
  digit are finite except a leading case of Brocard type (Theorem 33.4).)
