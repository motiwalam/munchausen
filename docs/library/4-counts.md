# 4. Counting solutions per base

This chapter is about `N_m(b)`, the number of nontrivial solutions in base `b`
under convention `m`. It separates what is proven from what the data shows.

## 4.1 What is proven

Upper bounds:

- `N_m(b)` is finite, because a solution has at most `b` digits
  (Proposition 1.1). A trivial bound is the number of digit multisets,
  `C(2b, b)`, about `4^b`.
- For a fixed length the bound is much smaller:

Proposition 4.1. `N_{m,k}(b) <= 2 (X_k(b) + 1)^(k-1)`, where `X_k(b)` is the
largest digit with `x^x < b^k`. For fixed `k` this is
`O((k ln b)^(k-1))`, a power of `log b`.

Proof. By Proposition 1.2 every digit is at most `X_k(b)`. Fix the last `k-1`
digits; there are at most `(X_k(b) + 1)^(k-1)` ways. The leading digit `a` must
then satisfy `a^a - a b^(k-1) = R`, where `R` depends only on the fixed digits.
The left side is a strictly convex function of `a`, so at most two values of `a`
work.

No bound of the form "at most `C` solutions in every base" holds under
`0^0 = 0`:

Proposition 4.2. Under `m = 0`, for every `L >= 2`, the base
`b = 2^(L (2^L - 1))` has at least `2^(2^L - 1) - 2` nontrivial solutions. So
`N_0(b)` is unbounded. Along this sequence of bases it grows like
`b^(1/L)` with `L ~ log2 log2 b`, which is faster than any power of `log b`.

Proof. Let `N = L (2^L - 1)`. For `s = jL` with `1 <= j <= 2^L - 2`, the
digit `2^s` is self-paying: `2^L - 1` divides `2^(jL) - 1`, so `N` divides
`s (2^s - 1)`, and `2^s < 2^N = b`. That gives `2^L - 2` self-paying digits,
and Corollary 2.4 gives the count.

| `L` | base | self-paying digits | solutions at least |
|---:|---|---:|---:|
| 2 | `2^6 = 64` | 2 | 6 |
| 3 | `2^21` | 6 | 126 |
| 4 | `2^60` | 14 | 32,766 |
| 5 | `2^155` | 30 | 2,147,483,646 |

For `L = 2` and `L = 3` every one of these solutions was checked with exact
integers. For `L = 4` and `L = 5` the numbers are too long to write out, so
`analysis/verify_constructions.py` checks the exponent identity of each digit.
For base 64 the search finds exactly these 6 among the solutions with at most
30 digits.

Under `0^0 = 1` it is unknown whether `N_1(b)` is bounded. Self-paying digits
do not combine freely there, because each zero in between weighs 1.

Lower bounds for single bases:

- `N_0(b) >= 2^(C+1) - 2` if `b` has `C` self-paying digits (Corollary 2.4).
- `N_m(b) >= 1` if `b` is one of the 2-digit bases of section 2.4.

A parity rule:

- `N_0(b)` has the same parity as the number of solutions whose last digit is
  2 or more. Solutions ending in 0 or 1 come in twins (Proposition 2.1).

## 4.2 The data

Exhaustive results for bases 2 to 40. `n0` and `n1` count nontrivial
solutions under `0^0 = 0` and `0^0 = 1`. "shared" counts solutions without a
zero, which are solutions under both conventions (Proposition 1.4). "longest" is
the largest number of digits, under either convention.

| base | n0 | n1 | shared | longest | | base | n0 | n1 | shared | longest |
|---:|---:|---:|---:|---:|---|---:|---:|---:|---:|---:|
| 2 | 0 | 1 | 0 | 2 | | 22 | 1 | 1 | 1 | 20 |
| 3 | 2 | 2 | 2 | 2 | | 23 | 1 | 0 | 0 | 22 |
| 4 | 3 | 2 | 2 | 3 | | 24 | 1 | 1 | 1 | 23 |
| 5 | 2 | 0 | 0 | 4 | | 25 | 5 | 2 | 2 | 24 |
| 6 | 2 | 2 | 2 | 5 | | 26 | 1 | 2 | 0 | 25 |
| 7 | 1 | 1 | 1 | 5 | | 27 | 0 | 0 | 0 | - |
| 8 | 2 | 0 | 0 | 3 | | 28 | 0 | 3 | 0 | 27 |
| 9 | 6 | 3 | 3 | 8 | | 29 | 1 | 0 | 0 | 28 |
| 10 | 2 | 1 | 1 | 9 | | 30 | 0 | 1 | 0 | 29 |
| 11 | 5 | 2 | 2 | 8 | | 31 | 3 | 2 | 1 | 30 |
| 12 | 1 | 1 | 1 | 10 | | 32 | 4 | 0 | 0 | 31 |
| 13 | 5 | 4 | 4 | 12 | | 33 | 3 | 2 | 1 | 32 |
| 14 | 1 | 4 | 1 | 13 | | 34 | 1 | 1 | 1 | 33 |
| 15 | 7 | 5 | 2 | 15 | | 35 | 0 | 0 | 0 | - |
| 16 | 4 | 2 | 2 | 16 | | 36 | 0 | 1 | 0 | 35 |
| 17 | 4 | 4 | 3 | 16 | | 37 | 3 | 3 | 3 | 36 |
| 18 | 2 | 3 | 1 | 17 | | 38 | 2 | 3 | 2 | 37 |
| 19 | 0 | 0 | 0 | - | | 39 | 2 | 2 | 1 | 38 |
| 20 | 2 | 2 | 2 | 17 | | 40 | 3 | 1 | 1 | 39 |
| 21 | 1 | 2 | 1 | 20 | | | | | | |

## 4.3 Relationships between the quantities

- The two conventions share every zero-free solution, so their counts move
  together. Over bases 10 to 40 the correlation of `n0` and `n1` is 0.56.
  Of the 55 solutions under `0^0 = 1` in these bases, 34 are zero-free.
- Base parity matters under `0^0 = 0`. Over bases 10 to 40, odd bases average
  2.67 solutions and even bases 1.56. Under `0^0 = 1` the averages are 1.87
  and 1.69. Section 5.3 explains the difference.
- The longest solution usually has `b-1` digits: in 22 of the 28 bases from 10
  to 40 that have a solution. Two bases have `b`-digit solutions, 15 and 16,
  both under `0^0 = 0` only.
- Perfect powers with self-paying digits always have solutions under
  `0^0 = 0`: bases 25 and 32 have 5 and 4.

## 4.4 Bases with exactly `n` solutions

Bases 10 to 40, nontrivial solutions:

| `n` | `0^0 = 0` | `0^0 = 1` |
|---:|---|---|
| 0 | 19, 27, 28, 30, 35, 36 | 19, 23, 27, 29, 32, 35 |
| 1 | 12, 14, 21, 22, 23, 24, 26, 29, 34 | 10, 12, 22, 24, 30, 34, 36, 40 |
| 2 | 10, 18, 20, 38, 39 | 11, 16, 20, 21, 25, 26, 31, 33, 39 |
| 3 | 31, 33, 37, 40 | 18, 28, 37, 38 |
| 4 | 16, 17, 32 | 13, 14, 17 |
| 5 | 11, 13, 25 | 15 |
| 7 | 15 | |

If each base had a Poisson number of solutions, with the refined model's mean
(section 5.3), bases 10 to 39 would show:

| `n` | 0 | 1 | 2 | 3 | 4 | 5 | 6+ |
|---|---:|---:|---:|---:|---:|---:|---:|
| `0^0 = 0`, expected | 6.3 | 8.9 | 7.1 | 4.2 | 2.1 | 0.9 | 0.4 |
| `0^0 = 0`, observed | 6 | 9 | 5 | 3 | 3 | 3 | 1 |
| `0^0 = 1`, expected | 8.6 | 10.7 | 6.7 | 2.8 | 0.9 | 0.2 | 0.1 |
| `0^0 = 1`, observed | 6 | 7 | 9 | 4 | 3 | 1 | 0 |

The counts roughly follow the Poisson shape. The upper tail is heavier than
Poisson. Twins and constructed solutions come in groups, not one at a time, and
small bases have extra solutions (section 5.4).

## 4.5 Bases without solutions

Bases 19, 27 and 35 have no nontrivial solution under either convention. They
are the only such bases from 3 to 40.

What is known:

- Under `0^0 = 0` a base without solutions has no self-paying digit
  (Corollary 2.4) and is not a 2-digit base (section 2.4). Both conditions
  exclude only a sparse set of bases.
- Beyond that, no characterization is known. The probabilistic model expects
  about `e^(-E)` of bases to have no solution, where `E` is the expected count.
  For large bases that is about 37% of even bases and 32% of odd bases under
  `0^0 = 1`, and about 37% of even bases and 14% of odd bases under
  `0^0 = 0`. With both conventions together, about 20% of large even bases and
  9% of large odd bases are expected to be empty.

An observation, not a result: 19, 27 and 35 are all `== 3 (mod 8)`, and so is
11, which does have solutions. In the model, an odd base is empty under both
conventions with probability about 0.06. Three empty bases among the four
`== 3 (mod 8)` bases from 11 to 35 then has probability about `10^-3`. But I
noticed the residue class after seeing the data, and across all 15 odd bases
from 11 to 39, three empty ones has probability about 6%. I know of no
mechanism. Base 43, the next one, is a direct test.

## 4.6 Every base has finitely many; infinitely many bases have one

- Every base has finitely many solutions (Proposition 1.1).
- Infinitely many bases have a solution under each convention: the 2-digit
  families of section 2.4 give infinitely many, and under `0^0 = 0` so do the
  self-paying digits.
- Whether infinitely many bases have no solution is open. The model says that
  about 15% of bases do, under both conventions together.
