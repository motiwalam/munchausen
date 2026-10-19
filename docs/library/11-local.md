# 11. Near-solutions, local obstructions, and a fast search for short solutions

This chapter looks at solutions from two new sides. The first is the numbers
that miss by a little: how many `n` have `n - F(n) = D` for a small `D`. They
show that a solution is an ordinary draw from each base's own distribution of
near misses. The second is the arithmetic of a fixed digit string modulo small
primes. It proves that almost every short string is impossible in every base.
It explains why short solutions are more common than the per-base model says,
and it gives a search for short solutions that is about 150 times faster. The
chapter also proves that almost all bases have no short solution.

## 11.1 The defect spectrum

For a base `b` and an integer `D`, let `N_D(b)` be the number of `n` with at
least 2 digits and `n - F(n) = D`. So `N_0(b)` is the number of nontrivial
solutions. The option `--offset D` of `fast search` starts the search with
`D` in place of 0, so it counts `N_D(b)` with the same exact search. It agrees
with brute force for bases 6 and 7, offsets 0 to 40, both conventions.

The model of chapter 5 says that a solution is a coincidence. If so, `D = 0`
is not special. Each offset `D` in the same residue class as 0 modulo
`2(b - 1)` is another draw of the same coincidence, with the true weights
`x^x` and all their arithmetic. The offsets `D = j (b - 1)` with `j` even form
that class.

Short numbers need care. A number with few digits cannot satisfy
`n = F(n) + D` when `n < D`, so large offsets undercount short numbers, which
follow other statistics anyway (section 11.4). The comparison therefore counts
only numbers with at least `b - 6` digits, where every offset below `10^6` sees
the same lengths (`analysis/defects_bulk.py`, bases 12 to 32, `j` up to 120):

| bases 12-32, at least `b-6` digits | solutions (`D = 0`) | predicted by the offsets |
|---|---:|---:|
| `0^0 = 0`, even | 13 | 10.9 |
| `0^0 = 0`, odd | 20 | 22.2 |
| `0^0 = 1`, even | 15 | 12.8 |
| `0^0 = 1`, odd | 15 | 14.0 |

The odd bases under `0^0 = 0` have about twice as many near-solutions as the
even ones, for every offset in the class. That is the parity effect of section
5.3, now seen in the near misses.

Three further tests:

- Within a base, the counts `N_D` over the offsets have variance/mean ratio
  0.98 (median over 42 cases; range 0.70 to 1.64). That is a Poisson law.
- Across bases, `N_0(b)` scatters around the base's own mean `lambda(b)` like
  a Poisson draw: `sum (N_0 - lambda)^2 / lambda = 48.8` over 42 cases.
- The empty base 19 has an ordinary spectrum: `lambda = 1.02` under
  `0^0 = 1` and 1.35 under `0^0 = 0`, inside the range 0.88 to 2.17 of the
  other bases. Shared solutions without zeros count under both conventions,
  so the union has a mean of about 1.9, and an empty base has probability about
  0.15. Its emptiness is chance.

So a base does not "know" whether it has a solution. The count of solutions is
one Poisson draw, with the same mean as the count of near-solutions.

## 11.2 Empty bases and missing b-digit solutions, again

Empty bases. The spectrum gives each base its own expected count
`lambda_m(b)`, so it tests the even-base deficit of section 9.7 without the
model. Expected number of bases with no long solution (at least `b-6` digits),
summed over bases 12 to 32 as `sum exp(-lambda_m(b))`:

| bases 12-32 | expected | observed |
|---|---:|---:|
| even, `0^0 = 0` | 4.1 | 3 |
| even, `0^0 = 1` | 3.6 | 1 |
| odd, `0^0 = 0` | 1.3 | 2 |
| odd, `0^0 = 1` | 2.6 | 5 |

The even bases have fewer empty cases than expected and the odd bases more.
The total, 11 against 11.6, is normal. The residue modulo `b` is the one
residue that these offsets do not match. Offsets `D = 2 j b (b - 1)` match it
too, and they predict slightly fewer solutions, not more (11.0 and 13.1 under
`0^0 = 1`). So no mechanism tied to `D = 0` is visible, and I count the
even-base deficit of section 9.7 as chance.

Missing `b`-digit solutions. No base from 3 to 45 has a `b`-digit solution
under `0^0 = 1`, and only bases 15 and 16 have one under `0^0 = 0`. The
refined model expects 3.6 and 5.0 (the basic model 3.2 under `0^0 = 1`). The
spectrum shows that the model overestimates this length. With offsets
restricted to exactly `b` digits (`analysis/bdigit_spectrum.py`, bases 10 to
30, 40 offsets each):

| bases 10-30 | `b`-digit solutions | predicted by the offsets | refined model |
|---|---:|---:|---:|
| `0^0 = 0` | 2 | 1.30 | 2.33 |
| `0^0 = 1` | 0 | 1.30 | 1.74 |

Perturbed weights show the same shortfall: over bases 12 to 24 and 40 seeds,
0.65 to 0.83 `b`-digit solutions per world, against 1.04 to 1.39 in the model.
So the cause is in the model, not in `x^x`.

The cause is the forced top digits. A `b`-digit sum needs at least three
copies of `b - 1`, and its top digits are fixed by the large counts: the
leading digit is 1, and the next one is about `0.10 b` when there are three
copies. These digits must also be in the multiset. The three copies of
`b - 1` use up slots, so the other counts are smaller. That lowers the chance
that the forced digits are present. `analysis/forced_top.py` computes the
correction exactly for the top `t` digits: for `b` digits it is 0.86 to 0.91
for `t = 1` and 0.6 to 0.85 for `t = 2` or 3 in bases 16 to 30. For `b - 1`
and `b - 2` digits it stays within noise of 1. The correction shrinks like
`1/b`, so the model's share of 8% for `b` digits holds only in the limit.

With the spectrum's calibration, 0 solutions against 1.3 expected under
`0^0 = 1` has probability 0.27. The missing `b`-digit solutions are therefore
not evidence for the original conjecture of section 7.1.

## 11.2a How well the model predicts a single base

The spectrum measures each base's own mean `lambda_m(b)` (lengths `b-6` to
`b`). Against the refined model of chapter 5, the ratio `lambda / model`
averages 0.98 under `0^0 = 0` and 1.12 under `0^0 = 1` over bases 12 to 32. So
the model is right on average. Its spread from base to base is about 20%,
twice the sampling error of the offsets (chi-square 108 and 85 on 20 degrees
of freedom). It shows no clear pattern in `b mod 3`, `b mod 4` or the number
of prime factors of `b - 1`.

Part of the spread comes from the forced top digits of section 11.2. A model
that multiplies each length's expectation by the correction for the top two
digits (`analysis/second_order.py`) follows the bases more closely:

| | correlation with the measured `lambda`, refined model | second-order model |
|---|---:|---:|
| `0^0 = 0` | 0.83 | 0.86 |
| `0^0 = 1` | 0.45 | 0.67 |

The same effect shows in the lengths. Near-solutions in bases 24 and 28
(`analysis/length_spectrum.py`, 150 offsets each) follow the law of
`J = b - k` for `J <= 3`. In single cells they are far off: base 24 has 3 and
5 near-solutions with `J = 11`, against 0.3 expected. In such a cell the top
digits of `F` are fixed by one or two large digits, so all offsets share the
same luck.

## 11.3 Local obstructions

A digit string `s` with `k` digits is a solution in base `b` exactly when
`Q_s(b) = 0`, where

    Q_s(r) = s_1 r^(k-1) + ... + s_k - F(s),

and `b` exceeds every digit. `Q_s` has integer coefficients.

Proposition 11.1. If `Q_s` has no root modulo some prime `p`, then `s` is not a
solution in any base.

Proof. An integer root `b` would give the root `b mod p`.

For a random polynomial modulo `p`, the chance of no root is close to
`1/e`. So the test with one prime removes about 37% of the strings, and the
tests with several primes act like independent events. With the 18 primes up
to 61, the share of strings that pass is `0.632^18 = 2.6 * 10^-4` if they are
independent. The measured share is `3 * 10^-4` to `6 * 10^-4`
(section 11.5).

Covering congruences. Fix all digits but one, `x`. Whether `Q_s` has a root mod
`p` then depends only on `x mod p (p - 1)`, because `x^x mod p` depends on
`x mod p` and `x mod (p - 1)`. If the classes excluded by several primes
covered all integers, the family would have no solution at all, in any base:
a proof, like the covering congruences behind the Sierpinski numbers.
`analysis/cover.py` checks the 133 three-digit families under `0^0 = 1` with
the other digits up to 6. Three are covered, `(2, 0, x)`, `(4, 0, x)` and
`(6, 0, x)`, all by the prime 2 alone: their `Q_s` is always odd. In the other
families, the classes of `x` that no prime up to 47 excludes have a median
density of 2%. The obstructions look independent, so I do not expect
coverings beyond such parity cases.

## 11.4 Why short solutions are common

Section 10.5 found 9 short exceptions (3 to 5 digits) where the per-base model
expected 1. For a fixed string the right question is whether the real root
`b*` of `Q_s` is an integer. The spacing heuristic says this happens with
probability `1 / Q_s'(b*)`. The local factors correct it: the number of roots
`rho_s(p)` of `Q_s` mod `p` is 0 for an obstructed string and averages 1. The
heuristic with local factors is

    E = sum over strings s of  prod_p rho_s(p) / Q_s'(b*).

`analysis/root_local.py`, `0^0 = 1`, primes up to 31:

| length | digits up to | expected, spacing only | expected, with local factors | observed |
|---:|---:|---:|---:|---:|
| 3 | 60 | 2.31 | 5.09 | 6 |
| 4 | 22 | 1.38 | 1.39 | 2 |
| 5 | 11 | 1.13 | 2.42 | 6 |

With the local factors, the 3-digit and 4-digit counts match. The 5-digit
solutions lie in bases 6 to 48, where the heuristic is crude. So the short
solutions are coincidences as well. They are coincidences of a different kind
from the long ones: one equation for the base, with the local densities of
`Q_s` as the singular series.

The same heuristic says how complete the lists are. The expected number of
solutions with a digit above the list's bound (`analysis/list_tails.py` and a
log-space version for large digits):

| length | complete for bases up to | expected missing solutions |
|---:|---:|---:|
| 3 | `10^51.5` | `10^-74` |
| 4 | `10^186.5` (section 11.5) | `10^-490` |
| 5 | `10^30.9` (section 11.5) | `10^-109` |
| 6 | `10^11.0` (section 11.5) | `10^-45` |
| 7 | `10^5.5` (section 11.5) | `10^-24` |
| 9 | `10^5` (section 3.4) | `10^-29` |
| 18, 21, 22, 24, 26, 28 | `10^4` (section 3.4) | `10^-40` or less |

So under this heuristic the lists of chapter 3 are complete beyond their
ranges, and the missing lengths are missing everywhere. That is false.
The binomial families of chapter 22 give solutions of every length `k >= 3`,
including 9, 18, 21, 22, 24, 26 and 28 digits, in bases far above the searched
ones (Corollary 22.7). Their roots are integers by an algebraic identity,
which the heuristic does not model. The table is right about strings without
such an identity, in the ranges stated.

## 11.5 A search for short solutions that is 150 times faster

The test of Proposition 11.1 splits over positions. For a fixed prefix of
`k - 1` digits, the values of the prefix part of `Q_s` modulo `p`, over all
residues `r`, form a bit mask. The last digit `x` passes the test for `p` if
`w(x) - x` (minus the number of zeros, under `0^0 = 0`) is in the mask. So the
test costs a few bit operations per string and prime. Only the strings that
pass all 18 primes up to 61 go on to the exact root computation of section 3.1.

`fast/src/bin/kdigit.rs` implements this. It reproduces the lists of chapter 3
exactly, and runs much faster:

| length | digits up to | strings | Python (section 3.1) | `kdigit` | passed the test |
|---:|---:|---:|---:|---:|---:|
| 3 | 80 | 524,880 | 5 s | below 0.1 s | 140 |
| 4 | 44 | 4.0 million | 28 s | 0.2 s | 4,980 |
| 5 | 28 | 19.8 million | 2 min | 0.9 s | 12,473 |
| 6 | 20 | 81.7 million | 10 min | 4.1 s | 57,356 |

New ranges:

| length | digits up to | complete for bases up to | time | solutions under `0^0 = 1` |
|---:|---:|---:|---:|---|
| 4 | 150 | `10^82.3` | 9 s | the same 2 |
| 4 | 300 | `10^186.5` | 215 s | the same 2 |
| 5 | 60 | `10^21.8` | 21 s | the same 6 |
| 5 | 80 | `10^30.9` | 113 s | the same 6 |
| 6 | 40 | `10^11.0` | 201 s | the same 1, `(1,5,6,2,6,2)` in base 9 |
| 7 | 26 | `10^5.5` | 644 s | 1: `(1,6,5,6,5,4,7)` in base 9 |

Why small primes filter little. For 3-digit strings with digits up to 80
under `0^0 = 1`, the share of strings with a root mod `p` is 0.988 for
`p = 2`, 0.80 for `p = 3` and 0.69 for `p = 5`, and tends to 1/2 for large
`p`. At `r == 1 (mod p)` the value `Q_s(1)` is the sum of the terms
`s_i - s_i^(s_i)`, which vanish mod `p` for many digits. That is the digit-sum
identity of section 1.6 in the language of roots, and it makes the small
primes weak tests. The product of the 18 measured shares predicts 28.9
survivors. Eleven more strings have a rational root, so they pass every prime
by definition. That gives about 40, against 46 observed. So the tests for
different primes are close to independent.

Under `0^0 = 0` the new solutions are the self-paying families of chapter 2,
such as `(x, 0, 0, 0)` and `(x, 0, 0, 1)` with `x^(x-1)` a cube.

## 11.6 Almost all bases have no short solution

Theorem 11.2. For every `eps > 0`, the number of bases `b <= B` that have a
solution with at most `(1/2 - eps) ln b / ln ln b` digits is at most
`B^(1 - 2 eps + o(1))`. So almost all bases have no such solution, under
either convention.

Proof. By Proposition 10.4, the bases up to `B` with a solution of `k` digits
number at most `X (X + 1)^(k-1)`, with `X = X_k(B)` the largest digit with
`X^X < B^k`. Let `K = alpha ln B / ln ln B`. Then
`ln X_K = 2 ln ln B - O(ln ln ln B)`, so `K ln X_K = 2 alpha ln B (1 - o(1))`.
Summing over `k <= K` gives at most `K (X_K + 1)^K = B^(2 alpha + o(1))`. With
`alpha = 1/2 - eps` this is `B^(1 - 2 eps + o(1))`.

For `B = 10^96` and `alpha = 0.4` the bound is `B^0.46`, from 16-digit
solutions down (`analysis` computation in the text of this section). The
theorem is weak in absolute terms: it only covers lengths of order
`ln b / ln ln b`, while the model puts almost all solutions near `b` digits. It
is the first unconditional statement that solutions are absent from most
bases in a whole range of lengths.

## 11.7 Status

| question | status |
|---|---|
| are solutions special among near misses | no: `N_0(b)` is a Poisson draw with the mean of the near-solution counts (11.1) |
| empty bases | each base's own spectrum predicts its chance of being empty; the even-base deficit is chance (11.2) |
| missing `b`-digit solutions | the model overestimates `b` digits by about 1.6x at these bases (forced top digits); the data are normal (11.2) |
| local obstructions | proven to exclude 99.97% of short strings (11.3, 11.5) |
| short solutions under `0^0 = 1` | explained by the root heuristic with local factors (11.4) |
| completeness of the short lists | expected missing solutions below `10^-24` for lengths 3 to 7 (11.4) |
| short solutions in most bases | none below `(1/2 - eps) ln b / ln ln b` digits, for almost all `b` (Theorem 11.2) |
