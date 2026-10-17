# 5. A probabilistic model

The solutions near `b` digits show no algebraic structure. This chapter models
them as coincidences and tests the model against the data.
`analysis/model.py` implements it.

## 5.1 The basic model

Fix `d` and a digit multiset `c` with `d` digits. Its sum `S(c)` is one fixed
number. Assume that the digits of `S(c)` behave like independent uniform
digits, with a nonzero leading digit. Then the chance that `S(c)` has the
multiset `c` equals the chance that a random `d`-digit string has it. Summing
over all `c` whose sum has `d` digits gives a simple formula:

    E_d = P( F(n) has exactly d digits ),   n a random d-digit string.

`E_d` is the expected number of `d`-digit solutions. It is easy to estimate by
sampling.

## 5.2 The large-base limit

Let `b` grow with `j = b - d` fixed. The digit counts of a random string become
independent Poisson variables with mean 1. A digit `b - y` weighs about
`e^(-y) b^(b-y)`, so the largest digit present decides the length of the sum:

- `d = b` needs at least 3 copies of `b-1`, because `2/e < 1 <= 3/e`;
- `d = b-1` needs 1 or 2 copies of `b-1`;
- `d = b-j`, for `j >= 2`, needs no digit above `b-j` and at least one copy of
  `b-j`.

These events do not overlap and together cover almost everything. So the
expectations add up to exactly 1:

| digits | share |
|---|---:|
| `b` | 8.0% |
| `b-1` | 55.2% |
| `b-2` | 23.2% |
| `b-3` | 8.6% |
| `b-4` | 3.2% |
| `b-5` or fewer | 1.8% |

## 5.3 The refined model: the digit-sum identity

Every integer satisfies `n == digit sum (mod b-1)`. The basic model ignores
this. For a solution it becomes a condition on the multiset
(Proposition 1.5):

    sum over digits x of ( w(x) - x ) == 0   (mod b-1).

The refined model draws the digits of `S(c)` at random among the strings that
obey the identity. A multiset that meets the condition then becomes `b-1`
times as likely, and every other multiset becomes impossible. On average this
changes nothing, unless the condition holds more often than `1/(b-1)` of the
time. It does, because of the prime 2:

- In an odd base, `b-1` is even. Modulo 2, `x^x == x` for every `x >= 1`. So
  under `0^0 = 0` every term of the sum is even, and the condition modulo the
  2-part of `b-1` holds twice as often as for random residues. The expected
  number of solutions doubles.
- Under `0^0 = 1` the zeros contribute 1 each, so the doubling only applies
  when the number of zeros is even. For Poisson counts that happens with
  probability `(1 + e^(-2)) / 2`, so the factor is `1 + e^(-2)`, about 1.135.
- For an odd prime `p` dividing `b-1`, the terms are not all zero modulo `p`.
  With about `b` digits the sum is spread evenly, and the factor is 1.

Limits for large bases:

| | even base | odd base |
|---|---:|---:|
| `0^0 = 0` | 1 | 2 |
| `0^0 = 1` | 1 | 1.135 |

## 5.4 Comparison with the data

Bases 10 to 38, nontrivial solutions, summed over all digit lengths:

| convention | bases | basic model | refined model | observed |
|---|---|---:|---:|---:|
| `0^0 = 0` | even | 17.2 | 17.3 | 22 |
| `0^0 = 0` | odd | 16.0 | 32.5 | 38 |
| `0^0 = 1` | even | 17.2 | 17.4 | 26 |
| `0^0 = 1` | odd | 16.0 | 19.1 | 26 |

The refined model explains the large difference between odd and even bases
under `0^0 = 0`. The remaining surplus is concentrated in small bases, which
contain the algebraic families of chapter 2. The model counts none of these,
because each one is forced by an identity, not by chance. For bases 20 to 38
under `0^0 = 1`, the basic model expects 20.6 solutions and 26 occur, which is
1.2 standard deviations.

## 5.5 The excess of `(b-1)`-digit solutions

In bases 10 to 38, solutions with `b-1` digits are more common than the basic
model predicts. Split by convention and base parity, with the refined model:

| convention | bases | basic model | refined model | observed |
|---|---|---:|---:|---:|
| `0^0 = 0` | even | 8.4 | 8.3 | 9 |
| `0^0 = 0` | odd | 7.8 | 15.5 | 17 |
| `0^0 = 1` | even | 8.4 | 8.4 | 13 |
| `0^0 = 1` | odd | 7.8 | 8.9 | 14 |

Under `0^0 = 0` the parity effect accounts for the whole excess. Under `0^0 = 1` an excess remains: 27 observed against 17.3
expected.

Tests for a hidden correlation found none (`analysis/correlation.py`,
`analysis/distance.py`):

- For random multisets in bases 30 and 31, the top 10 digits of `S(c)` fit the
  multiset no more often than random digits do. The ratio is 0.9 to 1.0.
- The bottom 8 digits behave the same way. The ratio is 1.0 to 1.1.
- The whole histogram of `S(c)` is no closer to `c` than a random histogram.
  For base 16, the chance of a distance of at most 9 is 0.0179 for real sums
  and 0.0193 for random strings with the same digit sum.

Under the refined model, 27 or more occurs with probability 0.019. But I picked
this group as the largest deviation among about 14 groups. Allowing for that,
the chance of some group deviating this much is about 23%. So the remaining
excess is consistent with chance. Bases 39 to 41 add new data that does not
depend on this choice (section 5.7).

## 5.6 Predictions

- Base 100 is even, so no parity factor applies. The model expects 1.01
  nontrivial solutions per convention: 0.55 with 99 digits, 0.24 with 98, 0.09
  with 97, 0.08 with 100, and 0.06 with fewer.
- A `b`-digit solution under `0^0 = 1` is expected in about 8% of large bases.
  Bases 3 to 38 have none, against 2.7 expected. Under the model that happens
  about 7% of the time. So I expect a counterexample to the conjecture of
  chapter 7 in some larger base.
- Under `0^0 = 0` the model expects about 1.5 solutions per base on average,
  because odd bases count double.

## 5.7 New bases as a test

Bases 39 and 40 were searched after the model was built. The refined model
expects 2.10 and 1.04 solutions under `0^0 = 0`, and 1.19 and 1.09 under
`0^0 = 1`. Observed: 2 and 3 under `0^0 = 0`, and 2 and 1 under `0^0 = 1`.

## 5.8 What the model means

For large bases, a Munchausen number behaves like a coincidence: each digit
multiset has a small, independent chance to reproduce itself. The model then
predicts the number of solutions, their lengths, their leading digits, and the
odd-even difference. It does not predict which multisets succeed. A formula for
the solutions would have to do exactly that, and nothing in the data hints at
such a rule.
