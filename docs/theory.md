# What we know about Munchausen numbers

This document collects the mathematics behind the search. It has three parts:

1. Exact results: lemmas with proofs, and families of solutions that can be
   written down without a search.
2. A probabilistic model that predicts how many Munchausen numbers a base has,
   and how long they are. The exhaustive results for bases 2 to 38 test it.
3. The cost of an exhaustive search, ideas that do not lower it, and what this
   means for base 100.

Notation follows `docs/algorithm.md`: `b` is the base, `d` the number of
digits, `w(x) = x^x`, and `F(n)` is the Munchausen sum. `F_0` and `F_1` are the
sums under `0^0 = 0` and `0^0 = 1`. A solution is nontrivial if it is not 0 or
1.

The scripts in `analysis/` produce every number in this document.

## Summary

- Large-base Munchausen numbers behave like random coincidences. A simple model
  predicts about one nontrivial solution per base and convention, and the data
  for bases 20 to 38 agrees with it.
- Small bases have more solutions than the model predicts. Most of the surplus
  comes from explicit algebraic families, which the model ignores.
- The conjecture "no `b`-digit solution for `b > 2`" is false under
  `0^0 = 0`: bases 15 and 16 have one each. Under `0^0 = 1` it holds up to base
  38. The model expects a counterexample in about 1 base in 12.
- The exhaustive search costs about `1.87^b`. I found no exact method with a
  smaller growth rate. A complete search of base 100 needs about `10^20`
  seconds on the test laptop. Base 100 has no nontrivial solution with 50
  digits or fewer, and the model expects about one solution with 97 to 100
  digits.

## 1. Exact results

### 1.1 Length

A solution has at most `b` digits, so it is below `b^b`. `docs/algorithm.md`
gives the proof.

### 1.2 The two conventions

`F_1(n) = F_0(n) + z(n)`, where `z(n)` is the number of zeros in `n`. So a
number without zeros is a solution under both conventions or under neither. A
number with zeros is a solution under at most one convention.

### 1.3 Twins under `0^0 = 0`

Let `n` be a number whose last digit is 0. Then `n + 1` has the same digits,
except that the last digit is 1. So `F_0(n + 1) = F_0(n) + 1`, and `n` is a
solution if and only if `n + 1` is a solution.

Under `0^0 = 0`, every solution that ends in 0 or 1 therefore has a twin.
Bases 2 to 38 contain 8 such pairs, for example `(4,0,0)` and `(4,0,1)` in
base 8. Under `0^0 = 1`, a 0 and a 1 weigh the same, so there are no twins.

### 1.4 Composition: digits that pay for themselves

Suppose that `a^(a-1) = b^k` for some digit `2 <= a < b` and some `k >= 1`.
Then the digit `a` at position `k` contributes `a * b^k = a^a` to the number,
and exactly `a^a` to its sum. It pays for itself.

Lemma. Let `a^(a-1) = b^k`, and let `m < b^k`. Put `n = a * b^k + m`.

- Under `0^0 = 0`, `n` is a solution if and only if `m` is a solution. The
  zeros between `a` and `m` add nothing.
- Under `0^0 = 1`, `n` is a solution if and only if `F_1(m) + p = m`, where `p`
  is the number of zeros between `a` and `m`. In particular, if `m` has
  exactly `k` digits, then `n` is a solution if and only if `m` is one.

Proof. The digits of `n` are `a`, then `p` zeros, then the digits of `m`. So
`F(n) = a^a + p * w(0) + F(m) = a * b^k + p * w(0) + F(m)`, and `F(n) = n`
reduces to `p * w(0) + F(m) = m`.

When does `a^(a-1) = b^k` hold? Both sides have the same prime factors, so `a`
and `b` are powers of one integer `r`. With `a = r^s` and `b = r^t`, the
condition is `k * t = s * (r^s - 1)` and `t > s`. The cases with `b <= 127`:

| base `b` | digit `a` | position `k` | solutions it gives under `0^0 = 0` |
|---:|---:|---:|---|
| 8 | 4 | 2 | `(4,0,0)`, `(4,0,1)` |
| 9 | 3 | 1 | `(3,0)`, `(3,1)` |
| 25 | 5 | 2 | `(5,0,0)`, `(5,0,1)`, `(5,1,3)` |
| 32 | 16 | 12 | `16` followed by 12 digits `0...00` or `0...01` |
| 49 | 7 | 3 | `(7,0,0,0)`, `(7,0,0,1)` |
| 64 | 4 | 1 | `(4,0)`, `(4,1)` |
| 64 | 16 | 10 | `16` followed by 10 digits ending in `00`, `01`, `40` or `41` |
| 81 | 9 | 4 | `(9,0,0,0,0)`, `(9,0,0,0,1)` |

The search confirms every entry. Bases 49, 64 and 81 lie beyond the exhaustive
range, but a search limited to 12 digits finds exactly these. In base 64 the
two compositions nest. The block `4` sits at position 1 and the block `16` at
position 10, and together they give `16 0...0 4 0` and `16 0...0 4 1`.

`(5,1,3)` in base 25 is the composition of `5` at position 2 with `(1,3)`,
which is a 2-digit solution. It also works under `0^0 = 1`, and so does `(3,1)`
in base 9.

### 1.5 Two-digit solutions

`(a, c)` is a solution in base `b` if and only if `a * b + c = a^a + c^c`. So
each pair of digits gives at most one base: `b = (a^a + c^c - c) / a`, if this
is an integer greater than `a` and `c`. Three infinite families follow:

- `(1, c)` in base `c^c - c + 1`: `(1,2)` in base 3, `(1,3)` in base 25.
- `(c, c)` in base `2 * c^(c-1) - 1`: `(2,2)` in base 3, `(3,3)` in base 17,
  `(4,4)` in base 127.
- `(a, 1)` and, under `0^0 = 0`, `(a, 0)` in base `a^(a-1)`. These are the
  compositions with `k = 1`.

Kures (2021) describes the first family.

### 1.6 Solutions with `b` digits

Lemma. For `b >= 7`, a `b`-digit solution contains the digit `b-1` at least 3
times.

Proof. Let `c` be the count of `b-1`, and suppose that `c <= 2`. Every other
digit weighs at most `(b-2)^(b-2)`, so

    F(n) <= 2 (b-1)^(b-1) + b (b-2)^(b-2).

Divide by `b^(b-1)`. The bound becomes `2 (1-1/b)^(b-1) + (1-2/b)^(b-2)`. Both
terms decrease as `b` grows, and at `b = 7` the sum is 0.979. So
`F(n) < b^(b-1) <= n`, and `n` is not a solution.

The bases below 7 are covered by the exhaustive search. Under `0^0 = 1`, base 2
has the only `b`-digit solution (`10`), so the conjecture holds there for
bases 3 to 38. Under `0^0 = 0` it fails:

- base 15: `(1,2,4,3,14,14,13,3,4,1,9,1,1,0,14)`,
- base 16: `(1,2,3,11,2,3,0,9,15,15,5,7,2,15,6,11)`.

Both contain the digit `b-1` exactly 3 times, and both contain a 0. So under
`0^0 = 1` neither is a solution.

### 1.7 The top digits of a solution

The leading digit of a `d`-digit solution is `floor(F(n) / b^(d-1))`, and the
top few digit values supply almost all of `F(n)`. For a `(b-1)`-digit
solution, `3 (b-1)^(b-1) > (3/e) b^(b-1) > b^(b-1)`, so the digit `b-1`
appears at most twice. One copy puts the leading digit near `b/e`. Two copies
put it near `2b/e`. For all 26 solutions in bases 20 to 38 under `0^0 = 1`,
the two largest digit values alone give the leading digit. Let `x` and `y` be
the two largest digits present. Then the leading digit is
`floor((c_x x^x + c_y y^y) / b^(d-1))`.

## 2. A probabilistic model

### 2.1 The model

Fix `d` and a digit multiset `c` with `d` digits. Its sum `S(c)` is one fixed
number. The model treats the digits of `S(c)` as independent and uniform, with
a nonzero leading digit. Then the chance that `S(c)` has the digit multiset
`c` equals the chance that a random `d`-digit string has it. Summing over all
`c` whose sum has `d` digits gives a simple formula:

    E_d = P( F(n) has exactly d digits ),   n a random d-digit string.

`E_d` is the expected number of `d`-digit solutions. `analysis/model.py`
estimates it by sampling.

### 2.2 The large-base limit

As `b` grows with `j = b - d` fixed, the digit counts of a random string
become independent Poisson variables with mean 1. The sum is then dominated
by the largest digit present. A value `b - y` weighs about
`e^(-y) * b^(b-y)`, so:

- `d = b` needs at least 3 copies of `b-1`, because `2/e < 1 <= 3/e`.
- `d = b-1` needs 1 or 2 copies of `b-1`.
- `d = b-j` for `j >= 2` needs no digit above `b-j`, and at least one copy of
  `b-j`.

These events do not overlap, and together they cover almost every multiset.
So the expected numbers add up to exactly 1:

| digits | expected solutions |
|---|---:|
| `b` | 0.080 |
| `b-1` | 0.552 |
| `b-2` | 0.232 |
| `b-3` | 0.086 |
| `b-4` | 0.032 |
| `b-5` or fewer | 0.018 |
| total | 1.000 |

In words: for a large base, expect one nontrivial Munchausen number per
convention, most likely with `b-1` digits. If solutions appear independently,
their number is close to a Poisson variable with mean 1. Then about 37% of
large bases have no nontrivial solution.

For finite bases the expectation is a little higher. It is 1.32 at base 9,
1.16 at base 20, and 1.05 at base 38.

### 2.3 Comparison with the data

| bases | convention | expected | observed |
|---|---|---:|---:|
| 3 to 19 | `0^0 = 1` | 20.4 | 36 |
| 20 to 38 | `0^0 = 1` | 20.6 | 26 |
| 3 to 38 | `0^0 = 0` | 41.1 | 78 |

In bases 20 to 38 the model fits within its random error: 26 against 20.6 is
1.2 standard deviations. Five of these 19 bases have no nontrivial solution
under `0^0 = 1`. The model expects about six.

By digit length, for bases 15 to 38 under `0^0 = 1`:

| digits | expected | observed |
|---|---:|---:|
| `b` | 1.85 | 0 |
| `b-1` | 13.3 | 24 |
| `b-2` | 5.9 | 6 |
| `b-3` | 2.4 | 3 |
| `b-4` to `b-10` | 2.2 | 2 |

The model underestimates the `(b-1)`-digit solutions, and the gap is larger
than its random error. I tested whether the digits of `S(c)` correlate with
`c` (`analysis/correlation.py`). For bases 30 and 31, the top 10 digits of
`S(c)` fit the multiset no more often than random digits do. The same holds
for the bottom 8 digits. So the cause of this gap is unknown.

The small bases have a large surplus, and the exact results explain much of
it. Bases 3 to 19 contain the compositions of section 1.4 and the 2-digit
families of section 1.5. Under `0^0 = 0` they also contain the twins of
section 1.3. The
model counts none of these, because each one is forced by an identity, not by
chance.

### 2.4 Predictions

- Base 100: the model expects 1.01 nontrivial solutions per convention: 0.55
  with 99 digits, 0.24 with 98, 0.09 with 97, 0.08 with 100, and 0.06 with
  fewer. Base 100 has no composition, because `a^(a-1)` is never a power of
  100 for `a < 100`.
- The conjecture under `0^0 = 1`: about 8% of large bases are expected to have
  a `b`-digit solution. None appears in bases 3 to 38, where the model expects
  about 2.7. Under the model, a gap like that happens about 7% of the time. So
  the data does not support the conjecture strongly. I expect a
  counterexample in some larger base.

### 2.5 Can we derive solutions instead of searching?

For special bases, yes. Sections 1.3 to 1.5 give solutions without a search,
whenever `b` is a suitable perfect power or of the form `c^c - c + 1` or
`2 * c^(c-1) - 1`.

For the solutions near `b` digits, the evidence says no. Their number, their
lengths, and their leading and trailing digits match a model in which each
digit multiset has a small, independent chance to work. A formula would have to
predict which multisets win. Nothing in the data hints at such a rule. Section
3 shows that the search also finds no exploitable structure.

## 3. How hard is the exhaustive search?

### 3.1 Growth rates

| set | size | growth per base |
|---|---|---:|
| digit multisets with at most `b` digits | `C(2b, b) ~ 4^b / sqrt(pi b)` | 4.0 |
| combinations the Python search checks | `nb7` in `src/nb.py` | 3.9 |
| nodes of the prefix-pruned tree | measured | 1.87 |

The tree size is the cost. `docs/comparison.md` gives the measurements.

### 3.2 Where the tree comes from

At the top of the tree the search fixes the counts of the largest digits. The
leading digits of the sum are then mostly small digits, and a small digit only
adds a lower bound on its own count. So the top levels prune almost nothing.
For base 21 and `d = 20`, each node at level `k = 19` has 15 children on
average.

Many of these children are atypical. They give a large digit far more copies
than a random number would have. Such a node survives until its free digit
positions run out. In base 21, the nodes at the widest level carry 12.5 large
digits on average, against 7.6 for a random number.

`analysis/typical.py` measures this effect. It drops every node with more than
`s` large digits above the random expectation. This is not a valid search; it
only measures the tree.

| base | `s = 2` | `s = 4` | `s = 8` | full tree |
|---:|---:|---:|---:|---:|
| 16 | 2,260 | 3,669 | 4,536 | 4,557 |
| 19 | 8,927 | 17,335 | 27,621 | 28,422 |
| 21 | 15,262 | 36,241 | 75,936 | 82,468 |
| 23 | 61,981 | 160,748 | 330,597 | 366,889 |

These counts are for `d = b-1` under `0^0 = 1`. From base 16 to 23, the full
tree grows 1.87x per base, and the tree with `s = 2` grows 1.60x per base. So
the atypical nodes raise the growth rate. At base 23 they make up 83% of the
tree.

An exact search must keep them, because a node with many large digits can
still lead to a solution. A cap on `s` would miss real solutions. In a random
100-digit number, the count of digits in the upper half has a standard
deviation of 5.

### 3.3 Ideas that do not lower the growth rate

- Meet in the middle on digit values. Split the digits into large and small
  values. The small values only change the low part of the sum, but that part
  is `A + L`. Here `A` depends on the large counts and `L` on the small ones.
  The digit counts of a sum do not split into a function of `A` plus a
  function of `L`. So there is no key on which to join the two halves.
- An exact join exists if the bottom `q` digits are enumerated as a string. In
  that case `B - F_small(B)` must equal a value computed from the large counts
  alone. But `q` must cover the weights of the small digits, which is about
  half the number. Then there are about `b^(b/2)` strings, far more than
  `1.87^b` nodes.
- Meet in the middle on positions. Splitting `n` into a top string `T` and a
  bottom string `B` gives the exact equation `T * b^q - F(T) = F(B) - B`. Each
  side then has `b^(d/2)` strings. That gives up the symmetry that makes
  multisets cheap.
- Lattice reduction. The equation `sum (w(s_i) - s_i b^i) = 0` is a
  subset-sum problem with density about `b / log2(b)`, which is above 1. At
  that density lattice methods fail, because the relaxed problem has many
  solutions.
- Congruences. `S = sum c_x w(x)` is linear modulo `b^j`, and
  `S == digit sum (mod b-1)`. Both constraints involve every count. So they
  only prune near the leaves, where the tree is already small.
- The feasibility check (`docs/comparison.md`) removes 10 to 13% of the nodes.
  That is a constant factor.

### 3.4 Base 100

The `fast` engine now handles bases up to 127, for numbers with at most 62
digits. Exhaustive results for base 100, both conventions:

| digits searched | nodes | time |
|---:|---:|---:|
| up to 30 | 141,449 | 0.055 s |
| up to 40 | 15,778,515 | 0.88 s |
| up to 45 | 531,426,476 | 21 s |
| up to 50 | 3,611,595,932 | 139 s |

No base-100 number with 50 digits or fewer is a nontrivial Munchausen number.
The model expects about 0.002 such solutions, so this result is not surprising.

The interesting part is 97 to 100 digits. Base 38 took 520 seconds, and each
base costs about 1.9x more. At that rate base 100 needs about `10^20` seconds.
Even a growth rate of 1.6x per base would leave about `10^15` seconds. So I see
no way to enumerate base 100 in an hour.

## 4. Open questions

- Why are `(b-1)`-digit solutions about 1.8x more common than the model
  predicts in bases 15 to 38? The leading and trailing digits show no
  correlation, so any cause sits in the middle digits.
- Is there an exact way to cut the atypical nodes? A method that only explores
  typical nodes would grow about 1.6x per base instead of 1.87x.
- Under `0^0 = 1`, does a `b`-digit solution exist? The model expects one in
  about 1 base in 12.
