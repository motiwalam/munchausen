# 12. The Munchausen polynomial

Fix a digit string `s = (s_1, ..., s_k)`, most significant first. Its
Munchausen polynomial is

    Q_s(r) = s_1 r^(k-1) + s_2 r^(k-2) + ... + s_k - F(s).

It has integer coefficients, and `s` is a solution in base `b` exactly when
`Q_s(b) = 0` and `b` exceeds every digit (section 3.1). This chapter studies
`Q_s` as a polynomial in its own right: its Galois group, its roots modulo
primes, and its roots that are not ordinary bases. The roots at negative
integers turn out to be Munchausen numbers in negative bases.

## 12.1 The Galois group is the full symmetric group

For a polynomial of degree `n` with Galois group `G`, the Chebotarev density
theorem says that the share of primes `p` for which it has no root mod `p`
equals the share of elements of `G` that move every root. For `G = S_n` this
is the share of derangements, `D_n / n!`.

`analysis/galois.py` measures the share over the primes from 200 to 20,000,
for 60 random strings per length (digits up to 20, `0^0 = 1`):

| length `k` | degree | `S_(k-1)` predicts | median | range |
|---:|---:|---:|---:|---:|
| 3 | 2 | 0.500 | 0.501 | 0.478-0.522 |
| 4 | 3 | 0.333 | 0.335 | 0.308-0.356 |
| 5 | 4 | 0.375 | 0.374 | 0.345-0.631 |
| 6 | 5 | 0.367 | 0.367 | 0.339-0.390 |

So `Q_s` generically has the full symmetric group as its Galois group, as
Hilbert's irreducibility theorem leads one to expect for a polynomial whose
constant term `F(s)` is unrelated to its other coefficients.

The one exception among the 240 strings is `(9, 18, 18, 9, 15)`, with share
0.631. Its digit polynomial is `9 r (r + 1)(r^2 + r + 1) = 9 u (u + 1)` with
`u = r^2 + r`. So `Q_s` is a polynomial in `r^2 + r`, and its Galois group lies
in the dihedral group `D_4`, whose derangement share is `5/8 = 0.625`. Such
decomposable digit polynomials are the natural source of smaller groups.

This also explains the sieve of section 11.5. A random polynomial mod `p` of
degree `n` has no root with probability close to `D_n / n!`, which tends to
`1/e = 0.368`. The 18 primes of the sieve act like independent tests.

## 12.2 The local test is complete in the limit

Proposition 12.1. If `Q_s` is irreducible of degree `n >= 2`, then `Q_s` has no
root modulo `p` for a set of primes of density at least `1/n`.

Proof. The Galois group acts transitively on the roots. By Jordan's theorem, a
transitive group contains an element that fixes no root. Cameron and Cohen
(1992) proved that such elements make up at least a share `1/n` of the group.
The Chebotarev density theorem turns that share into a density of primes.

So a string that passes the test for every prime has a reducible `Q_s`. The
sieve of section 11.5 tests 18 primes. Among its survivors that are not
solutions, a sample of 400 gives these counts (`sympy` factorization):

| length | digits up to | survivors | irreducible in the sample | reducible, with a rational root |
|---:|---:|---:|---:|---:|
| 4 | 44 | 4,980 | 394 | 6 |
| 5 | 20 | 2,563 | 384 | 16 |

No survivor in the samples factors without a linear factor. More primes would
remove the irreducible survivors. The reducible ones have a rational root.
That root is either a negative integer, an integer at most the largest digit,
or a fraction (sections 12.3 and 12.4).

## 12.3 Negative bases

In base `-b`, with `b >= 2`, every integer has exactly one representation with
digits `0` to `b - 1` and no sign. So a string `s` with digits below `b` is a
Munchausen number in base `-b` when `Q_s(-b) = 0`. These are integer roots of
the same polynomial at `r < -max(s)`.

Proposition 12.2. A Munchausen number in a negative base has an odd number of
digits.

Proof. Its value `F(s)` is positive. A string of length `k` in base `-b` with a
nonzero leading digit has the sign of `(-b)^(k-1)`, because the leading term
outweighs all the others. So `k - 1` is even.

`analysis/all_roots.py` finds every integer root of the strings that pass the
local test. Under `0^0 = 1`:

| length | digits up to | negative-base solutions |
|---:|---:|---|
| 3 | 140 | `(1,1,1)` in base -2; `(1,3,1)` in base -7; `(1,2,6)` in base -217; `(1,7,1)` in base -911 |
| 4 | 44 | none (Proposition 12.2) |
| 5 | 60 | `(1,3,4,3,3)` in base -5 |
| 6 | 20 | none (Proposition 12.2) |

Check of the last one: `625 - 375 + 100 - 15 + 3 = 338` and
`1 + 27 + 256 + 27 + 27 = 338`.

Three of the four 3-digit ones are partners of ordinary solutions. The two
roots of a quadratic sum to `-s_2 / s_1`:

Proposition 12.3. Let `(s_1, s_2, s_3)` be a solution in base `b` with `s_1`
dividing `s_2`. Then it is also a solution in base `-(b + s_2 / s_1)`.

Proof. The other root of `Q_s` is `-s_2 / s_1 - b`, an integer. Its absolute
value `b + s_2 / s_1` exceeds `b`, which exceeds every digit.

The 3-digit solutions with leading digit 1 are `(1,3,1)` in base 4, `(1,2,6)`
in base 215 and `(1,7,1)` in base 904. Their partners are bases -7, -217 and
-911. The fourth one, `(1,1,1)` in base -2, has the partner root 1, which is
not a base.

Under `0^0 = 0` the families of chapter 2 appear again with negative bases.
For odd `x`, `(x, 0, 0)` and `(x, 0, 1)` are solutions in base
`-x^((x-1)/2)` as well as in base `x^((x-1)/2)`. A swap-like solution is
`(3, 0, 0, 0, 27)` in base `-3^20`: `3 * 3^80 = 27^27`.

Complete lists for small negative bases. `analysis/negabase.py` checks every
digit multiset in bases -2 to -10 (all lengths). A number with `d` digits in
base `-b` can be as small as about `b^(d-2)`, so lengths up to `b + 1` occur,
one more than in a positive base. Nontrivial solutions:

| base | `0^0 = 1` | `0^0 = 0` |
|---:|---|---|
| -2 | `(1,1,1)` | `(1,1,0)`, `(1,1,1)` |
| -3 | none | none |
| -4 | none | `(1,3,0,2,3)` |
| -5 | `(1,3,4,3,3)` | `(1,0,3)`, `(1,3,4,3,3)` |
| -6 | none | none |
| -7 | `(1,3,1)`, `(1,2,6,6,2,5,1)`, `(1,4,0,1,0,6,5)` | `(1,3,0)`, `(1,3,1)`, `(1,2,6,6,2,5,0)`, `(1,2,6,6,2,5,1)` |
| -8 | `(7,5,7,6,2,0,3)` | `(4,0,0)`, `(4,0,1)` |
| -9 | none | none |
| -10 | `(4,0,5,8,1,9,1,1,1)`, `(5,8,1,1,8,2,4,9,2)`, `(1,9,2,1,7,4,5,8,9,8,9)` | `(4,0,5,8,1,9,4,3,0)`, `(4,0,5,8,1,9,4,3,1)`, `(5,8,1,1,8,2,4,9,2)`, `(1,9,2,1,7,4,5,8,9,8,9)` |

Bases -11 and -12 (`analysis/data/negabase_11_12.txt`): under `0^0 = 1`,
`(2,2,0,9,0,3,7,6,3)` and `(1,3,8,9,2,10,2,5,10,7,1)` in base -11, and
`(10,8,8,9,11,2,4,7,6,0,11)` in base -12; under `0^0 = 0`, the 11-digit one of
base -11 and its twin, and none in base -12.

All lengths are odd, as Proposition 12.2 requires. The first base -10 example
is 404201091:
`4 * 10^8 + 5 * 10^6 - 8 * 10^5 + 10^4 - 9 * 10^3 + 100 - 10 + 1 = 404201091`
and `4^4 + 1 + 5^5 + 8^8 + 1 + 9^9 + 1 + 1 + 1 = 404201091`. The last one has
11 digits, more than the base. Twins appear under `0^0 = 0` as in section 2.1.
Bases -3, -6 and -9 have no solution under either convention.

## 12.4 Roots that are too small to be bases

An integer root `r` with `|r|` at most the largest digit gives a value
`P_s(r) = F(s)` in a representation whose digits are too large for `r`. There
are many of these for small `r`. Examples under `0^0 = 1`:
- `(3,1,2)` at `r = 3`: `27 + 3 + 2 = 32 = 27 + 1 + 4`;
- `(4,1,3,1)` at `r = 4`: `256 + 16 + 12 + 1 = 285 = 256 + 1 + 27 + 1`.

The search with digits up to 28 finds 32 such 5-digit strings. These are not
Munchausen numbers. They are the reason why the local test alone can never
prove that a string fails in every base: a rational root of `Q_s` passes every
local test. The real-root bound `r > max(s)` must come from outside.

## 12.5 One varying digit: the root as a function of `x`

Fix two digits of a 3-digit string and let the third, `x`, vary. The real root
`b*(x)` of `Q_s` is then a function of `x`, and a solution is an `x` where
`b*(x)` is an integer above the digits. `analysis/near_integer.py` computes
the distance `||b*(x)||` to the nearest integer exactly, with integer square
roots, for odd `x` up to 6,001 (`0^0 = 1`).

Two behaviours appear, and they match the two cases of Theorem 8.3.

- Square class. For `(x, 1, 5)` with `x` odd, the dominant term `x * x^x` is
  the square `x^(x+1)`. The root sits just below an integer, at a distance of
  `1/(2x)` up to lower-order terms: `x ||b*(x)|| = 0.500` for every `x` from 19
  to 6,001. So the root approaches the integers but never reaches them, which
  is the content of Theorem 8.3.
- Outside it. For `(1, x, 1)`, `(6, 1, x)` and `(2, x, 3)`, the fractional
  parts look uniform. Below 0.01, 0.05 and 0.25 lie 1.8 to 2.1%, 9.7 to 10.2%
  and 48.5 to 49.6% of the values, against 2%, 10% and 50% for a uniform law.
  The record small distances behave like the minimum of independent uniform
  draws (`x ||b*(x)||` between 0.06 and 2.6). The only exact hits are the known
  solutions: `x = 3` and `x = 7` for `(1, x, 1)`, and `x = 5` for `(6, 1, x)`
  in base 91.

For `(1, x, 1)` the condition is that `x^2 + 4 x^x + 4` is a perfect square.
For odd `x`, `4 x^x = 4x Y^2` with `Y = x^((x-1)/2)`, so it is the Pell-type
equation `U^2 - 4x Y^2 = x^2 + 4` with a prescribed `Y` (section 8.2). The
uniform fractional parts are what the spacing heuristic assumes. They do not
decide the question, because a solution needs `b*(x)` to be an integer to
within `x^(-x/2)`, far below the resolution of this test.

## 12.6 Status

| question | status |
|---|---|
| Galois group of `Q_s` | `S_(k-1)` for random strings (Chebotarev statistics); smaller for decomposable digit polynomials |
| sieve survival per prime | the derangement share of `S_(k-1)`, about `1/e` |
| can a string pass every local test without a rational root | only if `Q_s` is reducible (Proposition 12.1); none found |
| negative bases | new solutions found; odd length only (Proposition 12.2); quadratic partners (Proposition 12.3) |
| one varying digit | square class: the root stays `1/(2x)` below an integer; otherwise its fractional part is uniform (12.5) |
