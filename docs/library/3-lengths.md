# 3. Solutions of a fixed length

This chapter fixes the number of digits `k` and asks about all bases at once.
Which bases have a `k`-digit solution? Are there finitely or infinitely many?

## 3.1 Searching all bases at once

Proposition 1.3 says that a digit string is a solution in at most one base. So
a search can fix the digits and solve `P_s(b) = F(s)` for the base `b`.
`analysis/kdigit.py` does this with exact integer arithmetic. It solves by
Newton's method from above, which cannot skip the root because `P_s` is convex
and increasing.

By Proposition 1.2, a `k`-digit solution in base `b` only uses digits `x` with
`x^x < b^k`. So enumerating all strings with digits up to `M` finds every
`k`-digit solution in every base `b` with `b^k <= (M+1)^(M+1)`.

| length `k` | digits up to | complete for bases up to | strings | time |
|---:|---:|---:|---:|---:|
| 2 | 60 | `10^54.5` | 3,660 | 0.1 s |
| 3 | 80 | `10^51.5` | 524,880 | 5 s |
| 4 | 44 | `10^18.6` | 4.0 million | 28 s |
| 5 | 28 | `10^8.5` | 19.8 million | 2 min |
| 6 | 20 | `10^4.6` | 81.7 million | 10 min |

The results agree with the exhaustive searches for every base up to 38.
`analysis/data/k<k>.txt` holds the lists.

## 3.2 Under `0^0 = 1`

Every solution with 3 to 6 digits, in every base in the range above, and
with 7 and 8 digits in the ranges of section 19.1.5 (bases up to `10^7.2` for
7 digits and `10^4.4` for 8 digits):

| length | solutions (base: digits) |
|---:|---|
| 3 | 4: `(1,3,1)`, `(3,1,3)`; 25: `(5,1,3)`; 91: `(6,1,5)`; 215: `(1,2,6)`; 904: `(1,7,1)` |
| 4 | 10: `(3,4,3,5)`; 20: `(6,5,3,4)` |
| 5 | 6: `(2,2,3,5,2)`, `(2,3,4,5,2)`; 7: `(1,3,4,5,4)`; 13: `(3,3,6,6,1)`; 14: `(2,6,0,3,6)`; 48: `(3,8,6,2,0)` |
| 6 | 9: `(1,5,6,2,6,2)` |
| 7 | 9: `(1,6,5,6,5,4,7)` |
| 8 | 11: `(1,8,4,5,3,2,7,8)`, `(1,8,4,5,3,4,8,7)` |

So 3435, the famous base-10 example, is one of only two 4-digit solutions in
all bases up to `10^18`. The other one is `(6,5,3,4)` in base 20.

Two of the 3-digit solutions fit a pattern. `(1, x, 1)` is a solution when
`b^2 + x b = x^x + 1`. That needs `x^2 + 4 (x^x + 1)` to be a perfect square.
This holds for `x = 3` (`121 = 11^2`, base 4) and `x = 7` (`1815^2`, base 904),
and for no other `x` up to 80. Chapter 16 extends this to `x <= 4 * 10^9`.

Two-digit solutions are plentiful under both conventions (section 2.4). Under
`m = 1`, only base 3 has more than one of them. The search above showed this
for all bases up to `10^54`, and Theorem 15.7 proves it for every base.

## 3.3 Under `0^0 = 0`

Under `m = 0` the solutions with 3 to 8 digits, in the same ranges as in
section 3.2, are the self-paying families of section 2.5, the swaps of section
2.3, and these others:

| length | solutions (base: digits) |
|---:|---|
| 3 | 4: `(1,3,0)`, `(1,3,1)`, `(3,1,3)`; 5: `(1,0,3)`; 25: `(5,1,3)`; 91: `(6,1,5)`; 215: `(1,2,6)`; 904: `(1,7,0)`, `(1,7,1)` |
| 4 | 5: `(2,0,2,4)`; 10: `(3,4,3,5)`; 20: `(6,5,3,4)`; 128: `(8,0,2,4)` |
| 5 | 6: `(2,2,3,5,2)`, `(2,3,4,5,2)`; 7: `(1,3,4,5,4)`; 11: `(6,6,5,0,0)`, `(6,6,5,0,1)`; 13: `(3,3,6,6,0)`, `(3,3,6,6,1)` |
| 6 | 9: `(1,5,6,2,6,2)`; 11: `(5,1,7,5,0,3)` |
| 7 | 9: `(1,6,4,7,0,6,3)`, `(1,6,5,6,5,4,7)` |
| 8 | 9: `(3,4,6,6,4,0,8,4)`; 11: `(1,8,4,5,3,2,7,8)`, `(1,8,4,5,3,4,8,7)` |

`(8,0,2,4)` in base 128 is the self-paying 8 at position 3 on top of the
2-digit solution `(2,4)`.

The self-paying families make the lists infinite. For 3 digits they are
`(r,0,0)` and `(r,0,1)` whenever `r^(r-1) = b^2`. That covers every odd `r`, in
base `r^((r-1)/2)`, and every square `r`, for example `r = 16` in base `2^30`.
The swap `(3,0,27)` in base `3^40` is the first 3-digit swap.

## 3.4 Which lengths occur?

Under `m = 0`, every length occurs, in infinitely many bases (Proposition 2.7).

Under `m = 1` that is not true in the searched range. Combining the exhaustive
search of bases 2 to 41 with a search of bases 39 to 127 for numbers with at
most 30 digits:

    no solution with 9, 18, 21, 22, 24, 26 or 28 digits in any base up to 127.

`analysis/missing_lengths.py` extends this with the exact tree search of
`analysis/tree.py`, which is fast for short numbers in large bases:

| length | no solution in any base up to |
|---:|---:|
| 9 | 100,000 |
| 18, 21, 22, 24, 26, 28 | 10,000 |

For these lengths, larger bases are very unlikely to help. A 9-digit solution
in a base `b >= 128` can only use digits `x` with `x^x < b^9`. Under the
random model of chapter 5, the chance of a 9-digit solution in base 128 is
below `10^-8`, and it falls quickly with `b`. Algebraic families escape this
estimate, and they exist: the binomial families of chapter 22 give solutions
of every length `k >= 3` under `m = 1`, these lengths included, in bases far
beyond any search (Corollary 22.7). So these lengths are missing only in the
bases searched, and, by the model, in all bases of moderate size.

The model also predicts how many lengths are missing. For large `k`, the
expected number of `k`-digit solutions, summed over all bases, tends to 1
(section 5.2). If solutions occur independently, a length has none with
probability about `e^(-1)`, or 37%. Under `m = 1`, 7 of the 29 lengths from 2
to 30 are missing, which is 24%.

## 3.5 Finitely or infinitely many?

Every base has finitely many solutions (Proposition 1.1). The interesting
question is about a fixed length across all bases.

| length | `0^0 = 0` | `0^0 = 1` |
|---|---|---|
| 1 | only 0 and 1 | only 1 |
| 2 | infinitely many (section 2.4) | infinitely many (section 2.4) |
| `k >= 3` | infinitely many (Proposition 2.7) | infinitely many (Corollary 22.7) |

This library first conjectured that the last entry was finite. The evidence
was the lists in section 3.2, and a heuristic.
Take a digit string `s` whose largest digit is `x`. Its base, if any, is the
root of `P_s(b) = F(s)`, which is about `x^(x/(k-1))`. The chance that this
root is an integer is about `1 / P_s'(b)`, roughly `x^(-x(k-2)/(k-1))`. There
are about `k x^(k-1)` strings with largest digit `x`. Summed over `x`, the
expected number of solutions is finite for every `k >= 3`. For `k = 2` the
chance is about `1/a` for the leading digit `a`, the sum diverges, and indeed
there are infinitely many.

For `k = 3` and digits above 80 the tail of that sum is below `10^-70`. So
the heuristic says the six 3-digit solutions under `m = 1` are all of them.

That conclusion is false. Chapter 22 builds infinitely many solutions of every
length `k >= 3` from the binomial coefficients of `(c r + e)^(k-1)`
(Corollary 22.7). For these strings `Q_s(r) = (c r + e)^(k-1) - x^x` exactly,
so the root is an integer whenever `x^x` is a `(k-1)`-th power. The heuristic
treats the root as a random number and cannot see such identities. The first
3-digit member beyond `(1,2,6)` is `(1,6,46666)` in base
`46666^23333 - 3`, about `10^108942`, far above the range of section 3.2. So
the 3-digit list is complete for bases up to `10^51.5`, not for all bases.

Under `m = 0` the self-paying and swap families escape the heuristic. They
come from exact identities between powers, not from chance.

## 3.6 Short solutions in base 100

The exhaustive search of base 100 up to 50 digits found no nontrivial solution
under either convention (chapter 6). Base 100 has no self-paying digit, because
100 is `10^2` and `2` does not divide `1 * (10 - 1)`. It also has no 2-digit
solution.
