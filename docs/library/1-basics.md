# 1. Basics

This chapter fixes the notation and proves the facts that every later chapter
uses.

## 1.1 Definitions

- `b >= 2` is the base. A number `n` has the base-`b` digits
  `s_{d-1} ... s_1 s_0`, with `s_{d-1} != 0`, so it has `d` digits. Position
  `i` holds `s_i`, and position 0 is the last digit.
- The convention `m` is 0 or 1. It is the value of `0^0`.
- `w(x)` is the weight of a digit: `w(x) = x^x` for `x >= 1`, and `w(0) = m`.
- `F(n)` is the Munchausen sum: the sum of `w(s_i)` over all digits.
- `n` is a solution, or a Munchausen number, if `F(n) = n`.
- The trivial solutions are 1 in both conventions and 0 under `m = 0`. Unless
  a statement says otherwise, "solution" means a nontrivial one.
- `c_x` is the number of times the digit `x` occurs in `n`. The vector `c` is
  the digit multiset of `n`.
- `N_m(b)` is the number of solutions in base `b`. `N_{m,k}(b)` counts those
  with exactly `k` digits.

## 1.2 Length

Proposition 1.1. A solution in base `b` has at most `b` digits.

Proof. A number with `d` digits is at least `b^(d-1)`. Its sum is at most
`d (b-1)^(b-1)`. For `d = b+1` the bound is `(b+1) (b-1)^(b-1)`, which is less
than `b^b` for every `b >= 2`. For larger `d` the gap grows. So no solution has
more than `b` digits.

So every base has finitely many solutions, and `N_m(b)` is finite.

Proposition 1.2. A `k`-digit solution in base `b` only uses digits `x` with
`x^x < b^k`.

Proof. One digit `x` already contributes `x^x` to `F(n) = n < b^k`.

Write `X_k(b)` for the largest such digit. For fixed `k`,
`X_k(b) ~ k ln(b) / ln(k ln b)`, so short solutions use small digits only.

## 1.3 Balance

Rewrite `F(n) = n` as a sum over the digits:

    sum over positions i of ( s_i * b^i - w(s_i) ) = 0.

The term `beta(x, i) = x * b^i - w(x)` is the balance of digit `x` at position
`i`. A number is a solution exactly when its balances add up to zero. Some
placements have balance zero on their own:

| placement | why its balance is zero |
|---|---|
| a 0 anywhere, under `m = 0` | `0 * b^i - 0 = 0` |
| a 1 at position 0 | `1 - 1 = 0` |
| a digit `a` at position `k >= 1` with `a^(a-1) = b^k` | `a * b^k = a^a` |

Chapter 2 builds solutions out of these.

## 1.4 One base per digit string

Proposition 1.3. A digit string with at least two digits is a solution in at
most one base.

Proof. Fix the digit string `s`. Its value `P_s(b) = sum s_i b^i` grows
strictly with `b`, because the leading digit is at least 1. Its sum `F(s)` does
not depend on `b`. So `P_s(b) = F(s)` has at most one solution `b`.

So the search can be turned around: fix the digits and solve for the base.
Chapter 3 uses this to list every short solution in every base up to an
enormous bound.

## 1.5 The two conventions

Proposition 1.4. `F_1(n) = F_0(n) + z(n)`, where `z(n)` is the number of zeros
in `n`.

So a number without zeros is a solution under both conventions or under
neither. A number with zeros is a solution under at most one convention.
Chapter 4 calls the zero-free solutions shared.

## 1.6 Congruences

Every number satisfies `n == (digit sum of n) (mod b-1)`, because
`b == 1 (mod b-1)`. For a solution, `n = F(n)`, so:

Proposition 1.5. For every solution,

    sum over digits x of ( w(x) - x ) == 0   (mod b-1).

This is a condition on the digit multiset alone. Its parts modulo the prime
powers of `b-1` give simple rules:

- Odd base, `m = 1`: a solution has an even number of zeros. Proof: modulo 2,
  `x^x == x` for every `x >= 1`, so the sum reduces to `c_0 * 1`.
- Odd base, `m = 0`: the condition modulo 2 always holds, for the same reason.
  Chapter 5 shows that this doubles the expected number of solutions.
- `b == 1 (mod 4)`, `m = 0`: the number of digits `== 2 (mod 4)` is even.
  Proof: `x^x == x (mod 4)` except for `x == 2 (mod 4)`, where the two sides
  differ by 2.
- `b == 1 (mod 3)`, `m = 0`: the number of digits `== 2 (mod 6)` is a multiple
  of 3. Proof: modulo 3, `x^x == x` except for even `x == 2 (mod 3)`, where
  `x^x == 1` and `x == 2`.

For even bases, `n` and its last digit have the same parity, which gives:

- Even base: the last digit is odd exactly when the number of odd digits is
  odd. Under `m = 1`, count the zeros together with the odd digits.

The catalog in `analysis/` has 719 solutions in odd bases under `m = 1` and
1,327 solutions in even bases. All of them obey these rules, as they must.

## 1.7 The leading digit

The leading digit of a `d`-digit solution is `floor(F(n) / b^(d-1))`. The
largest digits present supply almost all of `F(n)`. For all 26 solutions in
bases 20 to 38 under `m = 1`, the two largest digit values alone give the
leading digit. For a `(b-1)`-digit solution, the digit `b-1` occurs at most
twice, because `3 (b-1)^(b-1) > (3/e) b^(b-1) > b^(b-1)`. One copy puts the
leading digit near `b/e`, and two copies put it near `2b/e`.

## 1.8 Solutions with `b` digits

Proposition 1.6. For `b >= 7`, a `b`-digit solution contains the digit `b-1`
at least 3 times.

Proof. If `b-1` occurs at most twice, then
`F(n) <= 2 (b-1)^(b-1) + b (b-2)^(b-2)`. Divided by `b^(b-1)` this is
`2 (1-1/b)^(b-1) + (1-2/b)^(b-2)`. Both terms decrease as `b` grows, and at
`b = 7` the sum is 0.979. So `F(n) < b^(b-1) <= n`, and `n` is not a solution.

With `c` copies of `b-1` the sum is about `(c/e) b^(b-1)`, so the leading digit
is 1 for 3 to 5 copies. Both known `b`-digit solutions (bases 15
and 16, under `0^0 = 0`) start with the digit 1 and contain `b-1` exactly
three times.

