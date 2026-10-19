# 2. Constructions

Most solutions in large bases look random (chapter 5). This chapter covers the
ones that do not: families that follow from an identity and need no search.
Every family below was checked with exact integers by
`analysis/verify_constructions.py`, and the searches in chapter 3 find exactly
these members in their ranges.

## 2.1 Twins under `0^0 = 0`

Proposition 2.1. Under `m = 0`, a number `n` whose last digit is 0 is a
solution if and only if `n + 1` is a solution.

Proof. `n + 1` has the same digits as `n`, except a 1 in the last position in
place of a 0. So `F(n + 1) = F(n) + 1`.

So under `m = 0` every solution that ends in 0 or 1 has a twin. Under `m = 1` a
0 and a 1 weigh the same, and there are no twins. Bases 2 to 41 contain 8 twin
pairs, for example `(4,0,0)` and `(4,0,1)` in base 8.

## 2.2 Self-paying digits

A digit `a >= 2` at position `k >= 1` is self-paying if `a * b^k = a^a`, that
is `a^(a-1) = b^k`. Its balance is zero, so it adds the same amount to `n` and
to `F(n)`.

Proposition 2.2 (which bases have them). Write `b = r^t`, where `r` is not a
perfect power. The self-paying digits of base `b` are `a = r^s` for
`1 <= s < t` with `t | s (r^s - 1)`, at position `k = s (r^s - 1) / t`.

Proof. `a^(a-1) = b^k` means that `a` and `b` are powers of one integer. With
`b = r^t` and `a = r^s`, the equation becomes `s (r^s - 1) = t k`, and `a < b`
means `s < t`.

So only perfect powers have self-paying digits. Every odd square `r^2` has one:
the digit `r` at position `(r-1)/2`. Base 64 has two: 4 at position 1 and 16 at
position 10. Some perfect powers have none, for example 4, 16, 27, 36 and 100.
There are 47 bases up to 4096 with at least one self-paying digit
(`analysis/selfpaying.py` lists them).

Proposition 2.3 (structure under `0^0 = 0`). Under `m = 0`, setting a
self-paying digit to 0 turns a solution into a solution. Putting a self-paying
digit on a position that holds 0 does the same. Every solution therefore splits
uniquely into:

- a core: a solution, or 0, with no self-paying digit and a last digit other
  than 1,
- a set of self-paying digits on positions where the core has a 0,
- optionally a final 1, if the core ends in 0.

Every such combination is a solution.

Proof. Each operation changes the balance by the balance of one placement,
which is zero. The core is what remains after removing all self-paying digits
and a final 1.

Corollary 2.4. If base `b` has `C` self-paying digits, then
`N_0(b) >= 2^(C+1) - 2`. Take the core 0, any subset of the self-paying digits,
and an optional final 1, and leave out the two trivial solutions.

Under `m = 1` a zero weighs 1, so removing a digit does not leave a solution.
Self-paying digits still help when they sit directly on top of a solution with
the right number of digits:

Proposition 2.5. Let `a` be self-paying at position `k`, and let `m'` be a
number below `b^k` with `p` zeros between its leading digit and position `k`.
Then `a * b^k + m'` is a solution if and only if `F(m') + p * w(0) = m'`.

Examples: `(3,1)` in base 9 and `(5,1,3)` in base 25 under both conventions.
In the second, 5 is self-paying at position 2 and `(1,3)` is a solution in base
25.

## 2.3 Swaps

Two digits can pay for each other. Put `a` at position `k` and `c = a^a` at
position 0. If `a * b^k = c^c`, then the value of each digit equals the weight
of the other one: `a * b^k = c^c` and `c = a^a`. With zeros in between and
`m = 0`, the number `(a, 0, ..., 0, a^a)` is a solution. The condition is

    b^k = a^(a^(a+1) - 1),  and  a^a < b.

Examples:

- `a = 2`, `k = 1`: `(2,4)` in base 128.
- `a = 3`: `3^80 = b^k`, so `(3, 0, ..., 0, 27)` is a solution in bases 81,
  243, `3^8`, `3^10`, `3^16`, `3^20`, `3^40` and `3^80`. In base `3^t` it has
  `80/t + 1` digits.
- Every odd `a` gives a 3-digit swap `(a, 0, a^a)` in base
  `a^((a^(a+1) - 1) / 2)`.
- `a = 4`: `(4, 0, ..., 0, 256)` with 187 digits in base 2048.

Swaps also combine with self-paying digits under `m = 0`. Base 81 has
`(3, 0, ..., 0, 9, 0, 0, 0, 27)`, with the self-paying 9 at position 4.

Under `m = 1`, the zeros must be paid for. Base 64 has an example that combines
everything:

    (16, 0, 0, 0, 0, 0, 1, 0, 0, 4, 8)

16 and 4 are self-paying. The 1 at position 4 and the 8 at position 0 form a
swap: `8^8 = 64^4`. The 8 is worth 8, which pays for the weight of the 1 plus
the seven zeros.

## 2.4 Two-digit solutions: a complete description

Proposition 2.6. The two-digit number `(a, c)` is a solution if and only if

    a  divides  w(c) - c,   and   b = (a^a + w(c) - c) / a  is larger than a and c.

The base is then `b`.

Proof. `a b + c = a^a + w(c)`, solved for `b`.

Infinite families:

- `a = 1`: `(1, c)` in base `c^c - c + 1`, for every `c >= 2`. Examples:
  `(1,2)` in base 3, `(1,3)` in base 25. Under `m = 1`, also `(1,0)` in base
  2.
- `a = c`: `(c, c)` in base `2 c^(c-1) - 1`. Examples: `(2,2)` in base 3,
  `(3,3)` in base 17, `(4,4)` in base 127.
- `c = 1`, and under `m = 0` also `c = 0`: `(a, 1)` and `(a, 0)` in base
  `a^(a-1)`, for every `a >= 3`. The digit `a` is self-paying.
- Any `a`, and every `c == 0` or `c == 1 (mod a)`, because then `a` divides
  `c^c - c`. For example `(2, c)` in base `(c^c - c + 4) / 2` for every `c >= 2`.

There are 2,637 two-digit solutions with digits up to 60. Of these, 119 have
the form `(1, c)` and 118 the form `(c, c)`. Another 174 end in 0 or 1, and the
other 2,226 are pairs with `a | c^c - c`.

## 2.5 Solutions of every length under `0^0 = 0`

Proposition 2.7. Under `m = 0`, every length `k >= 2` has infinitely many
bases with a `k`-digit solution.

Proof. Take `t >= 2`, `r = t (k-1) + 1` and `b = r^t`. Then
`r^(r-1) = r^(t(k-1)) = b^(k-1)`, so `r` is self-paying at position `k-1`, and
`r < b`. So `(r, 0, ..., 0)` and `(r, 0, ..., 0, 1)` are `k`-digit solutions.

Under `m = 1` a family for every `k >= 3` exists too, but its bases are
enormous. The digits are the coefficients of `(c r + e)^(k-1)` without the
constant term, followed by one large digit `x` that makes `x^x` a
`(k-1)`-th power (Theorem 22.6, Corollary 22.7). The smallest member is
`(1,2,6)` in base 215; the next 3-digit one is `(1,6,46666)` in base
`46666^23333 - 3`. Chapter 3 gives evidence that below such sizes some
lengths have no solution at all.
