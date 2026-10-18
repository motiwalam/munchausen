# Round 2: computations for questions 41, 42, 35, 43 and 44

DRAFT. Each claim is marked proven (a proof is here), computed (an
exhaustive computation, with its range) or heuristic (the probabilistic
model, or a judgment from data).

## Question 43: lengths in base -1+i

Theorem R2.1 (proven). In base `beta = -1+i` (digits 0 and 1), the
representation of a rational integer `n` is its base -4 representation with
each base -4 digit `B` written as the block `(B mod 2, 0, [B >= 2], [B >= 2])`
at positions `4j` to `4j+3` (least significant first). So a positive integer
has `8m + 1` digits if its leading base -4 digit is 1, and `8m + 4` digits if
it is 2 or 3. Both residues occur for every `m`: `16^m` and `2 * 16^m`.

Proof. `beta^4 = -4`. Cut a representation of `z` into blocks of four digits,
so that `z = sum_j C_j (-4)^j` with `C_j = a_0 + a_1 beta + a_2 beta^2 + a_3
beta^3` and `a_k` in {0, 1}. Since `beta^2 = -2i` and `beta^3 = 2 + 2i`,

    C = (a_0 - a_1 + 2 a_3) + i (a_1 - 2 a_2 + 2 a_3).

Let `y_j` be the imaginary part of `C_j`. It lies in {-2, ..., 3}. If `z` is
real, `sum_j y_j (-4)^j = 0`. Reducing mod 4 gives `y_0 == 0`, so `y_0 = 0`,
because 0 is the only multiple of 4 in that range. Divide by -4 and repeat:
every `y_j` is 0. Now `a_1 - 2 a_2 + 2 a_3 = 0` forces `a_1 = 0` and
`a_2 = a_3`. Then `C_j = a_0 + 2 a_2` is a base -4 digit `B_j` in {0, 1, 2, 3},
and `z = sum B_j (-4)^j` is the base -4 representation of `z`, which is unique.
Conversely every such block string represents `z`, and representations in
base -1+i are unique, so this is the representation. A positive integer has
an odd number `2m + 1` of base -4 digits (Proposition 12.2). Its top block
ends at position `8m` when `B = 1` and at `8m + 3` when `B` is 2 or 3.

This answers question 43 and the first open question of section 14.7.
`analysis/r2c_gauss_m1i.py` checks the block form for every `|n| <= 10^6`
and 100,000 random integers below `10^60` (computed,
`analysis/data/r2c_gauss_m1i.txt`).

Corollary R2.2 (proven). The ones of a positive `n` number the base -4 digit
sum `s(n)`, and its digits number `8m + 1` or `8m + 4`. So the Munchausen
numbers of base -1+i are:

- under `0^0 = 0` (`F` counts ones), the `n` with `n = s(n)`: exactly 1, 2,
  3, 4, 5, 6 and 7;
- under `0^0 = 1` (`F` counts digits), the `n` equal to their length:
  exactly 1 and 9.

Proof. With `2m + 1` base -4 digits, `n > (4^(2m) - 1)/5` (Corollary 14.2),
while `s(n) <= 3 (2m + 1)` and the length is at most `8m + 4`. For `m >= 2`
both bounds are below 51, so `m <= 1` and `n <= 19`. For `m = 1`,
`n = 16 - 4 B_1 + B_0` and `s = 1 + B_1 + B_0` (the top digit must be 1,
since `n <= 19`), so `n = s` means `B_1 = 3`: n = 4 to 7. The length is 9,
so `n = 9` is the only one of length type. For `m = 0`, n = 1, 2, 3 with
lengths 1, 4, 4.

This is the census of section 14.5 (computed there to 18 digits), now
proven complete.
