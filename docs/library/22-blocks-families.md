# 22. Self-paying blocks and binomial families

This chapter answers the first new question of chapter 19: count the
self-paying blocks, and test whether they explain the 5-digit solutions in
bases 13 to 99. It also asks what blocks mean for the long solutions.

Each statement carries one mark:

- proven: a proof is in this chapter;
- computed: an exact computation, with its range;
- heuristic: the root heuristic of section 11.4, the basic model of
  chapter 5, or the base-by-base calibration of section 22.4.1 below. None
  of these is a proof.

Scripts are in `analysis/` with names starting `r4b_`. Their output is in
`analysis/data/r4b_*`. The runs used 2 to 4 threads of the shared 8-thread
machine. The longest run took about 2 minutes.

Notation. For a digit string `s`, `P_s(b)` is its value in base `b` and
`F(s)` the sum of its weights, with `0^0 = 0` or `0^0 = 1`. A k-digit string
split into a top part `t` of `L = k - m` digits and a tail `u` of `m` digits
is written `s = (t, u)`.

## Summary

| question | answer | status |
|---|---|---|
| 1, the three solutions | `(3,3,6,6,1)` in base 13 is the exact block `(3,3,6,6)` at shift 1 followed by the digit 1. `(3,8,6,2,0)` in base 48 is a block with remainder 1 followed by a 0, which weighs 1. `(2,6,0,3,6)` in base 14 has no block structure. None is a family member, none has a self-paying digit. | computed |
| 2, blocks | A block `(t, b, m)` is a solution of `b^m P_t(b) = F(t)`. Under `0^0 = 0` it is the solution `(t, 0, ..., 0)`. With `L >= 2` and digits up to 40 to 150 there are exactly 4: `(1,3)` in base 4, `(1,7)` in base 904, `(6,6,5)` in base 11, `(3,3,6,6)` in base 13. The rate is the basic rate of an `(L+m)`-digit solution divided by about `(k/L) X^m`, `X` the largest usable digit (about 8 here). In bases from 13 on, 2 exact blocks against 0.73 expected (P = 0.17). | computed; heuristic |
| 3, new families | For every `k >= 3` there are infinitely many k-digit solutions under both conventions: `(t_0, ..., t_(k-2), x)` with `t_i` the binomial coefficients of `(c r + e)^(k-1)`, in base `(x^(x/(k-1)) - e)/c`. Examples: `(1,6,46666)` in base `46666^23333 - 3`, `(1,6,12,8916100494921)`. This refutes the conjectured finiteness of chapter 3 (section 3.5) and corrects Corollary 8.4. | proven; computed (checks) |
| 3, refined heuristic | Blocks are already inside the root heuristic: `(t, 1)` and the block `t` have the same polynomial. Families add nothing at `D = 0` in bases up to 99. A base-by-base calibration with 1.24 million offsets puts the 5-digit expectation in bases 13 to 99 at 0.33 (0.26 to 0.49 over window and class choices), as the root heuristic says. 3 observed: P = 0.005 (0.002 to 0.014), 0.015 after the choice among 10 cells. The excess is about 9 times, not 17, and blocks do not explain it. | heuristic, computed |
| 3, completeness, 6 and 7 digits | The lists stay complete in their computed ranges. Beyond them the families give infinitely many solutions of every length, the nearest in base `10^108942` (3 digits) and, from a second family of chapter 25, `10^(4.04 * 10^7)` (4 digits; Theorem 25.5). For 6 and 7 digits the calibrated expectation in bases 3 to 99 is 1.4 and 1.2, against 1 and 1 observed. | proven, heuristic |
| 4, long solutions | In bases 2 to 43, 2 solutions under `0^0 = 1` have an exact split, against 3.4 expected from random digits. Blocks are a share of about `1/b` of the solutions, which the model of chapter 5 already counts. A search that assembles solutions from blocks finds that share at the full cost. No correction, no shortcut. | computed against heuristic |

## 22.1 The three 5-digit solutions in bases 13 to 99

### 22.1.1 Splits and remainders

Lemma 22.1 (proven). Let `s = (t, u)` with `u` of `m` digits. Put

    R_m = b^m P_t(b) - F(t).

Then `s` is a solution in base `b` exactly when `R_m = F(u) - P_u(b)`. In
particular `R_m = 0` exactly when the tail pays for itself,
`P_u(b) = F(u)`, where leading zeros of `u` weigh `0^0`.

Proof. `P_s(b) = b^m P_t(b) + P_u(b)` and `F(s) = F(t) + F(u)`.

So every solution comes with a remainder at every split, and the remainder
is fixed by the tail. A small remainder says only that the tail digits are
small. The split is exact when `R_m = 0`. Under `0^0 = 1` the tails of one
digit that pay for themselves are only `(1)`. A 0 costs 1, so `R_1 = 1`
for a solution that ends in 0. A tail of two digits pays for itself only if
it is a 2-digit solution of the base.

### 22.1.2 The data (computed)

`r4b_solutions.py` prints every split of every short solution under both
conventions (`data/r4b_solutions.txt`). For the three solutions:

| base | digits | `n` | largest weights | `R_1` | `R_2` | `R_3` | `R_4` |
|---:|---|---:|---|---:|---:|---:|---:|
| 13 | `(3,3,6,6,1)` | 93,367 | `6^6 + 6^6` = 99.94% of `n` | 0 | 46,578 | 92,220 | 85,656 |
| 14 | `(2,6,0,3,6)` | 93,344 | `6^6 + 6^6` = 99.97% | 46,650 | 46,635 | 46,636 | 76,828 |
| 48 | `(3,8,6,2,0)` | 16,823,904 | `8^8` = 99.72% | 1 | -91 | 32,741 | 15,925,221 |

What this shows:

- `(3,3,6,6,1)` in base 13 is an exact block followed by the digit 1:
  `13 * P_(3,3,6,6)(13) = 13 * 7182 = 93366 = 3^3 + 3^3 + 6^6 + 6^6`. The
  same block gives `(3,3,6,6,0)` and `(3,3,6,6,1)` under `0^0 = 0`. It is
  the only one of the three with an exact block anywhere inside: no other
  substring pays for itself at its position.
- `(3,8,6,2,0)` in base 48 is a block with remainder 1. The top part
  `(3,8,6,2)` gives `48 P = 16823904 = F + 1`, and the final 0 weighs 1.
  Under `0^0 = 0` the strings `(3,8,6,2,0)` and `(3,8,6,2,1)` are
  near-solutions at `D = 1`. The 8 is not self-paying: 48 is not a perfect
  power. The near identity `3 * 48^4 + 8 * 48^3 = 8^8 + 2^15` makes the top
  two digits close to `8^8`, but the gap `2^15 = 0.30 * 48^3` is an
  ordinary size.
- `(2,6,0,3,6)` in base 14 has no exact split and no small remainder. Its
  remainders are `6^6 - 6` and its neighbours, the weight of the last 6.
- None of them has a binomial prefix in the sense of section 22.3, and none
  has a self-paying digit, since 13, 14 and 48 are not perfect powers.

So one solution is block plus digit, one is block with remainder 1 plus
digit, and one has no structure. By Lemma 22.1, the second pattern is the
same as the first with the last digit 0 in place of 1. Under the root
heuristic the last digit of a 5-digit solution is close to uniform over the
about 9 usable digits, so two of three in `{0, 1}` has probability about
0.13 (heuristic).

One shared trait is visible. Two of the three are dominated by `6^6 + 6^6`,
and 8 of the 16 solutions under `0^0 = 1` with 3 to 7 digits contain a 6.
This is where the mass of the heuristic lies: `6^6 = 46656` is the weight
that lands among the 5-digit numbers of bases 9 to 14, and `2 * 6^6` does
so in bases 10 to 17. It is not a mechanism beyond the per-base counts of
section 22.4.

## 22.2 Self-paying blocks

### 22.2.1 Definition

Definition 22.2. A self-paying block is a triple `(t, b, m)`: a string
`t = (t_1, ..., t_L)` with `t_1 >= 1` and `t_L >= 1`, a shift `m >= 1`, and
a base `b > max(t)`, with

    b^m P_t(b) = F(t).

The zeros inside `t` weigh `0^0`. A partial block with remainder `r` has
`b^m P_t(b) - F(t) = r` in place of 0.

The condition `t_L >= 1` makes the shift unique: under `0^0 = 0` a block
ending in 0 is the same equation as the shorter block at the next shift.
`L = 1` gives the self-paying digits of chapter 2 (section 2.2).

Lemma 22.3 (proven). Under `0^0 = 0`, `(t, b, m)` is a block exactly when
`(t, 0, ..., 0)` with `m` zeros is a solution in base `b`. Under `0^0 = 1`
it is a block exactly when `(t, 0, ..., 0)` has `P - F = -m`, because each
trailing zero weighs 1.

Proof. The trailing zeros add nothing to `P` and `m w(0)` to `F`.

Lemma 22.4 (proven). If `(t, b, m)` is a block and `u` is a tail of `m`
digits with `P_u(b) = F(u)`, then `(t, u)` is a solution of `L + m` digits.
If `(t, b, m)` is a partial block with remainder `r`, then `(t, u)` is a
solution exactly when `F(u) - P_u(b) = r`.

Proof. Lemma 22.1.

So a block is one equation in `L + 1` unknowns, the `L` digits and the
base, where a solution of `L + m` digits is one equation in `L + m + 1`
unknowns.

### 22.2.2 The count (computed)

`r4b_blocks.py` runs `kdigit` with `--offset 0` and `--offset -m` and keeps
the strings that end in `m` zeros (Lemma 22.3). It is complete for the bases
with `b^(L+m) <= (M+1)^(M+1)`, `M` the digit bound (`data/r4b_blocks.txt`):

| `L + m` | digits up to | complete for bases up to | `L = 1` (self-paying digits) | `L >= 2` |
|---:|---:|---:|---|---|
| 2 | 400 | `10^521.9` | 398 at `m = 1` | none possible |
| 3 | 150 | `10^109.7` | 79 at `m = 2` | `(1,3)` in base 4 and `(1,7)` in base 904, both at `m = 1` |
| 4 | 80 | `10^38.6` | 27 at `m = 3` | none |
| 5 | 40 | `10^13.2` | | `(6,6,5)` in base 11 at `m = 2`; `(3,3,6,6)` in base 13 at `m = 1` |
| 6 | 24 | `10^5.8` | | none |
| 7 | 16 | `10^3.0` | | none |

The rows with `L + m >= 4` cover `m = 1, 2, 3`. All four blocks with `L >= 2`
are free of zeros, so they are blocks under both conventions. Each one gives
the known solutions: `(1,3,1)`, `(1,7,1)` and `(3,3,6,6,1)` under `0^0 = 1`,
and the twins `(1,3,0)`, `(1,7,0)`, `(6,6,5,0,0)`, `(6,6,5,0,1)`,
`(3,3,6,6,0)` under `0^0 = 0`. `(6,6,5)` gives no solution under `0^0 = 1`:
base 11 has no 2-digit solution.

### 22.2.3 The rate (heuristic)

The basic model of chapter 5 (section 5.1) applies to a block as to a
solution. The number `F(t) / b^m` must be an integer (chance `b^(-m)`) whose
digits are `t` (chance `1 / (b^(L-1) (b-1))` for a random value). Summed
over `t`:

Heuristic 22.5. The expected number of blocks with `L` digits at shift `m`
in base `b` is

    E_b(L, m) = N_L(b) / (b^(k-1) (b - 1)),    k = L + m,

where `N_L(b)` counts the `L`-digit strings with `b^(k-1) <= F(t) < b^k`,
times a local factor for the residues of `x^x`. With `X` the largest digit
with `X^X < b^k`, `N_L(b)` is about `L X^(L-1) dX` with `dX` the number of
digits whose weight lies in `[b^(k-1), b^k)`. So

    E_b(L, m) / E_b(L + m, 0) ~ (L / k) X^(-m).

A block is rarer than a solution of the same total length by the factor
`(k / L) X^m`, the number of choices for the `m` missing digits. In bases
13 to 99, the mean of `X` is 7.2 to 10.8 for `k = 4` to 7. Both rates
fall like `b^(-(k-1))` up to powers of `log b`, so the expected total over
all bases is finite for every `L >= 2`.
The self-paying digits (`L = 1`) are the exception: `x b^m = x^x` has a
solution exactly when `x^(x-1)` is an `m`-th power, an identity rather than
a coincidence.

`r4b_rates.py` computes `N_L(b)` exactly (`data/r4b_rates.txt`). Sums over
bases 13 to 99:

| `(L, m)` | basic `E` | basic `E` for `(L+m, 0)` | ratio | `(L/k)/X` or `(L/k)/X^2` |
|---|---:|---:|---:|---:|
| (4, 1) | 0.0126 | 0.112 | 0.112 | 0.096 |
| (5, 1) | 0.0110 | 0.104 | 0.105 | 0.087 |
| (6, 1) | 0.0127 | 0.130 | 0.098 | 0.080 |
| (3, 2) | 0.00133 | 0.112 | 0.0119 | 0.0086 |
| (4, 2) | 0.00112 | 0.104 | 0.0107 | 0.0072 |

The ratio follows `(L/k) X^(-m)` within a factor 1.5.

### 22.2.4 The test (computed against heuristic)

`r4b_spectrum.c` takes one base at a time and computes
`V = b^m P_t(b) - F(t)` for every `t` with digits up to `X_b` whose `|V|`
can be at most `W = 0.05 b^(k-1)`. It prunes prefixes whose lower digits
cannot bring `V` into the window. It counts `N_0`, the exact blocks, and
the strings with `V = D` for every offset `D` with `b <= |D| <= W` in the
class of 0 modulo `2(b-1)`. The mean count per offset in the class is the
expected `N_0` of that base, measured on the true weights. Section 22.4.1
describes the method for solutions. For blocks under `0^0 = 1`
(`data/r4b_spectrum.txt`):

| `(L, m)` | bases | exact blocks | class mean | basic `E` | P(at least observed) |
|---|---|---:|---:|---:|---:|
| (2, 1) | 13 to 99 | 0 | 0.25 | 0.038 | |
| (2, 1) | 100 to 20,000 | 1, `(1,7)` in 904 (chapter 16) | 0.023 | 0.0013 (to 999) | 0.023 |
| (3, 1) | 13 to 20,000 | 0 | 0.34 | 0.020 | |
| (4, 1) | 13 to 5,000 | 1, `(3,3,6,6)` in 13 | 0.039 | 0.0126 | 0.038 |
| (5, 1) | 13 to 1,400 | 0 | 0.021 | 0.011 | |
| (6, 1), (7, 1) | 13 to 500, 200 | 0 | 0.038 | | |
| `m = 2, 3`, all `L` | 13 up | 0 | 0.02 | | |
| all, `L >= 2` | 13 up | 2 | 0.73 | | 0.17 |

The class means for `L + m = 3` and 4 rest on few offsets per base (the
window holds `0.05 b^(k-1)` values and the class step is `2(b-1)`), so they
are uncertain by a factor of about 2. For `L + m = 3` the bases below 40
have no offset in the class at all and add nothing to the mean. In bases
below 13 the window is too small for the method. There, `(1,3)` in base 4
and `(6,6,5)` in base 11 are the observed blocks.

The partial blocks show no special role for `R = 0`. Summed over bases from
13 on, the counts `N_R` for `R = -5, ..., 5` are 0, 0, 2, 0, 0, 1, 1, 0, 0,
0, 0 for `(L, m) = (4, 1)`, and 2, 2, 2, 2, 2, 3, 1, 1, 0, 2, 1 for 5-digit
strings. The values `R = -(L - 1)` recur for every `(L, m)` with `m >= 1`.
They come from `t = (a, 0, ..., 0)` with `a` self-paying: the `L - 1` zeros
cost 1 each.

Answer (heuristic, tested). Blocks are coincidences of one equation in
fewer unknowns. They occur at the rate of Heuristic 22.5, which makes them
about `(k/L) X^m` times rarer than solutions of the same length. The 2
exact blocks in bases from 13 on match 0.73 expected. The 5-digit block
`(3,3,6,6)` in base 13 is a 0.04 event on its own.

## 22.3 Binomial families: infinitely many solutions of every length

The near offsets of section 19.2 showed the families `(1, 0, 0, x)` and
`(1, 3, 3, x)` with `x^x` a cube. They sit at `D = x - 3` and `D = x - 56`
and miss `D = 0`. The general version of this family reaches `D = 0`.

### 22.3.1 The construction

Theorem 22.6 (proven). Let `j >= 2`, `c >= 1`, `e >= 1`, and

    t_i = c^(j-i) C(j, i) e^i    (i = 0, ..., j-1),
    x = e^j + t_0^(t_0) + ... + t_(j-1)^(t_(j-1)).

Suppose that `x^x = y^j` for an integer `y`, that `c` divides `y - e`, and
that `b = (y - e)/c` exceeds `x` and every `t_i`. Then
`(t_0, ..., t_(j-1), x)` is a `(j+1)`-digit solution in base `b` under both
conventions.

Proof. The `t_i` are the coefficients of `(c r + e)^j` without its constant
term, so `P(b) = (c b + e)^j - e^j + x = y^j - e^j + x = x^x - e^j + x`.
All digits are positive, so `F = sum t_i^(t_i) + x^x` under both
conventions. `P = F` is the definition of `x`.

Corollary 22.7 (proven). For every `k >= 3` there are infinitely many
`k`-digit solutions under `0^0 = 1`, and under `0^0 = 0`.

Proof. Let `j = k - 1`, `c = j` and `e = j u` with `u >= 1`. Every `t_i` is
a positive multiple of `j`, because `t_i` contains `c^(j-i)` with
`j - i >= 1`. So `t_i^(t_i) == 0 (mod j)`, and `e^j == 0`, so `j | x`. Then
`x^x = y^j` with `y = x^(x/j)`, and `j | y` because `j | x`. So
`c = j` divides `y - e`. Finally `x >= t_0^(t_0) = (j^j)^(j^j)`, so
`y >= x^2` and `b = (y - e)/j > x > t_i`. Different `u` give different
digit strings.

For `j = 2` the condition on `x` is that `x` is even (or a square). With
`c = 1` this holds for every odd `e`, and `e = 1` gives the known
`(1,2,6)` in base `6^3 - 1 = 215`. For `j = 3` and `c = 1` it holds for
`e == 2 (mod 3)`.

### 22.3.2 The smallest members (computed)

`r4b_families.py` (`data/r4b_families.txt`) lists the members with
`c <= 6` and `e <= 12` for `k = 3` to 9. It checks `(1,2,6)` and
`(1,6,46666)` with exact integers, and the 58 members whose `x` can be
written down modulo 20 large primes. For the others it decides `j | x` and
`c | y - e` from residues, which suffices by Theorem 22.6. The smallest
member of each length, after `(1,2,6)`:

| `k` | `(c, e)` | digits | `x` | base `b` |
|---:|---|---|---:|---:|
| 3 | (1, 3) | `(1, 6, x)` | 46,666 | `46666^23333 - 3`, about `10^108942` |
| 4 | (1, 2) | `(1, 6, 12, x)` | 8,916,100,494,921 | `x^(x/3) - 2`, about `10^(3.85 * 10^13)` |
| 5 | (2, 2) | `(16, 64, 96, 64, x)` | about `10^190.3` | about `10^(10^192.0)` |
| 6 | (1, 4) | `(1, 20, 160, 640, 1280, x)` | about `10^3977` | about `10^(10^3980)` |
| 7 | (1, 1) | `(1, 6, 15, 20, 15, 6, x)` | about `1.05 * 10^26` | about `10^(10^26.7)` |
| 8 | (3, 1) | `(2187, 5103, 5103, 2835, 945, 189, 21, x)` | about `10^18921` | about `10^(10^18924)` |
| 9 | (2, 2) | `(256, 2048, 7168, 14336, 17920, 14336, 7168, 2048, x)` | about `10^76220` | about `10^(10^76224)` |

The search has 26, 22, 13, 12, 17, 9 and 13 members for `k = 3` to 9. It
leaves out other shapes, such as a leading digit that is not a `j`-th
power. Smaller members of some length can exist outside it.

The 3-digit example is short enough to state in full:
`P = b^2 + 6b + 46666 = (b + 3)^2 - 9 + 46666 = 46666^46666 + 46657`, and
`F = 1 + 6^6 + 46666^46666 = 46666^46666 + 46657`.

### 22.3.3 The 3-digit case and Corollary 8.4

Section 8.2 completes the square: a 3-digit string `(p, q, r)` is a
solution when `(2pb + q)^2 = 4pF + q^2 - 4pr`. Corollary 8.4 bounds `x`
when the dominant term `4p x^x` is a square, through the claim that the
remainder `R` then has `|R| >= 2Y - 1`
(`analysis/square_class_bound.py`). That claim needs `R != 0`, and
`R = 0` can happen.

Proposition 22.8 (proven). Let one digit `x` vary and the other two be
fixed, under `0^0 = 1`. Then `R = 0` only if `x` is the last digit and
`x = p^p + q^q + q^2/(4p)`. If moreover `x` is even, then `p = c^2` is a
square, `q = 2ce`, and the solutions are exactly the members of Theorem 22.6
with `j = 2`.

Proof. If `x` leads, `R = 4x(q^q + r^r - r) + q^2 > 0`, since
`w(d) >= d` with equality only for `d = 1`, and `w(0) - 0 = 1`. If `x` is in
the middle, `R = 4p(p^p + r^r - r) + x^2 > 0`. If `x` is last,
`R = 4p(p^p + q^q - x) + q^2`, which vanishes at the stated `x`. For even
`x`, `p x^x` is a square exactly when `p` is, say `p = c^2`. Then
`q^2/(4c^2)` must be an integer, so `q = 2ce`, and the equation becomes
`(2c^2 b + 2ce)^2 = 4c^2 x^x`, that is `c b + e = x^(x/2)`, the equation of
Theorem 22.6. For `q = 0` (`e = 0`) the digit `x = c^(2c^2) + 1` is prime to
`c`, so `c | x^(x/2)` forces `c = 1`, and `(1, 0, 2)` in base 2 is not
valid.

Computed (`r4b_families.py`, `p, q <= 60`). Every 3-digit solution with
`R = 0` is a member of Theorem 22.6; no odd `x` occurs. With both fixed
digits at most 20, the setting of Corollary 8.4, there are 9:
`(1,2,6)`, `(1,6,x)`, `(1,10,x)`, `(1,14,x)`, `(1,18,x)`, `(4,8,x)`,
`(4,16,x)`, `(9,6,x)` and `(9,18,x)`, with `x` = 6, 46666, 10000000026,
11112006825558066, 39346408075296537575506, 16777476,
18446744073709551888, 387467146 and 39346408075296924995922. So the correct
form of Corollary 8.4 is: the square class with two digits at most 20 holds
the known solutions with `x <= 35` and these 8 more, in bases from
`10^108942` up.

Consequences for other chapters (proven by Corollary 22.7):

- Chapter 3, section 3.5: under `0^0 = 1` the number of `k`-digit
  solutions is infinite for every `k >= 3`, not finite.
- Chapter 7, section 7.2, and the README: "proven when one digit is large
  and lies in its square class" holds only with the 8 additions above.
- Section 11.4: the lists are complete in their ranges, but they are not
  the final answer, and no length is missing everywhere. The 9-digit
  solutions and those with 18, 21, 22, 24, 26 and 28 digits exist, in
  bases far above the searched ones.

## 22.4 A refined heuristic for short solutions

### 22.4.1 A base-by-base calibration (computed)

The offsets of section 19.2 calibrate all bases at once. The far offsets
`D = j * 75600` change `n` by up to `1.5 * 10^7`, which is more than `n`
itself in bases up to 27, and they gave 10 hits. `r4b_spectrum.c` instead
calibrates each base on its own window `b <= |D| <= 0.05 b^(k-1)`. That is
at most 5% of the smallest `k`-digit number. For 5 digits it uses 1.24
million offsets in the class of 0 in bases 13 to 99, with 257 hits. The
estimate of `N_0` for a base is the mean count per offset in the class of
0 modulo `2(b-1)`, which carries the digit-sum identity and the parity
effect. Classes modulo `lcm(2(b-1), q)` with `q = 8, 9, b, b^2` test the
other local factors. The estimate is not a model of the strings: it counts
the true values of `P - F`.

Under `0^0 = 1` (`data/r4b_spectrum.txt`, `data/r4b_spectrum_windows.txt`):

| digits | bases | observed | class `2(b-1)` | other classes | root heuristic (19.2) | P(at least observed) |
|---:|---|---:|---:|---|---:|---:|
| 4 | 13 to 99 | 1 | 1.40 | 0.8 to 2.3 | | 0.75 |
| 4 | 100 to 20,000 | 0 | 0.017 | | | |
| 5 | 13 to 99 | 3 | 0.33 | 0.27 to 0.49 | 0.28 (primes), 0.33 (p-adic) | 0.0047 |
| 5 | 100 to 5,000 | 0 | 0.002 | | | |
| 6 | 3 to 12 | 1 | 1.19 | 0.99 to 1.31 | | |
| 6 | 13 to 99 | 0 | 0.23 | 0.16 to 0.27 | | |
| 7 | 3 to 12 | 1 | 0.99 | 0.81 to 1.03 | | |
| 7 | 13 to 99 | 0 | 0.20 | 0.11 to 0.21 | | |
| 8 | 3 to 12 | 2 | 1.13 | 1.09 to 1.12 | | |
| 8 | 13 to 99 | 0 | 0.23 | 0.22 to 0.25 | | |

The window size changes the 5-digit estimate in bases 13 to 99 between
0.26 and 0.39 for windows from `0.01 b^4` to `0.4 b^4`. The 4-digit
estimates scatter more, 0.77 to 1.40, because the 4-digit windows hold
fewer strings. Below base 13 the windows of 4 and 5 digits are too small,
and the estimates there are not used.

The offsets near 0 are normal once the class is fixed. For 5 digits in
bases 13 to 99, the offsets `0 < |D| <= 300` in the class of 0 hold 7
strings against 6.1 expected. The excess of section 19.2 at small `D`
comes from offsets outside this class, from the self-paying digits of
bases 25, 49, 64 and 81, and from the clusters of section 19.2.

### 22.4.2 Where blocks and families enter

Lemma 22.9 (proven). Under `0^0 = 1`, the polynomial of the 5-digit string
`(t, 1)` is `r P_t(r) - F(t)`, the polynomial of the block `(t, r, 1)`.
Under `0^0 = 0` the same holds for `(t, 0)` and `(t, 1)`.

Proof. `P_(t,1)(r) - F(t, 1) = r P_t(r) + 1 - F(t) - 1`.

So the root heuristic already gives the block route its weight. In bases
13 to 99 that route is the line `(4, 1)` of section 22.2.4: 0.039 of the
0.33. Tails of 2 digits need a 2-digit solution of the base and add below
0.002. Concatenations of two blocks need two coincidences in the same base;
by Heuristic 22.5 they add less still.

The structures that the root heuristic cannot see are the identities:
self-paying digits, the families of Theorem 22.6, and the families
`(1, 0, 0, x)` and `(1, 3, 3, x)` of section 19.2. Each holds with
probability 1 where it holds, and the heuristic gives it a weight near 0.
At `D = 0` under `0^0 = 1` none of them has a 5-digit member in a base up
to 99:

- a self-paying digit (bases 25, 49, 64 and 81 for 5 digits) needs a tail
  that pays for itself while its zeros cost 1, and the complete 5-digit
  list has no solution in these bases;
- the binomial families have bases above `10^108942` (section 22.3.2);
- the families `(1, 0, ..., 0, x)` and `(1, 3, 3, x)` of section 19.2 miss
  `D = 0`.

Refined heuristic 4.2. The expected number of `k`-digit solutions in a
range of bases is the base-by-base class mean of section 22.4.1, which
contains the generic coincidences and the block routes, plus the number of
family members in the range, which is computed exactly. For 5 digits in
bases 13 to 99 under `0^0 = 1` this is `0.33 + 0 = 0.33`.

### 22.4.3 The 5-digit excess (heuristic)

Three solutions against 0.33 is an excess of about 9 times. Under a
Poisson law, P(at least 3) = 0.0047, and 0.0024 to 0.014 over the window
and class choices of section 22.4.1. Ten cells of section 22.4.1 have bases from
13 on (4 to 8 digits, two base ranges). The chance that one of them is as
extreme is 0.015.

The factor 17 of section 19.2 came from the calibration by `D = j L`, with
10 hits and a factor 0.64. The base-by-base calibration, with 257 hits,
gives a factor of 1.19 against the root heuristic with primes and 1.02
against the p-adic version. So the root heuristic was right for these bases,
and the far offsets were a poor calibrator.

Answer. Blocks do not explain the 5-digit count. They are part of the
heuristic, and their share is 0.04 of the 0.33. One of the three solutions
is a block solution, a 0.04 event on its own. The excess stays a
fluctuation at the level of P = 0.005 for the cell and 0.015 after the
choice of the cell. Fresh data cannot come from more bases, since the
5-digit list is complete up to `10^30.9` and the expectation above base 99
is 0.002.

Update (chapter 35). The medium lengths do not share the excess. At
lengths 6 to 12 in bases 7 to 20 the refined model with the top digit
forced matches the window calibration of section 22.4.1 cell by cell
(correlation 0.99 under `0^0 = 1`, 0.94 under `0^0 = 0`), and the totals
fit the census (section 35.2). Two of the four generic short exceptions of
section 10.5 under `0^0 = 1` are this 5-digit excess (section 35.1.4).

### 22.4.4 Completeness and the counts for 6 and 7 digits

Within their ranges the lists are exhaustive computations, so they do not
change (computed). The tail estimates of section 11.4, such as `10^-74`
missing 3-digit solutions, hold for generic strings only (heuristic). By
Corollary 22.7 every length has infinitely many solutions in larger bases.
The smallest known ones beyond the lists are in section 22.3.2. Whether
generic solutions exist between the list bounds and these bases is the
question that the tail estimates answer, and they say no.

For 6 and 7 digits the refined heuristic is the same as the root
heuristic in the searched ranges, because no family member falls there.
The calibrated expectations in bases 3 to 99 are 1.41 (6 digits) and 1.19
(7 digits), against 1 observed each: `(1,5,6,2,6,2)` and
`(1,6,5,6,5,4,7)` in base 9. Bases above 99 add less than 0.001. So the 6-
and 7-digit counts fit, and so does the 8-digit count (1.35 against the 2
solutions in base 11).

## 22.5 Blocks and long solutions

### 22.5.1 Exact splits in the known solutions (computed against heuristic)

By Lemma 22.1, a solution has an exact split at `m` exactly when its tail
of `m` digits pays for itself. The model of chapter 5 treats the digits of
a solution as random, so this happens with probability `T_m(b) / b^m`,
where `T_m(b)` counts the tails of `m` digits, leading zeros allowed, with
`P_u(b) = F(u)`. `r4b_long.py` counts the solutions with at least 4 digits
in bases 2 to 41 and 43 (`data/r4b_long.txt`):

| convention | solutions | `m` | observed | expected |
|---|---:|---:|---:|---:|
| `0^0 = 1` | 59 | 1 | 2 | 3.38 |
| `0^0 = 1` | 59 | 2 | 0 | 0.05 |
| `0^0 = 1` | 59 | 3 | 0 | below 0.01 |
| `0^0 = 0` | 69 | 1 | 8 | 8.58 |
| `0^0 = 0` | 69 | 2 | 6 | 0.84 |
| `0^0 = 0` | 69 | 3 | 2 | 0.10 |

Under `0^0 = 1` the two exact splits are `(3,3,6,6,1)` in base 13 and a
30-digit solution in base 31 that ends in 1. The counts match the model.

Under `0^0 = 0` the excess at `m = 2` is three twin pairs (chapter 2,
Proposition 2.1): the self-paying digit 16 in base 32, `(6,6,5,0,0)` in base
11, and a 14-digit solution in base 15 ending in `0, 0`. Two of the pairs
are chance events, against 0.42 pairs expected, and the third is an
identity. The 32 exact substrings of length at least 2 found inside these
solutions are the same structures seen at several shifts.

### 22.5.2 No correction to the model (heuristic)

A solution of `k` digits with an exact split at `m` is a block of `k - m`
digits with a self-paying tail. Under `0^0 = 1`, `T_1(b) = 1` and
`T_2(b)` is the number of 2-digit solutions of the base, usually 0. So the
block route is a share of about `1/b` of the solutions, 1% in base 100. The
model of chapter 5 counts these solutions with the right weight already,
as Lemma 22.9 says for short strings. Section 22.5.1 above confirms this in
the data. Blocks therefore do not explain the excess of `(b-1)`-digit
solutions in chapter 5 (section 5.5) either: an exact split is a property
of a few low digits, and those digits are random in the model.

The families of Theorem 22.6 do not touch the long solutions. A member with
`k` digits lives in a base above `x^(x/(k-1))/c`, with `x >= (j^j)^(j^j)`
for `c = e = j`, far above `k`.

### 22.5.3 No search shortcut (heuristic)

A search that assembles solutions from blocks has two parts: find the
blocks of `k - m` digits, then append the self-paying tails. The first part
is the search for `(t, 0, ..., 0)` under `0^0 = 0` (Lemma 22.3). It is the
same tree of chapter 10 with `m` digits fixed to 0, about `1.64^b` nodes.
It returns only the share `T_m(b) / b^m` of the solutions, about `1/b`.

The general split of Lemma 22.1 is a meet in the middle: match tops and tails
by `R_m = F(u) - P_u(b)`. The tables hold strings, `b^(k-m)` tops and `b^m`
tails. For `b = 100` and `k = 99` the larger table has at least `100^50`
entries, against `1.64^100`, about `10^21.5`, nodes for the multiset tree.
Strings cost more than multisets, so the split loses.

Answer to question 4. Blocks are a real mechanism for short strings in
the sense of Lemma 22.4, but they are coincidences at the rate of
Heuristic 22.5, already inside both models. They change no prediction for
long solutions and give no faster search. The real new structure is the
binomial family, and it lives only in astronomically large bases.

## Files

- `analysis/r4b_solutions.py`: splits, remainders and inner blocks of the
  short solutions; data `r4b_solutions.txt`.
- `analysis/r4b_blocks.py`: every exact block from `kdigit`; data
  `r4b_blocks.txt`.
- `analysis/r4b_rates.py`: the basic rate of Heuristic 22.5; data
  `r4b_rates.txt`.
- `analysis/r4b_spectrum.c`, `analysis/r4b_spectrum.py`: base-by-base
  spectra of solutions and blocks; data `r4b_spectrum.txt` and
  `r4b_spectrum_windows.txt`. The raw runs go to `fast/target/r4b/`; all
  of them take about 10 minutes on 4 threads.
- `analysis/r4b_families.py`: Theorem 22.6, its members and the 3-digit
  case; data `r4b_families.txt`.
- `analysis/r4b_long.py`: exact splits in the solutions of bases 2 to 43;
  data `r4b_long.txt`.

## New questions

- Classify the identity families of short solutions. Theorem 22.6 covers
  leading digits that are `j`-th powers. Are there others, for example with
  `p x^x` a `j`-th power for `p` not a `j`-th power, or with two large
  digits?
- Is `(1,6,46666)` in base `46666^23333 - 3` the next 3-digit solution
  under `0^0 = 1` after `(1,7,1)` in base 904? The tail estimate says yes for
  generic strings. A proof would need a bound for the Pell-type case of
  section 8.2 up to `10^108942`.
- The base-by-base calibration of section 22.4.1 is cheap. Apply it to the
  4-digit list with larger windows, and to the bulk of long solutions in
  bases 12 to 40, as a check on section 11.1.
