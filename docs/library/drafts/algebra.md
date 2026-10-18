# Draft: the Munchausen polynomial as an algebraic object

This draft answers, fully or in part, questions 1, 2, 4, 8, 11 and 12 of
`questions.md`. Every statement is marked:

- proven: the proof is here;
- computed: an exact computation found it, and the range is stated;
- heuristic: an argument that is not a proof.

Notation follows chapter 12. A digit string is `s = (s_1, ..., s_k)`,
`P_s(r) = s_1 r^(k-1) + ... + s_k`, `F = F(s)` and `Q_s = P_s - F`. The
weight of a digit is `w(x) = x^x`, with `w(0) = 0` or `1`. `M` is the largest
digit of `s`. Scripts are in `analysis/` with names starting `alg_`; their
output is in `analysis/data/alg_*`.

## Summary

| question | what is now known | status |
|---|---|---|
| 1. Aurifeuillian origin of 904 | `log(M/L) = 2 sum psi(j) / (j x^((j-1)/2))` exactly, so `M/L -> e^2`; only x = 3 and 7 split `x^x + 1` into algebraic factors that differ by `x`; a factor pair for every 3-digit solution | proven (Theorems 1, 2), computed (tables) |
| 1. two large digits | no new 3-digit solution with two digits up to 1000 and one up to 30 | computed |
| 12. `b(b+x) = x^x + 1` | no solution for even `x`, odd square `x`, or `x` up to `4 * 10^9` other than 3 and 7; no finite set of primes can finish the proof; any further solution is an abc triple of quality above 1.99999999 | proven, computed |
| 2. reducible `Q_s` | for k = 5, reducible means a rational root or a decomposable `P_s`, for all digits; for k = 6, 7 the other splits occur only for `M <= 4` (searched up to 9 and 6) | proven (k = 5), computed |
| 2. intersective `Q_s` | none for k <= 5; for k = 6 an exact criterion; none found for k = 6, 7 | proven, computed |
| 11. rational roots | for k = 3 a non-integer rational root comes with an integer root of the other sign (Gauss); none above the largest digit for k = 3 (digits <= 80) and k = 4 (<= 44); 17 Munchausen numbers in the rational bases `p/q`, `q > 1`, `p <= 8` | proven, computed |
| 8. partners | for k = 5, a solution in bases `b` and `-c` needs `P_s(r) = G(r^2 + delta r)`; none under `0^0 = 1` with digits <= 300; the only 3-digit non-partner is `(1,1,1)` in base -2 for digits <= 200 | proven, computed |
| 4. Galois groups | for k = 4 the group is `S_3` once `M >= 5`; for k = 5 it is `S_4` once `M >= 6`, unless `P_s` is decomposable; for k = 6 the smaller groups come from `r^5` and the Dickson polynomial `D_5` | proven, computed |

## 1. Aurifeuillian factors and the base-904 solution (question 1)

### 1.1 The equation

The string `(1, x, 1)` is a solution under `0^0 = 1` exactly when

    b (b + x) = x^x + 1.                                          (1)

Under `0^0 = 0` the same equation gives `(1, x, 0)`. The known solutions are
x = 3 (base 4) and x = 7 (base 904). Write `N = x^x + 1`.

The two factors are coprime: a common prime divides `x` and `N`, but
`N == 1 (mod x)`. For odd `x`, `x^x + 1` is the product of `Phi_2d(x)` over
the divisors `d` of `x`.

Proposition 1 (prime x). Let `x` be an odd prime and `Phi = Phi_2x(x)`.
Every solution of (1) has the form `b = (x+1) A`, `b + x = B`, or `b = A`,
`b + x = (x+1) B`, with `A B = Phi` and `A == B == 1 (mod 2x)`.

Proof. Here `N = (x+1) Phi`. A prime `p` dividing `Phi` has
`x^(2x) == 1` and `x^x == -1 (mod p)`, so the order of `x` mod `p` is `2x`
and `p == 1 (mod 2x)`; `p = 2` is excluded because `Phi` is a sum of `x` odd
terms. So every divisor of `Phi` is `1 (mod 2x)`. Since `b` and `b + x` are
coprime, `b = d A` and `b + x = e B` with `d e = x + 1`, `gcd(d, e) = 1`,
`A B = Phi`. Reducing `e B - d A = x` mod `x` gives `e == d (mod x)`. Since
`|e - d| < d e = x + 1`, either `e - d = 0`, impossible for coprime `d, e`
with `d e > 1`, or `e - d = +-x`, which forces `{d, e} = {1, x+1}`.

For x = 7 the pair is `A = 113`, `B = 911`, `904 = 8 * 113`. For x = 3 it is
`A = 1`, `B = 7`, `4 = 4 * 1`. Both are the second form, and both use the
Aurifeuillian factors of `Phi`.

### 1.2 The M/L law

For squarefree `x == 3 (mod 4)` the polynomial `Phi_2x(x t^2)` splits in
`Z[t]` into two factors of degree `phi(x)`. Their values at `t = 1` are the
Aurifeuillian factors `L < M` with `L M = Phi_2x(x)`. For squarefree
`x == 1 (mod 4)` the same holds for `Phi_x(x t^2)`, a factor of `x^x - 1`.
Let `psi` be the quadratic character of `Q(sqrt x)`, that is
`psi(j) = (D / j)` with `D = 4x` or `x` its discriminant.

Theorem 1. For squarefree `x > 1`, `x` odd,

    log(M / L) = 2 * sum over odd j >= 1 with gcd(j, x) = 1 of psi(j) / (j x^((j-1)/2)).

So `log(M/L) = 2 + (2/3) (x/3) / x + O(x^-2)` when `3` does not divide `x`,
`log(M/L) = 2 + O(x^-3)` when it does, and in all cases
`|log(M/L) - 2| <= 2 / (3 (x - 1))`. In particular `M / L -> e^2`.

Proof (case `x == 3 (mod 4)`; the other case is the same with `2x` in place
of `4x`). Let `zeta` be a primitive `4x`-th root of unity. The roots of
`Phi_2x(x t^2)` are `zeta^a / sqrt(x)` for `a` in `(Z/4x)^*`. The Galois
element `sigma_c` sends `sqrt x` to `psi(c) sqrt x`, so it sends the root with
exponent `a` to the root with exponent `c a` or `c a + 2x`. A short check
shows that the set `A = {a : psi(a) = 1}` is stable, closed under
`a -> -a`, and that `a -> a + 2x` maps it to its complement. So
`G(t) = x^(phi(x)/2) prod over a in A of (t - zeta^a / sqrt x)` has rational
coefficients, and `L, M = |G(1)|, |G(-1)|` up to order. Hence

    log(M/L) = sum over a in A of log|1 + zeta^a/sqrt x| - log|1 - zeta^a/sqrt x|
             = 2 Re sum over odd j of S_j / (j x^(j/2)),   S_j = sum over a in A of zeta^(a j).

Now `S_j = (c_4x(j) + sum over a of psi(a) zeta^(a j)) / 2`, with `c_4x` a
Ramanujan sum. For odd `j`, `c_4x(j) = 0`, because `4x / gcd(j, 4x)` is
divisible by 4. The second sum is `psi(j) tau(psi)` with Gauss sum
`tau(psi) = sqrt(4x) = 2 sqrt x` when `gcd(j, x) = 1`, and 0 otherwise,
since `psi` is primitive of conductor `4x`. So `S_j = psi(j) sqrt x`, which
gives the series. The sign of `S_1` shows which factor is `M`. The bound
follows from `sum over odd j >= 3 of 1 / (j x^((j-1)/2)) <= 1 / (3 (x - 1))`.

Computed (`alg_aurifeuille.py`, `data/alg_aurifeuille_300.txt`): for all 132
squarefree odd `x` up to 300, `log(M/L)` agrees with the series to within
`10^-30`. Some values:

| x | x mod 4 | M/L | x (log(M/L) - 2) | (x/3) |
|---:|---:|---:|---:|---:|
| 3 | 3 | 7.0000 | -0.162 | 0 |
| 5 | 1 | 6.4545 | -0.676 | -1 |
| 7 | 3 | 8.0619 | +0.610 | +1 |
| 11 | 3 | 6.9792 | -0.628 | -1 |
| 15 | 3 | 7.3897 | +0.001 | 0 |
| 19 | 3 | 7.6611 | +0.687 | +1 |
| 79 | 3 | 7.4522 | +0.672 | +1 |
| 299 | 3 | 7.3726 | -0.665 | -1 |

The column `x (log(M/L) - 2)` tends to `+-2/3`, with the sign of `(x/3)`, and
to 0 when `3 | x`. This is the observed range 6.98 to 8.06 of question 1.

### 1.3 Why x = 7 works and nothing larger does

Proposition 2. For squarefree `x == 3 (mod 4)`,
`L == 1 - x + x (x + mu(x)) / 2` and `M == 1 + x + x (x + mu(x)) / 2 (mod x^2)`.
So `M - L == 2x (mod x^2)`, and `E = M - (x+1) L - x` is divisible by `x^2`.

Proof. `L = +-prod over a in A of (sqrt x - zeta^a)`. Expand in powers of
`sqrt x`: the coefficient of `(sqrt x)^j` is `+-e_j`, the `j`-th elementary
symmetric function of the `zeta^a`, an integer of `Q(sqrt x)`. Terms with
`j >= 3` are divisible by `x^2`. From the proof of Theorem 1,
`e_1 = S_1 = sqrt x`, and `e_2 = (S_1^2 - S_2) / 2 = (x + mu(x)) / 2`, since
`S_2 = -mu(x)` by the same Ramanujan-sum computation. `L == 1 (mod x)` fixes
the sign. `M` is the same with `-zeta^a`.

So the Aurifeuillian pair `((x+1) L, M)` satisfies (1) to precision `x^2`
for every prime `x == 3 (mod 4)`: `b (b + x) == N (mod x^2)` holds by
structure. A solution needs `E = 0`. By Theorem 1,
`M - (x+1) L = L (M/L - x - 1)`, and `M/L < 8.1 < x + 1` for `x >= 11`, so
`E < 0`. For x = 7, `M/L = 8.06` is within `x/L` of `x + 1 = 8`, and
`E = 0`. For x = 3, `L = 1` and `E = 0`.

Computed: for every squarefree `x == 3 (mod 4)` up to 300 other than 3 and 7,
the largest power of `x` dividing `E` is exactly `x^2`.

So (1,7,1) in base 904 is Aurifeuillian in a precise sense. The identity
gives the factor pair and the congruence mod `x^2`. What remains is the
numerical coincidence `e^2 + 0.67/7 = 8.06`, close to `x + 1 = 8`.

### 1.4 No other algebraic factor pair

Call a factor of `x^x + 1` algebraic if it is a product of values at `t = y`
of irreducible factors in `Z[t]` of `Phi_2d(s t^2)`, where `x = s y^2`, `s`
squarefree and `d | x`. These are the cyclotomic values `Phi_2d(x)` and the
Aurifeuillian halves.

Theorem 2. Let `x >= 3` be odd. If `b (b + x) = x^x + 1` and `b` is a product
of algebraic factors, then `x = 3` or `x = 7`.

Proof. Write `log Phi_2d(x) = phi(d) log x + eps_d`. Then
`eps_d = -sum over j of c_2d(j) / (j x^j)`, and `|c_2d(j)| <= j` gives
`|eps_d| <= 1 / (x - 1)`. An Aurifeuillian pair `L_d, M_d` has
`log L_d, log M_d = (phi(d) log x + eps_d -+ rho_d) / 2` with
`rho_d = log(M_d / L_d)`. A solution has `|log((N/b) / b)| = log(1 + x/b)`,
below `x^(2 - x/2)`. On the other hand
`log((N/b)/b) = D log x + (sum of +-eps_d) + (sum of +-rho_d over pairs split
between b and N/b)`, where `D` is the difference of the degrees. `D` is odd,
because the degrees add up to `x`.

- No pair split: `|D log x| <= tau(x)/(x - 1) + x^(2 - x/2)`, false for all
  `x >= 3` since `tau(x) <= x - 1`.
- `y = 1`, so one pair, `rho = 2 + O(1/x)` by Theorem 1:
  `|D log x +- rho| <= tau(x)/(x-1) + x^(2-x/2)`. For `x >= 11`,
  `log x - 2 - 2/(3(x-1)) > tau(x)/(x-1) + x^(2-x/2)`, which excludes
  `|D| = 1`, and `|D| >= 3` is excluded since `3 log x > 2.2 + 1`. Below 11
  only x = 3 and 7 are squarefree and `3 (mod 4)`.
- `y >= 3`: the same Gauss-sum argument, with the imprimitive character
  mod `4d`, gives `|rho_d| <= 2/y + 1/sqrt x` when `d / s` is squarefree and
  `|rho_d| <= 1/sqrt x` otherwise, plus a total of at most `0.7/sqrt x` from
  the terms `j >= 3`. There are at most `2^omega(y)` pairs of the first kind
  and `tau(y^2) <= y` pairs in all, so the sum of the `|rho_d|` is at most
  `4/3 + 1/sqrt 3 + 0.14 < 2.1`. The `eps` terms add at most
  `tau(x)/(x-1) <= 0.41`. Since `|D| >= 1` and `log x >= log 27 = 3.29`,
  the total cannot be near 0.

Computed (`alg_algebraic171.py`, `data/alg_algebraic171_201.txt`): for every
odd `x` up to 201, the best algebraic split has `|log(N/b^2)|` equal to
0.0077 for x = 7 and at least 0.54 for every `x >= 11` (x = 11 is the
closest). When no Aurifeuillian pair exists it is at least `log x - 0.72`.

### 1.5 The factor pair of every 3-digit solution

A 3-digit solution `(p, q, r)` in base `b` gives the factor pair
`F - r = b (p b + q)`. Under `0^0 = 1` (and the twins under `0^0 = 0`):

| solution | `F - r` | pair `(b, pb+q)` | identity |
|---|---|---|---|
| `(1,3,1)`, base 4 | `3^3 + 1 = 28` | `(4, 7)` | cyclotomic and Aurifeuillian: `(x+1) L`, `M` with `L = 1` |
| `(1,7,1)`, base 904 | `7^7 + 1` | `(8 * 113, 911)` | Aurifeuillian `((x+1) L, M)` (sections 1.2-1.3) |
| `(1,2,6)`, base 215 | `6^6 - 1` | `(6^3 - 1, 6^3 + 1)` | difference of squares; needs `2^2 + 1 - 6 = -1` |
| `(5,1,3)`, base 25 | `5^5 + 5^2` | `(5^2, 5^3 + 1)` | square class: `b = x^((x-1)/2)`; needs `3^3 - 3 + 1 = 5^2` |
| `(1,0,3)`, base 5, `0^0 = 0` | `3^3 - 2 = 25` | `(5, 5)` | the same coincidence `3^3 - 2 = 5^2` |
| `(3,1,3)`, base 4 | `2 (3^3 - 1) = 52` | `(4, 13)` | `4 = 2 Phi_1(3)`, `13 = Phi_3(3)`; needs `x - 1 = 2` |
| `(6,1,5)`, base 91 | `6^6 + 5^5 - 4 = 7 * 13 * 547` | `(91, 547)` | none; `91 = 6^3 - 5^3`, but `91 | F - r` needs `6 * 5^5 == 4 (mod 91)`, a coincidence |

So five of the six have an algebraic factor pair, each completed by one small
coincidence between powers. Only `(6,1,5)` in base 91 has none. The 4-digit
solutions have no such structure: 3435 gives `3430 = 10 * 7^3`, a cube by
chance, and `(6,5,3,4)` in base 20 gives `50060 = 20 * 2503`.

### 1.6 Two large digits

An algebraic factorization of `F - r` needs `F - r` to be a sum of two
powers with a common odd exponent, or a constant plus a power. For a 3-digit
string with two large digits `u, v` this forces the shape `(u, v, 1)` with
`F - r = u^u + v^v` (or `(u, v, 0)` under `0^0 = 0`). Since every such
identity still has to land on the exact quadratic, the clean test is
exhaustive: solve `p b^2 + q b + r = F` for all strings with two digits up
to `D` and the third up to `S`.

Computed (`alg_twolarge.py`, `data/alg_twolarge_1000_30.txt`, D = 1000,
S = 30, both conventions, 184 million strings, 4.5 minutes): under
`0^0 = 1` the solutions are exactly the six of chapter 3. Under `0^0 = 0`
they are those, the self-paying families `(x,0,0)`, `(x,0,1)`, and the swaps
`(3,0,27)` in base `3^40` and `(4,0,256)` in base `2^1024`. These bases reach
`10^1500`.

Answer (question 1). The pair `(8 * 113, 911)` is the Aurifeuillian pair
`((x+1) L, M)` of `7^7 + 1`. Theorem 1 gives the exact law
`log(M/L) = 2 sum psi(j) / (j x^((j-1)/2))`, so `M/L = e^2 (1 + 2(x/3)/(3x) + ...)`.
The pair always satisfies (1) modulo `x^2` (Proposition 2). It satisfies (1)
exactly only when `M/L` is within about `x/L` of `x + 1`, which happens for
x = 3 and 7 and never again. By Theorem 2 no other algebraic factor pair of
`x^x + 1` solves (1). Among the six 3-digit solutions, five have an
algebraic factor pair; `(6,1,5)` in base 91 is the counterexample candidate
and indeed has none.

## 2. The equation b(b+x) = x^x + 1 (question 12)

Write `f(x) = 4 x^x + x^2 + 4`. Then (1) holds exactly when `f(x)` is the
square of `U = 2b + x`.

### 2.1 What is proven

Proposition 3. (1) has no solution with `x` even or with `x` an odd square.

Proof. In both cases `x^x = Y^2` is a square. Then
`(2Y)^2 < f(x) < (2Y + 1)^2`, because `0 < x^2 + 4 < 4Y + 1` for `x >= 2`.

So only odd non-squares remain. For odd `x`, `f(x) == 1 (mod 8)`, and
`f(x) == 4 (mod p)` for `p | x`, so `f` is a square at 2 and at the primes
of `x`. Proposition 1 is the factor form for prime `x`. Three more
reformulations follow.

Proposition 4 (x-adic form). Let `x` be an odd prime and `beta` the root of
`t^2 + x t - 1 = 0` in `Z_x` with `beta == 1 (mod x)`. Let `R` be the residue
of `beta` mod `x^x` in `[0, x^x)`. Then (1) has a solution exactly when
`R < x^(x/2)`, and then `b = R`.

Proof. A solution has `b == 1 (mod x)` (Proposition 1: `A == 1`), so
`b == beta (mod x^x)` by Hensel, and `b < x^(x/2)`. Conversely, if
`R < x^(x/2)`, then `R (R + x) - 1` is a positive multiple of `x^x` below
`2 x^x`, so it equals `x^x`.

So a solution means that the top `(x-1)/2` base-`x` digits of `beta` mod
`x^x` all vanish. For x = 7, `R = 904` and `7^3.5 = 907.5`. For the other
primes up to 59, `R` lies between `x^(x - 0.8)` and `x^x`, as a random
residue would (`alg_abc171.py`). Heuristically
this happens with probability `x^(-x/2)`.

Proposition 5 (unit form). Let `x == 3 (mod 4)` be squarefree with `x^2 + 4`
prime, and `epsilon` the fundamental unit of `Z[sqrt x]`. A solution of (1)
gives `(2b + x) + 2 x^((x-1)/2) sqrt x = +-(x + 2 +- 2 sqrt x) epsilon^k` for
some integer `k`.

Proof. Both sides have norm `x^2 + 4 = p`. The prime `p` splits, and the two
elements `x + 2 +- 2 sqrt x` generate the two primes above `p`; they are
distinct because their gcd divides `16 x`, which is prime to `p`. So the
left side is one of them times a unit of norm 1.

For x = 3: `11 + 6 sqrt 3 = (5 - 2 sqrt 3)(2 + sqrt 3)^2`. For x = 7:
`1815 + 686 sqrt 7 = (9 + 2 sqrt 7)(8 + 3 sqrt 7)^2`. Both have `k = 2`. So
(1) asks whether the `sqrt x`-coordinate of a binary recurrence
`gamma epsilon^k` is ever `2 x^((x-1)/2)`. For fixed `x` this is an S-unit
equation in a recurrence, with finitely many solutions (Petho, Shorey and
Tijdeman). The difficulty is that the field changes with `x`.

Theorem 2 (section 1.4) is a fourth partial result: no solution comes from
an algebraic factorization, except x = 3 and 7.

### 2.2 Local tests cannot finish the proof

Proposition 6. (a) The primes 3 and 5 never exclude an odd `x`.
(b) For every finite set `S` of primes, the `x == 1 (mod lcm(p - 1 : p in S))`
pass the test at every `p` in `S`. They have positive density. So no finite
set of congruences proves that (1) has no solution with `x > 7`.

Proof. (b) If `x == 1 (mod p - 1)` and `p` does not divide `x`, then
`x^x == x (mod p)`, so `f(x) == (x + 2)^2`. If `p | x`, `f(x) == 4`. (a) For
odd `x`, `x - 1` is even and `x^2 == +-1 (mod 3)` and `(mod 5)`. So
`x^(x-1) == +-1`, and `f(x) == (x + 2)^2` or `(x - 2)^2`.

The reason is the trivial solution `b = 1` of `b (b + x) = x^n + 1` with
n = 1. At the primes with `x == 1 (mod p-1)`, `x^x` looks like `x^1`. Any
proof must use infinitely many primes, or global information.

### 2.3 Computations

Sieve (`alg_sieve171.c`, `data/alg_sieve171_4e9.txt`). For every `x` from 2
to `4 * 10^9`, the program looks for an odd prime `p < 65536` with `f(x)` a
nonresidue mod `p`. Every `x` other than 3 and 7 has one, and a prime up to
229 always suffices. So (1) has no further solution with `x <= 4 * 10^9`, that
is with `b` up to about `10^(1.9 * 10^10)` (computed, about 18 minutes). The
previous bound was x = 2500.

| odd primes used | share of `x <= 10^9` not yet excluded |
|---:|---:|
| 3, 5 | 0.900 (only the even `x` are gone) |
| up to 13 | 0.352 |
| up to 31 | 0.048 |
| up to 73 | 0.00071 |
| up to 179 | 3.2e-8 |

Exact densities (`alg_density171.py`). For the 31 primes `p` with
`p - 1 | 20160`, from 11 to 20161, the residues mod `p` are independent of
`x mod 20160`. The exact share of odd `x` that pass all 31 tests is 0.00029.
So all but a density `1.5 * 10^-4` of all integers `x` are excluded by
congruences (proven). The share flattens near `1 / 10080` because of the
class `x == 1 (mod 20160)` of Proposition 6.

Other exponents (`alg_exponents171.py`, `data/alg_exponents171.txt`). The
equation `b (b + x) = x^n + 1` for `x <= 3000`, `2 <= n <= 1500` has these
solutions: `n = 2` with `x` a Fibonacci number `F_2k` (`5x^2 + 4` a square);
`n = 3` with `x` in {3, 5, 8, 64, 119}; and `(x, n) = (7, 7)`. For `n = 3`
this list is complete for all `x`: the curve `Y^2 = X^3 + X^2 + 64`
(`X = 4x`) has rank 2 and exactly 10 integral points (Sage). So `(7, 7)` is
the only solution with `n >= 4` in the box. The diagonal `n = x` meets the
sporadic set once.

### 2.4 A reduction to the abc conjecture

Proposition 7. A solution of (1) with odd `x` gives the abc triple
`(x^2 + 4) + 4 x^x = (2b + x)^2`. Its quality is at least
`log(4x^x) / log(2x (x^2 + 4)(2 x^(x/2) + 1))`, which exceeds 1.6299 for
`x >= 29` and tends to 2.

Proof. The terms are coprime because `x` is odd and `gcd(x^2 + 4, x) = 1`.
The radical is at most `2 x (x^2 + 4) U` with `U < 2 x^(x/2) + 1`.

The best known triple, `2 + 3^10 * 109 = 23^5` (Reyssat), has quality 1.6299.
With the sieve, any further solution has `x > 4 * 10^9` and quality above
`2 - 10^-8`. So:

- the abc conjecture implies that (1) has finitely many solutions;
- even the weak form "`c < K rad(abc)^(2 - delta)` for some `delta > 0`"
  suffices, and an effective version would finish the proof with the sieve.

This is the same status as Brocard's problem `n! + 1 = m^2` (abc gives
finiteness, Overholt 1993), but (1) needs much less than abc.

### 2.5 What blocks a full proof

1. The equation is a Pell equation `U^2 - 4x Y^2 = x^2 + 4` with the extra
   condition `Y = x^((x-1)/2)`. For fixed `x` it is an S-unit question in a
   binary recurrence (Proposition 5), solved by Baker's method. The field
   `Q(sqrt x)`, its unit and the recurrence all change with `x`. No method
   handles a family of recurrences whose fields vary.
2. Congruences fail for a structural reason (Proposition 6).
3. The factor form (Proposition 1) asks for a divisor of `Phi_2x(x)` in a
   window of relative width `x^(1 - x/2)`. Results on divisors of cyclotomic
   values (Zsigmondy, Bilu-Hanrot-Voutier) control which primes occur, not
   where the divisors lie. Theorem 2 handles the divisors that come from
   identities; the others behave like random numbers.
4. The x-adic form (Proposition 4) asks that `(x-1)/2` consecutive digits of
   an algebraic `x`-adic number vanish. Statements of this kind are open
   even for a fixed base.

The cleanest known open problem that implies the result is the weak abc
inequality of section 2.4.

Answer (question 12). Not solved. Proven: no solution for even `x`, for odd
square `x`, for `x` in residue classes covering all but density
`1.5 * 10^-4` of the integers, and none from an algebraic factorization. For
prime `x` the problem is a divisor of `Phi_2x(x)` near
`sqrt(Phi / (x+1))`. Computed: none for `x <= 4 * 10^9` except 3 and 7. No
finite set of congruences can finish the proof (Proposition 6). Any further
solution would be an abc triple of quality above 1.99999999, so a weak abc
inequality implies the result.

## 3. Reducible Q_s and intersective polynomials (question 2)

### 3.1 Degree at most 4

Proposition 8. If `k <= 5` and `Q_s` has a root modulo all but finitely many
primes, then `Q_s` has a rational root. So no `Q_s` with `k <= 5` is
intersective without a rational root, and the local test is complete for
`k <= 5`.

Proof. Without a rational root, `Q_s` is irreducible or, for k = 5, a
product of two irreducible quadratics with fields `Q(sqrt D_1)` and
`Q(sqrt D_2)`. The irreducible case is Proposition 12.1. If the two fields
are equal, the primes inert in it (density 1/2) give no root. If they
differ, the primes inert in both (density 1/4) give no root.

Proposition 9 (k = 6). `Q_s` of degree 5 has a root modulo almost every
prime but no rational root exactly when `Q_s = g h` with `g` an irreducible
quadratic, `h` an irreducible cubic with group `S_3`, and
`Q(sqrt disc g) = Q(sqrt disc h)`.

Proof. The only split without a linear factor is 2 + 3. An element
`(tau, pi)` of the Galois group fixes no root when `tau != 1` and `pi` is a
3-cycle. If `h` has group `A_3`, the group is `C_2 x C_3` and contains such
an element. If `h` has group `S_3`, the group is `C_2 x S_3`, which contains
one, or the graph of the sign map, which does not; the latter means equal
quadratic fields. Chebotarev turns this into primes.

The classic `(x^3 - 19)(x^2 + x + 1)` is of this shape, so the question for
k = 6 is real.

### 3.2 Two quadratic factors, k = 5

Let `a = s_2/s_1`, `b = s_3/s_1`, `c = s_4/s_1`, `d = s_5/s_1`,
`B = b - a^2/4`, `q = c - ab/2 + a^3/8` and `C = a^2/16 - B/2`. Then
`q = 0` exactly when `P_s(r)` is a polynomial in `(r + a/4)^2`, that is,
when `P_s` is decomposable.

Theorem 3. If `Q_s` (k = 5) is a product of two quadratics over `Q` and
`q != 0`, then
`F <= s_1 (d - B^2/4 - aq/4 + s_1^2 q^2 + max(C, 0)^2)`. This bound is below
`F(s)` for every string with `M >= 3`.

Proof. Write `Q_s / s_1 = (r^2 + beta_1 r + gamma_1)(r^2 + beta_2 r + gamma_2)`
and `beta_1,2 = a/2 +- tau`. Comparing coefficients gives
`gamma_1 + gamma_2 = B + tau^2` and
`tau (gamma_1 - gamma_2) = a tau^2 / 2 - q`. If `tau = 0` then `q = 0`.
Otherwise, from `gamma_1 gamma_2 = d - F/s_1`,

    F / s_1 = d - B^2/4 - aq/4 + q^2 / (4 tau^2) + C tau^2 - tau^4 / 4.

By Gauss's lemma `2 s_1 tau` is an integer, so `q^2/(4 tau^2) <= s_1^2 q^2`,
and `C u - u^2/4 <= C^2`. For `M >= 7` each term is at most a power of `M`:
`s_1 |q| <= M + M^2/2 + M^3/8 <= M^3/4`, so the bound is at most
`M^7/8 < M^M <= F`. For `3 <= M <= 12` an exact check of all strings
(`alg_k5bound.py`) gives a largest ratio bound/F of 0.84.

Corollary. For k = 5 and every string with `M >= 3`, `Q_s` is reducible
exactly when it has a rational root, or when `P_s = s_1 G((r + a/4)^2)` and
either `G(u) - F/s_1` has rational roots or, for a root `theta`,
`theta + a^2/16` is a square in `Q(theta)` (Capelli). With the computation
below, this holds for all strings.

Computed (`alg_reducible.py`, `data/alg_reducible_k5_9.txt`, digits <= 9,
both conventions, 180,000 strings): 59 and 87 reducible `Q_s` under
`0^0 = 1` and `0^0 = 0`. Each has a rational root or a decomposable `P_s`.
Example: `(4,4,3,1,5)` gives `(2r^2 + r - 60)(2r^2 + r + 61)`, from
`P = u^2 + u + 5`, `u = 2r^2 + r`.

The third mechanism of the conjecture in question 2, `Q_s` close to
`s_1 (r^4 - Z^4)`, is a special case: `r^4` is decomposable.

### 3.3 k = 6 and k = 7

Computed (`data/alg_reducible_k6_9.txt`, `data/alg_reducible_k7_6.txt`):

| k | digits up to | strings | rational root | decomposable `P_s` | other splits | largest digit of the other splits | largest `F` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 6 | 9 | 1.8 million | 91 | 0 | 22 (all 2+3) | 4 | 796 |
| 7 | 6 | 1.4 million | 678 | 47 | 37 (36 are 2+4, one 3+3) | 4 | 372 |

Every split not explained by a rational root or a decomposition has
`M <= 4`, although digits up to 9 and 6 were searched. Example:
`(3,3,2,4,0,4)` gives `(r^2 + 5r + 9)(3r^3 - 12r^2 + 35r - 63)` with
`F = 571`. Their small factors have roots of size about 3, which is
possible only while `F` is small, since for large `F` all roots have size
about `(F/s_1)^(1/(k-1))`. None of them has a root modulo every prime below
3000, so none is intersective. For k = 6 the degree is prime, so `P_s` is
always indecomposable, and no 2+3 split has `M >= 5`.

The method of Theorem 3 does not extend. For k = 6 the same elimination
gives a curve of genus 1 instead of a rational one, and the integrality step
needs the root sum `Z cos(2 pi/5) + ...` to be near a rational with bounded
denominator, which is a Diophantine approximation question.

Answer (question 2). For k = 5 the conjecture is a theorem: reducibility
comes only from a rational root or a decomposition `P_s = G(h)`, and the
near-binomial case is part of the decomposition case. No `Q_s` with `k <= 5`
is intersective without a rational root (Proposition 8). For k = 6 an
intersective `Q_s` needs a 2+3 split with equal quadratic fields
(Proposition 9); none exists with digits up to 9. Conjecture, refined: for
every `k` there is a polynomial bound `F <= C_k M^(c_k)` outside which every
factorization of `Q_s` without a linear factor comes from a decomposition of
`P_s`. If true, no `Q_s` with large digits is intersective unless it is
decomposable.

## 4. Galois groups (question 4)

Theorem 4. (a) For k = 4 and `M >= 5`, every irreducible `Q_s` has group
`S_3`. (b) For k = 5 and `M >= 6`, every irreducible `Q_s` has group `S_4`,
unless `P_s` is decomposable, and then the group lies in `D_4`.

Proof. On `|r| <= M + 1`, `|P_s(r)| < (M+1)^k`, and outside that
interval `P_s` has no critical point (Cauchy's bound for `P_s'`). If
`F > (M + 1)^k`, which holds for `M >= 5` (k = 4) and `M >= 6` (k = 5),
`Q_s` has exactly one real root (k = 4) or two (k = 5). (a) `A_3` needs three
real roots. (b) Complex conjugation is a transposition, so the group is
`S_4` or `D_4`. `D_4` means a rational root `y` of the resolvent cubic. With
`t = F/s_1` the resolvent equation is linear in `t`:

    t = (-y^2 + a^2 y / 4 + a^2 B / 4 - ac + 4d) / 4 + q^2 / (4 (y - B)).

`s_1^2 y` is an integer and `4 s_1^2 B` is an integer, so if `q != 0`,
`t <= (a^4/64 + a^2 B/4 - ac + 4d)/4 + s_1^2 q^2`. This is below `F/s_1` for
all `M >= 3` (`alg_k5bound.py`, analytic for `M >= 7`). So `q = 0`.

So for k = 5 the "integral points on `y^2 = cubic(N)`" of question 4 do not
arise for large digits: the smaller groups need a rational point on a
rational curve with two poles, and the pole at `y = B` bounds `F`.

Computed (`alg_galois.py`): k = 4, digits <= 10: all 26,580 irreducible
`Q_s` have group `S_3`. k = 5, digits <= 8: 1,967 have group `D_4`, all with
decomposable `P_s`, and the other 102,865 have `S_4`. k = 6, digits <= 5:
81 have group `F_20` (order 20), the rest `S_5`. The 81 are `s_1 r^5 + s_6`,
the cyclic case of Ritt, and `(1,0,5,0,5,x)` and `(5,0,5,0,1,x)`, which are
Dickson polynomials: `r^5 + 5r^3 + 5r = D_5(r, -1)` and
`5r^5 + 5r^3 + r = D_5(sqrt5 r, -1) / (5 sqrt5)`. These are exactly the two
exceptional families of Ritt's and Fried's theory.

Answer (question 4). For k = 4 and k = 5 the smaller groups are classified:
none for k = 4 once `M >= 5`; for k = 5 only `D_4` and its subgroups, and
only for decomposable `P_s`, once `M >= 6`. Computation shows the same for
all smaller digits. For k = 6 the only smaller groups up to digit 5 come
from `r^5` and `D_5`.

## 5. Rational roots and rational bases (question 11)

Proposition 10 (k = 3). If `Q_s` (k = 3) has a rational root `p/q` in lowest
terms, its other root `p'/q'` is rational with `q q' = s_1`, and the roots
have opposite signs.

Proof. Gauss's lemma gives `Q_s = (q r - p)(q' r - p')` over `Z`. The product
of the roots is `(s_3 - F)/s_1 < 0`.

So a root `p/q > M` with `q = s_1 > 1` comes with a negative integer root:
a negative-base solution (if it exceeds `M`) that is not a partner in the
sense of Proposition 12.3. Both roots are non-integers only when
`s_1 = q q'` with `q, q' > 1`.

Computed (`alg_rational.py`): for k = 3 with digits <= 80 and k = 4 with
digits <= 44, no `Q_s` has a non-integer rational root above `M`. For k = 3
the non-integer rational roots are the negative partners of the positive
solutions with `s_1` not dividing `s_2`: `-13/3` for `(3,1,3)`, `-126/5` for
`(5,1,3)`, `-547/6` for `(6,1,5)`, two improper ones, and `3/2` for
`(2,1,0)` (`2r^2 + r - 6 = (r + 2)(2r - 3)`). For k = 4 there are none at all.

Rational base systems. In the number system of Akiyama, Frougny and
Sakarovitch with base `p/q`, every `N >= 1` has a unique expansion
`N = sum a_i / q (p/q)^i`, digits `0 <= a_i < p`. Call `N` Munchausen if
`N = sum w(a_i)`. Since `F <= (length) (p-1)^(p-1)`, each base has finitely
many, and the search is finite (`alg_afs.c`, `data/alg_afs_8.txt`, all 49
verified with exact fractions).

Proposition 11. For `q > 1` there are no twins: changing the last digit by 1
changes the value by `1/q`, not an integer.

Under `0^0 = 1`, the bases `p/q` with `q > 1` and `p <= 8` have 17 Munchausen
numbers:

| base | `0^0 = 1` | `0^0 = 0` |
|---|---|---|
| 3/2 | 8 = `(2,1,0,1,1)`, 15 = `(2,1,2,0,2,0)` | 9 |
| 4/3 | none | 124 |
| 5/2 | 60, 546 | none |
| 5/3 | 583 | 604 |
| 6/5 | 15227, 33827 | 34331 |
| 7/2, 7/3, 7/4 | 96983; 146841; 103858 | 7/3: 6847, 10224, 146841 |
| 7/5 | 299637, 346791 | 165890, 212851 |
| 7/6 | 741782, 744115 | none |
| 8/3 | none | 4945213 |
| 8/5 | 2665246, 6011678 | 5094699 |
| 8/7 | 11673299 | 11071801 |

Check of the first: `1/2 + (1/2)(3/2) + (1/2)(3/2)^3 + (3/2)^4 = 8 = 4 + 1 + 1 + 1 + 1`.

Answer (question 11). Rational roots of the polynomial are rarer than
integer roots, not more common. By Gauss's lemma their denominators split
`s_1`, and for k = 3 every one found is the partner of an integer root. None
lies above `M` for k = 3 (digits <= 80) or k = 4 (digits <= 44). The
meaningful version is the AFS system, where Munchausen numbers exist, are
finite in each base, and have no twins.

## 6. Partners (question 8)

### 6.1 Three digits

By Proposition 10 the two roots of a quadratic `Q_s` are a solution in base
`b` and a non-partner negative-base solution only if `s_1` does not divide
`s_2` or the partner root is at most `M`.

Computed (`alg_twolarge.py`): all 3-digit strings with digits up to 200, and
those with two digits up to 1000 and one up to 30. The negative-base
solutions under `0^0 = 1` are `(1,1,1)` in base -2, `(1,3,1)` in base -7,
`(1,2,6)` in base -217 and `(1,7,1)` in base -911. Only `(1,1,1)` is not a
partner. Under `0^0 = 0` the only other non-partner is its twin `(1,1,0)`.
The rest, `(1,0,3)` in base -5 and the even polynomials `(x,0,0)`, `(x,0,1)`
and `(3,0,27)`, are partners with `delta = 0`.

### 6.2 Five digits and more

Theorem 5. Let `k` be odd and `s` a solution in base `b` and in base `-c`.
Then `c >= b` and `delta = c - b < 4M/s_1`. If moreover
`P_s(r) != P_s(-r - delta)` as polynomials, then
`b <= 1 + 2 k M (1 + delta)^(k-1)`. For k = 5 this forces `M <= 30`.
If `P_s(r) = P_s(-r - delta)`, then `P_s = G(r^2 + delta r)`, and every
solution in base `b` is also one in base `-(b + delta)`.

Proof. `P_s(-c)` is at most its even part, which is below `P_s(b)` if
`c < b`. If `delta >= 4M/s_1`, then
`P_s(-c) >= c^(k-2) (s_1 c - 2M) > b^(k-2) (s_1 b + 2M) >= P_s(b)`. If
`R(r) = P_s(r) - P_s(-r - delta)` is not zero, it has integer coefficients
of size at most `2 k M (1 + delta)^(k-1)`, and `b` is a root of it. For
k = 5, `F = P_s(b) <= 5 M b^4` against `F >= M^M` gives `M <= 30`. If
`R = 0`, `P_s` is symmetric about `-delta/2`. For k = 5 the condition reads
`s_2 = 2 delta s_1` and `s_4 = delta (s_3 - delta^2 s_1)`.

Computed. For `M <= 80` the 5-digit lists of chapter 11 are complete. Under
`0^0 = 1` none of the six solutions has a negative-base root. Under
`0^0 = 0` the strings with both are `(x,0,0,0,0)`, `(x,0,0,0,1)` with
`x^(x-1)` a fourth power, and `(3,0,0,0,27)` in bases `+-3^20`, all with
`delta = 0`. The decomposable family (`alg_partners5.py`, digits <= 300,
83 million strings) has no solution under `0^0 = 1`; under `0^0 = 0` only
these.

Answer (question 8). For three digits, `(1,1,1)` in base -2 is the only
non-partner up to digit 200 (two digits up to 1000). For five digits, a
string that works in a base `b` and a base `-c` must have
`P_s(r) = G(r^2 + delta r)`, apart from strings with digits up to 30, which
the complete lists exclude. Under `0^0 = 0` the even polynomials give
infinitely many such strings. Under `0^0 = 1` none exists with digits up to
300, and the decomposable family needs two square conditions at once, so I
expect none at all (heuristic).

## 7. New questions

1. Is there a closed form for `sum psi(j) z^j / j` at `z = x^(-1/2)` that
   gives `M/L` directly, and does Theorem 1 extend to the Aurifeuillian
   factors of `a^n +- b^n` in general (Brent's and Stevenhagen's
   formulas)?
2. The diagonal `n = x` of `b(b+x) = x^n + 1` meets the sporadic set only at
   (7, 7) for `n >= 4`. Is the set of `(x, n)` with `n >= 4` finite?
   For `n = 5` the curve `U^2 = 4x^5 + x^2 + 4` has genus 2, so this is
   decidable for each `n`.
3. Theorem 3 for every `k`: is every split of `Q_s` without a linear factor
   decomposable once `F > C_k M^(c_k)`? The k = 6 case reduces to
   approximating `cos(2 pi/5) Z` by rationals with bounded denominator.
4. Why do 3-digit negative bases have no non-partner solution, while
   positive bases have three with `s_1` not dividing `s_2`?

## Scripts and data

| script | output |
|---|---|
| `alg_aurifeuille.py` | `data/alg_aurifeuille_300.txt`: `M/L`, the series, Proposition 2 |
| `alg_algebraic171.py` | `data/alg_algebraic171_201.txt`: best algebraic split of `x^x + 1` |
| `alg_twolarge.py` | `data/alg_twolarge_1000_30.txt`, `data/alg_3digit_all_200.txt` |
| `alg_sieve171.c` | `data/alg_sieve171_4e9.txt` |
| `alg_local171.py`, `alg_density171.py` | local densities, `data/alg_density171.txt` |
| `alg_exponents171.py` | `data/alg_exponents171.txt` |
| `alg_abc171.py` | `data/alg_abc171.txt`: abc quality and the x-adic residues |
| `alg_reducible.py` | `data/alg_reducible_k5_9.txt`, `_k6_9.txt`, `_k7_6.txt` |
| `alg_k5bound.py` | the bounds of Theorems 3 and 4 against `F` |
| `alg_galois.py` | `data/alg_galois_k4_10.txt`, `_k5_8.txt`, `_k6_5.txt` |
| `alg_rational.py` | `data/alg_rational_k3_80.txt`, `_k4_44.txt` |
| `alg_afs.c` | `data/alg_afs_8.txt` |
| `alg_partners5.py` | `data/alg_partners5_300.txt` |
