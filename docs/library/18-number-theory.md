# 18. The equation b(b+x) = x^n + 1 and other number theory

This chapter answers, fully or in part, questions 32, 36, 39, 34, 31 and 40 of
`questions.md`, in that order. It also settles a large part of question 12.
Every statement is marked:

- proven: the proof is here;
- cited: a published theorem, used without proof;
- computed: an exact computation found it, and the range is stated;
- heuristic: an argument that is not a proof.

Scripts are in `analysis/` with names starting `r2nt_`. Their output is in
`analysis/data/r2nt_*`.

## Summary

| question | what is now known | status |
|---|---|---|
| 32, prime powers | for `x` a prime power, the solutions of `b(b+x) = x^n + 1` with `n >= 2` are `(x, n) = (3,2), (8,2), (3,3), (5,3), (8,3), (64,3), (7,7)` | proven (Theorem 18.8) |
| 32, general | every other solution with `n >= 4` has `n` odd, `x` not a square, and either `x == 0 (mod 8)` or `x` odd with two distinct prime factors and a "mixed" ideal; then `n < 6.4 * 10^4 d log x` when `d < n`, with `d` the order of an ideal class | proven, computed constant |
| 32, `n = 4, 6` | no solution | proven |
| 32, small `x` | for odd `x <= 1001`, `(7, 7)` is the only solution with `n >= 4`, for every `n` | computed (Theorem 18.12) |
| 32, `n = 5` | no solution with `x <= 10^10`; the curve has genus 2 and Jacobian of analytic rank 3, so Chabauty methods do not apply | computed |
| 32, finiteness | follows from abc, and from the weak form with exponent `2 - delta` | proven (conditional) |
| 12, `n = x` | a solution with `x > 7` needs `x > 4 * 10^9` odd, composite, not a prime power, a mixed non-principal ideal `B` whose class has order `d` dividing `x`, and `x / d < 3.3 * 10^4 log x` | proven, computed |
| 36 | base 25 is the only base below `10^51` with a 2-digit and a 3-digit solution, and the only base below `10^460` with a 2-digit solution that also has a 3-digit one | computed; heuristic beyond |
| 39 | no integer with three bases among the 2,117 integers with a 2-digit representation with digits up to 90 and the 483 with two 2-digit bases and digits up to 150; an integer with two 2-digit bases has every other representation of a rigid shape with at least 4 digits | proven (Lemma 18.16), computed |
| 34 | the root heuristic with local factors is exactly symmetric in the sign of the root; in the square class with the largest digit in front, a finer heuristic favours positive roots about 9 to 1; this covers two of the three positive non-partners | proven, heuristic, computed |
| 31 | yes: `log(M/L) = 2 sum over odd j of g_k(j) / (j s^((j-1)/2) y^j)` with a twisted Ramanujan sum `g_k`, for every Aurifeuillian pair of `Phi_m(s y^2)`; `M/L -> e^(2/y)` or `1` | proven, checked in 456 cases |
| 40 | open; the reduction of chapter 13 cannot be built with pure powers: it needs exponents of size `exp(c sqrt(k / log k))` | proven (barrier) |

## 18.1 The equation b(b+x) = x^n + 1 (question 32)

### 18.1.1 Setting and elementary exclusions

Let `x >= 2`, `n >= 1` and `b >= 1` be integers with

    b (b + x) = x^n + 1.                                          (1)

With `U = 2b + x` this is `U^2 = 4 x^n + x^2 + 4`. For `n = 1`, `b = 1` is
a solution for every `x`. Chapter 16 found: `n = 2` exactly when
`5 x^2 + 4` is a square, that is `x` an even-index Fibonacci number; `n = 3`
exactly for `x` in {3, 5, 8, 64, 119}, from the 10 integral points of the
curve `Y^2 = X^3 + X^2 + 64` of rank 2 (computed, rechecked with Sage and
`analysis/r2nt_genus2.gp`: conductor 433, rank 2).

Proposition 18.1 (proven). Equation (1) has no solution in each of these
cases: (a) `n >= 4` even; (b) `n >= 4` and `x` a square; (c) `n >= 2` and
`x == 2 (mod 4)`; (d) `n >= 2` and `x == 4 (mod 8)`.

Proof. (a), (b): then `x^n = Y^2` with `Y = x^(n/2)` an integer, and
`(2Y)^2 < U^2 < (2Y + 1)^2`, because `0 < x^2 + 4 < 4Y + 1` once
`Y >= x^2`. (c), (d): `x` is even, so `U = 2V` is even and
`V^2 = x^n + (x/2)^2 + 1`. If `x == 2 (mod 4)`, then `x^n == 0` and
`(x/2)^2 == 1 (mod 4)`, so `V^2 == 2 (mod 4)`. If `x == 4 (mod 8)`, then
`x^n == 0` and `(x/2)^2 == 4 (mod 8)`, so `V^2 == 5 (mod 8)`. Neither is a
square.

So the open cases with `n >= 4` have `n` odd, `x` not a square, and `x` odd
or `x == 0 (mod 8)`.

### 18.1.2 The quadratic field

Let `x` be odd, `D = x^2 + 4`, `K = Q(sqrt D)` and `O_K` its ring of
integers. Put

    eps = (x + sqrt D) / 2,     eps' = (x - sqrt D) / 2 = -1 / eps.

Then `eps` is a unit of norm -1 and trace `x`, and for every integer `b`

    N(b + eps) = (b + eps)(b + eps') = b^2 + b x - 1.

So (1) says `N(b + eps) = x^n`.

Lemma 18.2 (proven). Let `x` be odd and `b` a solution of (1).

- (a) The ideals `(b + eps)` and `(b + eps')` are coprime.
- (b) Every prime `p` dividing `x` splits in `K`.
- (c) `P = (eps + 1)` has norm `x`, `P' = (eps' + 1)` is its conjugate,
  `P P' = (x)`, and `P`, `P'` are coprime.

Proof. (a) A common prime ideal divides the difference `eps - eps' = sqrt D`
and the product `x^n`. But `gcd(D, x) = gcd(4, x) = 1`. (b) `D == 4 (mod p)`
is a nonzero square and `p` is odd. (c) `N(eps + 1) = eps eps' + eps + eps' + 1 = x`.
The difference `(eps + 1) - (eps' + 1) = sqrt D` is prime to `x`.

For each prime power `p^a` exactly dividing `x`, let `pi_p` be the prime
above `p` that divides `P`, so `P` is the product of the `pi_p^a` and `P'`
the product of the conjugates `pi_p'^a`.

Lemma 18.3 (proven). For a solution of (1) with `x` odd,
`(b + eps) = B^n`, where `B` is the product over `p^a || x` of `q_p^a` with
`q_p` in {`pi_p`, `pi_p'`}. Moreover `B != B'`.

Proof. `(b + eps)(b + eps') = (x)^n` is the product of the
`(pi_p pi_p')^(a n)`. By Lemma 18.2(a) each `pi_p^(a n)` divides exactly one
of the two factors, and its conjugate divides the other. `B = B'` would put
`pi_p` and `pi_p'` into `B` for some `p`.

Call a solution pure if `B = P` or `B = P'`, and mixed otherwise. If `x` is
a prime power, every solution is pure.

Units. Let `eta0 > 1` be the fundamental unit of `O_K` and
`mu0 = log eta0`. Then `eps = eta0^r` with `r >= 1`, and `N(eps) = -1`
forces `N(eta0) = -1` and `r` odd. So `eta0 - 1/eta0 = y` is a positive
integer and `mu0 = arcsinh(y/2) >= arcsinh(1/2) = 0.4812`. Mostly `r = 1`;
`r > 1` means that `x` is the trace of `eta0^r`, a Lucas polynomial in `y`,
as for `x = 11 = ((1 + sqrt 5)/2)^5 + ((1 - sqrt 5)/2)^5`.

Size. Put `alpha = b + eps` and `alpha' = b + eps' = b - 1/eps`, so
`0 < alpha' < alpha`, and

    Lam0 = log(alpha / alpha') = log(1 + sqrt D / (b - 1/eps)).

From `(b + x/2)^2 = x^n + x^2/4 + 1` we get `b > x^(n/2) - x/2`. So for
`n >= 3`

    0 < Lam0 < tau_n = sqrt D / (x^(n/2) - x/2 - 1).              (2)

For `x >= 3` and `n >= 5`, `tau_n <= tau_5(3) < 0.276`.

### 18.1.3 Pure solutions: a lower bound for n

Let `z = (eps + 1)/(eps - 1)`. Then `log z = 2 artanh(1/eps) < 2.2 / x` for
`x >= 3`, and the exact series

    x log z = 2 - sum over i >= 1 of 4 eps^(-2i) / ((2i - 1)(2i + 1))      (3)

shows `2 - 1.34 / x^2 < x log z < 2`.

Proposition 18.4 (proven). Let `x` be odd, `n >= 5` odd, and `b` a pure
solution of (1). Then there is an odd integer `s >= 1` with

    |n log z - s mu0| = Lam0 < tau_n.

In particular `n log z >= mu0 - tau_n`.

Proof. Suppose `B = P`. By Lemma 18.3, `alpha = u (eps + 1)^n` with a unit
`u = +-eta0^k`. Then `alpha' = u' (eps' + 1)^n`, `|u / u'| = eta0^(2k)`, and
`(eps + 1)/(eps' + 1) = (eps + 1)/(1 - 1/eps) = eps z`. So

    Lam0 = 2k mu0 + n (r mu0 + log z) = -s mu0 + n log z,   s = -(2k + n r).

`s` is odd because `n r` is odd. If `B = P'`, the same computation with
`alpha` and `alpha'` exchanged gives `-Lam0 = -s mu0 + n log z`. In both
cases `|n log z - s mu0| = Lam0`. If `s <= -1`, the left side is at least
`mu0 >= 0.48 > tau_n`, against (2). So `s >= 1` and
`n log z >= s mu0 - Lam0 >= mu0 - tau_n`.

Corollary 18.5 (proven). A pure solution with `n >= 5` odd has `x < 11 n`.

Proof. `n >= (mu0 - tau_n) / log z > (0.4812 - 0.276) x / 2.2 > 0.093 x`.

For `n = 5` this leaves `x <= 53`, and none of them is a solution (computed).
For `r = 1` the bound is much stronger: `n` is about `s x log x / 2`. The
known solution `(7, 7)` has `s = 1` and `mu0 / log z = 6.97`.

The diagonal `n = x` is now clear. By (3), `x log z` lies slightly below 2,
so `n = x` forces `s mu0` close to 2. This is the `e^2` of Theorem 16.1 seen
from the unit side: `mu0 = log eps` is about `log x`, and `log x = 2` near
`x = e^2 = 7.39`.

Proposition 18.6 (proven). For odd `x >= 9`, equation (1) with `n = x` has
no pure solution. So for odd prime powers `x`, `b(b+x) = x^x + 1` has only
the solutions `x = 3` and `x = 7`.

Proof. Here `tau_x < 5 * 10^-4` and `1.34 / x^2 < 0.017`. By
Proposition 18.4 and (3), `|2 - s mu0| < 0.018` with `s >= 1` odd and
`mu0 = arcsinh(y/2)`, `y` a positive integer. For `s = 1` this needs
`y` in `(2 sinh 1.982, 2 sinh 2.018) = (7.12, 7.39)`. For `s = 3` it needs
`y` in `(1.42, 1.45)`. For `s >= 5` it needs `mu0 < 0.41 < 0.4812`. No
integer qualifies. The value `y = 7`, `s = 1` is the solution `x = 7`: there
`tau_7 = 0.008` is not small. `x = 5` fails by direct check (chapter 16).

Proposition 18.6 is elementary: it needs no linear forms in logarithms.

### 18.1.4 Pure solutions: all exponents

Laurent's theorem (cited: M. Laurent, Acta Arith. 133 (2008), Corollary 2
with `m = 10`; the constants are as quoted in arXiv 2608.20995 and must be
checked against the paper). Let `alpha1, alpha2 > 1` be multiplicatively independent
real algebraic numbers, `b1, b2` positive integers,
`Lam = b2 log alpha2 - b1 log alpha1`, `Dg = [Q(alpha1, alpha2) : Q]`,
`log A_i >= max(h(alpha_i), log(alpha_i) / Dg, 1 / Dg)` with `h` the
absolute logarithmic height, and `b' = b1 / (Dg log A2) + b2 / (Dg log A1)`.
Then

    log |Lam| >= -25.2 Dg^4 max(log b' + 0.38, 10 / Dg, 1)^2 log A1 log A2.

Theorem 18.7 (proven). For odd `x`, the only pure solution of (1) with
`n >= 4` is `(x, n) = (7, 7)`.

Proof. By Proposition 18.1, `n` is odd and `x` is not a square. Apply
Laurent's theorem to `alpha1 = eta0`, `alpha2 = z`, `b1 = s`, `b2 = n`,
`Dg = 2`. They are independent: `eta0` is a unit and `z` is not an algebraic
integer, because it is a root of the primitive polynomial `x T^2 - 4T - x`.
That polynomial also gives `h(z) = (1/2) log(x z)`. So
`log A1 = max(mu0, 1)/2` and `log A2 = (1/2) log(x z)` serve.

Part A: `x >= 10^5`. Then `tau_5 < 3.2 * 10^-8`, `log z < 2.0001 / x`, and
`tau_n < 1.0002 x^(1 - n/2)`. Proposition 18.4 gives
`n >= (mu0 - 3.2 * 10^-8) x / 2.0001`, and `s < 10^-3 n / max(mu0, 1)`.
Put `nu = n / max(mu0, 1)`, so `b' < 1.001 nu + 10^-7`. Laurent's bound and
(2) give

    (n/2 - 1) log x - 0.0002 < 100.8 M^2 max(mu0, 1) (log x + 10^-4),

with `M = max(log(1.001 nu + 1) + 0.38, 5)`. Hence
`nu < 2.0001 + 201.61 M^2`, which forces `nu < 22,000`: at `nu = 22,000` the
right side is 21,724, and it grows more slowly than `nu`. So
`n < 22,000 max(mu0, 1)`. With the lower bound,
`x < 2.0001 * 22,000 * max(mu0, 1) / (mu0 - 3.2 * 10^-8)`, which is below
44,010 if `mu0 >= 1` and below 91,450 if `mu0 >= 0.4812`. Both contradict
`x >= 10^5`.

Part B: `x < 10^5` (computed, `analysis/r2nt_pure.py`,
`data/r2nt_pure_1e5.txt`, 7 minutes). For each odd non-square `x` up to
100,001 the script finds `r` and `mu0` exactly, computes the largest `n`
that Laurent's bound allows (`n_hi(x)`, at most 249,246), and then:

- checks `n = 5, 7, ..., 15` exactly (`4 x^n + x^2 + 4` a square);
- for `n >= 17` verifies `n tau_n < mu0 / 2`. Then
  `|log z / mu0 - s/n| < 1 / (2 n^2)`, so `s/n` in lowest terms is a
  convergent of `log z / mu0` (Legendre). It runs through all convergents
  `p/q` with `q <= n_hi(x)` at 60 digits and tests
  `|q log z - p mu0| < tau_q`. A multiple `n = g q` passes only if `q` does,
  since the left side grows with `g` and `tau_n` falls.

The only hit is `(7, 7)`.

### 18.1.5 Prime powers

Theorem 18.8 (proven, with cited inputs). Let `x` be a prime power. The
solutions of (1) with `n >= 2` are exactly

    (x, n) = (3, 2), (8, 2), (3, 3), (5, 3), (8, 3), (64, 3), (7, 7).

Proof. Even `n >= 4` is excluded by Proposition 18.1.

- `n = 2`: `x = F_2k = F_k L_k`. For `k >= 3`, `F_k >= 2`, `L_k >= 4` and
  `gcd(F_k, L_k)` is 1 or 2, so a prime power needs both to be powers of 2.
  The powers of 2 among Fibonacci and Lucas numbers are 1, 2, 8 and 1, 2, 4
  (cited, classical). This leaves `F_4 = 3` and `F_6 = 8`.
- `n = 3`: the complete list {3, 5, 8, 64, 119}; 119 = 7 * 17 is not a prime
  power.
- `n >= 5` odd, `x` odd: every solution is pure, and Theorem 18.7 applies.
- `n >= 5` odd, `x = 2^a`: by Proposition 18.1, `a >= 3`. With `V = U/2`,
  `V^2 = 2^(a n) + 2^(2a - 2) + 1`. Szalay's theorem (cited: L. Szalay,
  `2^a + 2^b + 1 = x^2`, Publ. Math. Debrecen 2000; shorter proof by
  R. Scott, arXiv math/0608796) says that the solutions with `A >= B >= 1`
  of `2^A + 2^B + 1 = V^2` are `(A, B) = (2t, t + 1)`, `(5, 4)` and `(9, 4)`.
  `(a n, 2a - 2) = (2t, t + 1)` gives `a (4 - n) = 6`, so `n <= 3`. The other
  two give `a = 3` and `n = 5/3` or `n = 3`. So `n >= 5` is impossible.

Corollary 18.9 (proven). For a prime `p`, the generalized Ramanujan-Nagell
equation `U^2 - (p^2 + 4) = 4 p^n` has the solutions `n = 1` for every `p`,
`n = 2, 3` for `p = 3`, `n = 3` for `p = 5`, and `n = 7` for `p = 7`, and no
others.

The literature bounds the number of solutions of `U^2 - D = 4 p^n` by 4 or 5
(cited: M.-H. Le, via the survey of Le and Soydan, arXiv 2001.09617). For
`D = p^2 + 4` Corollary 18.9 gives the exact set.

### 18.1.6 Mixed solutions: a bound for n in terms of x

Theorem 18.10 (proven; the constant computed). Let `x` be odd and not a
square, `n >= 5` odd, and `b` a solution of (1). Let `d` be the order of the
class of `B` in the class group of `O_K`, so `d` divides `n` and the class
number. If `d < n`, then

    log tau_n >= -403.2 M^2 (max(mu0, 1)/2) ((d log x + mu0)/2),

with `M = max(log b' + 0.38, 5)` and
`b' = (n/d + 1)/(d log x + mu0) + (n/d)/max(mu0, 1)`. Consequently
`n < 6.4 * 10^4 d log x` for every odd `x >= 3`.

Proof. Write `B^d = (eta)`. Then `alpha = u eta^(n/d)` with
`u = +-eta0^k`, and `Lam0 = 2k mu0 + (n/d) theta` with
`theta = log|eta/eta'|`. Multiplying `eta` by a power of `eta0` shifts
`theta` by multiples of `2 mu0`, so take `|theta| <= mu0`.

`theta != 0`: the number `w = |eta / eta'|` satisfies
`w + 1/w = |Tr(eta^2)| / x^d`, and `w = 1` would give `B^(2d) = (x^d)`, that
is `B = B'`, against Lemma 18.3. So `|w + 1/w - 2| >= x^(-d)`, which gives
`2 sinh(|theta|/2) >= x^(-d/2)` and `|theta| >= 0.99 x^(-d/2)`.

If `k = 0` or `k theta > 0`, then `Lam0 >= (n/d)|theta| >= 0.99 x^(-d/2)`.
Since `d <= n/3`, this exceeds `tau_n`, against (2). So `k theta < 0`, and
`Lam0 = |b1 mu0 - (n/d)|theta||` with `b1 = 2|k| <= n/d + 1`. Apply
Laurent's theorem with `alpha1 = eta0`, `alpha2 = e^|theta|`, `Dg = 2`. The
number `w` is a root of `x^d T^2 - Tr(eta^2) T + x^d`, so
`h(w) <= (d log x + |theta|)/2`. The same argument as for `w = 1` shows
that `w` is not a unit, so it is independent of `eta0`. Laurent's bound and `Lam0 < tau_n` give the displayed inequality.
The constant comes from `analysis/r2nt_principal.py`
(`data/r2nt_principal.txt`), which evaluates the inequality with the worst
case `mu0 = log eps`. On a grid of `x` from 3 to `10^40` and `d` up to 101
the largest value of `n / (d log x)` that it allows is 63,441, at `x = 3`,
`d = 1`; for `x >= 4 * 10^9` and `d >= 3` it is below 32,500.

For `d = 1` (principal `B`) and large `x` the bound reads
`n < 5.6 * 10^4 log x`. So for each `x` with class number prime to `n` only
`O(log x)` exponents remain. Pure solutions are the case where in addition
`theta` lies within `log z` of an odd multiple of `mu0`; that extra fact gave
the lower bound of Proposition 18.4. Mixed solutions have no such lower bound,
and the `n = 3` solution `x = 119` shows that they exist.

Corollary 18.11 (question 12; proven, with the sieve of chapter 16). If
`b(b+x) = x^x + 1` has a solution with `x` other than 3 and 7, then `x` is
odd, `x > 4 * 10^9`, `x` is not a square and has at least two distinct prime
factors, the solution is mixed, `B` is not principal, and the order `d` of
its class divides `x` with `x / d < 3.3 * 10^4 log x`. In particular the
class number of `Q(sqrt(x^2 + 4))` is at least `x / (3.3 * 10^4 log x)`.

Proof. Even and square `x`: Proposition 16.3. `x <= 4 * 10^9`: the sieve
of section 16.2.3. Prime powers: Theorem 18.8. Pure solutions:
Proposition 18.6. Principal `B`: Theorem 18.10 with `d = 1` allows only
`x <= 747,069` (`r2nt_principal.py`). Otherwise `3 <= d` divides `x`, and
Theorem 18.10 gives the bound on `x / d`.

### 18.1.6.1 Small x, every exponent

For a fixed odd `x` the proof of Theorem 18.10 is a finite procedure: for each
choice of `B` it bounds `n`, and the convergents of `theta / (2 mu0)` give
the only candidates.

Theorem 18.12 (computed). For odd `x <= 1001` the only solution of (1) with
`n >= 4` is `(7, 7)`.

Proof. Squares and even `n` are excluded by Proposition 18.1, and `n <= 15`
by the direct check of `r2nt_pure.py`. For `n >= 17`,
`analysis/r2nt_allnx.gp` builds `K` with a certified class group
(`bnfcertify`). For each of the `2^omega(x)` ideals `B` it finds the order
`d` of its class, skips even `d` (since `d | n` and `n` is odd), takes a
generator `eta` of `B^d`, and runs through the convergents `p/q` of
`theta / (2 mu0)` with `d q` up to the bound of Theorem 18.10, testing
`|q theta - 2 p mu0| < tau_(dq)`. By Legendre's theorem every solution with
`n >= 17` is among these candidates, because `n tau_n < mu0`. Of the 1,818 ideals `B`, 814 are not principal. Laurent's bound allows
exponents up to 7,816,158. No candidate appears (`data/r2nt_allnx_1001.txt`,
25 minutes).

The same program with the threshold lowered to `n >= 3` finds the known
solutions `(5, 3)`, `(7, 7)` and `(119, 3)`. The last one is mixed:
`119 = 7 * 17`, its ideal `B` is not principal, and its class has order
`d = 3 = n`. This is the shape that Corollary 18.11 leaves open for `n = x`.

### 18.1.7 The exponent n = 5

Computed:

- no solution with `x <= 10^10` (`analysis/r2nt_sieve_n.c`,
  `data/r2nt_sieve_n5_1e10.txt`; a modulus 64 and the odd primes up to 193
  exclude every `x`; 7 minutes);
- by Proposition 18.1 and Corollary 18.5 every solution is mixed with `x` odd,
  or has `x == 0 (mod 8)`;
- the curve `U^2 = 4 x^5 + x^2 + 4` has genus 2, and its minimal model is the
  equation itself, `b^2 + x b = x^5 + 1`, with conductor
  `800,027 = 331 * 2417` (PARI `genus2red`). Its known rational points have
  `x` in {-1, 0, 1, 1/64} and the point at infinity. The point at `x = 1/64`
  comes from `(2 + x^2/4)^2 - x^4/16 + 4 x^5` with `x^4/16 = 4 x^5`;
- the Jacobian has analytic rank 3 (`lfungenus2`, `lfunorderzero`,
  `data/r2nt_genus2.txt`).

So the Mordell-Weil rank is probably 3, larger than the genus. Then neither
Chabauty-Coleman (rank below genus) nor quadratic Chabauty (rank equal to
genus) applies. What remains is Baker's method for integral points on
hyperelliptic curves with a Mordell-Weil basis and the Mordell-Weil sieve
(Bugeaud, Mignotte, Siksek, Stoll, Tengely, Compositio 2008). That needs a
2-descent on the Jacobian and a saturated basis, which PARI and Sage do not
provide here. For `n = 5` the question is therefore decidable but not
decided.

Other exponents (computed, same program): for `n = 7, 9, 11, 13, 15` the only
solution with `x <= 10^9` is `(7, 7)`; for odd `n` from 17 to 201 there is
none with `x <= 10^8`.

### 18.1.8 The family uniformly in n

Proposition 18.13 (proven, conditional). (a) The abc conjecture implies that
(1) has finitely many solutions with `n >= 7`. (b) Faltings's theorem gives
finitely many for each `n >= 5`. (c) So abc implies that the set of
solutions with `n >= 4` is finite. The weak form `c < K rad(abc)^(2 - delta)`
for some `delta > 0` is enough.

Proof. For odd `x`, `(x^2 + 4) + 4 x^n = U^2` is a coprime triple. For
`x == 0 (mod 8)`, divide by 4. Its radical is below `8.1 x^(3 + n/2)`. If
`x^n <= U^2 <= K (8.1 x^(3 + n/2))^(2 - delta)`, then
`x^(delta n/2 - 6 + 3 delta) <= K'`. For `n > 12/delta - 6` this bounds
`x`, and then `n`. The full abc gives every `delta < 1`, so every `n >= 7`.
The remaining exponents are finitely many curves of genus at least 2.

Heuristic. Given `x` and `n`, `4 x^n + x^2 + 4` is a square with chance
about `1 / (4 x^(n/2))`. The sum over the region not yet searched (`n = 5`,
`x > 10^10`; `n = 7` to 15, `x > 10^9`; larger `n`, `x > 10^8` or
`n > 201`) is below `10^-14`. The pure structure makes most of these chances
much smaller still: a pure solution needs `n` of size `x log x / 2`.

### 18.1.9 New questions

1. Compute the 2-Selmer group of the Jacobian of `b^2 + x b = x^5 + 1`,
   prove that the rank is 3, and finish `n = 5` with the Mordell-Weil sieve.
2. Even `x == 0 (mod 8)` with an odd prime factor. Here `b + eps = 2 gamma`
   and `(gamma)` has 2-part of exponent `a n - 2`, not a multiple of `n`. Is
   there an analogue of Proposition 18.4?
3. Question 12 now asks whether `Q(sqrt(x^2 + 4))` can have an ideal class of
   order `d >= x / (3.3 * 10^4 log x)`, with `d | x`, containing a divisor of
   `(x)` of norm `x`. Can the theory of Richaud-Degert fields, where ideals of
   small norm are rarely principal, exclude this?

## 18.2 Bases with a 2-digit and a 3-digit solution (question 36)

Under `0^0 = 1` the 3-digit solutions in all bases up to `10^51` are
`(1,3,1)` and `(3,1,3)` in base 4, `(5,1,3)` in base 25, `(6,1,5)` in base
91, `(1,2,6)` in base 215 and `(1,7,1)` in base 904 (chapter 3,
`analysis/data/k3.txt`).

Lemma 18.14 (proven). If base `b` has a 2-digit solution `(a, c)` under
`0^0 = 1` and `m = max(a, c)`, then `b >= m^(m-1)`. So a base below `10^460`
with a 2-digit solution has its 2-digit digits at most 200.

Proof. `b = (a^a + g(c)) / a` with `g(c) = w(c) - c >= 0`. If `a = m`, then
`b >= a^(a-1)`. If `c = m > a`, then `b >= (c^c - c)/(c - 1) >= c^(c-1)`.
Finally `201^200 > 10^460`.

Proposition 18.15 (computed). Under `0^0 = 1`:

- base 25 is the only base below `10^51` with a 2-digit and a 3-digit
  solution: `(1,3)` and `(5,1,3)`;
- among the 8,502 bases of 2-digit solutions with digits up to 200, which by
  Lemma 18.14 include every base below `10^460` with a 2-digit solution, base
  25 is the only one with a 3-digit solution.

Under `0^0 = 0` the same holds below `10^51` and for the 3,978 bases of
2-digit solutions with digits up to 120 (every such base below `10^249`);
base 25 then has `(1,3)` and the three 3-digit solutions `(5,0,0)`, `(5,0,1)`
and `(5,1,3)`.

Method (`analysis/r2nt_two_three.py`, `data/r2nt_two_three_200_m1.txt`,
`data/r2nt_two_three_120_m0.txt`). Part 1 lists the 2-digit solutions of
each base in `k3.txt`. Part 2 finds every 3-digit solution `(p, q, r)` of a
given base `b`. Since `F` lies in `[p b^2, (p+1) b^2)` and `F < 3 w(M)` for
the largest digit `M`, each `p` allows at most two values of `M`. Then:
`M = q` fixes `r` by inverting the increasing function `w(r) - r`; `M = r`
fixes `q` from the convex function `w(q) - q b`, with two monotone pieces;
`M = p` fixes `r` for each `q`. Checked against brute force in all bases
below 50 under both conventions, and against the known solutions in bases
91, 215, 904, 6561 and `3^40`.

Why base 25 works. `25 = 3^3 - 3 + 1` is the base of `(1, 3)`, and
`25 = 5^2` makes 5 self-paying at position 2 in the square class
(`5 * 25^2 = 5^5`). The coincidence is `3^3 - 2 = 5^2`, the same one as in
`(1,0,3)` under `0^0 = 0`.

Heuristic. The 3-digit list is complete to `10^51`, and section 11.4 puts
the expected number of 3-digit solutions in larger bases at `10^-74`. So no
other base is expected. A proof for all bases would need the finiteness of
3-digit solutions, which is open; the 2-digit condition on `b` is an
independent constraint and does not seem to help.

## 18.3 Integers with three bases (question 39)

Lemma 18.16 (proven). Under `0^0 = 1`, let `N = a^a + w(c)` with
`0 <= c <= a` and `a >= 2`. Every representation of `N` as a Munchausen
number in some base, with `k` digits, contains the digit `a` exactly once,
unless `c = a` and the representation is `(a, a)`. The other `k - 1` digits
are below `c`, and their weights add up to `w(c)`. Consequently:

- if `c <= 1` or `c = a`, every representation of `N` has 2 digits;
- if `2 <= c < a`, every representation with more than 2 digits has between
  `c + 2` and `a + 1` digits.

Proof. Let `d` be the largest digit and `b > d` the base, so
`(d + 1)^(k-1) <= b^(k-1) <= N`. Note `a^a < N <= 2 a^a` and every weight is
at least 1.

- `d > a` is impossible: `w(d) >= (a+1)^(a+1) > 2 a^a >= N`.
- `d < a` is impossible. If `d <= 1`, all weights are 1, so `N = k`, but
  `N >= 2^(k-1) > k` for `k >= 3`, and `k = 2` gives `N = 2 < a^a`. If
  `d >= 2`, then `N <= k d^d` and `N > (d+1)^(d+1)`, so
  `k > (d + 1)(1 + 1/d)^d >= 2(d + 1)`. Also
  `(d+1)^(k-1) <= N <= k d^d < k (d+1)^d`, so `(d+1)^(k-1-d) < k`. But
  `k - 1 - d > k/2` and `3^(k/2) > k`.
- So `d = a`. Two copies of `a` weigh `2 a^a >= N`, which allows only
  `c = a` with nothing else: the string `(a, a)`. Otherwise `a` occurs once
  and the other digits `R` have weights adding up to `w(c)`.
- The largest digit `d'` of `R` is at most `c`. If `d' = c`, the rest of `R`
  has weight 0, so `R = (c)` and `k = 2`. So for `k >= 3`, `d' < c`.
- If `c <= 1`, `w(c) = 1` forces `|R| = 1`. If `c = a`, the bound below
  gives `|R| > a` and `|R| <= a` at once. If `2 <= c < a`:
  `|R| >= c^c / (c-1)^(c-1) > c`, and `(a+1)^|R| <= N < 2 a^a` gives
  `|R| <= a`.

Corollary 18.17 (proven). An integer with three bases under `0^0 = 1` either
has at most one 2-digit representation and at least two longer ones, or is
`N = a^a + c^c` with `2 <= c < a`, `c | a^a - a`, `a | c^c - c`, and a third
representation of `c + 2` to `a + 1` digits: one digit `a` and digits below
`c` whose weights add up to `c^c`.

Proof. Proposition 15.16 says that two 2-digit representations are `(a, c)`
and `(c, a)` with these divisibilities. Lemma 18.16 does the rest.

Computed (`analysis/r2nt_multibase.py`, `data/r2nt_multibase_90_150.txt`,
using the complete base finder `bases_of` of `dyn_multibase.py`):

- the 2,117 integers with a 2-digit representation with digits up to 90:
  1,779 have one base, 338 have two, none has three, and none has a
  representation with 3 or more digits;
- the 483 integers `a^a + c^c` with two 2-digit bases and `a, c <= 150`:
  none has a third base.

Together with chapter 15 (all known solutions, both conventions) no integer
with three bases under `0^0 = 1` is known.

Heuristic. A third base for `N = a^a + c^c` needs a representation of the
rigid shape of Corollary 18.17. In each candidate base the digits are fixed by
`N`, so two conditions must hold by chance: all digits but one lie below `c`,
and their weights add up to exactly `c^c`. The second is an exact equation
between integers of size up to `c^c`, of the kind that chapter 3 finds only
finitely often. The other route, two representations with 3 or more digits,
needs two such coincidences at one integer. So I expect no integer with three
bases under `0^0 = 1`, but I have no numerical estimate that I trust. For
`c = 2` the question is a Pillai-type equation: with `k = 5` it asks for
`a^a + 4 = a b^j + (a sum of distinct powers of b below b^5)`.

## 18.4 Signs of 3-digit roots (question 34)

For `s = (p, q, r)`, `Q_s(t) = p t^2 + q t + r - F` has the discriminant
`Delta = q^2 + 4p(F - r)` and the roots `t+ > 0 > t-`. The positive root
gives a solution in base `t+`, the negative one in base `t-`, when they are
integers beyond the digits. Proposition 12.3 pairs them when `p | q`
(partners). Question 34 asks why the non-partner solutions, `(3,1,3)` in
base 4, `(5,1,3)` in base 25 and `(6,1,5)` in base 91, have no negative
counterparts. (Below `(1,1,1)` in base -2 is set aside: its partner root is
1.)

Proposition 18.18 (proven). The root heuristic with local factors of section
11.4 gives the two roots of every 3-digit string the same weight.

Proof. The weight of a root `t` is `prod rho_s(l) / |Q_s'(t)|`. The local
factors depend only on `Q_s`, and `|Q_s'(t+)| = |Q_s'(t-)| = sqrt Delta`.

So the heuristic predicts as many non-partner solutions in negative bases as
in positive ones. Computed (`analysis/r2nt_negroots.py`,
`data/r2nt_negroots_70.txt`, digits up to 70): outside the square class the
weights are 0.939 for each sign, and the strings with a root within 0.01 of
an integer number 4,758 (positive) and 5,377 (negative), within 0.001, 446
and 520. The negative side is slightly larger because `|t-| > t+`, so the
condition "beyond the digits" holds more often. Under this symmetric model
each non-partner solution is positive with probability 1/2, and 3 out of 3
has probability 1/8.

The square class breaks the symmetry. Call `s` square class when
`Y^2 = 4 p w(d*)` is a perfect square, `d*` the digit of largest weight.
Then `Delta = Y^2 + E` with `E` from the two smaller weights, and
`sqrt Delta = Y + t` with `t` near `E / (2Y)`.

Lemma 18.19 (proven). In the square class, if `Delta` is a square, then
`t+` is an integer exactly when `Y + t == q (mod 2p)`, and `t-` exactly when
`Y + t == -q (mod 2p)`. If the leading digit `p` is odd and is the largest
digit, then `Y = 2 p^((p+1)/2)` is divisible by `2p`, so the two conditions
are `t == q` and `t == -q (mod 2p)`. For `0 < q < p` the smallest admissible
`t` are `q` for the positive root and `2p - q > q` for the negative root.

Proof. `t+- = (-q +- (Y + t)) / (2p)`.

Heuristic. In a family where one smaller digit varies, `t` jumps by a factor
of about the digit at each step, so `t` is spread evenly on a log scale and
the chance of hitting a given `t` is proportional to `1/t`. The positive root
then gets the extra weight
`sum over t == q of 1/t - sum over t == -q of 1/t = (pi/(2p)) cot(pi q/(2p))`
(mod `2p`, by the reflection formula of the digamma function), which
dominates for small `p`. Computed with `t` taken as the nearest integer to
`sqrt Delta - Y` and weight `1/(2 sqrt Delta)` per string: for non-partner
square-class strings with the largest digit in front, the expected numbers
are 0.0564 (positive) against 0.0064 (negative), against 0.0248 for each sign
under uniform residues. With the largest digit elsewhere they are 0.0012
and 0.0017. The offset `delta = (sqrt Delta - Y)/(2p)` shows the same
picture: for front-largest strings with `delta < 1`, 21,974 lie closer to the
positive target than to the negative one, and 214 the other way.

The two square-class solutions follow the mechanism. `(5,1,3)`: `Y = 250`,
`E = 501 = 2 * 250 + 1`, so `t = 1 = q`. `(3,1,3)`: `Y = 18`, `t = 7 == 1
(mod 6)`. Both are positive.

Answer. Nothing suppresses negative roots. Outside the square class the
heuristic is exactly symmetric (Proposition 18.18). Inside it, with the largest
digit in front, small `t` favours the positive root about 9 to 1
(Lemma 18.19). Two of the three positive non-partners are of this kind. The
third, `(6,1,5)` in base 91, is an ordinary coin flip that came up positive.
The prediction for negative bases is: a non-partner 3-digit solution there
is most likely outside the square class, or has the largest digit in the
middle or last position.

## 18.5 The M/L series for Aurifeuillian factors (question 31)

Let `s > 1` be squarefree, `D` the discriminant of `Q(sqrt s)` (`D = s` if
`s == 1 (mod 4)`, else `4s`) and `chi = chi_D` the Kronecker symbol. Let
`k >= 1` be odd and

    m = k |D| / 2  (D even),     m = k |D|  (D odd).

Then `Phi_m(s t^2)` splits in `Z[t]` as `+- c G(t) G(-t)` (Aurifeuillian
factorization). At `t = y` the two values are the Aurifeuillian factors
`L <= M` of `Phi_m(s y^2)`. Homogeneously: for `a = s A^2`, `b = B^2` and
`y = A/B`, they are the Aurifeuillian factors of the part
`b^phi(m) Phi_m(a/b)` of `a^n +- b^n`. Theorem 16.1 is the case `k = 1`,
`y = 1`. Define the twisted Ramanujan sum

    g_k(j) = sum over r | gcd(j, k) of r mu(k/r) chi(k/r) chi(j/r).

If `gcd(k, D) = 1` it equals `chi(k) chi(j) c_k(j)`, with `c_k` the
Ramanujan sum.

Theorem 18.20 (proven for `D` even; `D` odd by the same computation with the
character `chi(a) (-1)^a`; both checked numerically). For `s y^2 > 1`,

    log(M / L) = 2 | sum over odd j >= 1 of g_k(j) / (j s^((j-1)/2) y^j) |.

Proof (`D` even). The roots of `Phi_m(s t^2)` are `zeta^a / sqrt s`, with
`zeta` a primitive `2m`-th root of unity and `a` in `(Z/2m)^*`; here `4 | 2m`.
The Galois element `sigma_c` maps `sqrt s` to `chi(c) sqrt s`, so it maps the
root with exponent `a` to the root with exponent `c a` or `c a + m`. Since
`chi(u + m) = -chi(u)` (`m` is an odd multiple of `|D|/2`, and `chi_D` changes
sign under a shift by `|D|/2` when `D` is even), the set
`A = {a : chi(a) = 1}` is Galois stable and `a -> a + m` maps it to its
complement. So `G(t) = prod over a in A of (t - zeta^a / sqrt s)` has rational
coefficients up to a constant, and as in Theorem 16.1

    log(M/L) = | 2 Re sum over odd j of S_j / (j (y sqrt s)^j) |,
    S_j = sum over a in A of zeta^(a j) = (c_2m(j) + c_chi(j)) / 2,

with `c_chi(j) = sum over a in (Z/2m)^* of chi(a) zeta^(a j)`. For odd `j`,
`c_2m(j) = 0`, because `2m / gcd(j, 2m)` is divisible by 4. The character
`chi` modulo `2m` is induced by the primitive `chi_D` of conductor `|D|`, and
the standard formula for Gauss sums of induced characters gives
`c_chi(j) = sqrt|D| g_k(j)` with `k = 2m/|D|`. Since `sqrt|D| = 2 sqrt s`,
`S_j = sqrt s g_k(j)`, which is the series.

For `D` odd, `m` is odd, the roots are `+- zeta_m^c / sqrt s`, and the halves
are cut out by `psi(a) = chi(a)(-1)^a` on the exponents modulo `2m`; the
plain part of `S_j` vanishes for odd `j` and the twisted part reduces to the
modulus `m` with `k = m/|D|`.

Computed (`analysis/r2nt_aurifeuille.gp`, `data/r2nt_aurifeuille.txt`): for
every squarefree `s <= 40`, odd `k <= 15` with `m <= 240`, and `y = 1, 2, 3, 4`
(456 cases), the series agrees with `log(M/L)` from the factored polynomial
to within `2 * 10^-62`.

Corollary 18.21 (proven). `g_k(1) = mu(k) chi(k)`. So

    log(M / L) = 2 |mu(k) chi(k)| / y + O(1 / (s y^3)),

using `|g_k(j)| <= sigma(j)`. Hence:

- if `k` is squarefree and prime to `D`, `M/L -> e^(2/y)` as `s` grows; for
  `y = 1` this is the `e^2` of Theorem 16.1, now for every such `m`;
- if `k` is not squarefree or shares a prime with `D`, `M/L -> 1`.

Examples at `y = 1`: `s = 7, m = 14` (Theorem 16.1): 8.06; `s = 7, m = 42`
(`k = 3`): 6.06; `s = 3, m = 18` (`k = 3`, `gcd(k, D) > 1`): 1.95;
`s = 6, m = 36`: 1.40. Since the leading term is `2/y`, an Aurifeuillian pair
of `Phi_m(s y^2)` with `y >= 2` is balanced within a factor `e^(1 + o(1))`.
For (1) with `x = s y^2` this means that such pairs come close to the
balance `b ~ b + x` only through the cyclotomic degrees, as in Theorem 16.2;
the `e^2` coincidence of `x = 7` needs `y = 1`.

## 18.6 Powers as weights (question 40)

The problem: the base `b` in unary, exponents `e(0), ..., e(b-1)` in unary,
weights `w(x) = x^(e(x))` with `w(0)` in {0, 1}; is there `n >= b` with
`F_w(n) = n`? It is in NP (Proposition 13.6). NP-hardness stays open. Here
is why the reduction of Theorem 13.3 cannot be copied.

That reduction needs item digits `x_i` whose weights are `x_i b^(P_i)` plus
an error below `b^(L+1)`, at distinct positions `P_i >= L + 2`, with `k`
items for `k` numbers of the SUBSET-SUM instance and `b` polynomial in `k`.

Proposition 18.22 (proven). Let `b >= 3`, `2 <= x < b`, `e >= 2`, `P >= 1`,
`L >= 0` with `x^e != x b^P` and `|x^e - x b^P| < b^(L+1)`. Then

    P - L - 1 <= 25.2 max(log b' + 0.38, 10)^2 max(log x, 1),
    b' = (e - 1) / log b + P / max(log x, 1),

unless `x` and `b` are powers of one integer and `x^(e-1) = b^P`.

Proof. Put `Lam = (e - 1) log x - P log b`. From
`|x^(e-1) / b^P - 1| < b^(L+1-P) / x <= 1/2` we get
`|Lam| < 2 b^(L+1-P) / x < b^(L+1-P)`. If `x` and `b` are powers of one
integer `g`, then `Lam` is a multiple of `log g`, so `Lam = 0` and
`x^(e-1) = b^P` exactly. Otherwise they are independent, and Laurent's
theorem with `Dg = 1`, `log A1 = max(log x, 1)`, `log A2 = log b` gives
`log|Lam| >= -25.2 max(log b' + 0.38, 10)^2 max(log x, 1) log b`. Compare
with `log|Lam| < -(P - L - 1) log b`.

Corollary 18.23 (proven). In a weight table `x^(e(x))` with `k` item digits of
the shape above at distinct positions, the largest exponent satisfies

    k <= 25.2 max(log(2 e_max) + 0.38, 10)^2 log b + log2 b.

So if `b` is polynomial in `k`, then `e_max >= exp(c sqrt(k / log k))` for a
constant `c > 0`, which is not polynomial. The reduction of Theorem 13.3 has
no polynomial-size analogue with pure powers.

Proof. Exact items (`x^(e-1) = b^P`) are powers of the integer of which `b`
is a power, so there are fewer than `log2 b` of them (Proposition 13.8). The
others have distinct positions above `L + 1`, so the largest `P - L - 1` is
at least their number minus 1, and `P <= e log x / log b <= e`, so
`b' <= 2e`. Apply Proposition 18.22.

What remains open. A reduction must control long expansions instead of short
ones. Digits near `b` are a candidate: `(b - c)^e` equals
`sum over i of binom(e, i) (-c)^(e-i) b^i`, so its base-`b` digits are
explicit for small `c` and `e`. A reduction would have to make these
digits, which depend on the chosen subset, consistent with the digit
multiset. I found no gadget that does this, and no argument that excludes
one. The variant with `w(0) = 1` forced has the extra problem of section
13.1.2, since every zero then costs 1.

## Scripts and data

| file | content |
|---|---|
| `analysis/r2nt_pure.py` | pure solutions of (1), odd `x <= X` (Theorem 18.7, part B): `data/r2nt_pure_1e5.txt` |
| `analysis/r2nt_allnx.gp` | all `n` for odd `x <= 1001` (Theorem 18.12): `data/r2nt_allnx_1001.txt` |
| `analysis/r2nt_principal.py` | the Laurent bounds of Theorem 18.10 and Corollary 18.11: `data/r2nt_principal.txt` |
| `analysis/r2nt_sieve_n.c` | sieve for fixed `n`: `data/r2nt_sieve_n5_1e10.txt`, `data/r2nt_sieve_n7-15_1e9.txt`, `data/r2nt_sieve_n17-201_1e8.txt` |
| `analysis/r2nt_genus2.gp` | the `n = 5` curve and the `n = 3` elliptic curve: `data/r2nt_genus2.txt` |
| `analysis/r2nt_two_three.py` | question 36: `data/r2nt_two_three_200_m1.txt`, `data/r2nt_two_three_120_m0.txt` |
| `analysis/r2nt_multibase.py` | question 39: `data/r2nt_multibase_90_150.txt` |
| `analysis/r2nt_negroots.py` | question 34: `data/r2nt_negroots_70.txt` |
| `analysis/r2nt_aurifeuille.gp` | question 31: `data/r2nt_aurifeuille.txt` |

Build the sieve with
`gcc -O2 -o fast/target/r2nt_sieve_n analysis/r2nt_sieve_n.c -lgmp` and run
`fast/target/r2nt_sieve_n 5 10000000000`. Run the PARI scripts with
`gp -q < analysis/<script>.gp`.
