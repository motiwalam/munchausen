# Round 6: applications and connections

DRAFT. This file reads the library against other fields and asks what
transfers in each direction. It keeps three transfers that are worked out
with proofs, and lists the rest as analogies at the end.

1. Additive combinatorics, into the library. The anti-concentration idea of
   Littlewood and Offord proves that the refined coupled model of chapter 13
   obeys its Poisson law in the limit, with no assumption on the residues of
   `x^x` (section 1). This closes question 54 in its qualitative form.
2. Exponential congruences, both ways. The literature on `x -> x^x mod p`
   (Balog, Broughan and Shparlinski; Cilleruelo and Garaev; Kurlberg, Luca
   and Shparlinski; Holden and Moree) bounds collisions and fixed points.
   Assumption R is a collision bound for the shifted map `x^x - x`
   (section 2.2), and the 2-digit solutions with leading digit `a` are the
   fixed points of `x -> x^x` modulo `a` (section 2.4). One theorem of
   Kurlberg, Luca and Shparlinski transfers directly.
3. Sums of two squares, out of the library. For the weights `x^2` the
   2-digit solutions in base `b` number exactly `tau(b^2 + 1) - 2`
   (section 3). Here the parity doubling of section 5.3 is a theorem, the
   question of empty bases is Landau's problem, and the coincidence model
   is short by a factor of order `ln b`, for a reason one can name.

Each statement is marked proved (a proof is here), cited (a published
result, with its source), computed (an exact computation, with its range),
heuristic, conjecture, or analogy. Scripts are `analysis/r6a_*.py`, data
`analysis/data/r6a_*`.

The draft `round5-model.md` (merged while this one was written) answers
questions 80 and 82 by other routes. Section 1 here is a different
argument for the same goal as its section 3, and gives what that section
lacks: a statement for every large base. Section 2.2 is the mean-square
form of its Theorem 3.2.

## Summary

Ranked by depth.

| section | field | direction | result | status |
|---|---|---|---|---|
| 1 | additive combinatorics (Littlewood-Offord) | import | Theorem 1.3: for any modulus `Q`, a sum of uniform digits has no residue of probability above `2 e^(-J/5)`, with `J` about `ln Q / (2 ln ln Q)`, because the small digits have exact weights that grow faster than `2z`. Theorem 1.5: the refined case of Corollary 13.11 holds for every `b >= 12` with error `14.2 rho*(b) + 16 b^2 (b^2-1) l!/b^l`, and `rho*(b) <= 2 exp(-(1/10 + o(1)) ln b / ln ln b) -> 0`. So the refined coupled model has the bivariate Poisson law in the limit, unconditionally. The same proof works for `x^(x+t)` and `x!`. | proved |
| 2 | exponential congruences | both | Proposition 2.1: Assumption R follows from a bound `O(p)` on the collisions of `x^x - x` modulo `p`; a bound `p^(2-delta)`, the shifted analogue of the Cilleruelo-Garaev bound `p^(23/12)` for `x^x`, would give the rate `p^(-delta)`. Computed for all primes `11 <= p < 10^5`: the shifted map collides like a uniform random map, about `2(p-1)` pairs, while `x^x` follows the Holden-Moree prediction. Proposition 2.4: the last digits that go with a prime leading digit `p` have density `(1 + sum over d | p-1 of phi(d)/d) / p`. Corollary 2.5 (from Kurlberg, Luca and Shparlinski): for almost all primes `p` some `(p, c)` with `2 <= c <= p - 1` is a solution; for `p == 3 (mod 8)` with `(p-1)/2` prime none is. | proved; cited; computed; conjecture |
| 3 | sums of two squares, Landau, Hooley, Iwaniec | export | Theorem 3.1: base `b` has exactly `tau(b^2+1) - 2` two-digit narcissistic numbers (the fixed points of the happy-number map other than 1). Every odd base has at least 2; an even base has none exactly when `b^2 + 1` is prime, so "infinitely many empty bases" is Landau's problem. Infinitely many bases have at most 2 (Iwaniec). Proposition 3.3: the mean over odd bases is twice the mean over even bases, up to `O(1)`: `(4/pi) ln X` against `(2/pi) ln X`. The coincidence model gives a bounded mean; the local factors at the primes of `b^2 + 1` supply the `ln b`. | proved; cited; computed |
| 4 | other fields | analogies | cryptography, random mappings, covering systems, knapsack and lattice methods, fooling sets, singular series | analogy |

Library errors: one typo in Lemma 13.10, a confirmation for `round5-model.md`,
and one misprint in the literature
(section "Library corrections").

## 1. Anti-concentration: Assumption R in the limit

### 1.1 The question

The refined coupled model of section 13.2 draws, for each upper part `u`,
a random number with the right length and the right residue modulo
`q = b - 1`. Its Poisson theorem (Corollary 13.11) needs one input on the
weights. Write `g(x) = w(x) - x`, so `g(0) = m`, `g(1) = 0` and
`g(x) = x^x - x` for `x >= 2`. For a string `t`, let `R(t)` be the sum of
`g` over its digits. Lemma 13.10 needs, for `ceil(b/2) <= d <= b`,

    rho_d = max over r of P( R(t) == r (mod q) | A_d )

to be small, where `t` is a uniform string of `d - 1` digits and `A_d` is
the event that every digit `x` of `t` has `x^x < b^d`. (The original
statement conditions on the length event `G_d`. Theorem 3.2 of
`round5-model.md` shows that the product event `A_d`, which contains
`G_d`, is enough; the same reduction is used below.) Given `A_d`, the
`d - 2` digits after the leading one are independent and uniform on
`{0, ..., M_d}`, where `M_d` is the largest digit allowed.

Assumption R asks for `rho_d <= kappa / q`. The library and
`round5-model.md` attack it by equidistribution: every exponential sum
`sum over x of e(h g(x) / q)` must be smaller than its trivial bound. That
works where the digits cover many periods of `x mod p(p - 1)`
(Proposition 3.6 of `round5-model.md`), and it is open when `b - 1` has a
prime factor above `b^(2/3)`.

The Poisson limit needs less: `rho_d -> 0`, at any rate. That is an
anti-concentration statement, the subject of the Littlewood-Offord problem.
Erdos (1945) showed that a sum `sum e_i a_i` with random signs and
`|a_i| >= 1` takes no value with probability above about `n^(-1/2)`.
Halasz (1977) and Rogozin (1961) gave general concentration bounds, and
the inverse theorems of Tao and Vu (2009) and Nguyen and Vu (2011) say
that strong concentration forces the steps into a short generalized
arithmetic progression. The weights `x^x` give a very clean case: the
small digits have exact integer weights that grow so fast that their sums
determine their counts.

### 1.2 Small digits are dissociated

**Lemma 1.1** (proved). For every `z >= 3`, `g(z) >= 2 z g(z - 1)`.

Proof. `(z / (z-1))^(z-1) >= 2` for `z >= 2`, so
`z^z = z (z-1)^(z-1) (z/(z-1))^(z-1) >= 2z (z-1)^(z-1)`. Then
`z^z - z >= 2z (z-1)^(z-1) - z >= 2z ((z-1)^(z-1) - (z-1))`, since
`2z (z-1) >= z`.

The smallest ratio `g(z) / (2z g(z-1))` for `3 <= z < 400` is 1.238, at
`z = 5` (computed, `analysis/r6a_anticonc.py`).

**Lemma 1.2** (proved, dissociation). Let `2 <= z0 <= y`, `Z = {z0, ..., y}`
and `n <= 2 z0 + 1`. If two count vectors `c, c'` on `Z` have
`sum c_z = sum c'_z = n` and `sum c_z g(z) = sum c'_z g(z)`, then `c = c'`.
If moreover `n g(y) < Q`, the same holds for the sums modulo `Q`.

Proof. Suppose `c != c'` and let `w` be the largest `z` with
`c_z != c'_z`, say `c_w > c'_w`. Removing the common part above `w`, the
sums over `z <= w` agree. If `w = z0` this says `c_w g(w) = c'_w g(w)`,
a contradiction. If `w > z0`, the left side is at least
`(c'_w + 1) g(w)`, and the right side is at most
`c'_w g(w) + n g(w - 1) < c'_w g(w) + g(w)`, because
`g(w) >= 2w g(w-1) > n g(w-1)` by Lemma 1.1 and `2w >= 2 z0 + 2 > n`. A
contradiction again. Modulo `Q`: both sums lie in `[0, n g(y)]`, an
interval shorter than `Q`, so congruent sums are equal.

A brute-force check of all count vectors with `n <= 2 z0 + 1`, for
`y = 3, ..., 13` and `z0 = ceil((y+1)/2)`, finds no coincidence (computed).

### 1.3 The bound

Let `h(t) = t ln t - t + 1` for `t > 0` and `h(0) = 1`. The Chernoff
bounds for a sum `N` of independent Bernoulli variables with mean `mu`
read `P(N <= a) <= exp(-mu h(a/mu))` for `a <= mu` and
`P(N >= a) <= exp(-mu h(a/mu))` for `a >= mu` (cited: Janson, Luczak and
Rucinski, Random Graphs, Wiley 2000, Theorem 2.1).

**Theorem 1.3** (proved). Let `Q >= 2`, let `y >= 3` satisfy
`(y + 3) y^y < Q`, and put `z0 = ceil((y+1)/2)`, `J = y - z0 + 1` and
`n* = 2 z0 + 1`. Let `X_1, ..., X_k` be independent and uniform on
`{0, ..., M}` with `M >= y`, and `mu = k J / (M + 1)`. Then for every
residue `r` and every integer `1 <= n1 <= mu`,

    P( sum g(X_i) == r (mod Q) )
        <= exp(-mu h((n1 - 1)/mu)) + exp(-mu h((n* + 1)/mu))
           + max( n1! / J^n1, n*! / J^n* ).

If `J/2 <= mu <= J` and `J >= 11`, the right side is at most
`2 exp(-J/5)`.

Proof. Let `I` be the set of indices with `X_i` in `Z = {z0, ..., y}`, and
`N = |I|`, a binomial variable with mean `mu`. Condition on `I` and on the
values `X_i` for `i` not in `I`. Then the `X_i` with `i` in `I` are
independent and uniform on `Z`, and the event says that
`s = sum over i in I of g(X_i)` lies in one residue class modulo `Q`. If
`N = n <= n*`, then `0 <= s <= n* g(y) < (y + 3) y^y < Q`, because
`n* <= y + 3` and `g(y) < y^y`. So at most one value of `s` qualifies, and
by Lemma 1.2 at most one count vector of the values in `I`. A fixed count
vector has probability `n! / (prod c_z!) J^(-n) <= n! / J^n`. The function
`n -> n!/J^n` is log-convex (its ratio `(n+1)/J` increases), so on
`[n1, n*]` it is largest at an end. The two Chernoff bounds cover
`N <= n1 - 1` and `N >= n* + 1`.

For the second claim take `n1 = ceil(J/8)`. The lower tail
`mu h((n1-1)/mu)` increases with `mu` (its derivative is
`1 - (n1 - 1)/mu > 0`), so it is at least `(J/2) h(1/4) >= 0.2017 J`. The
upper tail decreases with `mu`, and `n* + 1 >= 2J + 2`, so it is at least
`J h(2) >= 0.386 J`. By Stirling, `n1!/J^n1 <= e^(-0.38 J + O(ln J))` and
`n*!/J^n* <= e^(-0.61 J + O(ln J))`, since `n* <= 2J + 3`. The sum is below
`2 e^(-J/5)` for every `J >= 11`; this was checked exactly for
`11 <= J <= 20,000`, and beyond that the last two terms are below
`e^(-J/5) / 2` by the exponents just given.

As `Q` grows, the largest admissible `y` is `(1 + o(1)) ln Q / ln ln Q`,
so `J = (1/2 + o(1)) ln Q / ln ln Q` and the bound is
`2 exp(-(1/10 + o(1)) ln Q / ln ln Q)`.

Table 1.1 (computed, `analysis/r6a_anticonc.py`,
`analysis/data/r6a_anticonc.txt`). The bound of Theorem 1.3, optimized
over `n1`, for `Q = 10^E` and `lambda = k/(M+1)`.

| `E` | `y` | `J` | bound, `lambda = 1/2` | bound, `lambda = 1` |
|---:|---:|---:|---:|---:|
| 10 | 9 | 5 | 0.90 | 0.89 |
| 30 | 21 | 11 | 0.090 | 0.036 |
| 100 | 56 | 28 | `5.7 * 10^-4` | `8.6 * 10^-6` |
| 300 | 138 | 69 | `9.1 * 10^-9` | `3.2 * 10^-13` |
| 1000 | 385 | 193 | `1.1 * 10^-23` | `2.1 * 10^-33` |

The bound is weak at sizes anyone will search: it says nothing below
`b = 10^10` and little below `10^30`. It is a limit theorem.

### 1.4 The refined Poisson law holds in the limit

**Lemma 1.4** (proved). Let `b >= 12` and `ceil(b/2) <= d <= b`. Then
`(M_d + 1)/2 <= d - 2 <= M_d + 1` and `M_d >= b/2`.

Proof. `(d-1)^(d-1) < b^d`, so `M_d >= d - 1`, which gives the right
inequality. `(b/2)^(b/2) < b^(b/2) <= b^d`, so `M_d >= b/2`. For the left
one, suppose `M = M_d >= 2d - 4`. Then `M >= b - 4`, and
`M^M < b^d <= b^((M+4)/2)` gives `M < b^(1/2 + 2/M) <= b^(3/4)`, which is
false for `b >= 12` (at `b = 12`, `8 > 6.45`, and `b - 4 - b^(3/4)`
increases).

**Theorem 1.5** (proved). Let `b >= 12`, `l = ceil(b/2)`, let `y(b)` be the
largest `y` with `(y + 3) y^y < b - 1`, and `J(b) = floor((y(b) + 1)/2)`.
In the refined coupled model of section 13.2,

    d_TV( (N_0, N_1), (Z_s + Z_0, Z_s + Z_1) )  <=  14.2 rho*(b) + 16 b^2 (b^2 - 1) l! / b^l,

where `rho*(b) = max over l <= d <= b of rho_d`, and `rho*(b) <= 2 e^(-J(b)/5)`
once `J(b) >= 11`. Hence `rho*(b) <= 2 exp(-(1/10 + o(1)) ln b / ln ln b)`,
and the refined coupled model has the bivariate Poisson law in the limit,
without Assumption R.

Proof. The proof of Lemma 13.10 bounds the refined `E[T]` by the sum over
`d` of `P(G_d and R == r_d)` for one residue `r_d` per length, where `R`
is the residue of the `d - 1` top digits of a uniform `d`-digit string.
Since `G_d` lies in `A_d`, each term is at most `P(A_d) rho_d`. The same
proof bounds the sum of `P(A_d)` over `d` by 7.1. So `E[T] <= 7.1 rho*(b)`
and `b_2 = 2 E[T] <= 14.2 rho*(b)`. The term `b_1` is as in Corollary
13.11, with the factor `b - 1` of the refined model. For the bound on
`rho_d`: condition on the leading digit. The other `k = d - 2` digits are
independent and uniform on `{0, ..., M_d}`, and `y(b) <= b/2 <= M_d`. By
Lemma 1.4, `mu = k J / (M_d + 1)` lies in `[J/2, J]`. Apply Theorem 1.3
with `Q = b - 1`.

Remarks.

- The two routes meet. For `12 <= b <= 6000`, Corollary 3.3 of
  `round5-model.md` gives the strong form, `kappa <= |H_0| + 5`. Above
  `10^29` Theorem 1.5 gives a weak form for every base. In between, only
  Conjecture 3.5 of `round5-model.md` speaks.
- The theorem never looks at `x^x` modulo a large prime. It uses about
  `ln b / ln ln b` small digits, whose weights are exact integers below
  `b`, and it works for any modulus. So it covers the joint residue modulo
  a composite `b - 1`, which `round5-model.md` leaves open (its new
  question 3), at the cost of the rate.
- The same bound with `Q = b^L` says that no string of `L` bottom digits of
  `S(c)` has probability above `2 e^(-J/5)`, with `J` about
  `L ln b / (2 ln(L ln b))`. It is a weak form of the bottom-digit
  uniformity that Table 24.6.1 measures (direction A5 of round 5).

### 1.5 Other weights

The proof uses three facts: the weights are integers, `g(z) >= c z g(z-1)`
for some `c > 1` beyond a point, and small weights are below `Q`. So
Theorem 1.3 holds, with other constants, for:

- `x^(x+t)` with fixed `t >= 0`: `g(z) / g(z-1)` grows like `e z^(1 + t/z)`;
- factorials `x! - x`: the ratio is about `z`. Take
  `z0 = ceil(2(y+1)/3)` so that `z > n*` on `Z`; then
  `J = (1/3 + o(1)) ln Q / ln ln Q`.

So a coupled model for factorions, built as in section 13.2, would have
its Poisson law in the limit for the same reason (proved for the bound;
the coupled model for factorions is not written out in the library).

The weights `x^d` of narcissistic numbers fail the third fact: `d` is
about the length, so `2^d` already exceeds `b - 1`. For them the residue
law is exact for a different reason, which also shows why `x^x` is hard.

**Proposition 1.6** (proved). For the weights `x^d`, let `k` digits be
independent and uniform on `Z/q` (the digits `0, ..., b-1` cover `Z/q`
once, with 0 twice). Then the residues of `sum (X_i^d - X_i)` modulo the
prime powers `p^e || q` are independent, and as `k -> infinity`

    q P( sum (X_i^d - X_i) == 0 (mod q) )  ->  product over p | q with (p-1) | (d-1) of p.

Proof. `x^d - x mod p^e` depends only on `x mod p^e`, and a uniform
residue mod `q` has independent uniform components (Chinese remainder
theorem). Modulo `p^e` the steps generate the subgroup `p^v Z/p^e`, where
`p^v` is the largest power of `p` (up to `p^e`) dividing every `x^d - x`.
Since `x^d == x (mod p)` for all `x` exactly when `(p-1) | (d-1)`, and
`p^d - p == -p (mod p^2)`, `v` is 1 in that case and 0 otherwise. The steps
take the value 0 (at `x = 0, 1`), so the sum is aperiodic on that
subgroup and tends to its uniform law.

This is the cell structure of section 19.4: all of `b - 1` is forced
exactly when `b - 1` is squarefree and `(p-1) | (d-1)` for every
`p | b - 1`, a Korselt-type condition. For `x^x` the residue modulo `p`
depends on `x mod p` and on `x mod (p - 1)`, and the second component ties
the primes of `b - 1` together. That coupling is what makes Assumption R
hard for `x^x` and trivial for `x^d`.

### 1.6 What would give the strong form

Theorem 1.3 is a forward Littlewood-Offord bound. The strong form,
`rho_d <= kappa / q`, is equidistribution. Between them sit the inverse
theorems: if a sum of independent steps hits one value with probability
`rho` much larger than `1/q`, the steps (most of them) lie in a short
generalized arithmetic progression modulo `q` (Tao and Vu 2009; Nguyen and
Vu 2011, for signed sums of fixed steps). Here the steps are random
choices among `M + 1` values, not signs, so the theorems do not apply as
stated (analogy). A version for this setting would reduce Assumption R to
showing that the values `x^x - x mod q`, `x <= M`, are not mostly in a
short progression, which is again a statement about `x^x` modulo large
primes.

## 2. The self-power map modulo a prime

### 2.1 What is known

The map `x -> x^x mod p` on `1 <= x <= p - 1` has a literature of its own,
which the library did not cite before `round5-model.md`.

- Crocker and Somer: the map takes at least `floor(sqrt((p-1)/2))` and at
  most `3p/4 + O(p^(1/2 + o(1)))` values (cited, as quoted in the papers of
  Balog, Broughan and Shparlinski and of Kurlberg, Luca and Shparlinski; I
  did not see the originals).
- Balog, Broughan and Shparlinski, "On the number of solutions of
  exponential congruences", Acta Arith. 148 (2011) 93-103 (arXiv
  1003.1997). The number `N(p; a)` of `x <= p - 1` with `x^x == a` is at
  most `p^(1/3 + o(1))` for `a = 1`, at most `p^(11/12 + o(1))` for a
  primitive root `a`, and at most `p^(12/13 + o(1))` uniformly. The number
  of collisions `x^x == y^y` is at most `p^(48/25 + o(1))`. They note that
  the map is used in some cryptographic protocols (Menezes, van Oorschot
  and Vanstone, Handbook of Applied Cryptography, sections 11.70 and
  11.71, as they cite it). (Cited; I read the arXiv version. This confirms
  the bound that `round5-model.md` quotes second hand.)
- Cilleruelo and Garaev (arXiv 1503.02730): `N(p; 1) <= p^(27/82 + o(1))`,
  and the collisions are at most `p^(23/12 + o(1))`, by bounds for
  exponential sums over subgroups due to Shkredov and Shteinikov (cited).
- Kurlberg, Luca and Shparlinski, "On the fixed points of the map
  x -> x^x modulo a prime", Math. Res. Lett. 22 (2015) 141-168 (arXiv
  1402.4464). For almost all primes there is a fixed point `x^x == x` with
  `2 <= x <= p - 1`. The number of fixed points is at most
  `p^(1/3 + o(1))`. They show that `p == 3 (mod 8)` with `(p-1)/2` prime
  has none, and that the map is far from a random map: more fixed points
  and shorter cycles (cited). Felix and Kurlberg, Finite Fields Appl. 48
  (2017) 141-159, sharpen the count of primes without one (cited, abstract
  only).
- Holden and Moree, "Some heuristics and results for small cycles of the
  discrete logarithm", Math. Comp. 75 (2006) 419-449. Their Conjecture
  6.4 (a) predicts the number of collisions `x^x == y^y`:
  `(p-1) + sum over m | p-1 of (phi(m)/m^2) (sum over d | (p-1)/m of phi(dm)/d)^2`
  (cited).
- Holden and Robinson, J. Aust. Math. Soc. 92 (2012) 163-178: counting
  solutions modulo `p^e` by Hensel's lemma and p-adic interpolation of
  `x^x` (cited). This is the method of Lemma 20.10 and Theorems 20.11 and
  20.12. The images `T(p^e)` of `x^x - x` over full periods
  (Theorems 20.8, 20.11, 20.12) are not in the papers above.

### 2.2 Assumption R as a collision count

**Proposition 2.1** (proved). Let `X_1, ..., X_k`, `k >= 2`, be independent
and uniform on `{0, ..., M}`, and `Q >= 2`. For every `r`,

    P( sum g(X_i) == r (mod Q) )  <=  N_M(Q) / (M + 1)^2,
    N_M(Q) = #{ (x, y) : 0 <= x, y <= M,  g(x) == g(y) (mod Q) }.

More generally `P(sum over 2j steps == r) <= P(S_j == S'_j)` for two
independent sums of `j` steps.

Proof. Condition on `X_3, ..., X_k`. With `nu` the law of `g(X_1) mod Q`,
the chance that `g(X_1) + g(X_2)` hits a given class is
`sum over a of nu(a) nu(v - a) <= sum over a of nu(a)^2` by Cauchy-Schwarz,
and `sum nu(a)^2 = N_M(Q) / (M+1)^2`. The general form is the same with the
two halves of the sum.

**Corollary 2.2** (proved). In the refined coupled model,
`E[T] <= 7.1 max over b/2 <= M <= b-1 of N_M(b-1) / (M+1)^2`. If
`N_(b-1)(b-1) <= C b`, then Assumption R holds with `kappa <= 4C`, and
if `N_(b-1)(b-1) <= b^(2 - delta)`, then `rho*(b) <= 4 b^(-delta)`.

Proof. Theorem 1.5, with Proposition 2.1 in place of Theorem 1.3, and
`N_M <= N_(b-1)`, `(M+1)^2 >= b^2/4`.

By Parseval, `N_M(Q) = (1/Q) sum over h of |sum over x <= M of e(h g(x)/Q)|^2`.
So Proposition 2.1 needs a mean-square bound for the exponential sums,
while the route of Theorem 3.2 of `round5-model.md` needs every sum to be
small. For `x^x` the mean square is exactly what Balog, Broughan and
Shparlinski and Cilleruelo and Garaev bound. The shifted analogue of their
bound, `#{x, y <= p-1 : x^x - x == y^y - y} <= p^(23/12 + o(1))`, would give
`rho*(b) <= b^(-1/12 + o(1))` for prime `b - 1`, far better than
Theorem 1.5.

Their method does not transfer as it stands. It writes `x^x == a` as
`x ind(x) == ind(a) (mod p - 1)`, a condition on discrete logarithms, and
counts with sum-product estimates. The shift breaks this:
`x^x - x == c` mixes the additive and the multiplicative structure. Only
`c = 0` stays multiplicative, `x^(x-1) == 1`, and that fibre is the set of
fixed points of Kurlberg, Luca and Shparlinski, of size at most
`p^(1/3 + o(1))`.

For composite `b - 1` Proposition 2.1 with two steps is poor: the residues
of `g` modulo small primes are far from uniform (modulo 3, five sixths of
the digits give 0), and two steps do not mix them. Over bases
`12 <= b <= 3000`, `max over M of (b-1) N_M / (M+1)^2` reaches 105 at
`b = 2521` (`b - 1 = 2^3 3^2 5 7`), while for the 426 bases with `b - 1`
prime it is between 2.57 and 4.18 (mean 3.07, at most 3.41 for `b >= 500`)
(computed, `r6a_selfpower.py digits`, `data/r6a_selfpower_digits.txt`).
So the collision route is the right one for the hard case, `b - 1` prime,
and the Fourier route of `round5-model.md` for smooth `b - 1`.

### 2.3 Collisions of x^x and of x^x - x (computed)

`analysis/r6a_selfpower.py collide` computes, for every prime
`11 <= p < 10^5`, the collisions `I(p)` of `x^x` and `N_g(p)` of
`g(x) = x^x - x` on `1 <= x <= p - 1`, the digit version `N_p(p)` on
`0 <= x <= p` (base `b = p + 1`), the largest fibre of `g`, and the number
`F(p)` of fixed points (the fibre of `g` over 0). Data:
`analysis/data/r6a_selfpower_collide.txt`, summary
`r6a_selfpower_collide_summary.txt`.

Table 2.1.

| primes `p` | count | `I(p) / HM(p)`: mean (min, max) | `I(p) / (p-1)` mean | off-diagonal `N_g(p) / (p-1)`: mean (min, max) | `N_p(p) / (p+1)` mean (max) | mean `F(p)` (max) | share with largest fibre = `F(p)` |
|---|---:|---|---:|---|---|---|---:|
| 11 to 999 | 164 | 0.977 (0.734, 1.230) | 2.56 | 1.054 (0.857, 1.429) | 2.130 (3.000) | 4.7 (15) | 0.51 |
| 1,000 to 9,999 | 1,061 | 0.997 (0.948, 1.049) | 2.64 | 1.015 (0.925, 1.319) | 2.022 (2.382) | 7.6 (33) | 0.56 |
| 10,000 to 49,999 | 3,904 | 1.000 (0.968, 1.021) | 2.64 | 1.004 (0.957, 1.088) | 2.006 (2.099) | 9.2 (48) | 0.55 |
| 50,000 to 99,999 | 4,459 | 1.000 (0.989, 1.012) | 2.64 | 1.002 (0.981, 1.052) | 2.003 (2.055) | 10.4 (51) | 0.57 |

`HM(p)` is the prediction of Holden and Moree, `N_p(p)` uses `0^0 = 0`
(the values under `0^0 = 1` differ by less than 0.01).

Three observations.

- The Holden-Moree prediction for `x^x` holds within 1.2% for every prime
  above 50,000 and within 0.03% on average (computed). I found no earlier
  check at this range; their paper reports data for smaller primes. The
  collisions of `x^x` are about `2.64 (p - 1)`.
- The shifted map has `N_g(p) - (p - 1)`, the off-diagonal collisions,
  within 0.2% of `p - 1` on average above 50,000, and within 5.2% for every
  such prime: the value of a uniform random map. The order structure that inflates the collisions of `x^x` (a value
  of small order has many preimages) is gone after the shift.
- The largest fibre of `g` is the fixed-point fibre for only 51% to 57% of
  the primes (computed). Other fibres `x^x == x + c` are often larger, and no
  bound for them is known. The largest fibres are larger than for a random
  map (about `ln p / ln ln p`, near 5 here): the maximum over `p < 10^5` is
  51, and it is a fixed-point fibre, large when `p - 1` has many divisors,
  as Kurlberg, Luca and Shparlinski explain. These fibres are too rare to
  move the collision count.

A full-period model of the shift, with `u = x mod p` and
`v = x mod (p - 1)` independent (the analogue of the Holden-Moree
heuristic), predicts off-diagonal collisions of `1.12 (p - 1)` on average
over the 121 primes `11 <= p <= 700`, against `1.06 (p - 1)` observed, with
a per-prime correlation of only 0.22 (computed, `r6a_selfpower.py model`).
So for the shift the plain random map is the better model. A guess
(heuristic): the excess of the full-period model comes from units of small
order, and on the range `x <= p - 1`, where `u = v = x`, these are not
paired with the exponents that make them collide.

**Conjecture 2.3.** `N_g(p) = (2 + o(1)) (p - 1)` as `p -> infinity`. By
Corollary 2.2 this gives Assumption R with `kappa <= 8 + o(1)` for every
base with `b - 1` prime; the computed constants of section 2.2 are near 3.

A weaker target suffices for every rate that the library uses:
`N_g(p) <= p^(2 - delta)` for some `delta > 0`.

### 2.4 Two-digit solutions are fixed points of x -> x^x

Proposition 2.6 says that `(a, c)` is a 2-digit solution exactly when
`a | w(c) - c` and the base `(a^a + w(c) - c)/a` exceeds `a` and `c`. For
`c >= 1` the condition is `c^c == c (mod a)`: the last digits that go with
the leading digit `a` are the fixed points of the self-power map modulo
`a`, which is the object of Kurlberg, Luca and Shparlinski. The base is
then about `a^(a-1)` or `c^c / a`, so the size condition holds except for
small digits.

**Proposition 2.4** (proved). Let `p` be prime. Among the integers `c >= 1`,
those with `c^c == c (mod p)` are periodic modulo `p (p - 1)` and have
density

    f(p) = ( 1 + sum over d | p-1 of phi(d)/d ) / p,

where `sum over d | n of phi(d)/d = product over l^a || n of (1 + a (1 - 1/l))`.

Proof. The residue `c^c mod p` depends on `u = c mod p` and
`v = c mod (p-1)`, and `(u, v)` runs over all pairs as `c` runs over a
period. If `u = 0`, `c^c == 0 == c`: `p - 1` pairs. If `u != 0`, the
condition is `u^(v-1) == 1`, that is `ord(u) | v - 1`, which holds for
`(p-1)/ord(u)` values of `v`. There are `phi(d)` units of order `d`, so the
count is `(p - 1) sum over d | p-1 of phi(d)/d`. Divide by `p (p - 1)`.

The formula agrees with a direct count for every prime `p <= 200`
(computed, `analysis/r6a_twodigit.py`). For `p = 3` it gives 5/6: the
last digits `c == 0, 1 (mod 3)` and the odd `c == 2 (mod 3)`.

**Corollary 2.5** (proved from cited results). Call `(p, c)` with `p`
prime and `2 <= c <= p - 1` a small partner of `p`. Under both conventions:

1. For almost all primes `p` (all but `o(pi(X))` up to `X`), some small
   partner `(p, c)` is a 2-digit solution, in base `(p^p + c^c - c)/p`.
2. If `p == 3 (mod 8)` and `(p - 1)/2` is prime, no small partner is a
   solution.
3. At most `p^(1/3 + o(1))` small partners are solutions.

Proof. A small partner is a solution exactly when `c^c == c (mod p)`, and
the base is above `p^(p-1) - 1 > max(p, c)`; zeros do not occur, so the
convention plays no role. Part 1 is the main theorem of Kurlberg, Luca and
Shparlinski, part 3 their bound (3) (from Balog, Broughan and
Shparlinski). Part 2 is their argument: `c^(c-1) == 1` forces
`ord(c) | gcd(c - 1, p - 1)`, so the order is 2 or `(p-1)/2`; order 2
means `c = p - 1`, which fails; order `(p-1)/2` with
`(p-1)/2 | c - 1 < p - 1` means `c = (p+1)/2`, and then
`1 == c^(c-1) == 2^(-(p-1)/2) == (2/p)`, false for `p == 3 (mod 8)`.

Computed (`r6a_twodigit.py`): 146 of the 2,261 odd primes below 20,000
have no small partner; 90 of them are of the form in part 2. Among the
first 1,000 primes there are 72, as Kurlberg, Luca and Shparlinski say,
but their printed list starts `3, 5, 7, 11, 53`, and 7 does not belong:
`4^4 == 4 (mod 7)`. OEIS A233518 lists 7 correctly among the primes with a
nontrivial fixed point.

The census share. Section 2.4 of the library counts 2-digit solutions with
digits up to 60, and "Problems found" (4) of `questions-round6.md` gives
the shares of all pairs `(a, c)` that are solutions: 35% up to 60, 21% up
to 200, 12.5% up to 600. The densities `f(a)` predict them.

Table 2.2 (computed, `r6a_twodigit.py`, `0^0 = 1`). Share of the pairs
`1 <= a <= Y`, `0 <= c <= Y` that are solutions, against
`(1/Y) sum over a <= Y of f(a)`, where `f(a)` is the density of
`c^c == c (mod a)` over a full period.

| `Y` | census share | mean of `f` |
|---:|---:|---:|
| 20 | 0.524 | 0.576 |
| 40 | 0.420 | 0.443 |
| 60 | 0.353 | 0.374 |
| 100 | 0.291 | 0.299 |
| 200 | 0.212 | 0.217 |
| 300 | 0.175 | 0.178 |

The share falls like `Y^(-0.44)` over this range. Its asymptotics are a
mean-value problem for the fixed-point density `f(a)`, which is not
multiplicative (the exponent couples the primes of `a`). For primes, the
average of `sum over d | p-1 of phi(d)/d` grows like `ln p` (heuristic:
`d | p - 1` with probability `1/phi(d)`), so `f(p)` is about `ln p / p` on
average.

### 2.5 What transfers and what does not

- From the literature to the library: Corollary 2.5 (proved), the method of
  Lemma 20.10 (already used, now with a source), the collision bounds for
  `x^x` (no direct use: Assumption R needs the shifted map).
- From the library to the literature: the full-period images of `x^x - x`
  modulo `3^e` and `5^e` (Theorems 20.11, 20.12), Conjecture 2.3 with its
  data, and the observation that the shifted map is random-like where `x^x`
  is not.
- Cryptography (analogy). Collision counts of `x^x` matter for signature
  schemes that use it, as Balog, Broughan and Shparlinski explain. Nothing
  in the library bears on those schemes.

## 3. Two-digit narcissistic numbers and the divisors of b^2 + 1

### 3.1 The count

A 2-digit narcissistic number in base `b` is `n = s1 b + s0` with
`1 <= s1 <= b - 1`, `0 <= s0 <= b - 1` and `n = s1^2 + s0^2`. The same
numbers are the 2-digit fixed points of the happy-number map `S_2` (sum of
the squares of the digits). As in Proposition 1.3, each digit string is a
solution in at most one base, `b = s1 + s0 (s0 - 1)/s1`; this
parametrization appears on the Wikipedia page "Perfect digital invariant".
I did not find the count below stated anywhere.

**Theorem 3.1** (proved). For every `b >= 2`, base `b` has exactly
`tau(b^2 + 1) - 2` two-digit narcissistic numbers. Together with 0 and 1
they are all the fixed points of `S_2` in base `b`.

Proof. Multiply `s1 b + s0 = s1^2 + s0^2` by 4 and complete the squares:

    (2 s1 - b)^2 + (2 s0 - 1)^2 = b^2 + 1.

Put `N = b^2 + 1`, `A = 2 s1 - b` and `B = 2 s0 - 1`. A solution gives a
representation `N = A^2 + B^2` with `B` odd, `B >= -1`, `A == b (mod 2)`
and `|A| <= b - 2`. Conversely take any representation with `B` odd and
`B > 0`. Then `A == b (mod 2)`, since `A^2 = b^2 + 1 - B^2 == b^2 (mod 2)`.
If `B = 1`, then `A = +-b`, which no digit gives. If `B >= 3`, then
`A^2 < b^2` and `A == b (mod 2)`, so `|A| <= b - 2` and `s1` is a digit;
and `B <= sqrt(N) <= 2b - 3` for `b >= 3`, so `s0` is a digit. `B = -1`
gives `A = +-b` again. So the solutions are the representations with `B`
odd and positive, minus the two with `B = 1`.

Count them with `r_2(N) = 4 sum over d | N of chi(d)`, `chi` the character
modulo 4. Every odd prime factor of `b^2 + 1` is `1 (mod 4)`, and `4` does
not divide it. If `b` is even, `N` is odd, every divisor has `chi = 1`, so
`r_2(N) = 4 tau(N)`; exactly one of `A, B` is odd, and swapping `A` and `B`
shows that half of the representations have `B` odd, half of those `B > 0`:
`tau(N)` of them. If `b` is odd, `N = 2N'` with `N'` odd, `A` and `B` are
both odd, `r_2(N) = 4 tau(N')`, and half have `B > 0`: `2 tau(N') = tau(N)`.
Subtract 2. For the fixed points: a number with `k >= 4` digits has
`S_2(n) <= k (b-1)^2 < b^(k-1) <= n`. With 3 digits and leading digit
`s2 >= 2`, `S_2(n) <= s2^2 + 2(b-1)^2 < s2 b^2 <= n`; with `s2 = 1`,
`n = S_2(n)` reads `b^2 - 1 = s0 (s0 - 1) - s1 (b - s1) <= (b-1)(b-2)`,
impossible. One digit: `x^2 = x`. (`b = 2` by hand: `N = 5`, count 0.)

Computed: a brute force over all digit pairs agrees for every `b <= 400`
(`analysis/r6a_narc2.py`). Base 10 has none, since 101 is prime, as is
well known (OEIS A005188 starts 1, ..., 9, 153).

### 3.2 Consequences

**Corollary 3.2** (proved, with cited results).

1. Every odd base `b >= 3` has at least two 2-digit narcissistic numbers:
   `b^2 + 1 = 2N'` with `N' > 1`, so `tau(b^2+1) >= 4`.
2. An even base has none exactly when `b^2 + 1` is prime. So "infinitely
   many bases have no 2-digit narcissistic number" is equivalent to
   Landau's problem, whether `n^2 + 1` is prime infinitely often (for
   `n > 1` a prime `n^2 + 1` needs `n` even). It is open.
3. Infinitely many bases have at most two: Iwaniec (Invent. Math. 47
   (1978) 171-188) proved that `n^2 + 1` has at most two prime factors for
   infinitely many `n`, and then `tau(n^2+1) <= 4`.
4. The mean over `b <= X` is `(3/pi) ln X + O(1)`: Hooley (Acta Math. 110
   (1963) 97-114) proved `sum over n <= X of tau(n^2+1) = (3/pi) X ln X + O(X)`
   (cited, constant as quoted by later papers). So a typical base has about
   `ln b` of them, and the count is unbounded on average.

### 3.3 The parity doubling is exact

**Proposition 3.3** (proved). Let `S_0(X)` and `S_1(X)` be the sums of
`tau(n^2 + 1)` over the even and over the odd `n <= X`. Then
`S_1(X) = 2 S_0(X) + O(X)`. With Hooley's theorem, the mean number of
2-digit narcissistic numbers is `(2/pi) ln X + O(1)` over even bases and
`(4/pi) ln X + O(1)` over odd bases.

Proof. `n^2 + 1` is never a square for `n >= 1`, and its divisors pair up
as `d, (n^2+1)/d` with exactly one of them at most `n`. So
`tau(n^2+1) = 2 #{d <= n : d | n^2 + 1}`. Let `rho(d)` be the number of
roots of `x^2 == -1 (mod d)`. Then

    S_e(X) = 2 sum over d <= X of #{ d <= n <= X : n == e (mod 2), n^2 == -1 (mod d) }.

For odd `d`, each root class modulo `d` splits evenly between the two
parities modulo `2d`, giving `(X - d)/(2d) + O(1)` integers of each
parity. For even `d`, `d = 2d'` with `d'` odd (4 never divides
`n^2 + 1`), the condition forces `n` odd, `rho(2d') = rho(d')`, and each
root class gives `(X - d)/d + O(1)` odd integers. Since
`sum over d <= X of rho(d) = O(X)`,

    S_0(X) = X A(X) + O(X),   S_1(X) = X A(X) + X A(X/2) + O(X),

with `A(Y) = sum over odd d <= Y of rho(d)/d`. And
`A(X) - A(X/2) = sum over X/2 < d <= X of rho(d)/d = O(1)`. So
`S_1 = 2 S_0 + O(X)`. Hooley's total `S_0 + S_1 = (3/pi) X ln X + O(X)`
then gives `A(X) = (1/pi) ln X + O(1)`, and the means follow, each parity
class holding `X/2 + O(1)` bases.

This is the parity doubling of section 5.3 as a theorem. In the refined
model the factor 2 for odd bases comes from the free residue modulo 2:
`x^2 == x (mod 2)` for every digit. Here the same factor appears as the
contribution of the prime 2 to `tau(b^2 + 1)`, which divides `b^2 + 1`
exactly when `b` is odd.

Table 3.1 (computed, `analysis/r6a_narc2.py`, `data/r6a_narc2.txt`).
Means of `tau(b^2 + 1) - 2` over even and odd `b <= X`.

| `X` | mean, even `b` | `(2/pi) ln X` | mean, odd `b` | `(4/pi) ln X` | ratio of the means of `tau` | even `b` with none |
|---:|---:|---:|---:|---:|---:|---:|
| `10^2` | 1.720 | 2.932 | 5.102 | 5.863 | 1.909 | 36.0% |
| `10^3` | 3.136 | 4.398 | 7.896 | 8.795 | 1.927 | 22.2% |
| `10^4` | 4.630 | 5.863 | 10.797 | 11.727 | 1.930 | 16.8% |
| `10^5` | 6.088 | 7.329 | 13.735 | 14.659 | 1.945 | 13.3% |
| `10^6` | 7.555 | 8.795 | 16.670 | 17.590 | 1.954 | 10.8% |

Both means grow by `(2/pi) ln` and `(4/pi) ln` to within 2% per factor
`sqrt(10)` from `10^3` on; the constant terms are about -1.2 and -0.9. The
ratio of the means of `tau` tends to 2 slowly, as the `O(X)` error of
Proposition 3.3 allows. A brute force over all digit pairs agrees with
`tau(b^2+1) - 2` for `b <= 400`, and the sieve for `tau` agrees with a
factorization for `b <= 3000`.

### 3.4 What the coincidence model misses at length 2

The basic model of chapter 5 gives a 2-digit string the chance that
`s1^2 + s0^2` has two digits, which tends to `pi/4` (a quarter disc). The
refined model multiplies this by `b - 1` times the share of digit pairs
with `s1^2 - s1 + s0^2 - s0 == 0 (mod b - 1)`. For two digits that factor
is a product of local factors over the primes of `b - 1` (a conic count
modulo each prime power), about 2 from the prime 2 in odd bases and
`1 - chi(p)/p` from an odd prime `p`; its mean over `b` is bounded. So the
model predicts a bounded mean, while the truth is `(2/pi) ln b` and
`(4/pi) ln b`: the model is short by a factor of order `ln b` in both
parities. For bases 3 to 14 the 2-digit
counts sum to 22, against 14.4 in the refined model and 9.0 in the basic
model (computed). That is 7.6 of the 42.7 excess that section 19.4 found
for lengths `d <= 5` (126 against 83.3), and the same ratio, 1.5.

The missing factor is a product of local factors, as direction A2 of
`questions-round6.md` proposes for every short length. The number of
digit pairs with `s1 b + s0 == s1^2 + s0^2 (mod l)` is the number of points
of the conic `A^2 + B^2 == b^2 + 1 (mod l)`. For an odd prime `l` not
dividing `b^2 + 1` it is `l - chi(l)`, a factor `1 - chi(l)/l` against
`l`. For `l == 1 (mod 4)` dividing `b^2 + 1` the conic is the pair of lines
`A = +-i B`, with `2l - 1` points, a factor `2 - 1/l`. So each prime of
`b^2 + 1` roughly doubles the expected count, which is how `tau(b^2 + 1)`
arises (proved for the local counts; that their product, with the area
term, reproduces `tau` on average is the content of Hooley's theorem).
The coincidence model keeps only the residue modulo `b - 1` and misses
every one of these factors.

## 4. Analogies

Connections that I checked but could not turn into a transfer with a proof.
Each is labeled analogy.

1. Random mappings (analogy). Kurlberg, Luca and Shparlinski find that
   `x -> x^x mod p` has more fixed points and shorter cycles than a random
   map. Section 26.7 finds that `F` has a smaller image than a random map.
   In both cases the map factors through a coarser object (the order of `x`;
   the digit multiset), which a random-mapping model must keep. Section 2.3
   adds a third case: after the shift `x^x - x` the collisions are those of
   a random map.
2. Covering systems (analogy, noted in section 11.3). The coverings of
   section 15.4 exclude strings in every base by congruences modulo powers
   of 2 and 3, as Sierpinski excluded primes `k 2^n + 1`. The modern theory
   of coverings (minimum modulus, Hough 2015) is about distinct moduli and
   does not apply to these.
3. Knapsack and lattice methods (analogy, with a count). By section 1.3 a
   `d`-digit solution is a choice of one digit per position with balances
   summing to 0: a multiple-choice subset sum with `b^d` choices and weights
   of about `d log2 b` bits, density near 1. Lattice attacks need density
   well below 1 (Lagarias and Odlyzko 1985), and the generic algorithms for
   density-1 knapsacks cost `2^(c d log2 b)` with `c` near 0.3, that is
   `b^(0.3 b)`. The tree beats this by working with the `4^b` multisets and
   the ordering of `x^x`, which a knapsack algorithm does not see.
4. Fooling sets (identification). Theorem 27.5 is a fooling-set lower bound
   in the sense of communication complexity (Kushilevitz and Nisan,
   Communication Complexity, 1997): `N_k` vectors, no two in one failing
   cylinder. Nothing new follows.
5. Singular series (analogy turned exact in section 3). Direction A2 of
   round 6 reads the root heuristic as a Hardy-Littlewood singular series.
   Section 3.4 is the simplest exact instance. For 3-digit narcissistic
   numbers the equation is a cubic surface in the digits for each `b`, and
   I did not find an analogue of Theorem 3.1.
6. Function fields (identification). Theorem 21.6 and Lemma 2.1 of
   `round5-model.md` are additive Hilbert 90 for the Frobenius of
   `F_q[T]/(B - 1)`; the weights `d^|d|` are additive (linearized)
   polynomials in the digits.
7. S-unit and perfect-power equations (analogy). Self-paying digits solve
   `a^(a-1) = b^k`, a perfect-power equation, and the identity families of
   chapters 22 and 25 use that `x^x` is a `j`-th power on a progression,
   like the families of Ko and Mills for `x^x y^y = z^z` (cited in 9.10).
   The Munchausen equation has many terms, and S-unit theorems bound the
   number of terms that can be nondegenerate, not their count; I found no
   transfer.

## Library corrections

1. Section 13.2.4, proof of Lemma 13.10: "In the refined model each value has
   probability at most `1/b^(d-2)`, that is `b - 1` times more". The refined
   `Y_u` is uniform on a residue class of `b^(d-1)` numbers, so each value has
   probability `1/b^(d-1)`, which is `b - 1` times the basic
   `1/((b-1) b^(d-1))`. The exponent `d - 2` is a typo; the conclusion
   `7.1 kappa / b` is right.
2. `round5-model.md`, section 3.5, quotes the uniform bound
   `p^(12/13 + o(1))` of Balog, Broughan and Shparlinski second hand. It is
   in their paper (arXiv 1003.1997, bound (2)), together with
   `M(p) <= p^(48/25 + o(1))` for the collisions.
3. Not in the library, but used here: the list (4) of primes without a
   nontrivial fixed point in Kurlberg, Luca and Shparlinski includes 7, and
   `4^4 == 4 (mod 7)`. Their count of 72 among the first 1,000 primes is
   right without it.

## Files

| file | content |
|---|---|
| `analysis/r6a_lib.py` | vectorized `x^x mod q`, the map `g`, small number theory |
| `analysis/r6a_anticonc.py` | Lemma 1.1 check and Table 1.1; data `r6a_anticonc.txt` |
| `analysis/r6a_selfpower.py` | `collide`: Table 2.1, data `r6a_selfpower_collide.txt` and `_summary.txt`; `model`: the full-period heuristic for the shifted map, `r6a_selfpower_model.txt`; `digits`: the constants of section 2.2, `r6a_selfpower_digits.txt` |
| `analysis/r6a_twodigit.py` | Proposition 2.4 check, Table 2.2, primes without small partners; data `r6a_twodigit.txt` |
| `analysis/r6a_narc2.py` | Theorem 3.1 check and Table 3.1; data `r6a_narc2.txt` |

The draft is not yet in `lean/` or `docs/exposition/`. Lemma 1.1, Lemma 1.2,
Lemma 1.4, Proposition 2.4 and Theorem 3.1 are elementary and natural
candidates for formalization.

## New questions

1. The shifted collision problem. Prove
   `#{x, y <= p - 1 : x^x - x == y^y - y (mod p)} <= p^(2 - delta)`. By
   Corollary 2.2 this gives Assumption R with a power rate for prime
   `b - 1`. The method of Cilleruelo and Garaev handles `x^x`; the shift
   needs a new idea for the fibres `x^x == x + c`, `c != 0`.
2. An inverse Littlewood-Offord theorem for random choices. If a sum of
   `k` independent steps, each uniform on a fixed multiset of `M` residues
   modulo `q`, hits one class with probability above `K/q`, must most of
   the multiset lie in a short progression? With such a theorem, Assumption
   R would follow from a non-concentration statement for `x^x - x` alone.
3. The rate of Theorem 1.5. Can the dissociation argument use the digits
   near `b`, whose weights are known modulo a prime `b - 1 = p`
   (`(p - t)^(p-t) == (-t)^(1-t)`), to push `rho*(b)` below a power of `b`
   in that case?
4. Two-digit census. What is the asymptotic of
   `(1/Y) sum over a <= Y of f(a)`, the density of fixed points of
   `x -> x^x mod a` averaged over `a`? The data suggest `Y^(-0.44)` on
   `Y <= 300`.
5. Three-digit narcissistic numbers. Is there an exact count, or an
   average order, for `s2 b^2 + s1 b + s0 = s2^3 + s1^3 + s0^3`? The model
   says a bounded mean; a cubic surface suggests local factors again.
6. A coupled model for factorions. Write the model of section 13.2 for the
   weights `x!` and check that Theorem 1.3 gives its Poisson limit, as
   section 1.5 claims.
