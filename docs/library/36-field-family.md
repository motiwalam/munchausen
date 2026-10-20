# 36. Three digits when the field changes

This chapter attacks the open regime of section 32.1.6: 3-digit strings
with two small digits and one large digit `x`, where the quadratic field of
the Pell equation changes with `x`. It answers questions 129 and 130 for
the last position, and it explains why the middle and leading positions are
harder.

Labels: proven (a proof is here, with cited inputs named), cited, computed
(a stated computation), proven and computed, heuristic, conditional.
Scripts are `analysis/r6f_ff_*`, data `analysis/data/r6f_ff_*`. The runs
used at most 3 threads.

Refereeing. The chapter began as a draft. Before it entered the library
every proof was checked line by line, the cited theorems were compared with
their statements in the literature, the bounds `X_A(p)` and `X_B(p)` were
recomputed from the inequalities by a separate script, and a slice of each
computation was rerun by a different method (section 36.7). No gap was
found in the proofs. A few hypotheses and constants are stated more
carefully than in the draft, and one numerical claim of Proposition 36.12
is labelled as computed at sample points only.

## Summary

| result | status |
|---|---|
| In the last position with `x` odd and `x > W + q^2/(4p)`, the equation is `U^2 + D = 4p x^x` with `D > 0`. In the imaginary field `Q(sqrt(-D))`, `x^x` is an `x`-th power and there are no units of infinite order. | proven (Lemma 36.1) |
| If the ideal `J` of norm `p` in `(mu) = J A^x` is ambiguous, primitive divisors of Lehmer numbers give `x <= X_A(p)`: 7,618 for `p = 1`, at most 340,896 for `p <= 20`, for every `q` | proven (Theorem 36.5) |
| `(1, q, x)` with `x` odd, `x > w(q) + 1 + q^2/4` and `x` prime to `q^2 + 4 + 4w(q)` is a solution only for `(1, 0, 3)` in base 5 (`0^0 = 0`), for every `q`. The same holds for odd `p <= 20` under explicit congruence conditions | proven and computed (Corollaries 36.6, 36.7) |
| For every `J`, a reduced lattice basis and Matveev's bound for three logarithms give `x <= X_B(p)`, about `8.2 * 10^38` to `2.4 * 10^40` for `p <= 20`, uniform in `q` | proven, effective (Theorem 36.9) |
| So for fixed `p, q` the string `(p, q, x)` is a solution for only finitely many `x`, of either parity, with an effective bound | proven (Corollary 36.10) |
| Middle position, `x` odd: every prime `l` of `x` with `l` prime to `2pA` has `(pA / l) = 1`. If `pA` is not a square (415 of the 440 families with `p, q <= 20`), the `x` that can occur have density 0 | proven (Proposition 36.11) |
| Leading position, `x` even, `x = n f^2`: the 2-adic bound of Theorem 32.2 holds with the unit of `Q(sqrt n)`, so the square part `f^2` of a solution is small, at most `4.5 * 10^9` for `x = 10^20` | proven, weak (Proposition 36.12); superseded by Theorem 38.6, which bounds every even leading `x` |
| Sieve: last position, `p, q <= 10`, odd `x` up to `max(X_A(p), W + q^2/(4p))`, up to `10^10`; all three open cases with small digits up to 20 and `x <= 10^8`, the middle and leading cases to `10^9`. Only known solutions and `R = 0` strings survive | computed (Proposition 36.8, section 36.5) |
| Why the middle and leading positions resist: in a real field the regulator enters every height. Middle: `h Reg` is about `x`. Leading: `Reg` is about `sqrt(x)` | proven sizes, measured (section 36.4.3); the leading case was finished in chapter 38 (Theorem 38.6) |
| Corrections: section 32.1.6 ("the only obstacle"), section 25.1.4 (what remains open), the constant in the proof sketch of Theorem 32.5 | section "Library corrections" |

## 36.1 The switch to the field of R

### 36.1.1 Setting

Notation of chapters 25 and 32: `w(0) = m`, `w(d) = d^d` for `d >= 1`. For
a 3-digit string with small digits and one large digit `x`, completing the
square gives `U^2 = N + R` with `N = 4 l x^x` (`l` the leading digit). The
open regime of section 32.1.6 has three cases:

| case | string | `U` | `U^2 - R` | `R` | field of `R` |
|---|---|---|---|---|---|
| L: last, `x` odd | `(p, q, x)` | `2pb + q` | `4p x^x` | `q^2 + 4p (W - x)` | imaginary once `x > W + q^2/(4p)` |
| M: middle, `x` odd | `(p, x, q)` | `2pb + x` | `4p x^x` | `x^2 + 4pA` | real, discriminant about `x^2` |
| Lead: leading, `x` even | `(x, q, r)` | `2xb + q` | `4 x^(x+1)` | `q^2 + 4xA` | real, discriminant about `4Ax` |

Here `W = w(p) + w(q)` and `A = w(p) + w(q) - q` (middle) or
`A = w(q) + w(r) - r` (leading).

Chapter 32 wrote these as Pell equations `U^2 - n V^2 = R` with `n` the
squarefree part of `4 l x^x`. There `V` is a power of `x` but carries no
useful structure, the field `Q(sqrt n)` changes with `x`, and its regulator
can be as large as `sqrt(x) log x`. The idea of this chapter is to factor
in the other field, `Q(sqrt R)`. There `4 l x^x` is a constant times an
`x`-th power (an `(x+1)`-th power in the leading case), and `U^2 - R` is a
norm. This is the setting of the Lebesgue-Nagell equation
`X^2 + D = C Y^n`, with the twist that `Y = n = x` and `D` grows with `x`.

In case L the constant `R` becomes negative as soon as `x` passes
`W + q^2/(4p)`, and the field is imaginary. An imaginary quadratic field
has no units of infinite order, and its class number is about `sqrt(|R|)`,
so about `sqrt(x)`, far below the exponent `x`. Both facts are what the
real Pell form lacked. Cases M and Lead stay real.

### 36.1.2 The ideal equation

Fix case L. Let `x` be odd and put

    D = 4p (x - W) - q^2 > 0,   U^2 + D = 4p x^x,   U = 2pb + q.

Let `K = Q(sqrt(-D))`, `D = f^2 D0` with `D0` squarefree, and

    mu = (U + sqrt(-D)) / 2,    N(mu) = p x^x,    mu - mu' = f sqrt(-D0),

where `'` is complex conjugation. `U` and `D` have the parity of `q`, and
`D == -q^2 (mod 4)`, so `mu` is in the ring of integers `O_K`.

Lemma 36.1 (proven). Suppose `x > 2 log2(pD)`. Then:

- (a) every prime `l` dividing `x` splits in `K`;
- (b) `(mu) = J A^x`, where `A` is an integral ideal of norm `x` with
  `A + A' = O_K`, and `J` is a fractional ideal with
  `s(J) = sum over P of |v_P(J)| log N(P) <= log(pD)`;
- (c) if `gcd(x, D) = 1`, then `J` is integral of norm `p` and lives above
  the primes of `p`.

Proof. Every prime ideal `P` with `P | mu` and `P | mu'` divides
`mu - mu' = sqrt(-D)`, so `min(v_P(mu), v_P(mu')) <= v_P(sqrt(-D))`.

Let `l | x`; `l` is odd. If `l` ramifies, `P = P'` and
`v_P(mu) = v_l(N(mu)) >= x`, while `v_P(sqrt(-D)) = v_l(D) <= log_3 D < x`.
If `l` is inert, `v_P(mu) = v_P(mu') >= x/2`, while
`v_P(sqrt(-D)) = v_l(D)/2 < x/2`. Both are impossible, which is (a).

For split `l | x` with primes `L, L'`:
`v_L(mu) + v_L'(mu) = v_l(p) + x v_l(x)`, and the smaller of the two is at
most `v_l(D)/2`. Round each valuation `v_P(mu)` to the nearest multiple of
`x`; put the multiples into `A^x` and the remainders into `J`. Since
`v_l(p) + v_l(D) <= log_3(pD) < x/2`, the larger valuation rounds to
`x v_l(x)` and the smaller to 0. So `A` has one prime above each `l | x`,
with exponent `v_l(x)`: `N(A) = x` and `A + A' = O_K`. If `a` is the
smaller valuation, the remainders at `L, L'` are `a` and `v_l(p) - a`,
with absolute values summing to `max(v_l(p), 2a - v_l(p))`, at most
`max(v_l(p), v_l(D))`. Primes above `l | p` with `l` prime to `x`
contribute `v_l(p) log l` to `s(J)` in each splitting type. Summing gives
`s(J) <= log p + log D = log(pD)`, which is (b).

Correction (Lean formalization, 2026-10-20). The proof said that the
remainders at `L, L'` sum to at most `v_l(p) + v_l(D)/2`, giving
`s(J) <= log p + (1/2) log D`. That fails when `l` divides `D` but not
`p`: the remainders are then `a` and `-a` with `a` up to `v_l(D)/2`,
summing to `v_l(D)`. The per-prime bound is `max(v_l(p), v_l(D))`, as
above, and the statement of (b), `s(J) <= log(pD)`, which is what Theorem
36.9 uses, is unchanged. `lemma36_1_round` in
`lean/Munchausen/FieldFamily.lean` proves the corrected bound (chapter
38, item 7 of its corrections). If `gcd(x, D) = 1`, the smaller valuation at each `l | x` is
0 and only the primes of `p` are left in `J`, with `N(J) = p x^x / x^x`,
which is (c).

Call `J` ambiguous if `J' = J`. Then `J^2 = (N(J))` is generated by a
rational number.

## 36.2 Ambiguous J: primitive divisors

### 36.2.1 Three tools

Lemma 36.2 (proven). For an imaginary quadratic field of discriminant
`Delta`, the class number satisfies `h <= sqrt(|Delta|) (log|Delta| + 2) / pi`.

Proof. For `Delta < -4`, `h = sqrt(|Delta|) L(1, chi) / pi`. The partial
sums `S(t)` of the character have `|S(t)| <= |Delta|/2`: the sum over a
period is 0, so `S(t)` is minus the sum over the rest of the period, and
one of the two pieces has at most `|Delta|/2` terms. Abel summation from
`N = |Delta|` gives
`|sum over n > N of chi(n)/n| <= 2 max|S| / (N + 1) < 1`, so
`L(1, chi) <= 1 + log|Delta| + 1`. For `Delta = -3, -4`, `h = 1`.

Lehmer pairs (cited). A Lehmer pair is a pair `(alpha, beta)` of algebraic
integers such that `(alpha + beta)^2` and `alpha beta` are nonzero coprime
rational integers and `alpha/beta` is not a root of unity. For odd `n` the
Lehmer number is `L_n = (alpha^n - beta^n)/(alpha - beta)`, a rational
integer. A prime is a primitive divisor of `L_n` if it divides `L_n` but not
`(alpha^2 - beta^2)^2 L_1 ... L_(n-1)`. Two pairs are equivalent if
`alpha1/alpha2 = beta1/beta2` is in `{+-1, +-sqrt(-1)}`; equivalent pairs
have the same `|alpha beta|`.

Lemma 36.3 (cited). (a) Y. Bilu, G. Hanrot and P. M. Voutier, Existence of
primitive divisors of Lucas and Lehmer numbers, J. reine angew. Math. 539
(2001) 75-122, Theorem 1.4: for every Lehmer pair and every `n > 30`, `L_n`
has a primitive divisor. (b) P. M. Voutier, Primitive divisors of Lucas and
Lehmer sequences, Math. Comp. 64 (1995) 869-888, Theorem 1, reproduced in
Table 2 of Bilu, Hanrot and Voutier: for odd `7 <= n <= 29`, the Lehmer
pairs without a primitive divisor of `L_n` are, up to equivalence, those
with `(a, b) = ((alpha + beta)^2, (alpha - beta)^2)` in this list:

| `n` | `(a, b)` |
|---|---|
| 7 | `(1, -7)`, `(1, -19)`, `(3, -5)`, `(5, -7)`, `(13, -3)`, `(14, -22)` |
| 9 | `(5, -3)`, `(7, -1)`, `(7, -5)` |
| 13 | `(1, -7)` |
| 15 | `(7, -1)`, `(10, -2)` |

There are none for `n = 11` and odd `17 <= n <= 29`. In all twelve,
`|alpha beta| = |a - b|/4 <= 9`.

The list was checked against K. Chakraborty and A. Hoque,
arXiv:2210.00561, Lemma 2.1 (which extracts it from BHV Table 2). P. M.
Voutier, n-defective Lehmer pairs for small n: corrections and
clarifications, arXiv:2411.07909 (2025), corrects the lists of BHV and of
Abouzaid only for `n` in {3, 4, 5, 6, 8, 10, 12}; the odd `n >= 7` used
here are untouched. The proof below uses no list for `n <= 5`.

Lemma 36.4 (proven). Let `(alpha, beta)` be a Lehmer pair, `n >= 7` odd,
and `P` a primitive divisor of `L_n`. Then `P` is odd,
`P == +-1 (mod 2n)`, and so `P >= 2n - 1`.

Proof. Let `Pi` be a prime above `P` in `Q(alpha, beta)`. If `P` divided
`alpha beta`, then `Pi` would divide `alpha` or `beta`, hence both (as
`alpha^n == beta^n` mod `Pi`), hence `(alpha + beta)^2`, against
coprimality. So `z = alpha/beta` is a unit at `Pi` with `z^n == 1`. Its
order `d` divides `n`. If `d < n`, then `Pi` divides
`alpha^d - beta^d = (alpha - beta) L_d`. It does not divide
`alpha - beta`, since `P` does not divide `(alpha^2 - beta^2)^2`; so
`P | L_d`, against primitivity (for `d = 1`, `L_1 = 1`). So `z` has order
`n` modulo `Pi`. Now `z = alpha^2/(alpha beta)`, and `alpha^2` is a root of
`X^2 - (a - 2c) X + c^2` with `c = alpha beta`, of discriminant `ab`. So
`z` lies in `F = Q(sqrt(ab))`, which is `Q` or quadratic, and its conjugate
is `1/z`. `P` does not divide `ab = (alpha^2 - beta^2)^2`, so it is
unramified in `F` if odd. If `P` splits (or `F = Q`), `n | P - 1`; if `P`
is inert, Frobenius is conjugation, `z^P == 1/z`, so `n | P + 1`. `P = 2`
would give `n | 1` or `n | 3`. So `P` is odd, `n | P -+ 1`, and since
`P -+ 1` is even and `n` odd, `2n | P -+ 1`.

### 36.2.2 The theorem

Theorem 36.5 (proven). In case L, let `x >= 11` be odd with `D > 0`,
`x > 2 log2(pD)` and `gcd(x, D) = 1`, and suppose `J` is ambiguous. If
`(p, q, x)` is a solution, then

    x <= 10 sqrt(D) (log 4D + 2) / pi.

The case `n >= 7` of the proof gives the much smaller
`x <= (14/13) sqrt(D) (log 4D + 2) / pi`; the bound above comes from
`n <= 5`.

Since `D < 4px`, this gives `x <= X_A(p)`, with `X_A(1) = 7,618`,
`X_A(10) = 145,768` and `X_A(20) = 340,896` (`r6f_ff_bounds.py`). The
bound does not depend on `q`.

Proof. Step 1 (normal form). An ambiguous integral ideal is a rational
integer times a product of distinct ramified primes: `J = (c) J1`, with
`J1` squarefree and ramified, `N(J1) = j1` squarefree, and
`J1 cap Z = j1 Z`. Then `c^2 j1 = p`. Put `mu1 = mu / c`, so
`(mu1) = J1 A^x`, `mu1` is integral, and `mu1 - mu1' = (f/c) sqrt(-D0)`.

Step 2 (a power). Let `e` be the order of the class of `A`. Its `x`-th
power is the class of `J1^(-1)`, which has order 1 or 2 since
`J1^2 = (j1)`. If the order is 1, put `t = e`; then `t | x`. If it is 2,
then `e` divides `2x` but not `x`, so `e = 2t` with `t | x` and `t` odd,
and the class of `A^t` has order 2 and equals the class of
`A^x = (A^t)^(x/t)`, that is of `J1`. In both cases `n = x/t` is odd and
`J1 A^t` is principal, `= (rho)`. Then

    (rho^n) = J1^n A^x = (j1)^((n-1)/2) (mu1),

so `rho^n = eps j1^((n-1)/2) mu1` with a root of unity `eps`. If `K` is
`Q(i)` every root of unity is an `n`-th power because `n` is odd; if `K` is
`Q(sqrt(-3))`, then `3 | D`, so `3` does not divide `x` or `n`, and the
same holds. Replacing `rho` by `rho / zeta` with `zeta^n = eps`, we may
take `eps = 1`.

Step 3 (a Lehmer pair). Put `alpha = rho / sqrt(j1)`,
`beta = rho' / sqrt(j1)`. Then `alpha beta = N(rho)/j1 = x^t`. Since
`J1' = J1`, both `rho` and `rho'` lie in `J1`, so
`rho + rho' in J1 cap Z = j1 Z` and `(alpha + beta)^2 = (rho + rho')^2 / j1`
is an integer. `alpha^2 = rho^2 / j1` is integral because
`(rho^2) = (j1) A^(2t)`, so `alpha` and `beta` are algebraic integers.
Coprimality: a prime `l` dividing `x^t` does not divide `j1` (`j1` divides
the discriminant of `K`, hence `4D`, while `x` is odd and prime to `D`); if
it divided `rho + rho'`, the prime `L` of `A` above `l` would divide `rho`
and `rho + rho'`, hence `rho'`, hence `L' | rho`, but `(rho) = J1 A^t`
holds only one of `L, L'`. Finally `(alpha/beta)^n = mu/mu' = e^(2 i theta)`
with `0 < theta < pi/2` and `tan theta = sqrt(D)/U`. A root of unity of `K`
has order at most 6, so a root of unity `e^(2 i theta)` with
`0 < 2 theta < pi` needs `theta >= pi/6`, that is `U^2 <= 3D`, so
`4p x^x <= 4D < 16px`, false. So `alpha/beta` is not a root of unity, and
`rho + rho' != 0` for the same reason. Thus `(alpha, beta)` is a Lehmer
pair.

Step 4 (the Lehmer number is small). For odd `n`,

    L_n = (alpha^n - beta^n)/(alpha - beta) = (mu1 - mu1')/(rho - rho')
        = (f/c) / g,

where `rho - rho' = g sqrt(-D0)` with `g` a nonzero integer (`rho` is not
real). So `f = c g L_n`, and every prime factor of `L_n` divides `f`.

Step 5 (large `n`). Let `n >= 7`. Since `alpha beta = x^t >= 11 > 9`, the
pair is not equivalent to one in the list of Lemma 36.3 (b), so Lemma 36.3
gives a primitive divisor `P` of `L_n`, and Lemma 36.4 gives
`P >= 2n - 1`. Then `P | f`, so `D0 = D/f^2 <= D/(2n - 1)^2`. The field
`K = Q(sqrt(-D0))` has `|Delta_K| <= 4 D0`, and by Lemma 36.2

    x = t n <= e n <= h n <= n * 2 sqrt(D0) (log 4D + 2) / pi
      <= (2n / (2n - 1)) sqrt(D) (log 4D + 2) / pi.

With `n >= 7` the factor is at most `14/13`.

Step 6 (small `n`). If `n <= 5`, then `t >= x/5` and
`x <= 5t <= 5e <= 5h <= 5 * 2 sqrt(D) (log 4D + 2) / pi` by Lemma 36.2 with
`|Delta_K| <= 4D`.

Validation (computed). `analysis/r6f_ff_lehmer.gp` builds the objects of
the proof in PARI for 40 planted equations `U^2 + D = 4 x^x` (with
`mu = rho^(x/e)` in eleven fields `Q(sqrt(-D0))`, `D0 <= 95`, class groups
of order up to 5) and for 5,285 artificial equations
`U^2 + D = 4p x^x`, `p = 1, 3, 5`, `9 <= x <= 21`, with ambiguous `J`. In
every case `L_n g = +-(f/c)`, as in Step 4 (`data/r6f_ff_lehmer.txt`). The
artificial equations have huge `D` and so `n = 1`; the planted ones have
`n` up to 59, and include `n = 3` with `e = 3` in `Q(sqrt(-23))`.

### 36.2.3 When J is ambiguous

Corollary 36.6 (proven and computed). Let `q >= 0`, either convention, and
let `x` be odd with `x > 1 + w(q) + q^2/4` and
`gcd(x, q^2 + 4 + 4 w(q)) = 1`. Then `(1, q, x)` is a solution in some base
only for `(1, 0, 3)` in base 5 under `0^0 = 0` (`25 + 3 = 1 + 27`).
More generally, let `p <= 20` be odd, `q >= 0`, `x` odd with
`x > W + q^2/(4p)`, and suppose the conditions of Corollary 36.7 hold. Then
`(p, q, x)` is a solution only in that one case.

Proof. For `p = 1`, `D = 4x - K0` with `K0 = q^2 + 4 + 4w(q)`, so
`gcd(x, D) = gcd(x, K0) = 1`, and by Lemma 36.1 (c) `J` has norm 1. So
`J = O_K` is ambiguous. For odd `p`, Corollary 36.7 gives the same. Theorem
36.5 then gives `x <= X_A(p) <= 340,896` once `x >= 11` and
`x > 2 log2(pD)` (with `D < 4px` both hold for `x >= 11` when `p = 1`, and
for every `x > W` when `p >= 3`). For `q >= 7` or `p >= 7` this contradicts
`x > W >= 7^7`. The remaining families have `p` in {1, 3, 5} and `q <= 6`.
For them the sieve of section 36.5 tested every odd `x <= 10^8`, and an
exact test of `4p x^x - D` for squareness checked every odd `x <= 7,619`
for `p = 1` and every `q <= 10` (section 36.7): only `(1, 0, 3)` is a
solution with `x > W + q^2/(4p)`.

Remark. When `K0` is a perfect square `k^2` (`q = 1` and `q = 3`), the
ideal `A` of a prime `x` is generated by `gamma = (k + sqrt(-D))/2`, of
norm `x`, and the equation says that the Lucas number `u_x(gamma, gamma')`
is `+-1`. Theorem 1.4 of BHV excludes this at once for `x > 30`. The
general proof has to go through the class group, and Lemma 36.2 is what
makes that cheap.

Corollary 36.7 (proven). Let `p` be odd and `x` odd with `D > 0` and
`x > 2 log2(pD)`. Suppose `gcd(x, p K0) = 1`, `K0 = q^2 + 4pW`, and for
every prime `l | p`, with `k = v_l(p)`: `l^ceil(k/2)` divides `q`, and if
`k` is odd, `l` does not divide `x - W`. Then `gcd(x, D) = 1` and `J` is
ambiguous, so Theorem 36.5 applies.

Proof. `D = 4px - K0`, so `gcd(x, D) = gcd(x, K0) = 1`, and `J` lives
above `p` by Lemma 36.1 (c). As `x` is prime to `p`, the part of `J` above
`l | p` is the `l`-part of `(mu)`. If `k` is even, `l^(k/2)` divides
`U = 2pb + q` and `l^k` divides `D = 4p(x - W) - q^2`, so
`mu / l^(k/2) = (U/l^(k/2) + sqrt(-D/l^k))/2` has integral trace and norm
and `l^(k/2)` divides `mu`. As `v_l(N(mu)) = k`, the `l`-part of `(mu)` is
`(l)^(k/2)`. If `k` is odd, `v_l(q^2) >= k + 1` and
`v_l(4p(x - W)) = k`, so `v_l(D) = k` is odd and `l` ramifies; the
`l`-part is `L^k` with `L = L'`. In both cases the `l`-part is ambiguous.

The test in `r6f_ff_lehmer.gp` confirms the rule against PARI on 6,778
artificial equations with `p` in {3, 5, 9, 15, 25, 27, 45, 75}: the rule
never calls a non-ambiguous `J` ambiguous. It misses 60 ambiguous cases,
all with a prime dividing both `x` and `p`, which the rule excludes for
simplicity. For even `p` the same analysis at 2 is longer and not needed
for the computation.

Proposition 36.8 (computed). Let `p, q <= 10`, either convention. Every odd
`x <= max(X_A(p), W + q^2/(4p))` that makes `(p, q, x)` a solution gives
one of these strings. Under `0^0 = 1`: `(1,3,1)` and `(3,1,3)` in base 4,
`(5,1,3)` in base 25, `(6,1,5)` in base 91, `(1,7,1)` in base 904. Under
`0^0 = 0`: `(1,0,3)` in base 5, `(4,0,1)`, `(5,0,1)`, `(7,0,1)`, `(9,0,1)`
in bases 8, 25, 343, 6561, and the swaps `(p, 0, p^p)` for
`p = 3, 5, 7, 9`, in base `p^((p^(p+1) - 1)/2)` (for `p = 3`, base `3^40`).

Method. `r6f_ff_sieve.c` tests `D` for quadratic residues modulo 150 odd
primes, with tables of period `l(l - 1)` (the method of `r6b_sieve.c`,
extended to odd `x` and the leading position). The 120 families of
`r6f_ff_runs.py closure 20 2.2e10` (all with `p, q <= 10`; the families
with larger digits have `W > 2.2 * 10^10`) cover `1.14 * 10^11` values of
`x` in 6 minutes on 3 threads. All 17 survivors are decided exactly by
`r6f_ff_runs.py check` (`data/r6f_ff_closure.txt`). The large ones are the
swaps `(p, 0, p^p)` with `R = 0` (case (i) of Theorem 25.7 with `e = 0`),
decided by the parity of the exponents in `x^x / p`.

With the run of section 36.5 (all odd `x <= 10^8`): for `p, q <= 10` every
solution `(p, q, x)` with `x` odd is listed above, or has
`x > max(10^8, W + q^2/(4p))`, `J` not ambiguous or `gcd(x, D) > 1`, and
`x <= X_B(p)` by Theorem 36.9.

## 36.3 Every J: a reduced basis and three logarithms

When `J` is not ambiguous, its class can have order about `h`, and the
Lehmer argument fails. A linear form in logarithms still works, because
the class group is torsion and costs only heights that grow like
`sqrt(x)`.

Theorem 36.9 (proven, effective). In case L, let `x >= 25` be odd with
`D > 0` and `x > 2 log2(pD)`. If `(p, q, x)` is a solution, then

    (x/2) log x - (1/2) log(8x)
        <= 2^38 * 4 (1 + log 2) (1 + log B') * pi * (4/sqrt 3) * e * w_s * log x,

where `e <= 2 sqrt(D) (log 4D + 2)/pi` is the order of the class of `A`,
`w_s = max(log(pD), pi)` and `B' = 5 x log x + 5 w_s + 6`. With `D < 4px`
this gives `x <= X_B(p)`: `8.2 * 10^38` for `p = 1`, `1.1 * 10^40` for
`p = 10`, `2.4 * 10^40` for `p = 20` (`r6f_ff_bounds.py`). The bound does
not depend on `q`.

Proof. Step 1 (the lattice). The set of `(s, r)` in `Z^2` with `J^s A^r`
principal is a lattice `Lam`. Since `(mu) = J A^x`, the class of `J` is the
class of `A^(-x)`, so `Lam = {(s, r) : r == x s mod e}`, of index `e`. It
contains `(1, x)`.

Step 2 (heights). For `(s, r)` in `Lam` let `(rho) = J^s A^r`. The number
`alpha = rho/rho'` has absolute value 1 at the complex place, so its height
is half the log of the norm of its denominator ideal. That norm is at most
`sum over P of |v_P(J^s A^r)| log N(P)`, so

    h(rho/rho') <= (1/2) (|s| s(J) + |r| log x) <= (1/2) ||(s, r)||,

with the weighted norm `||(s, r)|| = |s| w_s + |r| log x`. Every nonzero
vector of `Lam` has `||v|| >= pi`, since `w_s >= pi` and
`log x >= log 25 > pi`.

Step 3 (a short basis). Scale the coordinates by `w_s` and `log x`. The
scaled lattice has covolume `e w_s log x`, and a Lagrange-reduced basis
`b1, b2` has `|b1| |b2| <= (2/sqrt 3)` times the covolume. The weighted
norm is at most `sqrt 2` times the Euclidean norm, so

    ||v1|| ||v2|| <= (4/sqrt 3) e w_s log x.

Write `(1, x) = a v1 + b v2`. By Cramer's rule, with the angle of a reduced
basis between `pi/3` and `2 pi/3` and `|b2| >= |b1| >= pi / sqrt 2`, both
`|a|` and `|b|` are at most `(2 sqrt 2 / (sqrt 3 pi)) |(w_s, x log x)|`,
below `0.53 (w_s + x log x)`. The draft used `0.74`, which is also valid.

Step 4 (the linear form). With `rho_i` generating the ideals of `v_i`,
`mu = eps rho1^a rho2^b` for a root of unity `eps`. Let `theta` be the
argument of `mu`, `0 < theta < pi/2`, `tan theta = sqrt(D)/U`. Then

    Lam0 = 2 i theta = a log(rho1/rho1') + b log(rho2/rho2') + k log zeta,

with principal logarithms, `zeta = exp(2 pi i / w)` (`w <= 6` the number
of roots of unity in `K`), and `|k| <= (w/2)(|a| + |b| + 1) <= B'`.
`Lam0 != 0`. Matveev's theorem (E. M. Matveev, Izv. Math. 64 (2000)
1217-1269, Corollary 2.3, in the form for any number field and any
determination of the logarithms:
`|Lam| >= exp(-2^(6s+20) D^2 A_1 ... A_s (1 + log D)(1 + log B))` with
`A_j >= max(D h(alpha_j), |log alpha_j|, 0.16)` and
`B = max |b_j|`) with `s = 3`, `D = 2`, `A_j = ||v_j||` for `j = 1, 2`
(which is at least `2h`, at least `pi >= |log(rho_j/rho_j')|`, and at least
0.16) and `A_3 = pi` gives the lower bound. The upper bound:
`U^2 = 4p x^x - D >= 2p x^x`, so
`|Lam0| <= 2 tan theta = 2 sqrt(D)/U <= sqrt(2D/p) x^(-x/2) <= sqrt(8x) x^(-x/2)`.

Remarks.

- The two logarithms with large height come from the class group, and
  their heights multiply to about `e log(pD) log x`, linear in `e <= h`.
  This is where the imaginary field wins. In a real field the regulator
  would enter the height of every logarithm (section 36.4.3).
- With the cruder choice `rho = J A^(x mod e)` and `gamma` generating
  `A^e` the product of heights is about `e^2`, and since `e` can be as
  large as `h`, about `sqrt(x) log x`, the bound fails by a power of
  `log x`. The reduced basis is what saves it: the class of `J` lies in the
  cyclic group of `A`, so a vector `(s, r)` with `|s|, |r|` about
  `sqrt(e)` exists.
- The bound is far beyond any sieve. For `p, q <= 10` the computation of
  Proposition 36.8 and Theorem 36.5 leave exactly the strings with `J` not
  ambiguous or `gcd(x, D) > 1`, and `max(10^8, W + q^2/(4p)) < x <= X_B(p)`.

Corollary 36.10 (proven). For fixed `p >= 1`, `q >= 0` and either
convention, `(p, q, x)` is a solution for only finitely many `x`, and they
are effectively bounded: `x <= max(X_B(p), W + q^2/(4p))` for odd `x`,
Theorem 32.2 for even `x` and non-square `p`, Theorem 25.7 (ii) for even
`x` and square `p` (with case (i) of that theorem, `R = 0`, giving at most
one `x`).

So the last position is settled in finite terms, for every parity and
every square class. This answers question 129 for the last position, and
question 130 for the last position (every `lam` at once).

Uniformity. With `p, q <= B`, odd `x` in the last position satisfies
`x <= max(X_B(B), 2 B^B + B^2)`, and `X_B(B)` grows like `B (log B)^c`.
The second term is the real range `x <= W + q^2/(4p)`, where the field of
`R` is real; there `x` is bounded by its definition but not by a small
bound.

## 36.4 The middle and leading positions

### 36.4.1 Middle, x odd: a local density result

Proposition 36.11 (proven). Let `(p, x, q)` with `x` odd be a solution,
and `A = w(p) + w(q) - q`. Then every prime `l` that divides `x` and not
`2pA` satisfies `(pA / l) = 1`. If `pA` is not a perfect square, the set of
`x` for which some base makes `(p, x, q)` a solution has density 0.

Proof. `U^2 = 4p x^x + x^2 + 4pA == 4pA (mod l)` and `l` does not divide
`4pA`, so `pA` is a nonzero square modulo `l`. If `pA` is not a square
(note `A >= 1`), the primes with `(pA/l) = -1` have Dirichlet density 1/2,
so the sum of `1/l` over them diverges. For each `y` the `x` with no prime
factor `l <= y` of that kind have density `prod over such l <= y of
(1 - 1/l)` (by the Chinese remainder theorem), which tends to 0 as `y`
grows.

Of the 440 middle families with `p, q <= 20` (both conventions where
`q = 0`), 25 have `pA` a square: `(1, x, 3)`; `(p, x, 1)` with `p` odd or
`p = 4, 16`; and `(p, x, 0)` under `0^0 = 0` for the same `p`. In the last
two `A = p^p`. The family `(1, x, 1)` is the equation
`b(b + x) = x^x + 1` of chapters 16 and 18.

### 36.4.2 Leading, x even: the square part

Proposition 36.12 (proven, weak). Let `(x, q, r)` be a solution with `x`
even and not a square, `A = w(q) + w(r) - r != 0`, and `x = n f^2` with
`n > 1` squarefree. Then the inequality of Theorem 32.2 holds with `eta`
the fundamental unit of `Q(sqrt n)`, `R = q^2 + 4xA` and
`V = 2 f x^(x/2)`. With `log eta <= sqrt(n) (log 4n + 2)` it bounds `f^2`
(computed, `r6f_ff_bounds.py lead 20`, `data/r6f_ff_lead.txt`): for
`q, r <= 20` there is no restriction below about `10^11`, and
`f^2 <= 8.3 * 10^8` at `x = 10^12`, `4.5 * 10^9` at `x = 10^20`,
`3.4 * 10^11` at `x = 10^100`. Asymptotically the bound is
`f^2 = O((log x)^4)`; at the sampled `x` from `10^12` to `10^100` it is at
most `1500 (log x)^4`.

Proof. `4x^(x+1) = n V^2` with `V = 2 f x^(x/2)`, and `U = 2xb + q`. The
proof of Theorem 32.2 uses only that `beta = U - V sqrt n` has norm `R` and
`v_2(V) >= 1 + x/2`; both hold here. The field changes with `x`, but the
inequality is applied to one `x` at a time. The two side cases of that
proof give weaker restrictions; the script allows them too. Since
`f sqrt n = sqrt x`, the inequality depends on `f` only through the range
of `log eta`, which shrinks as `f` grows, and every term grows with
`log eta`; so the script tests the largest admissible `log eta`, and the
allowed `f^2` form an initial segment.

This extends Proposition 32.6 (one square class at a time) to every class
whose squarefree part is at least `x / (C (log x)^4)`. It excludes only a
set of density 0, so it is a small step.

Correction (chapter 38, 2026-10-20). Proposition 36.12 remains true but
is superseded. Theorem 38.6 shows that `(x, q, r)` with `x` even is a
solution for only finitely many `x`, for every `q >= 1` and `r`, with an
effective bound (at most `10^186` for `q, r <= 20`). The ideal of norm `x`
is generated by `theta = (q + sqrt R)/2` up to the primes of `Aq`, so
`mu / theta^(x+1)` is an S-unit, and a reduced basis of the S-unit lattice
costs only its covolume, `O(sqrt(x) log x)`. For `b (xb + 1) = x^x + 1`
the bound is `4.27 * 10^11`, and a sieve to it closes the family
(Corollary 38.8).

Referee note. The draft said "from `10^12` on, `f^2 <= 1500 (log x)^4`".
The script evaluates seven values of `x`, so that sentence is a
computation at those points, not a statement for every `x`. The
`O((log x)^4)` form follows from the inequality.

### 36.4.3 Why the real cases resist

In cases M and Lead the factorization `(mu) = J A^x` (or `A^(x+1)`) still
holds in the real field `K = Q(sqrt R)`, but `mu` is now a unit power
times products of class-group generators. Every logarithm in the linear
form carries the regulator `Reg` in its height. With `h Reg` about
`sqrt(Delta) L(1, chi) / 2` (class number formula):

- Lead: `Delta` is about `16 A x`, so `h Reg` is about `sqrt x`. The
  argument of Theorem 36.9 needs `Reg` below `sqrt(x)/(log x)^c` when `J`
  is principal-like and below `x^(1/3)` in general. The 2-adic route of
  Proposition 36.12 needs the regulator of `Q(sqrt n)` below
  `sqrt(x)/(log x)^2`.
- M: `Delta` is about `x^2`, so `h Reg` is about `x`. If `Reg` is small
  (as for `A = 1`, where `(x + sqrt(x^2 + 4))/2` is a unit), then `h` is
  about `x / log x`, as large as the exponent itself; this is the
  class-group obstruction of Corollary 18.11. If `A > 1`, the regulator is
  typically close to `x`.

Correction (chapter 38, 2026-10-20). The leading case does not resist.
The requirements "`Reg` below `sqrt(x)/(log x)^c`" and "below `x^(1/3)`"
come from giving every logarithm the height `Reg`. With a reduced basis
of the full S-unit lattice (units and ideal classes together, Minkowski's
second theorem), the product of the heights is about the covolume, at
most `sqrt(2 + |S|) h Reg prod log N(P)`, which is `O(sqrt(x) log x)`;
and the ideal of norm `x` is generated by `theta = (q + sqrt R)/2` up to
the primes of `Aq`. Matveev's bound then beats the exponent `x + 1`, and
the leading position is finite for every pair of small digits (Theorem
38.6). The middle case above is right: there `Delta` is about `x^2` and
the covolume about `x L(1, chi)`, of the size of the exponent (section
38.3.2). In the 25 middle families with `pA` a square, Theorem 38.2 bounds
prime powers `x` without linear forms in logarithms.

Table 36.4.3.1 (computed, `analysis/r6f_ff_classes.gp`, `quadclassunit`,
so under GRH; illustrations only). Means over 200 to 1,800 consecutive odd
or even `x` above `X`.

| case | digits | `X` | mean `h/sqrt(x)` | mean `e/sqrt(x)` | mean `Reg / log x` | mean `Reg / sqrt(x)` |
|---|---|---:|---:|---:|---:|---:|
| L | `p = 1, q = 0` | `10^8` | 0.75 | 0.25 | | |
| L | `p = 2, q = 1` | `10^8` | 2.21 | 0.90 | | |
| L | `p = 3, q = 2` | `10^8` | 1.46 | 0.46 | | |
| M | `p = 1, q = 1` | `10^6` | | | 1.00 | |
| M | `p = 1, q = 2` | `10^6` | | | 10,186 | |
| M | `p = 2, q = 1` | `10^6` | | | 16,374 | |
| Lead | `q = 1, r = 1`, field of `R` | `10^6` | | | | 0.99 |
| Lead | `q = 3, r = 2`, field of `R` | `10^6` | | | | 5.51 |
| Lead | `q = 1, r = 1`, `Q(sqrt x)` | `10^6` | | | | 0.24 |

In case L the order `e` of the class of `A` is typically a fixed fraction
of `sqrt x`, as the proof of Theorem 36.9 must allow. For `q = 1, 3` (`K0`
a square) it is tiny: the ideal of norm `x` is often principal (Remark
after Corollary 36.6). In case M with `A > 1` the regulator is between
`x/7` and `x/4` at `x = 10^6`; in case Lead both regulators are a fixed
fraction of `sqrt x`.

## 36.5 Computation

Computed. `r6f_ff_sieve.c` on the 1,362 families of
`r6f_ff_runs.py evidence 20 1e8`: the three open cases with small digits at
most 20, both conventions where a small digit is 0, and `x <= 10^8`
(`x` odd in cases L and M, even in case Lead): `6.81 * 10^10` values of
`x` in 17 minutes on 3 threads. Then the 922 families of cases M and Lead
for `10^8 < x <= 10^9`: `4.15 * 10^11` more values in 35 minutes
(`data/r6f_ff_evidence.txt`).

Every survivor is decided exactly by `r6f_ff_runs.py check`.

- 31,622 survivors are `(x, 0, 0)` and `(x, 0, 1)` in the leading position
  under `0^0 = 0` with `x` an even square. Here `A = 0`, so `R = 0`, and
  `x b^2 = x^x` has the root `b = x^((x-1)/2)` exactly when `x` is a
  square: the self-paying digit of Proposition 2.2. They are outside the
  open regime (`R = 0`).
- The other 35 survivors have `x <= 7`, or are the swaps `(p, 0, p^p)`
  with `R = 0`. They are the known solutions `(1,3,1)`, `(3,1,3)`,
  `(5,1,3)`, `(6,1,5)`, `(1,7,1)` (in their middle or last reading, and
  `(6,1,5)` also with `x = 6` leading), the `0^0 = 0` strings `(p, 0, 1)`
  and `(1, 0, 3)`, or strings with an integer root at most the largest
  digit.

So no 3-digit solution with two digits at most 20 and a large digit in the
open regime exists with `x <= 10^8` in the last position, or `x <= 10^9`
in the middle and leading positions. Heuristic 25.12 predicts this: a
string with large digit `x` is a solution with chance about `x^(-x/2)`.

## 36.6 What failed and why

1. Local arguments at the primes of `x` (Lemma 33.1). `l^x` divides
   `4l x^x`, so `R` must be an `l`-adic square. In case L this is implied
   by Lemma 36.1 (a); in case M it gives Proposition 36.11 and nothing
   more; in case Lead `R == q^2 (mod l)` is always a square, so there is no
   information. The `l`-adic Bugeaud-Laurent bound in the Pell form (the
   method of Theorem 32.2 at a prime `l | x`) costs a factor about
   `l^2/(log l)^4` and still needs a small regulator of `Q(sqrt(px))`.
2. Primitive divisors for every `J`. If `J` is not ambiguous, `mu` is
   `tau gamma^n` with a non-real `tau`, and `mu - mu'` is a twisted
   sequence `tau gamma^n - tau' gamma'^n`. Primitive divisor theorems for
   such sequences exist (Schinzel, Stewart) but with thresholds depending
   on the heights of `tau, gamma`, which grow here like `sqrt x`.
3. Two logarithms in place of three. A 2-logarithm form needs the class of
   `J` to be trivial or of order 2. Raising `mu` to the order `k` of `J`
   gives `pi_J gamma^N` with `h(pi_J)` about `k log p`; the product of
   heights `k e` is about `x`, too large by a power of `log x`.
4. The modular method. `U^2 + D = 4p X^x` has one `x`-th power and a term
   `D` that is not a power, so there is no Frey curve of signature
   `(x, x, 2)`.
5. Continued fractions. In the Pell form `|R|` is about `sqrt(N)` times
   `x`, above the range `|R| < sqrt N` where `U/V` must be a convergent.
6. Real fields. See section 36.4.3. The argument of Theorem 36.9 applies
   verbatim when the regulator is small, but the data show that it rarely
   is.

## 36.7 Independent checks

The referee checks of this chapter, separate from the scripts that
produced it.

- Proofs. Lemma 36.1, Lemma 36.2, Lemma 36.4, Theorem 36.5, Corollary
  36.7, Theorem 36.9 and Proposition 36.11 were checked line by line. The
  points that needed care: the rounding in Lemma 36.1 (b) (the bound is
  `max(v_l(p), v_l(D))` per prime, inside `log(pD)`; this note first said
  `v_l(p) + v_l(D)/2`, which is wrong when `l` divides `D` and not `p`,
  corrected 2026-10-20 after the Lean formalization); the hypothesis
  `x > 2 log2(pD)` in Corollary 36.7, which Lemma 36.1 (c) needs; the
  Lehmer pair of Step 3 (integrality of `alpha`, coprimality at the primes
  of `x` and of `j1`, and `alpha/beta` not a root of unity); the modulus in
  Lemma 36.4 (`P == +-1 mod 2n`, since `n` is odd); and the coefficient
  bound of Step 3 of Theorem 36.9 (0.53 suffices). None of these changes a
  statement.
- Literature. Lemma 36.3 (a) and the twelve pairs of (b) agree with
  Chakraborty and Hoque, arXiv:2210.00561, Theorem C and Lemma 2.1, and
  Voutier's 2025 corrections (arXiv:2411.07909) touch only even `n` and
  `n <= 6`. The complex form of Matveev's Corollary 2.3 used in Theorem
  36.9 is the one stated in P. Bacik, arXiv:2409.01221, Theorem 3.1. The
  original papers were not available to the referee.
- Bounds. `X_A(p)` and `X_B(p)` were recomputed by bisection from the
  inequalities, by a script written separately from `r6f_ff_bounds.py`:
  `X_A(1) = 7,618`, `X_A(10) = 145,768`, `X_A(20) = 340,896`,
  `X_B(1) = 8.155 * 10^38`, `X_B(10) = 1.11 * 10^40`,
  `X_B(20) = 2.426 * 10^40`. The count 25 of 440 in Proposition 36.11 was
  recounted.
- Corollary 36.6, `p = 1`. An exact test (integer square root of
  `4 x^x + q^2 + 4(W - x)`, no sieve) of every odd `x <= 7,619` and every
  `q <= 10`, both conventions for `q = 0`, finds only `(1, 0, 3)` in base 5
  (`0^0 = 0`), `(1, 3, 1)` in base 4 and `(1, 7, 1)` in base 904; the last
  two have `x <= W`.
- Proposition 36.8. A second sieve, `r6f_ff_refcheck.c`, tests squareness
  by Euler's criterion modulo 48 primes just below `2^32`, with direct
  modular powers instead of period tables. On the 120 families of
  Proposition 36.8 for every odd `x <= 3 * 10^6` (this covers `X_A(p)` for
  `p <= 10`), and in each of the 57 families whose range goes beyond
  `3 * 10^6` on two windows, `10^6` odd `x` around the top
  `W + q^2/(4p)` and `5 * 10^5` odd `x` at a random place below it
  (`2.66 * 10^8` values in all), its survivors are exactly the 17
  survivors of `data/r6f_ff_closure.txt`. On the 922 middle and leading
  families with small digits at most 20 and `x <= 2 * 10^6` its survivors
  are the survivors of `data/r6f_ff_evidence.txt` in that range
  (`data/r6f_ff_refcheck.txt`).

## Library corrections

Each item now has a note in the chapter or question file it corrects.

1. Section 32.1.6, last paragraphs: "Pell equations `U^2 - n V^2 = R` in
   which the field changes with `x`. The regulator of `Q(sqrt(px))` can be
   as large as `sqrt(x) log x`, and then every Baker bound is too weak ...
   now seen to be the only obstacle for three digits." The regulator is an
   obstacle of the Pell form only. In the last position the field of `R`
   is imaginary, and the problem is finite (Theorem 36.9). The table of
   section 32.1.6 now splits the row "`n` varies": last position finite,
   middle and leading open.
2. Section 25.1.4, update of chapter 32: "What remains open in case (iii)
   is ... odd `x` that does not lead, and even `x` that leads." Now: odd
   `x` in the middle, and even `x` that leads. In the last position odd
   `x` is finite for each pair of small digits.
3. Question 129 asks for uniformity over `Q(sqrt(px))`. Answered for the
   last position by passing to `Q(sqrt R)` (Theorem 36.9; uniform in `q`).
   Question 130 asks about square classes `lam > 1`: in the last position
   every class is covered at once (Corollary 36.10); the middle position
   remains.
4. Section 32.1.5, proof sketch of Theorem 32.5: "Partial summation with
   `|sum chi(k)| <= Delta` gives `L(1, chi) <= log Delta + 2`." With that
   bound partial summation gives `log Delta + 3`; the stated `+ 2` needs
   `|sum| <= Delta/2`, which is true (Lemma 36.2). The theorem is
   unaffected.

## Files

| file | contents |
|---|---|
| `analysis/r6f_ff_bounds.py` | `X_A(p)` (Theorem 36.5), `X_B(p)` (Theorem 36.9), the square-part bound of Proposition 36.12 |
| `analysis/r6f_ff_lehmer.gp` | checks of Steps 3 and 4 of Theorem 36.5 and of Corollary 36.7 against PARI |
| `analysis/r6f_ff_sieve.c` | sieve for the three positions, either parity, a range of `x` |
| `analysis/r6f_ff_runs.py` | inputs for the sieve (closure and evidence runs) and the exact check of survivors |
| `analysis/r6f_ff_classes.gp` | class numbers, orders and regulators of Table 36.4.3.1 |
| `analysis/r6f_ff_refcheck.c`, `analysis/r6f_ff_refexact.py` | the referee checks of section 36.7: a second sieve (Euler's criterion, primes below `2^32`), the exact test for `p = 1`, the recomputed bounds |
| `analysis/data/r6f_ff_bounds.txt`, `r6f_ff_lead.txt` | `X_A(p)`, `X_B(p)` for `p <= 20`; the square-part bound for `q, r <= 20` |
| `analysis/data/r6f_ff_closure.txt` | Proposition 36.8: survivors, decisions, family counts |
| `analysis/data/r6f_ff_evidence.txt` | section 36.5 |
| `analysis/data/r6f_ff_classes.txt` | Table 36.4.3.1 |
| `analysis/data/r6f_ff_lehmer.txt` | output of `r6f_ff_lehmer.gp` |
| `analysis/data/r6f_ff_refcheck.txt` | output of the referee checks |

## New questions

These are questions 149 to 153 of `questions.md`.

1. A computable bound for case L. Theorem 36.9 gives `10^40`. Mignotte's
   bounds for three logarithms, or a primitive divisor theorem for twisted
   sequences `tau gamma^n - tau' gamma'^n` uniform in the height of `tau`,
   would bring it within reach of the sieve and close the last position
   for `p, q <= 10`.
2. A class-group sieve. For `x` with `J` not ambiguous, a solution needs
   `[J] = [A]^(-x)` for one of the `2^omega(x)` ideals `A` of norm `x`, an
   event of chance about `2^omega(x) / e`. Can this be tested fast enough
   (forms of discriminant `-4D`) to run beyond `10^10`?
3. (Partially answered in chapter 38: for the 25 families with `pA` a
   square, prime powers `x` are effectively bounded, Theorem 38.2 and
   Corollary 38.3.) The middle position. Proposition 36.11 leaves the 25 families with `pA`
   a square for every `x`, and a density-0 set of `x` for the others. Is
   there a finiteness theorem for `x` prime, where `A` is a prime ideal and
   the class group has order about `x / log x` (`A = 1`) or the regulator
   is about `x` (`A > 1`)?
4. (Answered in chapter 38: finite for every even `x`, Theorem 38.6.)
   The leading position. Finiteness for those `x` where `Q(sqrt R)` has
   class number above `x^(1/6 + eps)`? These form a thin set, but it would
   be the first result in that case beyond fixed square classes.
5. Other weights. For factorions (chapter 33) the last position has
   `U^2 + |K| = 4p x!`, imaginary as well; `x!` is not a power, so the
   argument does not transfer. Which weights `w(x)` are perfect `x`-th
   powers up to a bounded factor on a large set, so that the imaginary
   argument applies?
