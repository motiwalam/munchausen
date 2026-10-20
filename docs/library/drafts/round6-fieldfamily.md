# Draft: three digits when the field changes with the large digit

This draft attacks the open regime of section 32.1.6: 3-digit strings with
two small digits and one large digit `x`, where the quadratic field of the
Pell equation changes with `x`. It answers question 129 for the last
position and question 130 for the last position, and it explains why the
middle and leading positions are harder. Numbering is provisional (`F.n`);
it becomes a chapter number when the draft lands.

Labels: proven (a proof is here, with cited inputs named), computed (a
stated computation), proven and computed, heuristic, conditional. Scripts
are `analysis/r6f_ff_*`, data `analysis/data/r6f_ff_*`. The runs used at
most 3 threads.

## Summary

| result | status |
|---|---|
| In the last position with `x` odd and `x > W + q^2/(4p)`, the equation is `U^2 + D = 4p x^x` with `D > 0`. In the imaginary field `Q(sqrt(-D))`, `x^x` is an `x`-th power and there are no units. | proven (Lemma F.1) |
| If the ideal `J` of norm `p` in `(mu) = J A^x` is ambiguous, primitive divisors of Lehmer numbers give `x <= X_A(p)`: 7,618 for `p = 1`, at most 340,896 for `p <= 20`, for every `q` | proven (Theorem F.5) |
| `(1, q, x)` with `x` odd, `x > w(q) + 1 + q^2/4` and `x` prime to `q^2 + 4 + 4w(q)` is a solution only for `(1, 0, 3)` in base 5 (`0^0 = 0`), for every `q`. The same holds for odd `p <= 20` under explicit congruence conditions | proven and computed (Corollaries F.6, F.7) |
| For every `J`, a reduced lattice basis and Matveev's bound for three logarithms give `x <= X_B(p)`, about `10^39` to `2.4 * 10^40` for `p <= 20`, uniform in `q` | proven, effective (Theorem F.9) |
| So for fixed `p, q` the string `(p, q, x)` is a solution for only finitely many `x`, of either parity, with an effective bound | proven (Corollary F.10) |
| Middle position, `x` odd: every prime `l` of `x` with `l` prime to `2pA` has `(pA / l) = 1`. If `pA` is not a square (415 of the 440 families with `p, q <= 20`), the `x` that can occur have density 0 | proven (Proposition F.11) |
| Leading position, `x` even, `x = n f^2`: the 2-adic bound of Theorem 32.2 holds with the unit of `Q(sqrt n)`, so the square part `f^2` of a solution is small, at most `4.5 * 10^9` for `x = 10^20` | proven, weak (Proposition F.12) |
| Sieve: last position, `p, q <= 10`, odd `x` up to `max(X_A(p), W + q^2/(4p))`, up to `10^10`; all three open cases with small digits up to 20 and `x <= 10^8`. Only known solutions survive | computed (Proposition F.8, section F.5) |
| Why the middle and leading positions resist: in a real field the regulator enters every height. Middle: `h Reg` is about `x`. Leading: `Reg` is about `sqrt(x)` | proven sizes, measured (section F.4.3) |

## F.1 The switch to the field of R

### F.1.1 Setting

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
can be as large as `sqrt(x) log x`. The idea of this draft is to factor in
the other field, `Q(sqrt R)`. There `4 l x^x` is a constant times an `x`-th
power (an `(x+1)`-th power in the leading case), and `U^2 - R` is a norm.
This is the setting of the Lebesgue-Nagell equation `X^2 + D = C Y^n`, with
the twist that `Y = n = x` and `D` grows with `x`.

In case L the constant `R` becomes negative as soon as `x` passes
`W + q^2/(4p)`, and the field is imaginary. An imaginary quadratic field has
no units of infinite order, and its class number is about `sqrt(|R|)`, so
about `sqrt(x)`, far below the exponent `x`. Both facts are what the real
Pell form lacked. Cases M and Lead stay real.

### F.1.2 The ideal equation

Fix case L. Let `x` be odd and put

    D = 4p (x - W) - q^2 > 0,   U^2 + D = 4p x^x,   U = 2pb + q.

Let `K = Q(sqrt(-D))`, `D = f^2 D0` with `D0` squarefree, and

    mu = (U + sqrt(-D)) / 2,    N(mu) = p x^x,    mu - mu' = f sqrt(-D0),

where `'` is complex conjugation. `U` and `D` have the parity of `q`, so
`mu` is in the ring of integers `O_K`.

Lemma F.1 (proven). Suppose `x > 2 log2(pD)`. Then:

- (a) every prime `l` dividing `x` splits in `K`;
- (b) `(mu) = J A^x`, where `A` is an integral ideal of norm `x` with
  `A + A' = O_K`, and `J` is a fractional ideal with
  `s(J) = sum over P of |v_P(J)| log N(P) <= log(pD)`;
- (c) if `gcd(x, D) = 1`, then `J` is integral of norm `p` and lives above
  the primes of `p`.

Proof. Every prime ideal `P` with `P | mu` and `P | mu'` divides
`mu - mu' = sqrt(-D)`, so `min(v_P(mu), v_P(mu')) <= v_P(sqrt(-D))`.

Let `l | x`. If `l` ramifies, `P = P'` and `v_P(mu) = v_l(N(mu)) >= x`, while
`v_P(sqrt(-D)) = v_l(D) <= log_3 D < x`. If `l` is inert, `v_P(mu) = v_P(mu')
>= x/2`, while `v_P(sqrt(-D)) = v_l(D)/2 < x/2`. Both are impossible, which
is (a).

For split `l | x` with primes `L, L'`: `v_L(mu) + v_L'(mu) = v_l(p) + x v_l(x)`
and the smaller of the two is at most `v_l(D)/2`. Round each valuation
`v_P(mu)` to the nearest multiple of `x`; put the multiples into `A^x` and
the remainders into `J`. Since `v_l(p) + v_l(D) < x/2`, the larger
valuation rounds to `x v_l(x)` and the smaller to 0. So `A` has one prime
above each `l | x`, with exponent `v_l(x)`: `N(A) = x` and `A + A' = O_K`.
The remainders at `L, L'` have absolute values summing to at most
`v_l(p) + v_l(D)`. Primes above `l | p` with `l` prime to `x` contribute
`v_l(p) log l` in each splitting type. Summing gives (b). If
`gcd(x, D) = 1`, the smaller valuation at each `l | x` is 0 and only the
primes of `p` are left in `J`, which is (c).

Call `J` ambiguous if `J' = J`. Then `J^2 = (N(J))` is generated by a
rational number.

## F.2 Ambiguous J: primitive divisors

### F.2.1 Three tools

Lemma F.2 (proven). For an imaginary quadratic field of discriminant
`Delta`, the class number satisfies `h <= sqrt(|Delta|) (log|Delta| + 2) / pi`.

Proof. For `Delta < -4`, `h = sqrt(|Delta|) L(1, chi) / pi`. The partial sums
`S(t)` of the character have `|S(t)| <= |Delta|/2` (the sum over a period is
0). Abel summation from `N = |Delta|` gives
`|sum over n > N of chi(n)/n| <= 2 max|S| / (N + 1) < 1`, so
`L(1, chi) <= 1 + log|Delta| + 1`. For `Delta = -3, -4`, `h = 1`.

Lehmer pairs (cited). A Lehmer pair is a pair `(alpha, beta)` of algebraic
integers such that `(alpha + beta)^2` and `alpha beta` are nonzero coprime
rational integers and `alpha/beta` is not a root of unity. For odd `n` the
Lehmer number is `L_n = (alpha^n - beta^n)/(alpha - beta)`, a rational
integer. A prime is a primitive divisor of `L_n` if it divides `L_n` but not
`(alpha^2 - beta^2)^2 L_1 ... L_(n-1)`.

Lemma F.3 (cited). (a) Y. Bilu, G. Hanrot and P. M. Voutier, Existence of
primitive divisors of Lucas and Lehmer numbers, J. reine angew. Math. 539
(2001) 75-122, Theorem 1.4: for every Lehmer pair and every `n > 30`, `L_n`
has a primitive divisor. (b) P. M. Voutier, Primitive divisors of Lucas and
Lehmer sequences, Math. Comp. 64 (1995) 869-888, Theorem 1 (as quoted in
BHV, Table 2, and in K. Chakraborty and A. Hoque, arXiv:2210.00561, Lemma
2.1): for odd `7 <= n <= 29`, the Lehmer pairs without a primitive divisor
of `L_n` are, up to equivalence, those with
`(a, b) = ((alpha + beta)^2, (alpha - beta)^2)` in a list of twelve pairs
with `|a| <= 14`, `|b| <= 22`. In all of them `|alpha beta| = |a - b|/4 <= 9`.

Lemma F.4 (proven). Let `(alpha, beta)` be a Lehmer pair, `n >= 7` odd, and
`P` a primitive divisor of `L_n`. Then `P` is odd and `P >= 2n - 1`.

Proof. Let `Pi` be a prime above `P` in `Q(alpha, beta)`. If `P` divided
`alpha beta`, then `Pi` would divide `alpha` or `beta`, hence both (as
`alpha^n == beta^n` mod `Pi`), hence `(alpha + beta)^2`, against
coprimality. So `z = alpha/beta` is a unit at `Pi` with `z^n == 1`. Its
order `d` divides `n`. If `d < n`, then `Pi` divides
`alpha^d - beta^d = (alpha - beta) L_d`. It does not divide
`alpha - beta`, since `P` does not divide `(alpha^2 - beta^2)^2`; so
`P | L_d`, against primitivity. So `z` has order `n` modulo `Pi`. Now
`z = alpha^2/(alpha beta)` lies in `F = Q(sqrt(ab))`, which is `Q` or
quadratic, and its conjugate is `1/z`. `P` does not divide `ab` and is
unramified in `F` if odd. If `P` splits (or `F = Q`), `n | P - 1`; if `P` is
inert, `z^(P+1) == N(z) = 1`, so `n | P + 1`. `P = 2` would give
`n | 1` or `n | 3`. So `P` is odd, `n | P -+ 1`, and since `P -+ 1` is even
and `n` odd, `2n | P -+ 1`.

### F.2.2 The theorem

Theorem F.5 (proven). In case L, let `x >= 11` be odd with `D > 0`,
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
`J1 cap Z = j1 Z`. Put `mu1 = mu / c`, so `(mu1) = J1 A^x` and
`mu1 - mu1' = (f/c) sqrt(-D0)`.

Step 2 (a power). Let `e` be the order of the class of `A`. Its `x`-th power
is the class of `J1^(-1)`, which has order 1 or 2 since `J1^2 = (j1)`. If
the order is 1, put `t = e`; then `t | x`. If it is 2, then `e` divides
`2x` but not `x`, so `e = 2t` with `t | x` and `t` odd, and the class of
`A^t` is the class of `J1`. In both cases `n = x/t` is odd and `J1 A^t` is
principal, `= (rho)`. Then

    (rho^n) = J1^n A^x = (j1)^((n-1)/2) (mu1),

so `rho^n = eps j1^((n-1)/2) mu1` with a root of unity `eps`. If `K` is
`Q(i)` every root of unity is an `n`-th power because `n` is odd; if `K` is
`Q(sqrt(-3))`, then `3 | D`, so `3` does not divide `x` or `n`, and the
same holds. Replacing `rho` by `rho / zeta` with `zeta^n = eps`, we may take
`eps = 1`.

Step 3 (a Lehmer pair). Put `alpha = rho / sqrt(j1)`,
`beta = rho' / sqrt(j1)`. Then `alpha beta = N(rho)/j1 = x^t`. Since
`J1' = J1`, both `rho` and `rho'` lie in `J1`, so
`rho + rho' in J1 cap Z = j1 Z` and `(alpha + beta)^2 = (rho + rho')^2 / j1`
is an integer. `alpha^2 = rho^2 / j1` is integral because
`(rho^2) = (j1) A^(2t)`. Coprimality: a prime `l` dividing `x^t` does not
divide `j1` (`j1 | D` up to a factor 2, `x` is odd and prime to `D`); if it
divided `rho + rho'`, the prime `L` of `A` above `l` would divide `rho` and
`rho + rho'`, hence `rho'`, hence `L' | rho`, but `A^t` holds only one of
`L, L'`. Finally `(alpha/beta)^n = mu/mu' = e^(2 i theta)` with
`tan theta = sqrt(D)/U`. A root of unity of `K` has order at most 6, which
would need `theta >= pi/6`, that is `U^2 <= 3D`, so `4p x^x <= 4D < 16px`,
false. So `alpha/beta` is not a root of unity, and `rho + rho' != 0` for
the same reason. Thus `(alpha, beta)` is a Lehmer pair.

Step 4 (the Lehmer number is small). For odd `n`,

    L_n = (alpha^n - beta^n)/(alpha - beta) = (mu1 - mu1')/(rho - rho')
        = (f/c) / g,

where `rho - rho' = g sqrt(-D0)` with `2g` a nonzero integer. So
`2f = c (2g) L_n`, and every odd prime factor of `L_n` divides `f`.

Step 5 (large `n`). Let `n >= 7`. Since `alpha beta = x^t >= 11 > 9`, Lemma
F.3 gives a primitive divisor `P` of `L_n`, and Lemma F.4 gives `P` odd,
`P >= 2n - 1`. Then `P | f`, so `D0 = D/f^2 <= D/(2n - 1)^2`. The field
`K = Q(sqrt(-D0))` has `|Delta_K| <= 4 D0`, and by Lemma F.2

    x = t n <= e n <= h n <= n * 2 sqrt(D0) (log 4D + 2) / pi
      <= (2n / (2n - 1)) sqrt(D) (log 4D + 2) / pi.

With `n >= 7` the factor is at most `14/13`.

Step 6 (small `n`). If `n <= 5`, then `t >= x/5` and
`x <= 5t <= 5e <= 5h <= 5 * 2 sqrt(D) (log 4D + 2) / pi` by Lemma F.2 with
`|Delta_K| <= 4D`.

Validation (computed). `analysis/r6f_ff_lehmer.gp` builds the objects of
the proof in PARI for 40 planted equations `U^2 + D = 4 x^x` (with
`mu = rho^(x/e)` in eleven fields `Q(sqrt(-D0))`, `D0 <= 95`, class groups
of order up to 5) and for 5,285 artificial equations
`U^2 + D = 4p x^x`, `p = 1, 3, 5`, `9 <= x <= 21`, with ambiguous `J`. In
every case `L_n g = +-(f/c)`, as in Step 4 (`data/r6f_ff_lehmer.txt`). The
artificial equations have huge `D` and so `n = 1`; the planted ones have
`n` up to 59, and include `n = 3` with `e = 3` in `Q(sqrt(-23))`.

### F.2.3 When J is ambiguous

Corollary F.6 (proven and computed). Let `q >= 0`, either convention, and
let `x` be odd with `x > 1 + w(q) + q^2/4` and
`gcd(x, q^2 + 4 + 4 w(q)) = 1`. Then `(1, q, x)` is a solution in some base
only for `(1, 0, 3)` in base 5 under `0^0 = 0` (`25 + 3 = 1 + 27`).
More generally, let `p <= 20` be odd, `q >= 0`, `x` odd with
`x > W + q^2/(4p)`, and suppose the conditions of Corollary F.7 hold. Then
`(p, q, x)` is a solution only in that one case.

Proof. For `p = 1`, `D = 4x - K0` with `K0 = q^2 + 4 + 4w(q)`, so
`gcd(x, D) = gcd(x, K0) = 1`, and by Lemma F.1 (c) `J` has norm 1. So
`J = O_K` is ambiguous. For odd `p`, Corollary F.7 gives the same. Theorem
F.5 then gives `x <= X_A(p) <= 340,896` once `x >= 11` and
`x > 2 log2(pD)`. For `q >= 7` this contradicts `x > W >= 7^7`. For
`q <= 6` (indeed `q <= 20`) the sieve of section F.5 tested every odd
`x <= 10^8`, and the sieve of Proposition F.8 every odd `x <= 7,618` for
`p = 1` and every `q <= 10`: only `(1, 0, 3)` is a solution with
`x > W + q^2/(4p)`.

Remark. When `K0` is a perfect square `k^2` (`q = 1` and `q = 3` under
`0^0 = 1`), the ideal `A` of a prime `x` is generated by
`gamma = (k + sqrt(-D))/2`, of norm `x`, and the equation says that the
Lucas number `u_x(gamma, gamma')` is `+-1`. Theorem 1.4 of BHV excludes this
at once for `x > 30`. The general proof has to go through the class group,
and Lemma F.2 is what makes that cheap.

Corollary F.7 (proven). Let `p` be odd and `x` odd with `D > 0`. Suppose
`gcd(x, p K0) = 1`, `K0 = q^2 + 4pW`, and for every prime `l | p`, with
`k = v_l(p)`: `l^ceil(k/2)` divides `q`, and if `k` is odd, `l` does not
divide `x - W`. Then `gcd(x, D) = 1` and `J` is ambiguous, so Theorem F.5
applies.

Proof. `gcd(x, D) = gcd(x, K0) = 1`, and `J` lives above `p` by Lemma F.1
(c). Let `l | p`. If `k` is even, `l^(k/2)` divides `U = 2pb + q` and `l^k`
divides `D = 4p(x - W) - q^2`, so `l^(k/2)` divides `mu`. As
`v_l(N(mu)) = k`, the `l`-part of `(mu)` is `(l)^(k/2)`. If `k` is odd,
`v_l(q^2) >= k + 1` and `v_l(4p(x - W)) = k`, so `v_l(D) = k` is odd and
`l` ramifies; the `l`-part is `L^k` with `L = L'`. In both cases the
`l`-part is ambiguous.

The test in `r6f_ff_lehmer.gp` confirms the rule against PARI on 6,778
artificial equations with `p` in {3, 5, 9, 15, 25, 27, 45, 75}: the rule
never calls a non-ambiguous `J` ambiguous. It misses 60 ambiguous cases,
all with a prime dividing both `x` and `p`, which the rule excludes for
simplicity. For even `p` the same analysis at 2 is longer and not needed for
the computation.

Proposition F.8 (computed). Let `p, q <= 10`, either convention. Every odd
`x <= max(X_A(p), W + q^2/(4p))` that makes `(p, q, x)` a solution gives
one of these strings. Under `0^0 = 1`: `(1,3,1)` and `(3,1,3)` in base 4,
`(5,1,3)` in base 25, `(6,1,5)` in base 91, `(1,7,1)` in base 904. Under
`0^0 = 0`: `(1,0,3)` in base 5, `(4,0,1)`, `(5,0,1)`, `(7,0,1)`, `(9,0,1)`
in bases 8, 25, 343, 6561, and the swaps `(p, 0, p^p)` for
`p = 3, 5, 7, 9`, in base `p^((p^(p+1) - 1)/2)` (for `p = 3`, base `3^40`).

Method. `r6f_ff_sieve.c` tests `D` for quadratic residues modulo 150 odd
primes, with tables of period `l(l - 1)` (the method of `r6b_sieve.c`,
extended to odd `x` and the leading position). The 120 families of
`r6f_ff_runs.py closure 20 2.2e10` (all with `p, q <= 10`; the families with
larger digits have `W > 2.2 * 10^10`) cover `1.14 * 10^11` values of `x` in
6 minutes on 3 threads. All 17 survivors are decided exactly by
`r6f_ff_runs.py check` (`data/r6f_ff_closure.txt`). The large ones are the
swaps `(p, 0, p^p)` with `R = 0` (case (i) of Theorem 25.7 with `e = 0`).

With the run of section F.5 (all odd `x <= 10^8`): for `p, q <= 10` every
solution `(p, q, x)` with `x` odd is listed above, or has
`x > max(10^8, W + q^2/(4p))`, `J` not ambiguous or `gcd(x, D) > 1`, and
`x <= X_B(p)` by Theorem F.9.

## F.3 Every J: a reduced basis and three logarithms

When `J` is not ambiguous, its class can have order about `h`, and the
Lehmer argument fails. A linear form in logarithms still works, because the
class group is torsion and costs only heights that grow like `sqrt(x)`.

Theorem F.9 (proven, effective). In case L, let `x >= 25` be odd with
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
is half the log of the norm of its denominator ideal, and

    h(rho/rho') <= (1/2) (|s| s(J) + |r| log x) <= (1/2) ||(s, r)||,

with the weighted norm `||(s, r)|| = |s| w_s + |r| log x`. Every nonzero
vector of `Lam` has `||v|| >= pi`, since `w_s >= pi` and `log x >= pi`.

Step 3 (a short basis). Scale the coordinates by `w_s` and `log x`. The
scaled lattice has covolume `e w_s log x`, and a Lagrange-reduced basis
`b1, b2` has `|b1| |b2| <= (2/sqrt 3)` times the covolume. The weighted
norm is at most `sqrt 2` times the Euclidean norm, so

    ||v1|| ||v2|| <= (4/sqrt 3) e w_s log x.

Write `(1, x) = a v1 + b v2`. By Cramer's rule and the bounds on the
coordinates of `v1, v2`, `|a|, |b| <= 0.74 (w_s + x log x)`.

Step 4 (the linear form). With `rho_i` generating the ideals of `v_i`,
`mu = eps rho1^a rho2^b` for a root of unity `eps`. Let `theta` be the
argument of `mu`, `0 < theta < pi/2`, `tan theta = sqrt(D)/U`. Then

    Lam0 = 2 i theta = a log(rho1/rho1') + b log(rho2/rho2') + k log zeta,

with principal logarithms, `zeta = exp(2 pi i / w)` (`w` the number of roots
of unity in `K`), and `|k| <= (w/2)(|a| + |b| + 1) <= B'`. `Lam0 != 0`.
Matveev's theorem (E. M. Matveev, Izv. Math. 64 (2000) 1217-1269, Corollary
2.3, in the form for complex numbers and any determination of the
logarithms: `|Lam| >= exp(-2^(6s+20) D^2 A_1 ... A_s (1 + log D)(1 + log B))`
with `A_j >= max(D h(alpha_j), |log alpha_j|, 0.16)`) with `s = 3`, `D = 2`,
`A_1 A_2 <= ||v1|| ||v2||`, `A_3 = pi`, gives the lower bound. The upper
bound: `U^2 = 4p x^x - D >= 2p x^x`, so
`|Lam0| <= 2 sqrt(D)/U <= sqrt(2D/p) x^(-x/2) <= sqrt(8x) x^(-x/2)`.

Remarks.

- The two logarithms with large height come from the class group, and their
  heights multiply to about `e log(pD) log x`, linear in `e <= h`. This is
  where the imaginary field wins. In a real field the regulator would enter
  the height of every logarithm (section F.4.3).
- With the cruder choice `rho = J A^(x mod e)` and `gamma` generating `A^e`
  the product of heights is about `e^2`, and since `e` can be as large as
  `h`, about `sqrt(x) log x`, the bound fails by a power of `log x`. The
  reduced basis is what saves it: the class of `J` lies in the cyclic group
  of `A`, so a vector `(s, r)` with `|s|, |r|` about `sqrt(e)` exists.
- The bound is far beyond any sieve. For `p, q <= 10` the computation of
  Proposition F.8 and Theorem F.5 leave exactly the strings with `J` not
  ambiguous or `gcd(x, D) > 1`, and `max(10^8, W + q^2/(4p)) < x <= X_B(p)`.

Corollary F.10 (proven). For fixed `p >= 1`, `q >= 0` and either
convention, `(p, q, x)` is a solution for only finitely many `x`, and they
are effectively bounded: `x <= max(X_B(p), W + q^2/(4p))` for odd `x`,
Theorem 32.2 for even `x` and non-square `p`, Theorem 25.7 (ii) for even `x`
and square `p`.

So the last position is settled in finite terms, for every parity and every
square class. This answers question 129 for the last position, and
question 130 for the last position (every `lam` at once).

Uniformity. With `p, q <= B`, odd `x` in the last position satisfies
`x <= max(X_B(B), 2 B^B + B^2)`, and `X_B(B)` grows like `B (log B)^c`. The
second term is the real range `x <= W + q^2/(4p)`, where the field of `R`
is real; there `x` is bounded by its definition but not by a small bound.

## F.4 The middle and leading positions

### F.4.1 Middle, x odd: a local density result

Proposition F.11 (proven). Let `(p, x, q)` with `x` odd be a solution, and
`A = w(p) + w(q) - q`. Then every prime `l` that divides `x` and not `2pA`
satisfies `(pA / l) = 1`. If `pA` is not a perfect square, the set of `x`
for which some base makes `(p, x, q)` a solution has density 0.

Proof. `U^2 = 4p x^x + x^2 + 4pA == 4pA (mod l)` and `l` does not divide
`4pA`, so `pA` is a nonzero square modulo `l`. If `pA` is not a square, the
primes with `(pA/l) = -1` have Dirichlet density 1/2, so the sum of `1/l`
over them diverges. For each `y` the `x` with no prime factor `l <= y` of
that kind have density `prod over such l <= y of (1 - 1/l)` (by the Chinese
remainder theorem), which tends to 0 as `y` grows.

Of the 440 middle families with `p, q <= 20` (both conventions where
`q = 0`), 25 have `pA` a square: `(1, x, 3)`; `(p, x, 1)` with `p` odd or
`p = 4, 16`; and `(p, x, 0)` under `0^0 = 0` for the same `p`. In the last
two `A = p^p`.
The family `(1, x, 1)` is the equation `b(b + x) = x^x + 1` of chapters 16
and 18.

### F.4.2 Leading, x even: the square part

Proposition F.12 (proven, weak). Let `(x, q, r)` be a solution with `x`
even and not a square, `A = w(q) + w(r) - r != 0`, and `x = n f^2` with
`n > 1` squarefree. Then the inequality of Theorem 32.2 holds with `eta` the
fundamental unit of `Q(sqrt n)`, `R = q^2 + 4xA` and `V = 2 f x^(x/2)`.
With `log eta <= sqrt(n) (log 4n + 2)` it bounds `f^2`: for `q, r <= 20`
there is no restriction below about `10^11`, and `f^2 <= 8.3 * 10^8` at
`x = 10^12`, `4.5 * 10^9` at `x = 10^20`, `3.4 * 10^11` at `x = 10^100`.
From `10^12` on, `f^2 <= 1500 (log x)^4` (`r6f_ff_bounds.py lead 20`,
`data/r6f_ff_lead.txt`).

Proof. `4x^(x+1) = n V^2` with `V = 2 f x^(x/2)`, and `U = 2xb + q`. The
proof of Theorem 32.2 uses only that `beta = U - V sqrt n` has norm `R` and
`v_2(V) >= 1 + x/2`; both hold here. The field changes with `x`, but the
inequality is applied to one `x` at a time. The two side cases of that
proof give weaker restrictions; the script allows them too.

This extends Proposition 32.6 (one square class at a time) to every class
whose squarefree part is at least `x / (C (log x)^4)`. It excludes only a
set of density 0, so it is a small step.

### F.4.3 Why the real cases resist

In cases M and Lead the factorization `(mu) = J A^x` (or `A^(x+1)`) still
holds in the real field `K = Q(sqrt R)`, but `mu` is now a unit power times
products of class-group generators. Every logarithm in the linear form
carries the regulator `Reg` in its height. With `h Reg` about
`sqrt(Delta) L(1, chi) / 2` (class number formula):

- Lead: `Delta` is about `16 A x`, so `h Reg` is about `sqrt x`. The
  argument of Theorem F.9 needs `Reg` below `sqrt(x)/(log x)^c` when `J` is
  principal-like and below `x^(1/3)` in general. The 2-adic route of
  Proposition F.12 needs the regulator of `Q(sqrt n)` below
  `sqrt(x)/(log x)^2`.
- M: `Delta` is about `x^2`, so `h Reg` is about `x`. If `Reg` is small (as
  for `A = 1`, where `(x + sqrt(x^2 + 4))/2` is a unit), then `h` is about
  `x / log x`, as large as the exponent itself; this is the class-group
  obstruction of Corollary 18.11. If `A > 1`, the regulator is typically
  close to `x`.

Table F.4.3 (computed, `analysis/r6f_ff_classes.gp`, `quadclassunit`, so
under GRH; illustrations only). Means over 200 to 1,800 consecutive odd or
even `x` above `X`.

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
of `sqrt x`, as the proof of Theorem F.9 must allow. For `q = 1, 3` (`K0` a
square) it is tiny: the ideal of norm `x` is often principal (Remark after
Corollary F.6). In case M with `A > 1` the regulator is between `x/7` and
`x/4` at `x = 10^6`; in case Lead both regulators are a fixed fraction of
`sqrt x`.

## F.5 Computation

Computed. `r6f_ff_sieve.c` on the 1,362 families of
`r6f_ff_runs.py evidence 20 1e8`: the three open cases with small digits at
most 20, both conventions where a small digit is 0, and `x <= 10^8`
(`x` odd in cases L and M, even in case Lead). `RESULT_EVIDENCE`

## F.6 What failed and why

1. Local arguments at the primes of `x` (Lemma 33.1). `l^x` divides `4l x^x`,
   so `R` must be an `l`-adic square. In case L this is implied by Lemma F.1
   (a); in case M it gives Proposition F.11 and nothing more; in case Lead
   `R == q^2 (mod l)` is always a square, so there is no information. The
   `l`-adic Bugeaud-Laurent bound in the Pell form (the method of Theorem
   32.2 at a prime `l | x`) costs a factor about `l^2/(log l)^4` and still
   needs a small regulator of `Q(sqrt(px))`.
2. Primitive divisors for every `J`. If `J` is not ambiguous, `mu` is
   `tau gamma^n` with a non-real `tau`, and `mu - mu'` is a twisted sequence
   `tau gamma^n - tau' gamma'^n`. Primitive divisor theorems for such
   sequences exist (Schinzel, Stewart) but with thresholds depending on the
   heights of `tau, gamma`, which grow here like `sqrt x`.
3. Two logarithms in place of three. A 2-logarithm form needs the class of
   `J` to be trivial or of order 2. Raising `mu` to the order `k` of `J`
   gives `pi_J gamma^N` with `h(pi_J)` about `k log p`; the product of
   heights `k e` is about `x`, too large by a power of `log x`.
4. The modular method. `U^2 + D = 4p X^x` has one `x`-th power and a term
   `D` that is not a power, so there is no Frey curve of signature
   `(x, x, 2)`.
5. Continued fractions. In the Pell form `|R|` is about `sqrt(N)` times `x`,
   above the range `|R| < sqrt N` where `U/V` must be a convergent.
6. Real fields. See section F.4.3. Theorem F.9's argument applies verbatim
   when the regulator is small, but the data show that it rarely is.

## Library corrections

1. Section 32.1.6, last paragraphs: "Pell equations `U^2 - n V^2 = R` in
   which the field changes with `x`. The regulator of `Q(sqrt(px))` can be
   as large as `sqrt(x) log x`, and then every Baker bound is too weak ...
   now seen to be the only obstacle for three digits." The regulator is an
   obstacle of the Pell form only. In the last position the field of `R` is
   imaginary, and the problem is finite (Theorem F.9). The table of section
   32.1.6 should split the row "`n` varies": last position finite, middle
   and leading open.
2. Section 25.1.4, update: "What remains open in case (iii) is ... odd `x`
   that does not lead, and even `x` that leads." Now: odd `x` in the middle,
   and even `x` that leads.
3. Question 129 asks for uniformity over `Q(sqrt(px))`. Answered for the
   last position by passing to `Q(sqrt R)` (Theorem F.9; uniform in `q`).
   Question 130 asks about square classes `lam > 1`: in the last position
   every class is covered at once (Corollary F.10); the middle position
   remains.
4. Section 32.1.5, proof sketch of Theorem 32.5: "Partial summation with
   `|sum chi(k)| <= Delta` gives `L(1, chi) <= log Delta + 2`." With that
   bound partial summation gives `log Delta + 3`; the stated `+ 2` needs
   `|sum| <= Delta/2`, which is true (Lemma F.2). The theorem is unaffected.

## Files

| file | contents |
|---|---|
| `analysis/r6f_ff_bounds.py` | `X_A(p)` (Theorem F.5), `X_B(p)` (Theorem F.9), the square-part bound of Proposition F.12 |
| `analysis/r6f_ff_lehmer.gp` | checks of Steps 3 and 4 of Theorem F.5 and of Corollary F.7 against PARI |
| `analysis/r6f_ff_sieve.c` | sieve for the three positions, either parity, a range of `x` |
| `analysis/r6f_ff_runs.py` | inputs for the sieve (closure and evidence runs) and the exact check of survivors |
| `analysis/r6f_ff_classes.gp` | class numbers, orders and regulators of Table F.4.3 |
| `analysis/data/r6f_ff_closure.txt` | Proposition F.8: survivors, decisions, family counts |
| `analysis/data/r6f_ff_evidence.txt` | section F.5 |
| `analysis/data/r6f_ff_classes.txt` | Table F.4.3 |
| `analysis/data/r6f_ff_lehmer.txt` | output of `r6f_ff_lehmer.gp` |

## New questions

1. A computable bound for case L. Theorem F.9 gives `10^40`. Mignotte's
   bounds for three logarithms, or a primitive divisor theorem for twisted
   sequences `tau gamma^n - tau' gamma'^n` uniform in the height of `tau`,
   would bring it within reach of the sieve and close the last position for
   `p, q <= 10`.
2. A class-group sieve. For `x` with `J` not ambiguous, a solution needs
   `[J] = [A]^(-x)` for one of the `2^omega(x)` ideals `A` of norm `x`, an
   event of chance about `2^omega(x) / e`. Can this be tested fast enough
   (forms of discriminant `-4D`) to run beyond `10^10`?
3. The middle position. Proposition F.11 leaves the 25 families with `pA` a
   square for every `x`, and a density-0 set of `x` for the others. Is there
   a finiteness theorem for `x` prime, where `A` is a prime ideal and the
   class group has order about `x / log x` (`A = 1`) or the regulator is
   about `x` (`A > 1`)?
4. The leading position. Finiteness for those `x` where `Q(sqrt R)` has
   class number above `x^(1/6 + eps)`? These form a thin set, but it would
   be the first result in that case beyond fixed square classes.
5. Other weights. For factorions (chapter 33) the last position has
   `U^2 + |K| = 4p x!`, imaginary as well; `x!` is not a power, so the
   argument does not transfer. Which weights `w(x)` are perfect `x`-th
   powers up to a bounded factor on a large set, so that the imaginary
   argument applies?
