# Draft: k digits with one large digit

This draft takes the question behind "which digit strings are never
solutions" from three digits to `k >= 4`. Fix `k - 1` small digits and
their positions, and let one digit `x` vary. Is the set of `x` (and bases
`b`) that give a solution finite? Is it effectively finite?

For three digits the answer is now yes in every position except an odd
`x` in the middle (Corollary 38.9). For `k >= 4` the answer found here is:

- under abc, yes for every `k`, every position and every pattern, outside
  the identity families (Theorem K.7, a full proof of Theorem 33.19 with
  the constant `(k-1)/(k-2)`);
- unconditionally, yes on three kinds of slices: the Runge classes, where
  `x^x / l` is a `g`-th power for a prime `g | k - 1` (elementary, Theorem
  K.1); the binomial prefixes with `k - 1 | x` (a Thue equation in a fixed
  field, Theorem K.4, which answers question 131); and the patterns where
  the fixed polynomial `Ps - W` is a nonzero constant. Elsewhere the
  admissible `x` have density 0 when `Ps - W` has no rational root
  (Proposition K.3), which is the case for about 99% of the 4-digit
  patterns with `x` not leading;
- the rest is open, and for `k = 4` it has the size of the 3-digit middle
  position: the field in which `x^x` factors has `h R` at least about `x`
  in every position (Table K.5.1), while the explicit Schinzel-Tijdeman
  bound grows like a power of the height (section K.5).

Labels: proven (a proof is here, with cited inputs named), cited, computed
(a stated computation), proven and computed, conditional, heuristic.
Scripts are `analysis/r6k_*`, data `analysis/data/r6k_*`. The runs used at
most 5 threads.

## Summary

| result | status |
|---|---|
| A power identity `Ps + x r^j - W = lam A^g` forces `x` last, under both conventions, except the self-paying strings `(x, 0, ..., 0)` and `(x, 0, ..., 0, 1)` under `0^0 = 0` | proven (Lemma K.0, Theorem 25.2 extended) |
| Runge gap: if `x^x / l` is a `g`-th power for a prime `g | k - 1` (`l` the leading digit), then beyond an explicit `x_R` every solution is a power-identity member with `x` last | proven, elementary (Theorem K.1) |
| `k = 4`, small digits at most 20: `x_R` is at most 55 in every position; with the complete 4-digit list of chapter 3 the Runge classes are closed | proven and computed (Corollary K.2) |
| `k = 5`, small digits at most 5: `x_R <= 29`; the Runge classes (`x^x / l` a square) hold only the listed 5-digit solutions, the swap `(5, 0, 0, 0, 3125)` and self-paying strings under `0^0 = 0` | proven and computed (Corollary K.2') |
| Every prime `l | x` gives a root of `Ps - W` modulo `l^(v_l(x))`. If `Ps - W` has no rational root and degree at most 4, the `x` that occur have density 0; if it is a nonzero constant, `x` divides it | proven (Proposition K.3) |
| `k = 4`, digits at most 10: `Ps - W` has a rational root for 12, 14 and 15 of the 1,420 patterns with `x` last, second or third, and for 247 of 1,662 with `x` leading (20 more are constant) | computed (Table K.3.1) |
| Binomial prefix, `q^2 = 3pr`, `x` last, `3 | x`, `p` not a cube: `Y^3 - n V^3 = R0` in the fixed field `Q(n^(1/3))`; a 3-adic bound for two logarithms gives `x <= X_T(p, q, r)`, at most `1.81 * 10^10` for `p, q, r <= 20` | proven, effective (Theorem K.4; question 131) |
| A sieve to `X_T` closes all 55 such families: none has a solution with `3 | x` | proven and computed (Corollary K.5) |
| For `k = 4` the field of `Ps + x r^j - W` has `|D_K|` about `18 x^2` (last), `100 x^2` to `800 x^2` (leading), `6 x^3` (middle), and `h R` about `x` to `x^1.5` | computed under GRH, illustration (Table K.5.1) |
| The explicit Schinzel-Tijdeman bound (Berczes, Evertse and Gyory) is `m <= c(n) H^(11n)` over `Q`; with `H` about `x` and `m = x` it gives nothing | cited, discussion (section K.5) |
| Under abc: a `k`-digit solution with one digit `x > ((k-1)/(k-2) + eps) B + C(k, eps)` and the others at most `B` is a power-identity member with `x` last, or self-paying | conditional (Theorem K.7) |
| The explicit form `c < rad(abc)^(7/4)` handles only patterns whose Tschirnhaus remainder is constant (`k = 3`, binomial prefixes); for them with digits at most 20, `x <= 73` | conditional, computed (Corollary K.8) |
| Census: all 4-digit strings with three digits at most 10 and the fourth `x <= 10^7`, every position, both conventions (`5.92 * 10^10` values): only the listed solutions and the swaps `(p, 0, 0, p^p)`, `p = 4, 5, 7`, under `0^0 = 0`; under `0^0 = 1` nothing beyond 3435 and `(6, 5, 3, 4)` | computed (section K.7) |
| Corrections: section 32.1.7, the README item on Theorem 33.19 | section "Library corrections" |

## K.1 Setting

Notation of chapters 25 and 32: `w(0) = m`, `w(d) = d^d` for `d >= 1`.
Let `k >= 3` and `d = k - 1`. A string `s` has one digit `x` at the
position of `b^j` (`j = 0` last, `j = d` leading) and `k - 1` small digits
elsewhere. Write

    P(r) = Ps(r) + x r^j,    W = sum of w over the small digits,

where `Ps` is the polynomial of the small digits with `x` replaced by 0.
`s` is a solution in base `b` exactly when

    P(b) - W = x^x,   b > every digit.                          (K.1)

`l` is the leading digit (`l = x` if `j = d`). The fixed polynomial
`Fs = Ps - W` depends on the pattern only. For `x` last, (K.1) is
`H(b) = x^x - x + W` with `H(r) = r Pt(r)` and `Pt` the prefix
polynomial, the form in the question.

Identity families. For each pattern there are at most finitely many `x`
with a power identity `P - W = lam A^g` (Corollary 25.3: the prefix fixes
`x`). So "finitely many `x` for each pattern" is the right statement, and
the identity members are among the finitely many. For uniform statements
(over all patterns with digits at most `B`) the right statement is
"finitely many outside the identity families": Theorem 22.6 and Theorem
25.5 give infinitely many `k`-digit solutions with `x` large. The only
patterns with infinitely many `x` are the self-paying ones of Lemma K.0.

Lemma K.0 (proven). Let `s` have one large digit `x >= 2`, either
convention, and suppose `P(r) - W = lam A(r)^g` in `Q[r]` with `g >= 2`,
`lam > 0` and `A` nonconstant. Then `x` is the last digit, or the
convention is `0^0 = 0`, `x` leads, and every small digit is 0 except
possibly a last digit 1 (then `P - W = x r^d`).

Proof. This is Theorem 25.2, which is stated under `0^0 = 1`. Its proof
uses `w(t) >= t` for every digit, which holds under both conventions. The
case "`F(t) > s_k`" is unchanged. In the case "`F(t) = s_k`" (the last
digit `s_k` small), under `0^0 = 0` the equality `sum w(t_i) = s_k` with
`w(s_k) >= s_k` and `w >= 0` forces `w(s_k) = s_k`, so `s_k` is 0 or 1,
and every other small digit has weight 0, so it is 0. The leading digit
is not 0, so it is `x`, and `P - W = x r^d`. Under `0^0 = 1` this case
needs `s_k = 1` and no other small digit, as in Theorem 25.2.

The exceptions are real: `x b^d = x^x` has the root `b = x^((x-1)/d)`
whenever `x^(x-1)` is a `d`-th power (section 11.5). They are the
`k`-digit form of the families excluded in Corollary 38.9.

## K.2 The Runge gap

For three digits, Theorem 25.7 (ii) shows that a 3-digit string has no
solution with `x >= 2B + 4` when `N = 4 l x^x` is a square and `R != 0`.
The square there is the case `g = 2` of the following theorem. The idea is
Runge's: the curve `y^g = P(b) - W` has `g` places at infinity when `g`
divides `deg P` and the leading coefficient is a `g`-th power, and then an
integral point is pinned to a polynomial branch.

Theorem K.1 (proven). Let `s` be as in K.1 and `g` a prime dividing `d`,
`e = d/g`. Suppose that `x^x / l = Z^g` for a rational `Z > 0`. Let `T =
(P - W)/l`, `A` the monic polynomial of degree `e` with
`deg(T - A^g) < d - e` (the polynomial part of `T^(1/g)`), and
`Rm = T - A^g`. Let `Delta = l * den(A)`, `DR = den(Rm)` (common
denominators of the coefficients), `S` the digit sum, and

    bmax = ((W + x^x)/l)^(1/d),   bmin = ((W + x^x)/S)^(1/d),
    Rb = sum over i of |c_i| bmax^i,   Rm = sum c_i r^i.

If `s` is a solution in base `b` and

    (i)  x^x/l > Rb  and  g (x^x/l - Rb)^((g-1)/g) > Delta Rb,
    (ii) bmin > 1 + DR max |c_i|,

then `Rm = 0`, that is `P - W = l A^g` identically. By Lemma K.0, `x` is
last, or `s` is self-paying under `0^0 = 0`.

Proof. `P` has nonnegative coefficients and leading coefficient `l`, so
`l b^d <= P(b) = W + x^x <= S b^d`, which gives `bmin <= b <= bmax` and
`|Rm(b)| <= Rb`. From `T(b) = x^x / l = Z^g`:

    Z^g - A(b)^g = Rm(b).

Put `y = |A(b)|`. Then `y^g = A(b)^g >= Z^g - Rb > 0` by (i).
`Z = u/v` in lowest terms has `v^g | l`, so `v | l`, and `Delta Z` and
`Delta A(b)` are integers. If `y != Z`, then `|y - Z| >= 1/Delta`, and by
the mean value theorem

    Rb >= |Z^g - y^g| >= g min(Z, y)^(g-1) |Z - y| >= (g/Delta) (x^x/l - Rb)^((g-1)/g),

against (i). So `y = Z`, `A(b)^g = Z^g`, and `Rm(b) = 0`. If `Rm != 0`,
its first nonzero coefficient has absolute value at least `1/DR`, and
Cauchy's bound puts every root in `|z| <= 1 + DR max |c_i|`, against (ii)
since `b >= bmin`. So `Rm = 0`.

When the hypothesis holds. For `x` not leading, `l` is a small digit, and
`x^x / l` is a `g`-th power when `l` is one and `g | x`. For `x` leading,
`x^x / x = x^(x-1)` is a `g`-th power when `g | x - 1`. For `k = 3`
(`g = 2`) this is Theorem 25.7 (ii): `x` even behind a square leading
digit, or `x` odd and leading. For `k = 4` (`g = 3`): `3 | x` behind a
leading digit 1 or 8 (among digits up to 20), or `x == 1 (mod 3)` in
front. When the leading digit is a `g`-th power for every prime `g | d`
(for example 1), the classes cover a share
`1 - prod over primes g | d of (1 - 1/g)` of all `x`: 1/3 for `k = 4`,
1/2 for `k = 5`, 2/3 for `k = 7`, never all.

The quantities in (i) and (ii) are polynomials in `x` and `W` against
`x^(x/d)`, so they hold for all large `x`. `analysis/r6k_runge.py` finds
the largest `x` at which (i) or (ii) fails, for every pattern (it does
not need the hypothesis `x^x / l = Z^g`; the threshold is a property of
the pattern).

Corollary K.2 (proven and computed). Let `k = 4`, small digits at most
20, either convention, and suppose `3 | x` with leading digit 1 or 8 (`x`
not leading), or `x == 1 (mod 3)` with `x` leading. Then `s` is a
solution only if it is in the complete 4-digit list of chapter 3, or one
of `(1, 6, 12, 8916100494921)` (both conventions, Theorem 22.6),
`(8, 0, 0, 16777218)` under `0^0 = 1` (Theorem 25.5), `(8, 0, 0, 16777216)`
under `0^0 = 0` (the swap of section 2.3), or the self-paying
`(x, 0, 0, 0)` and `(x, 0, 0, 1)` under `0^0 = 0`.

Proof. `r6k_runge.py 4 20 300` gives `x_R <= 55` for every pattern
(`data/r6k_runge_k4.txt`). For `x <= 230` and small digits at most 20,
`l b^3 <= W + x^x < 10^544.3`, so `b < 10^181.5`, inside the complete
list of section 11.5 (every 4-digit solution in every base up to
`10^186.5`, both conventions). For `x > x_R`, Theorem K.1 gives an
identity, and by Lemma K.0 `x` is last or `s` is self-paying. With `x`
last and `l` in {1, 8} the identities with digits at most 20 are
`P - W = (r + e)^3` with prefix `(1, 3e, 3e^2)`, `e = 0, 1, 2`, and
`P - W = (2r + e)^3` with prefix `(8, 12e, 6e^2)`, `e = 0, 1`. Their `x`
is `W + e^3`. For `(1, 0, 0)` it is 3 or 1, with `b^3 = 27` or 1, not
valid; for `(1, 3, 3)` it is 56 and for `(8, 12, 6)` it is
`8916117272129`, both prime to 3 and outside the class; for `(1, 6, 12)`
and `(8, 0, 0)` they are the listed members.

Corollary K.2' (proven and computed). Let `k = 5`, small digits at most
5, either convention, and suppose `x^x / l` is a square (for example `x`
even behind a leading digit 1 or 4, or `x` odd and leading). Then `s` is
a solution only if it is in the complete 5-digit list of section 11.5,
or `(5, 0, 0, 0, 3125)` under `0^0 = 0` (a swap: `b^4 = 5^15624`), or
self-paying under `0^0 = 0`.

Proof. `r6k_runge.py 5 5 120` gives `x_R <= 29` for all 8,107 patterns
(`data/r6k_runge_k5.txt`). For `x <= 67`, `l b^4 <= W + x^x < 10^122.4`,
so `b < 10^30.6`, inside the list (complete to `10^30.9`, both
conventions). For larger `x` Theorem K.1 and Lemma K.0 leave the
identities with `x` last. `r6k_identities.py 5 5` lists the 28 prefixes
whose remainder is constant with an integer `x >= 2`, and decides each
exactly: 11 are in the class, and only `(3, 0, 0, 0, 27)` (in the list,
base `3^20`) and `(5, 0, 0, 0, 3125)` have a base
(`data/r6k_identities_k5.txt`).

## K.3 The local condition

Proposition K.3 (proven). Let `s` be a solution with large digit `x`.
Then for every prime `l | x`, `Fs = Ps - W` has a root modulo
`l^(v_l(x))` (namely `b`).

- (a) If `Fs` is a nonzero constant, `x` divides it, so `x <= |Fs|`.
- (b) If `Fs` has degree from 2 to 4 and no rational root, the set of `x`
  for which some base makes `s` a solution has density 0.
- (c) The same holds in any degree when some element of the Galois group
  of `Fs` fixes no root.

Proof. `x b^j == 0` and `x^x == 0` modulo `l^(v_l(x))`, so (K.1) reduces
to `Fs(b) == 0`. (a) is the case of a constant. For (c), Chebotarev gives
a set of primes of positive density at which `Fs` has no root; the sum of
`1/l` over it diverges, and the `x` divisible by none of its primes up to
`y` have density `prod (1 - 1/l)`, which tends to 0 (as in Proposition
36.11). For (b), an irreducible factor of degree at least 2 has an element
without a fixed point (Jordan), and so does a product of two irreducible
quadratics; a product with a linear factor has a rational root. This is
the argument of Theorem 33.10.

For `k = 3` this is Proposition 36.11 in the middle (`Fs = p r^2 - A`) and
the condition `gcd(x, q^2 + 4pW)`-type of Corollary 36.7 in the last
position. Unlike factorials (Theorem 33.10), `x^x` is divisible only by
the primes of `x`, so the condition restricts the primes of `x` and not
their size; it gives density 0, not finiteness.

Table K.3.1 (computed, `r6k_density.py 4 10`, `data/r6k_density.txt`). Patterns of 4-digit
strings with three digits at most 10, both conventions where a digit is
0, by the shape of `Fs`.

| position of `x` | patterns | `Fs` constant | `Fs = 0` | rational root | no rational root |
|---|---:|---:|---:|---:|---:|
| last | 1,420 | 0 | 0 | 12 | 1,408 |
| second (`b^2`) | 1,420 | 0 | 0 | 14 | 1,406 |
| third (`b^1`) | 1,420 | 0 | 0 | 15 | 1,405 |
| leading | 1,662 | 20 | 2 | 247 | 1,393 |

The two patterns with `Fs = 0` are the self-paying ones. The 20 constant
ones are `(x, 0, 0, r)`: `x b^3 = x^x + W - r` forces `x | W - r`. An
example of a rational root with `x` last is `(1, 1, 1)` under `0^0 = 1`:
`Fs = r^3 + r^2 + r - 3 = (r - 1)(r^2 + 2r + 3)`. For such patterns the
ideal of norm `x` in the field of `P - W` has a small generator (section
K.5).

## K.4 Binomial prefixes: a Thue equation (question 131)

Let `(p, q, r, x)` have `x` last and `q^2 = 3pr`. Then

    27 p^2 (p b^3 + q b^2 + r b) = (3pb + q)^3 - q^3,

so with `Y = 3pb + q` and `R0 = q^3 + 27 p^2 (W - x)` the equation is

    Y^3 - 27 p^2 x^x = R0.                                        (K.2)

`R0 = 0` is the power identity (Theorem 25.4). If `p` is a cube and
`3 | x`, `27 p^2 x^x` is a cube and Theorem K.1 applies. If `3 | x` and
`p` is not a cube, write `p^2 = n f^3` with `n > 1` cube-free,
`X = x^(x/3)`, `V = 3 f X`: then `Y^3 - n V^3 = R0`, a Thue equation in
the fixed field `K = Q(alpha)`, `alpha = n^(1/3)`, with a right side that
grows only linearly in `x`.

Theorem K.4 (proven, effective). Let `p` not be a cube, `q^2 = 3pr`,
`3 | x`, `x >= 30`, either convention, and let `eta > 1` be a unit of
`O_K`, `fL` the residue degree of the primes above 3 in the splitting
field `L = K(omega)`, `g0 = 3^fL - 1`. If `(p, q, r, x)` is a solution,
then `x` satisfies one of

    (A) x/3 + 3/2 - log_3|R0| <= C(D) g0 max(log b' + log log 3 + 0.4, 10)^2 log A1 log A2

for `D = 3` or `D = 6`, with `C(D) = 24 * 3 / (2 (log 3)^4) * D^4`,

    log A1 = max((2/3)(log|R0| + log eta), (log 3)/D),
    log A2 = max((2/3) log eta, (log 3)/D),
    b' = 1/(D log A2) + M/(D log A1),
    M = (log 3 + 2 log(alpha V + 1))/log eta + 1/2,

or one of the side bounds (B) `x/3 <= log_3|R0|`, (C) the bound of the
dependent case below, (D) the bound for `m = 0` below, all far smaller.
`analysis/r6k_thue_bound.gp` evaluates them with `|R0|` replaced by
`q^3 + 27 p^2 (W + x)`. For the 55 families with `p, q, r <= 20` (both
conventions where a digit is 0), `fL = 1` in every field, and the bound
`X_T` ranges from `1.11 * 10^9` (`p = 2`) to `1.81 * 10^10`
(`(15, 15, 5)`); the side bounds are below 2,100
(`data/r6k_thue_bound.txt`).

Proof. Step 1 (an associate of small height). `beta = Y - alpha V` is in
`Z[alpha]`, with norm `N(beta) = Y^3 - n V^3 = R0 != 0` (`n` is not a
cube). `K` has one real place, and its units are `+-eta^Z` times a finite
index; any unit `eta > 1` will do below. In the real embedding
`|beta| = |R0| / (Y^2 + Y alpha V + alpha^2 V^2) <= |R0| / (alpha V)^2`.
Choose `m` with `delta = beta eta^(-m)` and
`|R0|^(1/3) eta^(-1/2) < |delta| <= |R0|^(1/3) eta^(1/2)`. The complex
conjugates satisfy `|delta'|^2 = |R0| / |delta|`, so `|delta'|` lies
within `|R0|^(1/3) eta^(+-1/4)`, and since `delta` is an algebraic integer,

    h(delta) <= (1/3)(log|R0| + log eta).

If `m >= 0`, then `m log eta = log|beta| - log|delta| <= (1/2) log eta`
once `|beta| < 1`, so `m = 0`. If `m < 0`,
`|m| log eta = log|delta| - log|beta| <= 2 log|beta'| + (1/2) log eta`
with `|beta'|^2 = Y^2 + Y alpha V + alpha^2 V^2 <= 3 (alpha V + 1)^2`
(as `|Y - alpha V| < 1`), which gives `|m| <= M`. If instead
`|beta| >= 1`, then `(alpha V)^2 <= |R0|`, so `(2x/3) log x < log|R0|`,
far below every bound here.

Step 2 (3-adic closeness). Fix a prime of `L` above 3 and the valuation
`v` on `L` with `v(3) = 1`. Let `sigma` in `Gal(L/Q)` send `alpha` to
`omega alpha`. Then `sigma(beta) - beta = (1 - omega) alpha V`, and
`v(1 - omega) = 1/2`, `v(alpha) >= 0`, `v(V) >= 1 + (x/3) v_3(x) >= 1 + x/3`
because `3 | x`. The three conjugates of `beta` are algebraic integers with
product `R0`, so `v(beta) <= v_3(R0) <= log_3|R0|`. Hence

    v(sigma(beta)/beta - 1) >= x/3 + 3/2 - log_3|R0|.            (K.3)

`sigma(beta)/beta = a_1 a_2^m` with `a_1 = sigma(delta)/delta` and
`a_2 = sigma(eta)/eta`, a unit. If the right side of (K.3) is at most 0,
(B) holds. Assume it is positive.

Step 3 (cases). If `v(a_1) != 0`, then `v(a_1 a_2^m - 1) <= 0`, and (B)
holds. If `m = 0`, then `a_1 = sigma(beta)/beta` is not 1 (as
`sigma(beta) - beta != 0`), and Liouville's inequality
`v(z) <= [L:Q] h(z) / log 3` for `z = a_1 - 1` gives
`x/3 + 3/2 - log_3|R0| <= 6 (2 h(beta) + log 2) / log 3`, which is (D).
`a_2` is not a root of unity: in the embedding where `alpha` is real,
`|a_2| = |eta'| / eta = eta^(-3/2)`.

Dependent case (C). Suppose `a_1, a_2` are multiplicatively dependent.
The group they generate modulo torsion is then cyclic, generated by some
`gamma` in `L`, not a root of unity: `a_2 = zeta_2 gamma^(k_2)`,
`a_1 = zeta_1 gamma^(k_1)`. Voutier's bound (P. Voutier, Acta Arith. 74
(1996) 81-95: `deg(gamma) h(gamma) >= 2 / (log 3 deg(gamma))^3` for
`deg(gamma) >= 2`, and `h >= log 2` in degree 1) gives
`h(gamma) >= 2/(6 (log 18)^3)`, so `|k_2| <= h(a_2)/h(gamma) <= 48.1 log eta`
(with `h(a_2) <= 2 h(eta) = (2/3) log eta`). Also
`|log|a_1|| <= (3/4) log eta`, so `|k_1| <= |k_2|/2`. So
`sigma(beta)/beta = zeta gamma^N'` with `|N'| <= |k_2| (|m| + 1/2)`. Let
`w_L` be the number of roots of unity in `L` and `G` the order of `gamma`
modulo the prime (`G <= g0`). `v(zeta gamma^N' - 1) > 0` gives
`G | w_L N'`, and with `z = gamma^(9G)`, `v(z - 1) >= 3/2 > 1/2`, so
`v(z^t - 1) = v(z - 1) + v_3(t)`. Liouville gives
`v(z - 1) <= 6 (9 G h(gamma) + log 2)/log 3`. Together

    x/3 + 3/2 - log_3|R0| <= 6 (9 g0 (2/3) log eta + log 2)/log 3 + log_3(w_L |N'|).

Main case (A). If `a_1, a_2` are independent and `v(a_1) = 0`, Theorem
32.1 (Bugeaud and Laurent) with `p = 3`, `b_1 = 1`, `b_2 = |m|`, `a_2` or
`a_2^(-1)` as needed, applies in `Q(a_1, a_2)`, of degree `D` in {3, 6}
(`a_2` is not in `Q(omega)`, whose units are roots of unity). Its `g` is
at most `3^f - 1` for the residue degree `f <= fL` of the prime below.
`h(a_1) <= 2 h(delta)` and `h(a_2^(+-1)) <= (2/3) log eta` give `log A1`
and `log A2`. With (K.3) this is (A).

Remarks.

- Question 131 asked for the 2-adic version with `x` even. That works the
  same way with `v_2(V) >= x/3` for `x` even and `3 | x`. The 3-adic
  version needs only `3 | x`, which the Thue form needs anyway, so it
  covers every `x` of the class.
- The proof is that of Theorem 32.2 with the cube in place of the square.
  The field is fixed because `27 p^2 x^x` is `n` times a cube. When
  `3` does not divide `x`, `27 p^2 x^x = n' X'^3` with `n'` the cube-free
  part of `p^2 x^(x mod 3)`, and the field `Q(n'^(1/3))` changes with `x`;
  see section K.5.
- For a fixed cube class of `x` (as in Proposition 32.6), the field is
  fixed again. `3` need not divide `V` then, so the 3-adic step is not
  available, but the archimedean form of the same argument (Matveev, as
  in Proposition 32.6) gives finiteness for each class, effectively.
- For `d = k - 1 >= 4` and a binomial prefix with `d | x`,
  `lam' U^d - V^d = R'` is a Thue equation in a fixed field when it is
  irreducible (Capelli). Baker's bound for Thue equations (cited: A.
  Baker, Phil. Trans. Roy. Soc. London A 263 (1968) 173-191, of the form
  `log max(|U|, |V|) <= c(F) + (log |R'|)^c'`; not checked against the
  original) against `log V >= (x/d) log x` bounds `x` effectively. When
  the form is reducible, `lam'` is a `p`-th power for a prime `p | d`, the
  form is a product of `p` forms of degree `d/p`, all but one of size about
  `V^(d/p)`, and the remaining one is an integer smaller than 1 for large
  `x`: the gap of Theorem K.1, leaving only `R' = 0`. So binomial prefixes
  with `d | x` are effectively finite for every `k >= 4`.

Corollary K.5 (proven and computed). Let `p, q, r <= 20`, `q^2 = 3pr`,
`x >= 3`, `3 | x`, either convention. Then `(p, q, r, x)` is a solution
only for `(1, 6, 12, 8916100494921)`, `(8, 0, 0, 16777218)` under
`0^0 = 1` and `(8, 0, 0, 16777216)` under `0^0 = 0`.

Proof. For `p = 1, 8` this is Corollary K.2. For the 55 families with `p`
not a cube (`data/r6k_thue_bound.txt`), `r6k_sieve.c` tested every
`x == 0 (mod 3)` from 3 to `X_T` (at least the largest of the bounds (A)
for `D = 3, 6` and the side bounds): `1.11 * 10^11` values, no survivor
(`data/r6k_thue_sieve.txt`). The sieve keeps `x` only if for each of the
first 120 primes `l` some `b mod l` solves (K.1) modulo `l`, so it never
removes a solution.

So the binomial 4-digit families with `3 | x` are closed. With `3` not
dividing `x` they are open.

## K.5 Why the generic case resists

The fields. For `k = 3` every finished case had a field of discriminant
about `x` and an exponent about `x`: the imaginary field `Q(sqrt(-D))` of
chapter 36 (`h` about `sqrt x`), the field `Q(sqrt R)` of Theorem 38.6
(`h Reg` about `sqrt x`). The middle position, still open, has
discriminant about `x^2`. In general, (K.1) factors over the field `K_x`
of `P - W`, a polynomial of degree `d` whose coefficients grow with `x`,
and every Baker argument pays for the S-unit lattice of `K_x`, whose
covolume is about `h R` (times the logs of the primes of `S`). By
Brauer-Siegel `h R = |D_K|^(1/2 + o(1))`. The exponent is `x`, and the
linear form is about `x^(-x/d)`, so the method needs `h R` below
`x / (log x)^c`.

Table K.5.1 (computed, `analysis/r6k_fields.gp`, `bnfinit`, so `h R` is
under GRH; 40 values of `x` above `X` each, irreducible cases only;
`data/r6k_fields.txt`).

| pattern | `X` | mean `|D_K| / x^2` | mean `h R / x` | mean `h R / sqrt|D_K|` |
|---|---:|---:|---:|---:|
| last `(1, 1, 1, x)` | `10^4` | 18.6 | 0.98 | 0.26 |
| last `(1, 1, 1, x)` | `10^6` | 19.2 | 1.07 | 0.27 |
| last `(1, 2, 3, x)` | `10^6` | 17.1 | 0.89 | 0.28 |
| last `(2, 0, 0, x)`, `x == 1 (mod 3)` | `10^6` | 36.3 | 0.88 | 0.22 |
| middle `(1, x, 1, 1)` | `10^4` | 57,359 | 86.7 | 0.40 |
| middle `(1, x, 1, 1)` | `10^6` | `5.9 * 10^6` | 896 | 0.43 |
| middle `(1, 1, x, 1)` | `10^6` | `3.7 * 10^6` | 459 | 0.26 |
| leading `(x, 1, 1, 1)` | `10^6` | 95.5 | 5.07 | 0.53 |
| leading `(x, 1, 2, 0)` | `10^6` | 816 | 15.8 | 0.57 |

So for `k = 4` the discriminant is about `x^2` in the last and leading
positions and about `x^3` in the middle ones, and `h R` is at least about
`x`, the size of the exponent, in every position. The last position for
`k = 4` is as hard, by this measure, as the middle position for `k = 3`;
the middle positions are harder. The row `(2, 0, 0, x)` with `3` not
dividing `x` is the binomial case left open by Theorem K.4: the field is
the pure cubic `Q((4(W - x))^(1/3))`, with `|D_K|` between `12 c^2` and
`108 c^2` for `c = x - W` squarefree.

The Schinzel-Tijdeman route. (K.1) for `x` last is `F_x(b) = y^m` with
`F_x = H + x - W`, `y = x`, `m = x`. The Schinzel-Tijdeman theorem bounds
`m` when `F` has two distinct roots and `|y| > 1`. Its explicit form
(cited: A. Berczes, J.-H. Evertse and K. Gyory, Effective results for
hyper- and superelliptic equations over number fields, Publ. Math.
Debrecen 82 (2013) 727-756, Theorem 2.3, checked against arXiv:1301.7168)
reads, for `f(x) = b y^m` over `O_S` with `f` of degree `n` without
multiple roots and `y` not 0 or a root of unity,

    m <= (10 n^2 s)^(40 n s) |D_K|^(6n) P_S^(n^2) e^(11 n d h^),

with `h^` the logarithmic height of `(b, a_0, ..., a_n)`. Over `Q`
(`d = 1`, `s = 1`, `D_K = 1`, `P_S = 1`) this is
`m <= (10 n^2)^(40 n) H^(11 n)` with `H` the largest coefficient. Here
`H` is about `x` and `m = x`: the bound is `x <= c x^(11 d)`, which says
nothing. For a family argument one needs `m <= c H^kappa` with
`kappa < 1`. The sizes above say where such a `kappa` can come from:
in the proof, `m` is bounded by about the covolume `h R` of the field of
`F_x` times powers of `log H`, so `kappa = 1/2` for `d = 2` (chapter 36),
and `kappa` about 1 for `d = 3`, the borderline that the Baker method
misses by a power of `log x` (heuristic: these are the sizes of the class
number formula, not a proof that no other argument exists). I know of no
uniform Schinzel-Tijdeman bound better than polynomial in `H`.

What a rational root of `Fs` buys. If `Fs(m0) = 0` with `m0` an integer
and `x` last, then `N(m0 - theta) = (Fs(m0) + x)/l = x/l` for a root
`theta` of `P - W`: the ideal of norm `x` has a generator of height
`O(log x)`, as `theta` did in Lemma 38.5. This removes the class group
from the lattice, but not the regulator. In the cubic fields of Table
K.5.1 the regulator is not small. The trace argument of Theorem 38.2
needs a root `theta` of size about `x` (so that
`((theta + c)/(theta - c))^x` stays bounded). In the last position the
roots of `P - W` have size about `x^(1/3)`; in the leading position the
roots of the integral form `T^3 + q T^2 + r x T + (s - W) x^2` (with
`T = x r`) have size about `x^(2/3)`. In the two middle positions one
root is about `-x / l` and the other two are small, as in the 3-digit
middle position; whether the trace argument extends there is new
question 4.

## K.6 abc

Theorem 33.19 states, with a proof sketch, that abc bounds a dominant
digit in every length. Here is a full proof with the constant.

Theorem K.7 (conditional on abc). Let `k >= 3`, `d = k - 1`, and
`eps > 0`. There is `C = C(k, eps)` such that the following holds under
either convention. Let `s` be a `k`-digit solution with one
digit `x` and the other digits at most `B`, in any position. If
`x > (d/(d - 1) + eps) B + C`, then `P - W = l A^d` for a linear `A`
(a power identity with `x` last), or `s` is self-paying (Lemma K.0).

Proof. Let `Y = d l b + s_1` (`s_1` the second digit, which may be `x`)
and `C0 = d^d l^(d-1)`. Tschirnhaus: `C0 P(b) = Y^d + Q0(Y)` with
`Q0` in `Z[Y]` of degree at most `d - 2` (the coefficient of `Y^(d-1)`
cancels). Its coefficients are polynomials in the digits, so
`|Q0(Y)| <= c_d M^(2d) Y^(d-2)` for `Y >= 1`, with `M = max(B, x)`. The
equation is

    Y^d + E = C0 x^x,    E = Q0(Y) - C0 W.

If `E = 0`: the polynomial `Q0 - C0 W` vanishes at `Y`. Its coefficients
are integers at most `c_d M^(2d) + C0 W` in absolute value, and
`Y >= (x^x)^(1/d)` exceeds `1 +` that for `x > C`, so the polynomial is
0 by Cauchy's bound. Then `C0 (P - W) = Y^d` identically, a power
identity, and Lemma K.0 applies.

If `E != 0`: let `G = gcd(Y^d, E)`. The largest of the three terms is at
least `Y^d`. abc with an exponent `1 + eps'`, `eps' < 1/(2d)` small in
terms of `eps`, applied as in Theorem 33.16 (the radical of each term
divided by `G` is at most `Y`, `|E|` and `rad(C0) x <= d l x`), gives

    Y^d <= K (Y |E| d l x)^(1 + eps').

Below `eps` stands for `eps'` and `K_eps` for `K`.

Case 1, `|E| <= 2 c_d M^(2d) Y^(d-2)`. Then
`Y^(1 - (d-1) eps) <= K_eps (2 c_d d M^(2d+2))^(1+eps)`, and with
`eps < 1/(2d)` and `d log Y >= x log x - log 2`,
`x log x <= 2 d (log K_eps + O_d(log M))`. Since `M = max(B, x)`, this
gives `x <= C(k, eps)` or `x <= eps B` for large `B`.

Case 2, `|E| <= 2 C0 W <= 2 C0 (k - 1) max(1, B^B)`. Then
`Y^(d - 1 - eps) <= K_eps (2 (k-1) C0 B^B d l x)^(1+eps)`, and with
`C0 = d^d l^(d-1)`, `l <= M`,

    (d - 1 - eps)/d * x log x <= (1 + eps) B log B + O_d(log M) + log K_eps,

so `x log x <= (d/(d-1) + O(eps)) B log B + O_d(log x + log B) + O(log K_eps)`,
and `x <= (d/(d-1) + O(eps)) B + C`.

One of the two cases holds, since `|E| <= |Q0(Y)| + C0 W`.

For `d = 2` this is Theorem 33.16 (`2 + O(eps)`). The constant
`d/(d-1)` tends to 1: for long strings abc forbids a digit much larger
than the others outside the identities. For a fixed pattern it gives
finitely many `x`, and Theorem K.7 with Lemma K.0 says which `x` can be
identity members (at most one per identity, Corollary 25.3). Two or more
comparable large digits remain, as for 3 digits (Proposition 33.20).

The explicit form. With `c < rad(abc)^kappa` in place of abc, Case 2
needs `kappa < d` and Case 1 needs `kappa < d/(d-1)`. The explicit
`kappa = 7/4` of Laishram and Shorey used in section 33.4.2 is above
`3/2`, so it handles Case 1 only for `d = 2`. Case 1 is empty when `Q0`
is constant in `Y` and `x` is last, that is for the binomial prefixes.

Corollary K.8 (conditional on `c < rad(abc)^(7/4)`, computed). Every
4-digit solution `(p, q, r, x)` with `q^2 = 3pr`, `p, q, r <= 20` and
`R0 != 0` has `x <= 73` (`r6k_abc.py 20`, `data/r6k_abc.txt`), so it is
in the complete list of section 11.5. `R0 = 0` is a power identity. So
under this hypothesis every 4-digit solution with such a binomial prefix
is in the list or an identity member, for every `x`, not only `3 | x`.

## K.7 Computation

Census (computed, `r6k_sieve.c` with `r6k_runs.py census 4 10 1e7`,
`data/r6k_census4.txt`). Every 4-digit pattern with three digits at most
10 and one digit `x` in any of the four positions, both conventions where
a small digit is 0 (5,920 patterns; the two self-paying leading patterns
under `0^0 = 0` left out), every `x` from 1 to `10^7`: `5.92 * 10^10`
values, 80 survivors, all decided exactly by `r6k_runs.py check`.

- 60 are not solutions: the root `b` is at most the largest digit, or
  there is no integer root.
- 17 are readings of the known solutions of the list of section 11.5,
  `(2, 0, 2, 4)` and `(8, 0, 2, 4)` (`0^0 = 0`), 3435 and `(6, 5, 3, 4)`
  (both conventions), and `(7, 0, 0, 1)`, `(8, 0, 0, 1)`,
  `(10, 0, 0, 1)` (`0^0 = 0`), each counted once per choice of the digit
  called `x`.
- 3 are the swaps `(p, 0, 0, p^p)` under `0^0 = 0` for `p = 4, 5, 7`:
  `p b^3 + p^p = p^p + (p^p)^(p^p)`, so `b^3 = p^(p^(p+1) - 1)`, a cube
  exactly when `3 | p^(p+1) - 1`. The first two were checked with exact
  integers (bases of 206 and 3,641 digits), the third by this valuation.
  `p = 8` (`x = 16777216`) and `p = 10` are beyond `10^7`.

So under `0^0 = 1` there is no 4-digit solution with three digits at most
10 and the fourth digit at most `10^7` other than 3435 and `(6, 5, 3, 4)`.
The run took about 40 minutes on 2 threads.

Thue run (computed, section K.4): 55 families, `1.11 * 10^11` values,
no survivor (`data/r6k_thue_sieve.txt`).

Heuristic. A string with large digit `x` is a solution with chance about
`(x^x)^(1/d - 1)` (the root heuristic of section 3.5). Beyond `10^7` the
sum over the 5,920 patterns is below `10^(-10^7)`. The census is
evidence for the conjecture below, not a test of it.

Conjecture K.9 (heuristic). For every `k >= 3`, every pattern of small
digits and positions has only finitely many `x`, except the self-paying
patterns of Lemma K.0. This is implied by abc (Theorem K.7).

## K.8 What failed and why

1. Schinzel-Tijdeman with the height tracked: polynomial in `H`, section
   K.5. A bound `m << H^kappa` with `kappa < 1` would be needed.
2. Fixed fields for a general prefix. With `3 | x` and a leading digit
   that is not a cube, `Y^3 - C X^3 = -(a Y + E)` with `a != 0` unless the
   prefix is binomial: `beta = Y - C^(1/3) X` is still small, but its
   norm is about `X`, so its height is about `(1/3) log X`, the size of
   everything else. No small-height associate exists.
3. Elliptic curves for `x` even (`k = 4`). `y^2 = P(b) - W` with
   `y = x^(x/2)` is a family of elliptic curves of height about `log x`.
   The known effective bounds for integral points are exponential in a
   power of the height (for Mordell curves `y^2 = b^3 + c` the bound
   `log|b| <= c_eps |c|^(1+eps)` of H. M. Stark, Acta Arith. 24 (1973),
   cited from memory), against `log y = (x/2) log x` with `|c|` about
   `x`. Hall's conjecture would suffice.
4. Runge with other exponents. `x^x` is an `m`-th power for every
   `m | x`, but Runge's condition for `y^m = P - W` needs `gcd(m, d) > 1`
   and a `g`-th power leading coefficient; this is exactly Theorem K.1.
5. The S-unit equation (Siegel's identity with three roots of `P - W`).
   The ratios `(b - theta_i)/(b - theta_j)` are S-units within
   `x^(1/3) / b` of 1 at every place, but the S-unit regulator is about
   `h R` of a field with `|D_K|` about `x^2`, and the effective bounds for
   S-unit equations (K. Gyory and K. Yu, Acta Arith. 123 (2006) 9-41)
   grow with it. Same obstruction.
6. The trace argument of Theorem 38.2. It needs a root of size `x`; for
   `k = 4` there is none in the last and leading positions (section K.5).
   The middle positions have one, but their discriminant is about `x^3`.
7. The 2-adic argument one `x` at a time (as Proposition 36.12). It gives
   only the `x` whose field has a small regulator, a set of density 0.
8. Explicit abc (`kappa = 7/4`) for non-binomial prefixes: Case 1 of
   Theorem K.7 needs `kappa < 3/2` for `k = 4`.

## K.9 Independent checks

- Proofs. Lemma K.0, Theorem K.1, Proposition K.3, Theorem K.4 and
  Theorem K.7 were checked line by line. Points that needed care: the
  case `0^0 = 0` of Theorem 25.2 (Lemma K.0); in Theorem K.1, `A(b)` can
  be negative for even `g`, so the proof works with `|A(b)|`; the
  denominator of `Z` divides `l`; in Theorem K.4 the bound
  `v(beta) <= v_3(R0)` (all conjugates integral), the degree `D` of
  `Q(a_1, a_2)` (3 or 6, never 1 or 2), the dependent case (the
  generator `gamma` lies in `L`, since the group generated by `a_1, a_2`
  is cyclic modulo torsion), and `log(alpha V + 1)` in `M` (bounded by
  `log(alpha V) + 10^-14` for `x >= 30`; the first version of the script
  dropped the term, and the recomputed bounds are unchanged as integers).
- Bounds. `r6k_ref_bounds.py` recomputes `X_T` from the inequality with
  mpmath, separately from `r6k_thue_bound.gp`: all 55 agree to a relative
  `3 * 10^-7`, the gp value being the larger, and the `m = 0` side bound
  is below 1,000.
- Second sieve. `r6k_refsieve.c` reduces (K.1) modulo 40 primes above
  `2^31` with direct modular powers and decides roots by
  `gcd(f, b^l - b)`, with no tables. On 24 slices of the Thue run (8
  random families; `x` in `[3, 1.5 * 10^6]`, the top `1.5 * 10^6` below
  `X_T` and a random window; `1.2 * 10^7` values) it finds no survivor,
  as the main run. On all 5,920 census patterns for `x <= 2,000` its 78
  survivors are exactly the census survivors in that range
  (`data/r6k_referee.txt`).
- The complete list. `r6k_crosscheck.py` compares the census with the
  list of section 11.5 (`data/k4.txt`). Each of the 26 readings of a
  listed solution that falls in the census range is a survivor, and each
  of the 77 survivors with `x <= 230` (base below `10^186.5`) is a
  solution exactly when it is in the list. The first version of the exact
  test in `r6k_runs.py` missed roots `b` that are powers of 2 (an
  off-by-one in the bracketing); the cross-check found it, and it is
  fixed.
- Validation. The main sieve finds every known 4-digit solution with
  three digits at most 10 that lies in its range, among them
  `(8, 0, 0, 16777218)` under `0^0 = 1` and `(4, 0, 0, 256)`,
  `(5, 0, 0, 3125)`, `(7, 0, 0, 823543)`, `(8, 0, 0, 16777216)` under
  `0^0 = 0`, also with the residue-class stepping of the Thue run.

## Library corrections

1. Section 32.1.7 says that for `k` digits with `k - 1 | x` "completing
   the power works only when the prefix has the binomial shape ...
   Otherwise the equation defines a curve of genus at least 1 that changes
   with `x`, and Baker's method for such curves needs more". When the
   leading digit is a `(k-1)`-th power (or, more generally, `x^x / l` is a
   `g`-th power for a prime `g | k - 1`), Runge's method settles every
   prefix elementarily (Theorem K.1); the binomial shape is needed only
   when the leading digit is not such a power (Theorem K.4).
2. README, main results, the item on Theorem 33.19: "Every `k`-digit
   solution whose largest digit exceeds `C_k max(2, B)` is a
   power-identity member." Under `0^0 = 0` the self-paying strings
   `(x, 0, ..., 0)` and `(x, 0, ..., 0, 1)` are exceptions, as in the
   statement of Theorem 33.19 and the Lean correction of Corollary 33.17.
3. Question 131 asks for `x` even and `3 | x` with a 2-adic bound. The
   3-adic bound covers every `x` with `3 | x` (Theorem K.4), and the
   families with digits at most 20 are closed (Corollary K.5).

## Files

| file | contents |
|---|---|
| `analysis/r6k_sieve.c` | sieve for `k`-digit patterns with one large digit, any position, a residue class of `x` |
| `analysis/r6k_runs.py` | inputs (census, Thue) and the exact check of survivors |
| `analysis/r6k_runge.py` | the thresholds of Theorem K.1 |
| `analysis/r6k_density.py` | Table K.3.1 |
| `analysis/r6k_thue_bound.gp` | the bounds of Theorem K.4 |
| `analysis/r6k_abc.py` | Corollary K.8 |
| `analysis/r6k_fields.gp` | Table K.5.1 |
| `analysis/r6k_identities.py` | the identities inside the Runge classes (Corollary K.2') |
| `analysis/r6k_refsieve.c`, `analysis/r6k_ref_bounds.py`, `analysis/r6k_crosscheck.py` | the checks of section K.9 |
| `analysis/data/r6k_runge_k4.txt`, `r6k_runge_k5.txt`, `r6k_identities_k5.txt` | thresholds and identities |
| `analysis/data/r6k_thue_bound.txt`, `r6k_thue_sieve.txt` | Theorem K.4 and Corollary K.5 |
| `analysis/data/r6k_census4.txt` | the census with the exact check of its survivors |
| `analysis/data/r6k_fields.txt`, `r6k_abc.txt` | Table K.5.1, Corollary K.8 |
| `analysis/data/r6k_referee.txt`, `r6k_ref_bounds.txt` | the second sieve, the cross-check, the recomputed bounds |

## New questions

1. The binomial 4-digit families with `3` not dividing `x`. The field is
   a pure cubic field with `|D_K|` of order `x^2`. Is there an
   argument in the spirit of chapter 36 that uses the two complex places
   and gives a bound with `h R` replaced by something smaller, for example
   the order of the class of the ideal of norm `x`?
2. A sublinear Schinzel-Tijdeman bound. For `F_x = H + c` with `H` fixed
   of degree 3 and `|c|` about `x`, and `F_x(b) = y^m` with `|y| >= 2`,
   is `m << |c|^kappa` with `kappa < 1`? The class number formula makes
   `kappa = 1` the natural size of the Baker method.
3. Hall's conjecture for `k = 4`, `x` even. Does an effective bound
   `log|b| <= c (log H)^C` for integral points on `y^2 = cubic` of height
   `H` (a form of Lang-Hall) follow from anything weaker than abc?
4. The middle positions for `k = 4`. `P - W` has a root near `-x / l`, as
   in the 3-digit middle position where Theorem 38.2 works for the square
   families. Is there a 4-digit analogue of `theta + k` (an element of
   norm a constant times `x` built from the large root) and of the trace
   argument, for some patterns?
5. The rational-root patterns. For `x` last with `Fs(m0) = 0`, the ideal
   of norm `x` has a small generator. Are the regulators of the cubic
   fields in these patterns smaller than in Table K.5.1?
6. Larger digits for `k = 5`. Corollary K.2' closes the Runge classes
   for digits at most 5. With digits up to 20 the threshold may exceed
   67, the reach of the 5-digit list; a sieve as in section K.7 would
   close the gap. Is `x_R` linear in `B` for every `k`, as `2B + 4` is for
   `k = 3`?
