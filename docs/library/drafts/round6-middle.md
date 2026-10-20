# Draft: the middle position, and the leading one

This draft attacks the two open 3-digit cases of chapter 36: an odd large
digit `x` in the middle, and an even large digit in front (questions 151
and 152). Numbering is provisional (`M.n`); it becomes a chapter number when
the draft lands.

Labels: proven (a proof is here, with cited inputs named), computed (a
stated computation), proven and computed, heuristic, conditional. Scripts
are `analysis/r6m_*`, data `analysis/data/r6m_*`. The runs used up to 8
threads.

## Summary

| result | status |
|---|---|
| Middle, `x` odd, `pA = k^2` a square (the 25 families with `p, q <= 20` that Proposition 36.11 cannot touch). The element `theta + k`, `theta = (x + sqrt R)/2`, has norm `kx`. So the ideal of norm `x` is principal up to the primes of `k`, with a generator of height about `log x` | proven (Lemma M.1) |
| In these families an odd prime power `x` prime to `k` gives a unit `u` with `log u` within `O(k^3/x^2)` of `2ke`. Its trace is an integer, and `k^a 2 sinh(2ke)` (or `cosh`) is not one. So `x <= X_sq`, with no linear forms in logarithms | proven, elementary (Theorem M.2) |
| `X_sq = 7.6` for `(1, x, 1)`, `3,438` for `(1, x, 3)`, `5.07 * 10^10` for `(3, x, 1)`, `1.7 * 10^74` for `(4, x, 1)`, `3.0 * 10^167` for `(5, x, 1)`; computable for every `p` | computed (`r6m_square_bounds.py`) |
| So `(1, x, 1)`, `(1, x, 0)` (`0^0 = 0`), `(3, x, 1)` and `(3, x, 0)` (`0^0 = 0`) have no solution with `x` an odd prime power other than the known `x = 3, 7` of `(1, x, 1)`. `(1, x, 3)` has none with `x` an odd prime power other than `5^a`, `a` odd, `5^a > 10^9`, which are finite by Proposition 32.6. The other 18 square families have finitely many odd prime powers `x`, effectively | proven and computed (Corollary M.3) |
| Non-square `pA`: the element `z = (theta + sqrt(pA))/(theta - sqrt(pA))` lives in the biquadratic field `M = K(sqrt(pA))`, and for `p = 1` the ideal of `(mu / mu') z^(-+x)` is `I^(+-2cx)` with `I = L_1 / sigma(L_1)` of norm 1, not 1. Every solution is "mixed" in `M` relative to `Q(sqrt(pA))`. This is why the square trick has no analogue | proven, checked in 50 fields (Lemma M.4) |
| Why the middle position resists: the exponent is `x` and `h Reg` is about `x L(1, chi)`, also of size `x`. Every Baker argument through the S-unit lattice fails by a power of `log x`; Richaud-Degert fields occur only for `pA | x`, and there `h` is about `x / log x` | proven sizes, measured (section M.3) |
| Leading, `x` even: `theta = (q + sqrt R)/2` has norm `-xA`. So `mu = nu theta^(x+1)` with `nu` an S-unit for the primes above `Aq`, a fixed finite set | proven (Lemma M.5) |
| Leading, `x` even: `(x, q, r)` is a solution for only finitely many `x`, effectively, for every `q, r`. The S-unit lattice has covolume about `h Reg`, which is `O(sqrt(x) log x)`, far below the exponent `x + 1`. For `q, r <= 20` the bound is at most `10^186` | proven, effective (Theorem M.6) |
| `b (xb + 1) = x^x + 1`, the families `(x, 1, 1)` and `(x, 1, 0)` under `0^0 = 0`: `S` is empty, two logarithms, `x <= 4.27 * 10^11`; a sieve to that bound leaves nothing | proven and computed (Theorem M.7, Corollary M.8) |
| With chapters 25, 32 and 36: for every pair of small digits, 3-digit strings with one large digit are solutions for only finitely many `x`, except an odd `x` in the middle | proven (Corollary M.9) |
| Corrections: section 36.4.3 and Proposition 36.12 (the leading position does not resist), section 32.1.6, section 25.1.4, the README, question 152 | section "Library corrections" |

## M.1 Where the problem stands

Notation of chapters 25, 32 and 36: `w(0) = m`, `w(d) = d^d` for `d >= 1`.
A 3-digit string with one large digit `x` and small digits gives, after
completing the square, `U^2 = N + R`.

| position | string | `U` | `N` | `R` | status before this draft |
|---|---|---|---|---|---|
| last | `(p, q, x)` | `2pb + q` | `4p x^x` | `q^2 + 4p(W - x)` | finite (Theorem 32.2, Corollary 36.10) |
| middle | `(p, x, q)` | `2pb + x` | `4p x^x` | `x^2 + 4pA` | `x` even finite (Theorem 32.2, Theorem 25.7 (ii)); `x` odd open |
| leading | `(x, q, r)` | `2xb + q` | `4 x^(x+1)` | `q^2 + 4xA` | `x` odd: `N` a square, Theorem 25.7 (ii); `x` even open |

Here `W = w(p) + w(q)`, and `A = w(p) + w(q) - q` (middle) or
`A = w(q) + w(r) - r` (leading). `A >= 1` in both cases, except the
leading strings `(x, 0, 0)` and `(x, 0, 1)` under `0^0 = 0`.

Divided by `4p` (middle) or `4x` (leading) the equations are

    middle:   b (p b + x) = x^x + A,
    leading:  b (x b + q) = x^x + A.

Middle, `x` even. This is closed. If `p` is not a square, Theorem 32.2
bounds `x`. If `p` is a square, `N = 4p x^x` is a square, and Theorem 25.7
(ii) leaves no solution with `x >= 2B + 4`. What remains in the middle is
`x` odd.

## M.2 Middle position, pA a square

### M.2.1 The element theta + k

Let `(p, x, q)` be a middle string with `x` odd and `pA = k^2` for an
integer `k >= 1`. Put

    R = x^2 + 4k^2,   K = Q(sqrt R),   theta = (x + sqrt R)/2,
    mu = (U + sqrt R)/2 = pb + theta,   z = (theta + k)/(theta - k),

and `'` for the conjugation of `K`. `theta` is an algebraic integer with

    theta + theta' = x,   theta theta' = -k^2,
    N(theta + k) = k x,   N(theta - k) = -k x,   N(z) = -1,
    N(mu) = p^2 b^2 + p b x - k^2 = p x^x.

Lemma M.1 (proven). Suppose `x` is odd, prime to `k`, and `R` is not a
square. Then:

- (a) every prime `l | k` and every prime `l | x` splits in `K`;
- (b) for each `l | k` exactly one prime `L_l` above `l` divides `theta`,
  and `(theta) = Kk^2` with `Kk = prod over l | k of L_l^(v_l(k))`;
- (c) `(theta + k) = Kk P` and `(theta - k) = Kk P'`, where `P` is an
  ideal of norm `x` with `P + P' = O_K`; so `(z) = P / P'`;
- (d) `(mu) = J B^x`, where `J = prod over l | p of L_l^(v_l(p))` and `B`
  is an ideal of norm `x` with `B + B' = O_K`. If `x` is a prime power,
  `B` is `P` or `P'`.

Proof. (a) For odd `l | k`, `R == x^2 (mod l)` is a nonzero square. For
`l = 2 | k`, `R == x^2 == 1 (mod 8)`. For `l | x`, `R == 4k^2 (mod l)` is
a nonzero square. No prime of `kx` divides the conductor `f` of
`R = f^2 R0`: such a prime would divide `R` and one of `k, x`, hence both.
So the splitting is read off from `R`. (b) A prime above `l | k` that
divides both `theta` and `theta'` divides `x`, which is prime to `k`. So all of
`v_l(N(theta)) = 2 v_l(k)` sits on one prime `L_l`. (c) At `L_l`,
`v(theta) = 2 v_l(k)` and `v(k) = v_l(k)`, so `v(theta + k) >= v_l(k)`;
at `L_l'`, `theta` is a unit and `v(theta + k) = 0`. Comparing with the
norm `kx` gives `(theta + k) = Kk P` with `N(P) = x`. The same holds for
`theta - k` with an ideal `P''` of norm `x`. A prime dividing `P` and
`P''` divides `2k`, so `P''` is prime to `P`, and then `P'' = P'`. `P` and
`P'` are coprime because `theta + k` and `theta' + k` differ by
`sqrt R`, which is prime to `x`. (d) A prime dividing `mu` and `mu'`
divides `mu - mu' = sqrt R`, which is prime to `x` (as
`gcd(x, R) = gcd(x, 4k^2) = 1`) and to `k` (as `gcd(k, R) = gcd(k, x^2)`).
At `l | x`, all of `v_l(N(mu)) = x v_l(x)` sits on one of `L, L'`. At
`l | p` (so `l | k`), `mu = pb + theta` has `v_(L_l)(mu) >= v_l(p)`,
since `v_(L_l)(theta) = 2 v_l(k) >= v_l(p)` (from `k^2 = pA`), and
`v_l(N(mu)) = v_l(p)`. So `L_l` takes all of it. If `x = l^c`, then
`P = L^c` for one `L | l`, and `B` is `L^c` or `L'^c`.

The point of (c): in a field whose class number is about `x / Reg`, the
ideal of norm `x` has a generator of height about `log x`, up to the fixed
ideal `Kk`. Chapter 18 used the same fact for `k = 1`, where `theta` is a
unit and `P = (theta + 1)` (Lemma 18.2 (c)).

### M.2.2 A unit of bounded height

Theorem M.2 (proven). Let `x >= 2k^2` be a power of an odd prime not
dividing `k` (then `x^2 < R < (x + 1)^2`, so `R` is not a square and
Lemma M.1 applies), and suppose there are integers `e >= 1`, `a >= 0`
with `e v_l(p) = a v_l(k)` for every prime `l | k` (for `p = 1` take
`e = 1`, `a = 0`). Put `f(t) = 2 k^a sinh t` if `e` is odd and
`f(t) = 2 k^a cosh t` if `e` is even, `N0 = floor(f(2ke))`, and

    g- = 2ke - f^(-1)(N0),    g+ = f^(-1)(N0 + 1) - 2ke.

Both are positive. Let `Lam0 = log((U + sqrt R)/(U - sqrt R))`. If
`(p, x, q)` is a solution and `e Lam0 < g+`, then

    x^2 (g- - e Lam0) <= 2 e k^3.

Proof. Step 1 (a unit). By Lemma M.1, `(mu / mu') = (J / J') (z)^(s x)`
with `s = 1` if `B = P` and `s = -1` if `B = P'`. Also
`(theta / k) = Kk / Kk' = prod (L_l / L_l')^(v_l(k))`, and
`(J / J') = prod (L_l / L_l')^(v_l(p))`. The hypothesis on `e, a` gives
`(J / J')^e = (theta / k)^a`. So

    w = (mu / mu')^e z^(-s e x)

has the ideal `(theta / k)^a`, and `u = w (theta / k)^(-a)` is a unit of
`O_K`. In particular `k^a w = u theta^a` is an algebraic integer, and its
trace `T = k^a (w + w')` is a rational integer.

Step 2 (the conjugate). `N(mu / mu') = 1` and `N(z) = -1`, so
`N(w) = (-1)^(ex) = (-1)^e`, since `x` is odd. Hence `w' = (-1)^e / w`.

Step 3 (the size of `w`). `mu, mu' > 0` and `z > 1`, so `w > 0`. Write
`w = exp(-s tau)` with `tau = e (x log z - s Lam0)`. Then
`|T| = f(tau)` (up to sign `T = +-k^a (e^tau + (-1)^e e^(-tau))`).
Now `log z = 2 artanh(k / theta)`. With `y = k / theta < 1`,
`y <= artanh y <= y / (1 - y^2)`, and `theta^2 - k^2 = theta (theta +
theta') = theta x`, so `y / (1 - y^2) = k / x`. Also
`theta <= x + k^2 / x`. Together

    2k (1 - k^2 / x^2) <= 2k / (1 + k^2/x^2) <= x log z <= 2k.

So `tau` lies in `[2ke - 2e k^3 / x^2 - e Lam0, 2ke + e Lam0]`, and
`tau < 2ke` if `s = 1`.

Step 4 (integrality). `f` is increasing on `t > 0`. Since `e Lam0 < g+`,
`f(tau) < N0 + 1`, so the integer `|T|` is at most `N0`, and
`tau <= f^(-1)(N0) = 2ke - g-`. With the lower bound of Step 3,
`2e k^3 / x^2 + e Lam0 >= g-`.

Positivity. `f(2ke)` is not an integer: otherwise `e^(2ke)` would be a
root of a nonzero rational quadratic, against Lindemann's theorem
(`e^c` is transcendental for algebraic `c != 0`). So `g- > 0`, and
`g+ > 0` trivially.

Remarks.

- No linear form in logarithms is used. The equation says that the unit
  `u` has `log u` within `O(k^3 / x^2)` of the fixed number `2ke`, plus
  `a log(theta / k)`; only the integrality of a trace is needed. In
  particular a solution forces `u = +-1` (possible only if `a >= 1` and
  `tau = a log(theta / k)`) or `Reg(K) <= 2ke + a log(x/k) + 1`, a small
  regulator, while the regulator of `Q(sqrt(x^2 + 4k^2))` is typically
  about `x / 10` (Table M.2.4.1).
- For `k = 1` this is the "`e^2`" of Theorem 16.2 and Proposition 18.6,
  with an explicit constant: `2 sinh 2 = 7.2537`, so the unit must have
  trace 7, and `x <= 7.6`.
- `Lam0 <= 2 sqrt(R) / (U - sqrt R)` with `U >= 2 sqrt(p) x^(x/2)`, so
  `Lam0 < x^(2 - x/2)` for `x >= 2k + 11`. The hypothesis `e Lam0 < g+`
  costs nothing in practice.

The condition on `e, a` holds for all 13 equations behind the 25 square
families with `p, q <= 20`: for `(p, x, 1)` and `(p, x, 0)` (`0^0 = 0`)
one has `A = p^p`, `k = p^((p+1)/2)`, so `v_l(k) = v_l(p) (p + 1)/2` for
every `l`; this gives `(e, a) = ((p+1)/2, 1)` for odd `p` and
`(p + 1, 2)` for `p = 4, 16`. For `(1, x, 3)`, `p = 1`, `A = 25`, `k = 5`.

### M.2.3 The square families with small digits

Table M.2.3.1 (computed, `r6m_square_bounds.py 20`,
`data/r6m_square_bounds.txt`; 60 to 1,000 digits of precision).

| equation | families | `k` | `(e, a)` | `f(2ke)` | `g-` | `X_sq = sqrt(2ek^3/g-)` |
|---|---|---:|---|---:|---:|---:|
| `b(b + x) = x^x + 1` | `(1,x,1)`; `(1,x,0)`, `0^0 = 0` | 1 | (1, 0) | 7.2537 | 0.0343 | 7.64 |
| `b(b + x) = x^x + 25` | `(1,x,3)` | 5 | (1, 0) | 22026.4657 | `2.11 * 10^-5` | 3,438 |
| `b(3b + x) = x^x + 27` | `(3,x,1)`; `(3,x,0)`, `0^0 = 0` | 9 | (2, 1) | `3.88 * 10^16` (frac 0.044) | `1.13 * 10^-18` | `5.07 * 10^10` |
| `b(4b + x) = x^x + 4^4` | `(4,x,1)`; `(4,x,0)` | 32 | (5, 2) | `9.65 * 10^141` | `1.19 * 10^-143` | `1.66 * 10^74` |
| `b(5b + x) = x^x + 5^5` | `(5,x,1)`; `(5,x,0)` | 125 | (3, 1) | `6.57 * 10^327` | `1.27 * 10^-328` | `3.03 * 10^167` |
| `b(pb + x) = x^x + p^p`, `p = 7, 9, ..., 19, 16` | 16 families | `p^((p+1)/2)` | as above | about `e^(2ke)` | | about `e^(ke)` |

For `p >= 7` the bound is effective: `f(2ke)` is not an integer, so a
finite computation of `e^(2ke)` to enough digits gives `N0`, `g-` and
`X_sq`. The numbers are astronomically large (`2ke = 19,208` for `p = 7`,
about `1.2 * 10^14` for `p = 19`).

Corollary M.3 (proven and computed). Under either convention:

- (a) `(1, x, 1)` and `(1, x, 0)` (`0^0 = 0`) with `x` an odd prime power
  are solutions only for `x = 3` (base 4) and `x = 7` (base 904). This is
  Proposition 18.6 again, by a shorter route.
- (b) `(3, x, 1)` and `(3, x, 0)` (`0^0 = 0`) are never solutions with `x`
  an odd prime power.
- (c) `(1, x, 3)` is never a solution with `x` an odd prime power, except
  possibly `x = 5^a` with `a` odd and `5^a > 10^9`. Those are finitely
  many, effectively (Proposition 32.6 with the square class `5`).
- (d) For the other 18 square families with `p, q <= 20`, only finitely
  many odd prime powers `x` give a solution, and they are effectively
  bounded.

Proof. Prime powers `x` prime to `k`: Theorem M.2 gives `x <= X_sq`
once `x >= 2k^2` and `e Lam0 < g+` (true for `x >= 41` in the three
computed families; smaller `x` are in the sieve range). The sieve of
section 36.5 tested every odd `x <= 10^9` in all middle families with
`p, q <= 20`; its only survivors in these families are `x = 1, 3, 7`
of `(1, x, 1)` and `(1, x, 0)`. For `(3, x, 1)` and `(3, x, 0)` the sieve was extended
to every odd `x` with `10^9 < x <= 5.07 * 10^10` (section M.5): no
survivor. So (a), (b) and (c) hold for `x` prime to `k`.

Prime powers `x = l^c` with `l | k`. Then `x^x = l^(c x)`. If `c x` has
the parity that makes `N = 4p x^x` a square, Theorem 25.7 (ii) applies.
Otherwise the squarefree part of `x` is `l` or 1, a fixed class, and
Proposition 32.6 (fixed class, real Baker) or Proposition 32.7 (odd
squares, `p` not a square, `p, q <= 20`) applies. For `(3, x, 1)`:
`x = 3^c` with `c` odd makes `N = 4 * 3^(1 + c 3^c)` a square, so
Theorem 25.7 (ii) excludes `c >= 3` (`x >= 2B + 4 = 10`) and the sieve
`x = 3`; `c` even makes `x` an odd square, excluded by Proposition 32.7.
For `(1, x, 1)`, `k = 1` and there is nothing to do. For `(1, x, 3)`,
`x = 5^c` with `c` even is a square and `N` is a square; `c` odd is the exception in (c),
covered by the sieve for `5^c <= 10^9`. (d) is Theorem M.2 with the
same treatment of `l | k`.

### M.2.4 What the trace argument cannot do

Composite `x`. If `x` has two prime factors, `B` can take `P` at one of
them and `P'` at the other (a "mixed" solution, as in chapter 18). Then
`(B / B') = (z) Q^(-2)` with `Q = P_T / P_T'` the part of `P` at the
primes `T` where `B` takes `P'`. `w` acquires the factor `rho^(2ex/d)`
for a generator `rho` of `Q^d`, `d` the order of the class of `Q`, and
its height is no longer bounded. The tests of `r6m_square_check.gp` show
both shapes: every artificial solution with `x` a prime power has the unit
of Step 1, and every one with `omega(x) = 2` (9 cases, `x = 21` to 1909)
has none (`data/r6m_square_check.txt`). For `k = 1` chapter 18 turns this
into a class-number condition (Corollary 18.11) with Laurent's bound, which
needs the small unit `theta`. For `k > 1` the fundamental unit of `K` is
usually large (Table M.2.4.1), and that route is closed too.

Table M.2.4.1 (computed, `r6m_regulators.gp`, exact `quadregulator`,
`data/r6m_regulators.txt`). Regulators of `Q(sqrt(x^2 + 4k^2))`, `x`
the next primes after `X`.

| `k` | `X` | primes | mean `Reg / x` | `#{Reg <= 2k + log x + 1}` |
|---:|---:|---:|---:|---:|
| 1 | `10^5` | 2,000 | 0.0001 | 2,000 |
| 5 | `10^5` | 2,000 | 0.106 | 1 |
| 5 | `10^7` | 500 | 0.089 | 0 |
| 9 | `10^5` | 2,000 | 0.092 | 1 |

So for `k > 1` a solution with `x` a prime power would need one of the
rare fields with a small unit (first remark after Theorem M.2). Theorem
M.2 does not use this; it covers those fields too.

## M.3 Middle position, pA not a square

### M.3.1 What replaces theta + k

If `pA` is not a square, no element `y + z theta` with small integers
`y, z` has norm divisible by `x`: `N(y + z theta) = y^2 - pA z^2 + x y z`,
and `x | y^2 - pA z^2 != 0` needs `|y|` or `|z|` at least
`sqrt(x / (pA + 1))`. The square case used `y^2 = pA z^2`.

The reason is structural. With `X` an indeterminate and
`theta = (X + sqrt(X^2 + 4pA))/2`, the identity
`(theta + k)(theta' + k) = kX` holds with `k^2 = pA`. Over `Q(X)` it
needs `k` rational: the place `X = 0` splits in
`Q(X)(sqrt(X^2 + 4pA))` exactly when `pA` is a square in `Q`. When `pA`
is not a square, the identity lives over `F = Q(sqrt(pA))`.

Lemma M.4 (proven). Let `pA` not be a square, `x = l^c` a power of an
odd prime `l` prime to `pA` with `(pA / l) = 1` (Proposition 36.11 forces
this), and `R = x^2 + 4pA` such that neither `R` nor `pA R` is a
square (so `M` below has degree 4). Let `F = Q(k)` with
`k = sqrt(pA)`, `M = F(sqrt R)`, `sigma` the automorphism of `M` that
fixes `k` and sends `sqrt R` to `-sqrt R`, and `tau` the one that fixes
`sqrt R` and sends `k` to `-k`. Then:

- (a) `l` splits completely in `M`, and there is a prime `L_1` of `M`
  above `l` with `theta == k (mod L_1)`;
- (b) with `I = L_1 / sigma(L_1)`, the element
  `z = (theta + k)/(theta - k)` of `M` has the ideal
  `(z) = (I^(-1) tau(I))^c` (no other primes);
- (c) the prime `L = L_1 tau(L_1)` of `K` below `L_1` satisfies
  `L / L' = I tau(I)` in `M`, so `(L / L')^c = I^(2c) (z)`.

So for `p = 1` a solution has `(mu / mu') z^(-s x) = I^(2 s c x)` with
`s = +-1`: the ideal of the analogue of `w` is a power of `I^2`, not 1.

Proof. (a) `l` splits in `K` (`R == 4pA`, a nonzero square mod `l`) and
in `F`, so completely in `M` (degree 4, unramified at `l`). Modulo a
prime above `l`, `theta` is a root of `T^2 - x T - k^2 == T^2 - k^2`, so
`theta == k` or `-k`, and the two are distinct as `l` is odd and prime to
`k^2 = pA`. Applying `tau` (which fixes `theta`) switches them, so some
prime has `theta == k`.

(b) From `theta == k (mod L_1)`: `theta == -k` modulo `tau(L_1)`; since
`theta' = x - theta == -theta`, also `theta == -k` modulo `sigma(L_1)`
and `theta == k` modulo `sigma tau(L_1)`. `theta - k` is divisible by
`L_1` and `sigma tau(L_1)` and is `== -2k`, a unit, at the other two.
`N_(M/F)(theta - k) = (theta - k)(theta' - k) = -kx`, so above the prime
`L_1 cap F` of `F` (whose primes in `M` are `L_1`, `sigma(L_1)`) the
valuation is `v_l(x) = c`, all at `L_1`; likewise `c` at
`sigma tau(L_1)`. The same count gives `(tau(L_1) sigma(L_1))^c` for the
`l`-part of `theta + k`. At a prime `P` above a prime `p0 | k` of `F`:
`theta theta' = -k^2` and `theta + theta' = x` is a unit, so `theta` and
`theta'` are not both divisible by `P`; if `sigma(P) = P` this would
force both, so `P` splits in `M / F`. If `P | theta`, then
`v_P(theta) = 2 v_P(k) > v_P(k)`, so `v_P(theta + k) = v_P(theta - k) =
v_P(k)`; at `sigma(P)`, `theta` is a unit and so are `theta +- k`. So
these primes cancel in `z`. No other prime divides `N_(M/F)(theta +- k)
= +-kx`.

(c) `L = L_1 tau(L_1)` because `L_1 cap K` has the two primes `L_1`,
`tau(L_1)` of `M` above it, and `L' = sigma(L)`.

`r6m_biquad_check.gp` checks (b) and (c) with PARI in 50 fields
(`pA` from 2 to 30, not a square, two primes `x` each): every time the
ideal of `z` is `I^(-1) tau(I)` or its inverse and nothing else, and
`L / L' = I tau(I)` (`data/r6m_biquad_check.txt`).

In the square case `M = K`, `tau` is trivial, `sigma(L_1) = L'`, and
the ideal of `z` is `L / L'` itself: the ideal of `mu / mu'` is a power
of `(z)` up to the primes of `p`, which is what Theorem M.2 uses. In the
non-square case the ideal of `mu` is `tau`-invariant and takes `L_1` and
`tau(L_1)` together, while `theta + k` takes `tau(L_1)` and
`sigma(L_1)`. Every solution is "mixed" in `M` relative to `F`, in the
sense of chapter 18. The trace argument would need `I^2` to be principal
with a generator of bounded height; nothing is known about the class of
`I` in `Cl(M)`.

### M.3.2 The size of the obstruction

All Baker arguments of chapters 32 and 36 and of section M.4 below run
through a lattice of S-units. For the middle position with `x` odd the
lattice must contain the primes above `x` (the ideal of norm `x` has no
known small generator), and its covolume is `Reg` times the index of the
principal ideals in the group they generate, at most
`h Reg prod log N(P)`. (This describes the method; it is not a
theorem that no other argument exists.) The class number formula
gives

    h Reg = sqrt(Delta) L(1, chi) / 2,   Delta about x^2 (R = x^2 + 4pA),

so the covolume is about `x L(1, chi) (log x)^2`, while the linear form is
about `x^(-x/2)`, which only gives `x log x / 2 <= C h Reg (log x)^c`.
This fails by a factor `L(1, chi) (log x)^(c-1)`. Under GRH
`L(1, chi) >> 1 / log log x`, so it fails for all large `x`. In the last
position `Delta` is about `x` and `h` about `sqrt x` (chapter 36); in the
leading position `Delta` is about `x` again (section M.4). The middle
position is the only one where the discriminant is of the size of the
square of the exponent.

The Richaud-Degert idea. `R = x^2 + c` with `c = 4pA` is of
Richaud-Degert type `m^2 + r`, `r | 4m`, `-m < r <= m`, with `m = x`
exactly when `pA | x`. Other `m` give `r = c - 2jx - j^2`, which divides
`4(x + j)` only for finitely many `x` per `j`. So the small regulators of
Richaud-Degert type cover only the progression `x == 0 (mod pA)`, where
`x` shares primes with `pA`. And a small regulator is not enough: with
`Reg` about `2 log x`, the class number is about `x / (4 log x)`, and the
order of the class of `B` can be that large. The lattice covolume is still
about `x`. The data of Table 36.4.3.1 (`A = 1`, `Reg / log x = 1.00`) and
Table M.2.4.1 (`k = 1`) show this case. Chapter 18 needed
Corollary 18.11 (a class of order at least `x / (3.3 * 10^4 log x)`) for
exactly this reason.

So what is proven for `pA` not a square remains Proposition 36.11: the
`x` that can occur have density 0. Section M.6 lists the attempts that
failed.

## M.4 Leading position, x even

### M.4.1 The element theta

Let `(x, q, r)` be a leading string with `x` even and `q >= 1` (for
`q = 0` the equation is `x b^2 = x^x + A`, so `x | A` and `x <= A` unless
`A = 0`). Put

    R = q^2 + 4xA,   K = Q(sqrt R),   theta = (q + sqrt R)/2,
    mu = (U + sqrt R)/2 = x b + theta.

Then `theta + theta' = q`, `theta theta' = -xA`, `N(mu) = x^(x+1)`,
`mu - mu' = sqrt R`, and `mu == theta (mod x)`. The constant `R - q^2`
is divisible by `x`: this is the difference from the middle position,
where `R - x^2 = 4pA` is not.

Lemma M.5 (proven). Let `S` be the set of primes of `K` above the primes
dividing `A q`. If `x + 1 > log2 R` and `x > v_l(R)` for every `l | x`,
then `nu = mu / theta^(x+1)` is an S-unit.

Proof. Let `l | x` and `P | l`. If `l` ramifies, `P = P'` and
`v_P(mu) = v_P(mu')`, so `v_P(mu) <= v_P(sqrt R) = v_l(R)`, while
`v_P(mu) = (x + 1) v_l(x)`: false. If `l` is inert,
`v_P(mu) = v_P(mu') = (x + 1) v_l(x) / 2 <= v_l(R) / 2`: false. So `l`
splits, `v_P(mu) + v_P'(mu) = (x + 1) v_l(x)` and
`min(v_P(mu), v_P'(mu)) <= rho_l = v_l(R) / 2`. Let `P` be the prime with
the larger valuation. As `mu - theta = xb`,
`v_P(theta) >= min(v_P(mu), v_l(x)) = v_l(x)`, so
`v_P'(theta) = v_l(xA) - v_P(theta) <= v_l(A)`. If `l` divides neither
`A` nor `q`, then `v_P'(theta) = 0`, `v_P(theta) = v_l(x)`, `rho_l = 0`
(as `gcd(x, R) = gcd(x, q^2)`), `v_P'(mu) = 0` and
`v_P(mu) = (x + 1) v_l(x)`: `nu` is a unit at `P` and `P'`. At primes
not dividing `x`, `mu` is a unit and `theta` has valuation 0 outside the
primes of `A`.

`analysis/r6m_lead_check.gp` tests the lemma on artificial equations
`U^2 = 4 x^n + R` with `x <= 3000` even, `q <= 7`, `A <= 60`,
`3 <= n <= 9`: in all 321 solutions the support of `nu` lies above
`A q` (`data/r6m_lead_check.txt`).

### M.4.2 Finiteness

Theorem M.6 (proven, effective). For every `q >= 1`, `r >= 0` and either
convention, `(x, q, r)` with `x` even is a solution for only finitely many
`x`, and they are effectively bounded. Let `r = 1 + |S|`, `s = r + 1`,
`V_r` the volume of the unit ball in `R^r`, `K_r = 2^r / V_r`, and
`C(s) = 1.4 * 30^(s+3) s^4.5 * 4 (1 + log 2)` (Matveev, real field of
degree 2). If `x + 1 > log2 R` and `x > v_l(R)` for all `l | x`, a
solution satisfies

    ((x+1)/2) log x - log(3 sqrt R)
        <= C(s) (1 + log B') (log(xA) + 1) (sqrt(r+1)/2)^r K_r
           sqrt(2 + |S|) h Reg prod over P in S of log N(P),

with `h Reg <= (sqrt(Delta)/2)(log Delta + 2) <= sqrt(R) (log 4R + 2)`
(`Delta <= 4R` the discriminant of `K`) and
`B' = K_r max(x + 1, 4 K_r sqrt(r+1) (x + 1)(2 log x + log A) / 0.96)`.
For a fixed family the right side is `O(sqrt(x) (log x)^3)`.

Proof. Step 1 (the linear form). By Lemma M.5, `mu = nu theta^(x+1)`, so

    Lam0 = log(mu / mu') = log|nu / nu'| + (x + 1) log|theta / theta'|.

`nu / nu'` lies in the S-unit group `O_S^*` (S is closed under
conjugation). `0 < Lam0 <= 2 sqrt(R) / (U - sqrt R)` with
`U >= 2 x^((x+1)/2)`, so `log Lam0 <= log(3 sqrt R) - ((x+1)/2) log x`
for large `x`.

Step 2 (the S-unit lattice). Let `phi(gamma)` be the vector of
`log|gamma|_v` over the two real places and the places of `S`, with
`|gamma|_P = N(P)^(-v_P(gamma))`. `phi(O_S^*)` is a lattice of rank
`r = 1 + |S|` in the hyperplane `sum = 0`. Its covolume is at most
`sqrt(2) sqrt(1 + |S|/2) Reg h prod log N(P)`: the units give the
sublattice `Z (Reg, -Reg, 0, ...)`, and the projection to the
coordinates of `S` maps `phi(O_S^*)` onto the lattice of principal
S-ideals, of index at most `h` in `prod (log N(P)) Z`; the projection
orthogonal to the unit line scales volumes by `sqrt(1 + |S|/2)`. For
`gamma` in `O_S^*`, `h(gamma) = (1/4) ||phi(gamma)||_1` by the product
formula, so `2 h(gamma) >= |log|gamma||`, and `h(gamma) >= 0.24` unless
`gamma = +-1` (degree 2: Mahler measure at least the golden ratio for
integers, at least 2 otherwise).

Step 3 (short vectors). By Minkowski's second theorem there are
independent `v_1, ..., v_r` in the lattice with
`prod |v_i| <= (2^r / V_r) covol`. They span a sublattice of index
`N <= 2^r / V_r`. So `(nu / nu')^N = +- prod v_i^(m_i)` and by Cramer's
rule (the denominator is `N covol`, the numerator at most
`N ||phi(nu / nu')|| prod over j != i of |v_j|`)
`|m_i| <= ||phi(nu / nu')|| K_r / lambda_1`, with
`lambda_1 >= 0.96 / sqrt(r + 1)` and
`||phi(nu / nu')|| <= 8 h(nu) <= 4 (x + 1)(2 log x + log A)`.

Step 4 (Matveev). `N Lam0 = N (x + 1) log|theta/theta'| + sum m_i
log|v_i| != 0`. Matveev's bound (E. M. Matveev, Izv. Math. 64 (2000)
1217-1269, Corollary 2.3, real case, as used in Proposition 32.7) with
`A_i = 2 h(v_i) <= (sqrt(r+1)/2) |v_i|` and
`A_theta = 2 h(theta / theta') <= log(xA) + 1` gives the inequality. Its
right side is `O(sqrt(x) (log x)^3)` for a fixed family, its left side
grows like `x log x`.

The two features that the middle position lacks are both here: the ideal
of norm `x` is generated, up to `S`, by `theta`, of height `(1/2) log(xA)`;
and the discriminant is about `16 A x`, so `h Reg` is about `sqrt x`.

Table M.4.2.1 (computed, `r6m_lead_bounds.py matveev 20`,
`data/r6m_lead_matveev.txt`). `log10` of the bound of Theorem M.6 for the
families with `1 <= q <= 20`, `r <= 20`, taking `|S| = 2 omega(Aq)` (the
worst case).

| family | `A` | `|S|` | `log10 X_M` |
|---|---:|---:|---:|
| `(x, 1, 1)`, `(x, 1, 0)` (`0^0 = 0`) | 1 | 0 | 28.1 |
| `(x, 1, 2)` | 3 | 2 | 39.6 |
| `(x, 1, 7)` | 823,537 | 6 | 74.9 |
| largest, `(x, 20, 4)` | `1.05 * 10^26` | 20 | 185.5 |

The bounds are far beyond any sieve. The first row has a much better
bound from Laurent's theorem.

### M.4.3 The family b(xb + 1) = x^x + 1

For `(x, 1, 1)` (either convention) and `(x, 1, 0)` under `0^0 = 0`,
`A = 1` and `q = 1`, so `S` is empty: `R = 4x + 1`, `theta` has norm
`-x`, and for every even `x` the proof of Lemma M.5 gives
`(mu) = (theta)^(x+1)` with no size condition (`R` is prime to `x`, and
`2` splits since `R == 1 (mod 8)`).

Theorem M.7 (proven). If `b (xb + 1) = x^x + 1` with `x` even, then
`x <= 4.27 * 10^11`.

Proof. `mu = eps theta^(x+1)` with a unit `eps`, and
`N(eps) = x^(x+1) / (-x)^(x+1) = -1`. So `|eps / eps'| = eps^2` and

    Lam0 = (x + 1) log alpha - 2 j log eta,
    alpha = |theta / theta'| = (sqrt R + 1)/(sqrt R - 1),

with `eta > 1` the fundamental unit and `|eps| = eta^(-j)`. `j >= 1`,
since otherwise `Lam0 >= (x + 1) log alpha`, far above the upper bound
of Step 1 of Theorem M.6. `alpha` is a root of `x T^2 - (2x + 1) T + x`,
so `h(alpha) = (1/2) log(x alpha)`, and no power of `alpha` is a unit
(its ideal is `P / P' != 1`), so `alpha` and `eta` are
multiplicatively independent. Laurent's bound (M. Laurent, Acta Arith.
133 (2008) 325-348, Corollary 2 with `m = 10`, `C = 25.2`, as in section
18.1.4) with `D = 2`, `log A_1 = max(log eta, 1)/2`,
`log A_2 = (1/2) log(x alpha)`, `b_1 = 2j`, `b_2 = x + 1` gives

    -log Lam0 <= 25.2 * 16 * max(log b' + 0.38, 5)^2 log A_1 log A_2,
    b' = 2j / (2 log A_2) + (x + 1) / (2 log A_1).

The upper bound is `-log Lam0 >= ((x+1)/2) log x + log 2 - log(2 sqrt R)`.
`2j log eta < (x + 1) log alpha <= 2.0001 (x + 1) / sqrt R`. The right
side increases with `log eta` (since `M^2 Reg` has derivative
`M (M - 2) > 0` for `M >= 5`), and
`log eta <= h log eta <= (sqrt(R)/2)(log R + 2)`. `r6m_lead_bounds.py
laurent` evaluates the worst case: no even `x > 4.27 * 10^11` satisfies
the inequality (`data/r6m_lead_laurent.txt`).

Corollary M.8 (proven and computed). `(x, 1, 1)` is not a solution in
any base for any `x >= 2`, under either convention; nor is `(x, 1, 0)`
under `0^0 = 0`.

Proof. Odd `x`: `N = 4 x^(x+1)` is a square, and Theorem 25.7 (ii)
excludes `x >= 6`; `x <= 5` is in the lists of chapter 3. Even `x`:
`x <= 4.27 * 10^11` by Theorem M.7. The sieve of section 36.5 left no
survivor in these families for even `x <= 10^9`, and the sieve of
section M.5 none for `10^9 < x <= 4.265 * 10^11`.

### M.4.4 The leading position is finite

Corollary M.9 (proven). Fix the convention and two small digits, and
leave out the two leading families `(x, 0, 0)` and `(x, 0, 1)` under
`0^0 = 0`. Then a 3-digit string made of the two small digits and one
further digit `x` is a solution for only finitely many `x`, effectively
bounded, in each of these cases: `x` last, of either parity (members of
the family of Theorem 25.7 (i), `R = 0`, are at most one `x`); `x`
leading, of either parity; `x` in the middle and even. The only open case
is `x` odd in the middle.

Proof. Last: Corollary 36.10. Leading, `x` odd: `N = 4 x^(x+1)` is a
square, and Theorem 25.7 (ii) leaves no solution with `x >= 2B + 4` and
`R != 0`; `R = q^2 + 4xA = 0` only for the two excluded families.
Leading, `x` even: `q = 0` gives `x | A` with `A != 0`; `q >= 1` is
Theorem M.6. Middle, `x` even: section M.1.

The two excluded families have `R = 0`. They are the self-paying strings:
solutions for every odd `x >= 5` and every square `x` (section 36.5 and
the correction to Corollary 33.17).

## M.5 Computation

Computed (`analysis/r6f_ff_sieve.c` of chapter 36, 8 threads):

- middle, `(3, x, 1)` (`0^0 = 1`) and `(3, x, 0)` (`0^0 = 0`), every odd
  `x` with `10^9 < x <= 5.07 * 10^10`: `2.49 * 10^10` values each, no
  survivor (`data/r6m_sieve.txt`). With section 36.5 the two families
  have no solution with `x <= 5.07 * 10^10`.
- leading, `(x, 1, 1)` (`0^0 = 1`) and `(x, 1, 0)` (`0^0 = 0`), every even
  `x` with `10^9 < x <= 4.265 * 10^11`: `2.13 * 10^11` values each, no
  survivor (`data/r6m_sieve.txt`).

The sieve is the one of chapter 36, whose output section 36.7 checked
against a second sieve with different primes and direct modular powers.

Checks (computed, PARI):

- `r6m_square_check.gp`: artificial equations `p b^2 + x b - A = x^n`
  with `pA = k^2` (`(p, A)` in {(1, 1), (1, 25), (3, 27), (1, 4), (1, 9),
  (3, 3), (5, 125)}), `x` prime to `2k`, small `n`. All 11 solutions with
  `x` a prime power have the unit of Step 1 of Theorem M.2 with the
  predicted `(e, a)` (`(1, 0)` for `p = 1`, `(2, 1)` for `(3, 27)` and
  `(5, 125)`, `(1, 1)` for `(3, 3)`), and `k^a Tr(w)` is an integer. All 9
  with two prime factors have none. The solution
  `(x, n) = (7, 7)` of `b(b + 7) = 7^7 + 1` has `Tr(w) = -7`: the unit
  `(7 + sqrt 53)/2`, the "trace 7" of Theorem M.2.
- `r6m_lead_check.gp`: Lemma M.5 on 321 artificial equations.
- `r6m_regulators.gp`: Table M.2.4.1.

## M.6 What failed and why

1. Richaud-Degert fields (the lead in the brief). `x^2 + 4pA` is of
   Richaud-Degert type only for `pA | x` (section M.3.2). There the
   regulator is about `2 log x`, but then `h` is about `x / log x`, and
   the class of `B` can have order that large. The product, which is what
   enters every Baker bound, is still about `x`.
2. The factorization `(U - x)(U + x) = 4p x^x + 4pA`, that is
   `b (pb + x) = x^x + A`. It is the original equation. It says that
   `x^x + A` has two divisors `b` and `c = pb + x`; no divisor theory of
   `x^x + A` is known that uses this.
3. The joint S-unit lattice in the middle position (the method of Theorem
   M.6). It fails by the factor `L(1, chi) (log x)^c`, because
   `Delta` is about `x^2` (section M.3.2). Under GRH this never helps.
4. The trace argument for mixed `B` (composite `x` in the square
   families). The generator of `Q^d` has height about `d log x + Reg`,
   unbounded (section M.2.4).
5. The biquadratic field `M = K(sqrt(pA))` for non-square `pA`. The
   element `z` exists in `M`, but the ideal of `mu / mu'` is
   `(I^2 (z))^(cx)` with `I^2` of unknown class (Lemma M.4). With all four
   conjugates of `mu / (mu' z^x)` bounded, the obstruction is the
   denominator `I^(2cx)`.
6. Primitive divisors in the real case. `mu = eps rho^n` with a unit
   `eps` of large height; `mu - mu'` is a twisted Lucas sequence, and the
   known primitive-divisor results for twisted sequences have thresholds
   growing with the height of `eps` (chapter 36, section 36.6, item 2).
7. Fixed-`x`, varying-exponent results (Le, Bugeaud-Shorey bounds on the
   number of solutions of `U^2 - D = C x^n`). They bound the number of
   exponents `n` for fixed `x`, but give no way to exclude `n = x`.
8. Weak abc. `c < K rad(abc)^(2 - delta)` for any `delta > 0` bounds `x`
   in every position (as in Proposition 18.13); it is not known for any
   `delta > 0`.

## M.7 Library corrections

1. Section 36.4.3 says of the leading case: "The argument of Theorem 36.9
   needs `Reg` below `sqrt(x)/(log x)^c` when `J` is principal-like and
   below `x^(1/3)` in general." Both requirements come from giving every
   logarithm the height `Reg`. With a reduced basis of the full S-unit
   lattice (units and ideal classes together), the product of the heights
   is the covolume, about `h Reg`, which is `O(sqrt(x) log x)`; and the
   ideal of norm `x` is generated by `theta = (q + sqrt R)/2` up to the
   primes of `Aq`. The leading position is finite (Theorem M.6).
   Proposition 36.12 is superseded.
2. Section 36.4.3, middle case: the statement is right, and section M.3.2
   gives the exact size: the covolume is about `x L(1, chi)`, against an
   exponent `x`.
3. Section 32.1.6, last row of the table ("odd `x` in the middle, even
   `x` leading ... open"): even `x` leading is finite (Theorem M.6).
4. Section 25.1.4 (correction of chapter 36): "What remains open in case
   (iii) is odd `x` in the middle and even `x` that leads." Now only odd
   `x` in the middle, and in the 25 square families only composite `x`
   and the powers `5^a > 10^9`, `a` odd, of `(1, x, 3)`.
5. README, main results: "An odd large digit in the middle and an even one
   in front remain open." Even `x` in front is now finite.
6. Question 152 asks for finiteness when `Q(sqrt R)` has class number
   above `x^(1/6 + eps)`. Answered: finite for every even `x`.
7. Question 151 asks about prime `x`. Answered for the 25 square families
   (Corollary M.3, prime powers); open for `pA` not a square.

## M.8 New questions

These would be questions 159 to 163 of `questions.md`.

1. Mixed solutions in the square families. For `x` with two prime factors,
   a solution needs the class of `Q = P_T / P_T'` to absorb `z^x`. Is there
   a version of Corollary 18.11 for `k > 1`, where `K` has no small unit?
2. The class of `I^2` in the biquadratic field `M = Q(sqrt(x^2 + 4pA),
   sqrt(pA))`, for `x` prime. Is it ever principal with a generator of
   height `O(log x)`? A positive answer for a set of primes `x` of
   positive density would close the middle position on that set by the
   trace argument.
3. A computable bound for the leading families with `|S| > 0`. Theorem M.6
   gives `10^39` and more. With three logarithms and the `l`-adic places of
   `S`, can the bound for `(x, 1, 2)` or `(x, 2, 1)` be brought below
   `10^13`, within reach of the sieve?
4. Prime powers `x = 5^a`, `a` odd, in `(1, x, 3)`: the Pell form in
   `Q(sqrt 5)` with `V` a power of 5 gives a bound by Proposition 32.6.
   Compute it and close `(1, x, 3)` for prime powers.
5. Uniformity for the leading position. Theorem M.6 depends on `A`
   through `sqrt(A)` and the primes of `Aq`, so with `q, r <= B` it gives
   about `x <= B^(B + o(B))`. Is there a bound polynomial in `B`, as
   Theorem 32.5 gives for an even `x` behind a non-square digit?

## Files

| file | contents |
|---|---|
| `analysis/r6m_square_bounds.py` | Table M.2.3.1: `k, e, a`, `f(2ke)`, the gaps and `X_sq` |
| `analysis/r6m_lead_bounds.py` | Theorem M.7 (`laurent`) and Table M.4.2.1 (`matveev B`) |
| `analysis/r6m_square_check.gp` | Lemma M.1 and Theorem M.2 on artificial equations |
| `analysis/r6m_lead_check.gp` | Lemma M.5 on artificial equations |
| `analysis/r6m_regulators.gp` | Table M.2.4.1 |
| `analysis/r6m_biquad_check.gp` | Lemma M.4 (b) and (c) in 50 biquadratic fields |
| `analysis/data/r6m_*.txt` | the outputs; `r6m_sieve.txt` the sieve runs of section M.5 |
