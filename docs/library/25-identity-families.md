# 25. Identity families and 3-digit solutions

This chapter answers questions 64, 65 and 50 of `questions.md`: which
algebraic identities make short strings into solutions, whether
`(1,6,46666)` is the next 3-digit solution after `(1,7,1)`, and whether a
base can have three 3-digit solutions. All statements are under
`0^0 = 1` unless stated otherwise. Each statement carries one mark:

- proven: a proof is in this chapter;
- computed: an exact computation, with its range;
- heuristic: the root heuristic of section 3.5 and section 11.4. It is not
  a proof.

Scripts are in `analysis/` with names starting `r5f_`. Their output is in
`analysis/data/r5f_*`. The runs used one or two threads of the shared
machine. The longest run, the census of section 25.1.5, took about 25 minutes.

Notation. A digit string is `s = (s_1, ..., s_k)`, most significant first.
`P_s(r) = s_1 r^(k-1) + ... + s_k`, `w(d) = d^d` with `w(0) = 1`,
`F(s) = w(s_1) + ... + w(s_k)` and `Q_s = P_s - F(s)`. The string is a
solution in base `b` when `Q_s(b) = 0` and `b` exceeds every digit. Two
functions of one digit appear often: `g(d) = w(d) - d` and
`h_b(d) = d b - w(d)`.

## Summary

| question | answer | status |
|---|---|---|
| 64, positions | In every power identity `Q_s(r) = lam A(r)^j - W`, where `W` is the weight of a set of large digits, the last digit is one of the large digits. So with one large digit it is the last digit, and no identity puts a large digit in the middle or in front. | proven (Theorem 25.2) |
| 64, linear `A` | With `A = c r + e` the members are Theorem 22.6 (`e >= 1`) and a new family with `e = 0`: `(c^j, 0, ..., 0, x)` with `x = c^(j c^j) + j - 1`, for example `(8, 0, 0, 16777218)` in base `16777218^5592406 / 2`. It gives infinitely many solutions of every length `k >= 4`, and the smallest known ones for 4, 5 and 6 digits. A factor `lam` that is not a `j`-th power forces `x` to be a perfect power, a coincidence. | proven (Theorems 25.4, 25.5) |
| 64, other mechanisms | Nonlinear `A`, decomposable `P_s`, products, Aurifeuillian factors, several large digits and a self-paying digit with a paying tail all reduce to one extra Diophantine coincidence. The census of all small prefixes finds no member of any of them. | proven (reductions), computed (census) |
| 64, three digits | With two digits at most `B` and the third `x >= 2B + 4`: `R = 0` exactly for `(lam c^2, 2 lam c e, x)`, `x = w(p) + w(q) + lam e^2`; if the dominant term is a square and `R != 0` there is no solution; otherwise the equation is of Pell type and has no power identity. | proven (Theorem 25.7) |
| 64, conjecture | For each `k >= 3`, all but finitely many `k`-digit solutions are members of the two linear families, and every `k`-digit solution in a base above the largest base of the complete lists is one. | heuristic, computed evidence (Conjecture 25.8) |
| 65, families | `(1,6,46666)` is the next power-identity member after `(1,2,6)`. The 1,267 members with `x < 10^6605.8` are listed in order of base; all have `lam = 1` and even `x`. | proven (Theorem 25.10), computed (list) |
| 65, other strings | No 3-digit solution in bases from 905 to `10^3301` beyond the six known ones. In bases below `46666^23333 - 3`, any other 3-digit solution has two digits above 200 and one above 2000. | computed (Theorem 25.11) |
| 65, the rest | The expected number of such solutions is below `10^-3000`. So `(1,6,46666)` is the next 3-digit solution, but only the family part is proven. | heuristic (2.4) |
| 50, structure | The largest digits of the 3-digit solutions of one base take at most two consecutive values. Every base has at most 30 three-digit solutions, except at most 13 bases near `M^((M-1)/2)` for each `M`, which have at most `2M + 24`. | proven (Theorem 25.15) |
| 50, family bases | A base has at most one power-identity member, and a base with a member has at most 3 three-digit solutions. In the bases of the 80 members with `x < 10^300` the member is the only one. | proven (Propositions 3.4, 3.5), computed |
| 50, data | Every base up to `10^3301` has at most two 3-digit solutions; only base 4 has two. | computed |
| 50, the rest | A third solution in one base needs three independent coincidences. At most two is expected for every base, but no proof is known. | heuristic, open |

## 25.1 Identity families (question 64)

### 25.1.1 Where the large digits sit

Chapter 22 found the binomial families: for them
`Q_s(r) = (c r + e)^j - x^x` exactly. The general shape of such an identity
is the following.

Definition 25.1. Let `L` be a nonempty set of positions of `s` whose digits
are at least 2, the large digits, and let `W` be the sum of their weights.
A power identity for `(s, L)` is an equation

    Q_s(r) = lam A(r)^j - W

in `Q[r]`, with `j >= 2`, a rational `lam > 0` and a nonconstant
`A in Q[r]`. Equivalently, `P_s(r) - E = lam A(r)^j` with `E = F(t)`, where
`t` is the list of digits outside `L`.

With such an identity, `s` is a solution in base `b` exactly when
`W = lam A(b)^j` and `b` exceeds the digits. The heuristic of section 3.5
treats `Q_s(b) = 0` as a coincidence of probability about `1 / P_s'(b)`. An
identity replaces that coincidence by the condition `W = lam A(b)^j`, which
can hold for structural reasons: `W = x^x` is a `j`-th power whenever `j`
divides `x`.

Theorem 25.2 (proven). In every power identity the last position belongs to
`L`.

Proof. Suppose the last digit `s_k` is not large. The constant term of
`P_s(r) - E` is `s_k - F(t)`, and `s_k` is one of the digits of `t`. Since
`w(d) >= d` for every digit, `F(t) >= w(s_k) >= s_k`. Two cases remain.

- `F(t) > s_k`. Then `P_s(r) - E` has the coefficients
  `s_1 > 0, s_2, ..., s_(k-1) >= 0` and a negative constant term. By
  Descartes' rule of signs it has exactly one positive root, counted with
  multiplicity, so that root is simple. It has a positive root `rho`,
  since it is negative at 0 and positive for large `r`. But `rho` is a root
  of `A`, so its multiplicity in `lam A^j` is at least `j >= 2`.
- `F(t) = s_k`. This needs `t = (s_k)` and `w(s_k) = s_k`, so `s_k = 1`
  and every other digit is large. Then `A(0) = 0`, so `r^j` divides
  `P_s(r) - E`, and the coefficient of `r`, which is `s_(k-1)`, is 0. But
  `s_(k-1)` is large, so it is at least 2.

Both cases are impossible.

Corollary 25.3 (proven). Let `s` have one large digit `x`, and suppose
`Q_s(r) = lam A(r)^j - x^x`. Then `x` is the last digit. Write
`s = (t, x)`. Then

    r P_t(r) + C = lam A(r)^j,    x = F(t) + C,

for an integer `C`, so the digits `t` alone fix `j`, `A`, `lam`, `C` and
`x`. The string is a solution in base `b` exactly when `x^x = lam A(b)^j`
and `b > x`.

Proof. Theorem 25.2 puts `x` last. Then `P_s(r) - F(t) = r P_t(r) + x - F(t)`.

By Gauss's lemma we can take `A` in `Z[r]` with coprime coefficients and a
positive leading coefficient. Then `lam` is a positive integer, the content
of `r P_t(r) + C`. So the "digits placed in the middle" of question 64
cannot carry the large weight: an identity always ends in the large digit.

### 25.1.2 Linear A

Let `A = c r + e` with `c >= 1` and `gcd(c, e) = 1`. Then `j = k - 1`, and
the coefficients of `lam A^j` are the digits, so

    t_i = lam c^(j-i) C(j, i) e^i  (i = 0, ..., j-1),    x = F(t) + lam e^j.

All digits are at least 0, so `e >= 0`. The string is a solution in base
`b = (y - e)/c` exactly when `x^x = lam y^j` with `y == e (mod c)` and
`b > x`.

Theorem 25.4 (proven). In this situation:

- (a) If `lam = mu^j` is a `j`-th power, the members are those of Theorem
  22.6 with `c' = mu c` and `e' = mu e` when `e >= 1`, and those of Theorem
  1.5 below when `e = 0`. The condition is that `x^x = y^j` for an integer
  `y` and that `mu c` divides `y - mu e`. When `j | x` this is a
  congruence condition on the parameters.
- (b) If `lam` is not a `j`-th power, then `j` does not divide `x`.
  Write `x = x_1 x_2`, where `x_1` has only primes dividing `lam` and
  `gcd(x_2, lam) = 1`. Then `x_2` is a perfect `m`-th power, with
  `m = j / gcd(j, x) >= 2`.
- (c) If `lam` is a `j`-th power but `j` does not divide `x`, then `x` is a
  perfect `m`-th power, `m = j / gcd(j, x) >= 2`.

Proof. (a) is Theorem 22.6 after rescaling `A`. For (b), if `j | x` then
`x^x` is a `j`-th power, so `lam = x^x / y^j` is a rational `j`-th power and
hence an integer `j`-th power. For a prime `l` not dividing `lam`,
`v_l(x^x) = x v_l(x)` must be divisible by `j`. With `g = gcd(j, x)` this
means that `m = j/g` divides `(x/g) v_l(x)`, and `gcd(m, x/g) = 1`, so `m`
divides `v_l(x)`. (c) is the same argument with no prime of `lam`.

So the members of type (a) with `j | x` come in infinite families cut out
by congruences, as in Corollary 22.7 and Theorem 25.5. Types
(b) and (c) need the number `x`, of size about `w(max t)`, to be a perfect
power apart from a bounded set of primes. The heuristic chance of this is
about `x^(1/m - 1)`, which sums to a small finite number over all
parameters. This is the case "`p x^x` a `j`-th power with `p` not a `j`-th
power" of question 64: it exists, but only through a coincidence.

For 3 digits the counts are explicit (`r5f_members3.py`). Of the shapes
with `p, q <= 2000`, 8,604 have `x` even and `lam > 1`, which (b) excludes;
6,143 have `x` odd and need `x / lam` to be a square. The heuristic number
of squares among them is 0.89, almost all of it from the smallest `x`.
None occurs.

The case `e = 0` was left out of Theorem 22.6, because Proposition 22.8
showed that it gives nothing for 3 digits. For more digits it gives a new
family. Under `0^0 = 1` the `j - 1` zeros weigh 1 each, and the last digit
pays for them.

Theorem 25.5 (proven). Let `j >= 3` and `c >= 2`, such that every prime
factor of `c` divides `j - 1` and `c^(j c^j) == 1 (mod j)`. Put

    x = c^(j c^j) + j - 1,    b = x^(x/j) / c.

Then `(c^j, 0, ..., 0, x)`, with `j - 1` zeros, is a `(j+1)`-digit
solution in base `b` under `0^0 = 1`. The conditions hold for
`c = (j - 1)^a` with any `a >= 1`. So every length `k >= 4` has infinitely
many solutions of this form.

Proof. `x == c^(j c^j) - 1 == 0 (mod j)`, so `y = x^(x/j)` is an integer.
A prime `l` dividing `c` divides `j - 1`, so `x == j - 1 == 0 (mod l)`, and
`v_l(y) = (x/j) v_l(x) >= x/j > c >= v_l(c)`. So `c | y` and `b = y/c` is an
integer, with `b > x > c^j`. Then

    P = c^j b^j + x = y^j + x = x^x + x,
    F = w(c^j) + (j - 1) w(0) + w(x) = c^(j c^j) + j - 1 + x^x = x + x^x.

For `c = (j - 1)^a`, `c == (-1)^a (mod j)` and the exponent `j c^j` is even,
because `j (j - 1)` is even. So `c^(j c^j) == 1 (mod j)`.

For `j = 2` the conditions force `c = 1`, and `(1, 0, 2)` is not valid, as
Proposition 22.8 found. Under `0^0 = 0` the zeros are free, and
`(c^j, 0, ..., 0, c^(j c^j))` is the swap of section 2.3 with `a = c^j`.
So Theorem 25.5 is the swap under `0^0 = 1`: the value of the last digit
pays for the weight of `c^j` and for the `j - 1` zeros.

Check (computed, `r5f_identities.py`, `data/r5f_identities.txt`). The
4-digit member `(8, 0, 0, 16777218)` is checked with exact integers: `y`
has about `4.04 * 10^7` digits and `x^x` about `1.21 * 10^8`. The smallest
member of each length is checked modulo 24 primes above `10^9`.

Table 25.1.6 (computed). The smallest known solution of each length beyond
the complete lists of chapter 3, from Theorem 25.5 and the table of section
22.3.2:

| `k` | Theorem 25.5: `c`, `x` | its base | section 22.3.2: smallest | its base | smaller |
|---:|---|---|---|---|---|
| 4 | 2, `2^24 + 2 = 16777218` | `10^(4.04 * 10^7)` | `(1,6,12,x)`, `x = 8.9 * 10^12` | `10^(3.85 * 10^13)` | Theorem 25.5 |
| 5 | 3, `81^81 + 3`, about `10^154.6` | `10^(10^156.2)` | `(16,64,96,64,x)`, `x` about `10^190.3` | `10^(10^192.0)` | Theorem 25.5 |
| 6 | 2, `2^160 + 4`, about `10^48.2` | `10^(10^49.1)` | `x` about `10^3977` | `10^(10^3980)` | Theorem 25.5 |
| 7 | 5, `5^93750 + 5`, about `10^65528` | `10^(10^65532)` | `(1,6,15,20,15,6,x)`, `x` about `10^26.0` | `10^(10^26.7)` | section 22.3.2 |
| 8 | 6, about `10^(1.52 * 10^6)` | | `x` about `10^18921` | `10^(10^18924)` | section 22.3.2 |
| 9 | 7, about `10^(3.90 * 10^7)` | | `x` about `10^76220` | `10^(10^76224)` | section 22.3.2 |

The smallest `c` for `j = 3` to 12 (lengths 4 to 13) is 2, 3, 2, 5, 6, 7,
2, 9, 5, 11. For 10 digits, `c = 2` gives `x = 2^4608 + 8`, about
`10^1387`; section 22.3.2 lists no 10-digit member.

### 25.1.3 Nonlinear A, decompositions and products

Proposition 25.6 (proven). Let `s = (t, x)` have a power identity with
`deg A = d >= 2`, and suppose `A` is not a constant times a power of a
linear polynomial. Then `s` is a solution only if `y = A(b)` for the
integer `y` with `x^x = lam y^j`. This is one polynomial equation in `b`
for a number `y` of size about `x^(x/j)`, fixed by `t`.

Proof. Corollary 25.3. If `A = mu L^d` with `L` linear, the identity is the
linear one with exponent `j d`.

The heuristic chance that a number of size `y` is a value of a fixed
polynomial of degree `d >= 2` is about `y^(1/d - 1)`. So these members are
coincidences, like the strings of section 3.5. The other mechanisms of
question 64 reduce to the same two cases.

- Decomposable `P_s = G(h(r))`, chapter 12.1 and section 16.3. A power
  identity of the form `G(u) - E = lam (c u + e)^j` gives
  `A = c h + e`, which is nonlinear, so Proposition 25.6 applies. Without
  such an identity a root is a coincidence of the usual kind. The census
  of section 25.1.5 contains every decomposable prefix in its ranges.
- Products. A 3-digit identity `b (p b + q) = F - r` with two algebraic
  factors is the same as `(2 p b + q)^2 = 4 p (F - r) + q^2`, so it is a
  square identity, covered by Theorem 25.7. The Aurifeuillian pair of
  `(1,7,1)` in base 904 is not an identity: `4 * 7^7 + 53 = 1815^2` holds
  for `x = 7` and not as an identity in `x`, and chapter 16 shows that the
  Aurifeuillian route works only for `x = 3, 7`.
- Several large digits. By Theorem 25.2 the last digit is large. The other
  large digits are coefficients of `lam A^j`, and the solution needs
  `W = lam A(b)^j` for a sum `W` of two or more weights. A sum like
  `u^u + v^v` with `u != v` is a `j`-th power times a bounded factor only
  by a coincidence (for `j >= 3` it is a Fermat-type equation). Equal
  digits give `W = 2 x^x`, which is `2 y^j` when `j | x`. For linear `A`
  this needs `x = t_i = lam c^(j-i) C(j, i) e^i` for some `i`, and also
  `x = F(t') + lam e^j >= w(lam c^j) + lam e^j` (`t'` the other prefix
  digits). With `rho = e/c`, the first condition and `x > lam e^j` give
  `rho^(j-i) < C(j, i)`, and then `w(lam c^j) <= x` gives
  `(lam c^j)^(lam c^j - 1) < 2^(j + j^2)`. So `lam c^j` is bounded, and
  only finitely many small strings remain for each `j`. (If `i = 0`, then
  `x = lam c^j >= w(t_1)` forces `e = 0`, and then `x = j - 1`.)
- A self-paying digit with a paying tail, as `(5,1,3)` in base 25. The base
  `a^((a-1)/m)` must have a solution of the tail, which is a coincidence
  (section 18.2).
- A large digit in the middle or in front: excluded by Theorem 25.2. Theorem
  8.3 is the closest case: `(x, 0, ..., 0, d)` has `P_s(r) - E = x r^(k-1)`
  only with `E = d`, while an identity needs `E = F(t) = k - 2 + w(d) > d`.

When the remainder is not 0, that is `Q_s(r) = lam A(r)^j - x^x - kappa`
with `kappa != 0`, the equation `lam A(b)^j - x^x = kappa` is of Pillai
type. If `x^x` is itself `lam` times a `j`-th power, `kappa` must be at
least about `x^(x (j-1)/j)`, which fails for large `x`; this is the square
class of Corollary 8.4. Otherwise it is the generic Pell-type case.

### 25.1.4 Three digits

Theorem 25.7 (proven). Let `s = (p, q, r)` have two digits at most `B >= 1`
and a third digit `x >= 2B + 4`. Let `l` be the leading digit (so `l = x`
when `x` leads). Completing the square gives

    (2 p b + q)^2 = N + R,    N = 4 l x^x,    R = 4 p (F - r) + q^2 - N.

Then exactly one of the following holds.

- (i) `R = 0`. Then `x` is the last digit, `p = lam c^2` and
  `q = 2 lam c e` with `lam` squarefree, `c >= 1`, `e >= 0`, and
  `x = w(p) + w(q) + lam e^2`. Here `Q_s(r) = lam (c r + e)^2 - x^x`, and `s`
  is a solution exactly when `x^x = lam (c b + e)^2`. If `x` is even this
  needs `lam = 1` and `c | x^(x/2) - e` (Theorem 22.6 with `j = 2`). If `x`
  is odd it needs `x / lam` to be a perfect square.
- (ii) `R != 0` and `N` is a perfect square. Then `s` is not a solution.
- (iii) `R != 0` and `N` is not a perfect square. Then `s` has no power
  identity `Q_s = lam A^2 - x^x`, and `s` is a solution exactly when the
  Pell-type equation `U^2 - n V^2 = R` holds with `U = 2 p b + q`, where
  `N = n V^2` and `n > 1` is squarefree.

Proof. If `x` leads, `R = 4x (w(q) + g(r)) + q^2 > 0`, since `w(q) >= 1`
and `g(r) >= 0`. If `x` is in the middle, `R = 4p (w(p) + g(r)) + x^2 > 0`.
So `R = 0` needs `x` last, with `R = 4p (w(p) + w(q) - x) + q^2`. Then
`4p | q^2`. Write `p = lam c^2` with `lam` squarefree. For an odd prime `l`
dividing `lam`, `2 v_l(q) >= 1 + 2 v_l(c)` gives `v_l(q) >= v_l(c) + 1`;
the same count for the other primes and for 2 gives `2 lam c | q`. So
`q = 2 lam c e`, `q^2 / (4p) = lam e^2`, and `x` is as stated. The equation
becomes `(2 lam c (c b + e))^2 = 4 lam c^2 x^x`, that is
`x^x = lam (c b + e)^2`. For even `x`, `x^x` is a square, so `lam` is a
square and `lam = 1`. For odd `x`, `x^x = x (x^((x-1)/2))^2`, so `x / lam`
is a rational square, hence an integer square.

For (ii), let `N = V^2` and `U = 2 p b + q`. If `U > V` then
`R = (U - V)(U + V) >= 2V + 1`. If `U < V` then `|R| >= V + U > V`. So a
solution needs `|R| > sqrt(N)`. Now `sqrt(N) >= 2 x^(x/2)`, and `x/2 >= B + 2`
gives `x^(x/2) >= x^2 x^B >= x^2 (2B + 4)^B >= 6 x^2 B^B`, so
`sqrt(N) >= 12 x^2 B^B`. On the other hand `w` of a small digit is at most
`B^B`, and in the three positions

    last:    |R| <= 4B (2 B^B + x) + B^2,
    middle:  |R| <= 8 B^(B+1) + x^2,
    leading: |R| <= 8 x B^B + B^2,

each at most `9 x^2 B^B`, using `B <= x/2`. So `|R| < sqrt(N)`.

For (iii), a power identity with one large digit puts `x` last
(Theorem 25.2). Then `4p (P_s(r) - F(t))` is
`(2 p r + q)^2 - q^2 + 4p (x - F(t))`, and it is a constant times a square
exactly when `4p (x - F(t)) = q^2`, that is when `R = 0`. In case (i) with
`N` not a square there is no solution, since a solution makes `N` equal to
`(2 lam c (c b + e))^2`.

`analysis/r5f_bounds.py` checks the inequality `|R| < sqrt(N)` with
logarithms for `B = 1` to 400 and `x` from `2B + 4` to `2B + 400`
(`data/r5f_bounds.txt`).

So among 3-digit strings with one large digit, the identities are exactly
case (i), case (ii) has no solutions, and everything else is the generic
case (iii). This is the classification asked for in question 64, and it
corrects Corollary 8.4 in its final form: the square class adds exactly the
members of case (i). Cases (i) with odd `x` need a coincidence; none occurs
with `p, q <= 2000` (section 25.2).

The six known 3-digit solutions are all small cases: `x` is at most 7, so
`x < 2B + 4`. `(5,1,3)` in base 25 sits on the boundary of (ii):
`N = 4 * 5^6 = 250^2`, `U = 251` and `R = 501 = 2V + 1`.

### 25.1.5 The census (computed)

`r5f_identities.py` takes every prefix `t` of `k - 1` digits up to `D`,
finds every `(j, A, lam, C)` with `r P_t(r) + C = lam A(r)^j` from the
`j`-th root of the power series `1 + sum (t_i / t_0) s^i`, and decides the
two conditions of Corollary 25.3. The condition `x^x = lam y^j` is decided
with valuations and an exact integer root of `x`. The condition
`A(b) = y` is a congruence for linear `A`. For `deg A >= 2` it is tested
modulo every prime below 600; a prime without a root excludes the string.
A string is a member when both conditions hold (`data/r5f_identities.txt`).

| `k` | digits up to | `j` | `deg A` | shapes | `C` integral | `x^x = lam y^j` | members |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 120 | 2 | 1 | 14,520 | 562 | 87 | 65 |
| 4 | 60 | 3 | 1 | 164 | 97 | 4 | 3 |
| 5 | 30 | 2 | 2 | 1,566 | 232 | 65 | 0 |
| 5 | 30 | 4 | 1 | 44 | 35 | 1 | 0 |
| 6 | 16 | 5 | 1 | 17 | 17 | 1 | 0 |
| 7 | 10 | 2 | 3 | 334 | 101 | 42 | 0 |
| 7 | 10 | 3 | 2 | 12 | 7 | 1 | 0 |
| 7 | 10 | 6 | 1 | 10 | 10 | 1 | 0 |

What the census shows.

- Every member is linear with `lam` a `j`-th power and `j | x`. The 65
  members with 3 digits are the first ones of section 25.2. The 3 members with
  4 digits are `(1,6,12,x)` and `(8,24,24,x)` of Theorem 22.6 and
  `(8,0,0,x)` of Theorem 25.5.
- The linear shapes that pass the power test but are not members fail the
  congruence `c | y - e`, or have `b <= x`, like `(1,0,0,0,4)`.
- 108 nonlinear shapes pass the power test (`k = 5` and 7). Each is
  excluded by a prime below 60 at which `A(r) - y` has no root. Two of them
  have `j` not dividing `x`: `(1,0,2,0,1,0,9)` and `(1,2,1,0,0,0,9)`, where
  `x = 9` is a square, the sporadic case (c) of Theorem 25.4.
- No shape with `lam` not a `j`-th power passes the power test.

So in these ranges the only identity members are those of the two linear
families. The census took about 25 minutes, most of it for `k = 7`.

### 25.1.6 A conjecture

Conjecture 25.8 (heuristic). For each `k >= 3`:

- (a) all but finitely many `k`-digit solutions are members of Theorem
  22.6 or Theorem 25.5 (linear `A`, `lam` a `j`-th power, `j | x`);
- (b) every `k`-digit solution in a base above `B_k` is such a member, where
  `B_k` is the largest base in the complete list of chapter 3: `B_3 = 904`,
  `B_4 = 20`, `B_5 = 48`, `B_6 = 9`, `B_7 = 9`.

Evidence.

- The complete lists of chapter 3 and section 11.5 hold no solution above
  these bases up to `10^51` (3 digits), `10^186` (4 digits), `10^30.9`
  (5 digits) and `10^11` (6 digits). Theorem 25.11 extends 3 digits to
  `10^3301`.
- The root heuristic gives every string with largest digit `M` a chance of
  about `M^(-M (k-2)/(k-1))`. Summed beyond the lists this is `10^-74`
  for 3 digits (section 11.4) and below `10^-3000` for the 3-digit range of
  Theorem 25.11.
- Theorem 25.2 and Proposition 25.6 show that every other identity needs one
  more coincidence, and the census and the 3-digit list of section 25.2 find
  none of them.
- The members of the two linear families are infinite for every `k >= 3`
  (`k >= 4` for Theorem 25.5), so (a) cannot be improved to "finitely many
  solutions".

The conjecture fails under `0^0 = 0`, where the self-paying digits and the
swaps of chapter 2 give further identity families, with polynomials
`x r^m` and identities `x b^m = x^x`.

## 25.2 The next 3-digit solution (question 65)

### 25.2.1 The members of the families

By Theorem 25.7, the 3-digit power-identity members are the strings
`(lam c^2, 2 lam c e, x)` of case (i).

Proposition 25.9 (proven). Among the 3-digit members, a larger `x` gives a
larger base.

Proof. A member has `b <= y = sqrt(x^x / lam) <= x^(x/2)`. Take a member
`(p', q', x')` with `x' >= x + 1 >= 7`. Since `x' >= w(p') >= p'^2`,
`sqrt(lam') c' <= p' <= sqrt(x')`, so
`b' >= (y' - e')/c' >= x'^((x'-1)/2) - x'`. Now `x'^((x'-1)/2) >= 49 x'`,
and `x'^((x'-1)/2) >= (x + 1)^(x/2) >= 1.5 x^(x/2)` by Bernoulli's
inequality. So `b' >= (48/49) * 1.5 x^(x/2) > b`.

Theorem 25.10 (proven). After `(1,2,6)` in base 215, the next 3-digit
power-identity member is `(1,6,46666)` in base `46666^23333 - 3`.

Proof. A member with `x <= 46666` has `w(p) <= x` and `w(q) <= x`, so
`p, q <= 6`. With `p = lam c^2` and `q = 2 lam c e`, `e >= 1`, this leaves
`(1,2)`, `(1,4)`, `(1,6)`, `(2,4)`, `(3,6)` and `(4,4)`. The values of `x`
are 6, 261, 46666, 262, 46686 and 513. 261 and 513 are odd and not
squares, 262 and 46686 are even with `lam > 1`, and 46686 also exceeds
46666. With `q = 0` (`e = 0`), `x = w(p) + 1 == 1 (mod lam)`. Odd `x` needs
`lam | x`, so `lam = 1`, and then `x = c^(2c^2) + 1` lies strictly between
two consecutive squares. Even `x` needs `lam = 1` and `c | x^(x/2)`, and
`gcd(x, c) = 1` forces `c = 1`, `x = 2` and `b = 2`, which is not valid. So
only 6 and 46666 remain.

The list (computed, `r5f_members3.py`, `data/r5f_members3.txt`). Since
`x >= w(p)` and `x >= w(q)`, the strings with `p, q <= 2000` hold every
member with `x < 2001^2001`, about `10^6605.8`. There are 1,267 of them,
all with different values of `x`. All have `lam = 1` and even `x`. By
Proposition 25.9 their order by `x` is their order by base. 4 have
`x < 10^10`, 30 have `x < 10^100`, 233 have `x < 10^1000`. The first ones:

| rank | `(p, q, x)` | `(c, e)` | base |
|---:|---|---|---|
| 1 | `(1, 2, 6)` | (1, 1) | 215 |
| 2 | `(1, 6, 46666)` | (1, 3) | `46666^23333 - 3`, about `10^108941.8` |
| 3 | `(4, 8, 16777476)` | (2, 2) | about `10^(10^7.78)` |
| 4 | `(9, 6, 387467146)` | (3, 1) | about `10^(10^9.22)` |
| 5 | `(1, 10, 10000000026)` | (1, 5) | about `10^(10^10.70)` |
| 6 | `(1, 14, 11112006825558066)` | (1, 7) | about `10^(10^16.95)` |
| 7 | `(4, 16, 18446744073709551888)` | (2, 4) | about `10^(10^20.25)` |
| 8 | `(1, 18, x)`, `x` about `3.93 * 10^22` | (1, 9) | about `10^(10^23.65)` |
| 9 | `(9, 18, x)`, `x` about `3.93 * 10^22` | (3, 3) | about `10^(10^23.65)` |
| 10 | `(1, 22, x)`, `x` about `3.41 * 10^29` | (1, 11) | about `10^(10^30.70)` |
| 11 | `(4, 24, x)`, `x` about `1.33 * 10^33` | (2, 6) | about `10^(10^34.34)` |
| 12 | `(25, 10, x)`, `x` about `8.88 * 10^34` | (5, 1) | about `10^(10^36.19)` |

Members 8 and 9 have `x` values that differ in the 15th digit. With
`c = 1` every odd `e` gives a member, as section 22.3.1 noted. Each member
is checked modulo 24 primes above `10^9`, and the first two with exact
integers.

### 25.2.2 The other strings

Theorem 25.11 (computed). Under `0^0 = 1`:

- (a) every 3-digit solution in a base up to `10^3301` is one of the six of
  chapter 3: `(1,3,1)` and `(3,1,3)` in base 4, `(5,1,3)` in base 25,
  `(6,1,5)` in base 91, `(1,2,6)` in base 215, `(1,7,1)` in base 904;
- (b) every 3-digit solution in a base below `46666^23333 - 3` with at most
  one digit above 200 is one of these six.

So a 3-digit solution in a base strictly between 904 and `46666^23333 - 3`
has two digits above 200, a digit above 2000, and a base above `10^3301`.

Method (`r5f_sieve3.c`, `r5f_sieve3.py`, `data/r5f_sieve3.txt`). A string
is a solution exactly when `D = 4p (F - r) + q^2` is a square `s^2` and
`b = (s - q)/(2p)` is an integer above the digits. The C program tests `D`
for quadratic residues modulo the 108 odd primes below 600, with tables of
`w(d)` modulo each prime. Survivors are checked with exact integers.

- Range of (a): all strings with digits up to 2000. A solution with a
  digit `M > 2000` has `b^2 > M^M / (M + 1) >= 2001^2001 / 2002`, so every
  base below `10^3301.2` is covered.
- Range of (b): all strings with two digits up to 200 and one digit up to
  46,700, in each of the three positions. A solution in a base
  `b < b* = 46666^23333 - 3` has `M^M <= F < (M + 1) b*^2`, so
  `M <= 46666`.

The runs tested `1.36 * 10^10` strings (`data/r5f_sieve3.txt`). Only 12
distinct strings survived all 108 primes, and for each of them `D` is an
exact square. Seven are solutions: the six of chapter 3 and
`(1,6,46666)`, in base `10^108941.79`. The other five have a root that is
not an integer, or an integer root at most the largest digit, such as
`(3,1,2)` at `r = 3` from section 12.4. So the sieve leaves no string
undecided. Run time: about 15 minutes on one thread.

### 25.2.3 What is proven and what is heuristic

Heuristic 25.12. The strings that Theorem 25.11 leaves open have a digit
`M > 2000` and a second digit above 200. By the root heuristic each is a
solution with probability about `M^(-M/2)`, and there are fewer than
`3 M^2` of them for each `M`. The sum over `M > 2000` is below
`3 * 2000^2 * 2000^(-1000)`, about `10^-3294`.

Answer to question 65.

- Proven: `(1,6,46666)` is the second power-identity member after `(1,2,6)`
  (Theorem 25.10). In its base it is the only 3-digit solution
  (Proposition 25.17 and the computation of section 25.3.3).
- Computed: no other 3-digit solution exists in bases from 905 to
  `10^3301`, and below `46666^23333 - 3` none with at most one digit above
  200 (Theorem 25.11). The members up to `x = 10^6605.8`, in order of base,
  are in `data/r5f_members3.txt`.
- Heuristic: the remaining strings, with two digits above 200 and one above
  2000, add an expected `10^-3294` solutions. So `(1,6,46666)` is the next
  3-digit solution after `(1,7,1)`.
- Open: a proof needs the strings with two digits in `[201, 46666]` and a
  digit above 2000. They are generic Pell-type equations with two large
  digits, outside the reach of Theorem 25.7. An exhaustive run of the sieve
  over all strings with digits up to 46,700 has about `10^14` strings and
  was not run.

## 25.3 At most two 3-digit solutions per base (question 50)

### 25.3.1 The largest digit

Lemma 25.13 (proven). Let `s` be a 3-digit solution in base `b` with leading
digit `p` and largest digit `M`. Then `b^2 / 3 <= w(M) < (M + 1) b^2` and
`p = floor(F / b^2)`.

Proof. `F = p b^2 + q b + r` with `q b + r < b^2`, so `p = floor(F / b^2)`
and `b^2 <= F < (p + 1) b^2`. Each weight is at most `w(M)`, so
`F <= 3 w(M)`. And `w(M) <= F < (p + 1) b^2 <= (M + 1) b^2`.

Corollary 25.14 (proven). The largest digits of the 3-digit solutions of one
base take at most two values, and they are consecutive.

Proof. Let `M_1 <= M_2 - 2` both occur, with `M_2 >= 3`. Lemma 25.13 gives
`w(M_2) < (M_2 + 1) b^2 <= 3 (M_2 + 1) w(M_1)`. But
`w(M_2) / w(M_2 - 2) = M_2^2 (1 + 2/(M_2 - 2))^(M_2 - 2) >= 3 M_2^2`, which is
more than `3 (M_2 + 1)`. (`M_1 = 0` would give `b^2 <= 3`.)

Two facts about weights are used below, with `rho_M = w(M-1) / w(M)`:

- `rho_M = (1/M)(1 - 1/M)^(M-1) <= 1/(2M)` for `M >= 2`, since
  `(1 - 1/M)^(M-1)` decreases from 1/2;
- `w(d) - 2 w(d-1) >= w(d) / 2` for `d >= 2`.

The functions `g(d) = w(d) - d` and `h_b(d) = d b - w(d)` matter too.
`g` takes the values 1, 0, 2, 24, 252, ... and is injective. `h_b` is
increasing and then decreasing on `0 <= d < b`, because `w(d+1) - w(d)`
increases with `d`. So each value of `h_b` is taken at most twice.
The same holds for `d b^2 - w(d)`.

### 25.3.2 A bound for every base

Theorem 25.15 (proven). Let `b >= 5`. Under `0^0 = 1`, base `b` has at most
30 three-digit solutions, unless `|b - M^((M-1)/2)| <= 6` for a value `M`
with `b^2 / 3 <= w(M) < (M + 1) b^2`. In that case it has at most `2M + 24`.
There are at most 13 such exceptional bases for each `M`.

Proof. Fix one of the at most two values `M` (Corollary 25.14). Let `u, v`
denote digits below `M`. The solutions with largest digit `M` have one of
these shapes:

| shape | equation | count |
|---|---|---|
| `(M, M, M)` | one equation in `b` | at most 1 |
| `(M, M, u)` | `g(u) = M b^2 + M b - 2 w(M)` | at most 1 |
| `(M, u, M)` | `h_b(u) = 2 w(M) - M - M b^2` | at most 2 |
| `(u, M, M)` | `u b^2 - w(u) = 2 w(M) - M b - M` | at most 2 |
| `(u, M, v)` | `u` takes 2 values, then `g(v)` is fixed | at most 2 |
| `(u, v, M)` | `u` takes 2 values, then `h_b(v)` is fixed | at most 4 |
| `(M, u, v)` | below | |

For the shapes with one `M` and leading digit `u < M`, `F` lies in
`[w(M), w(M) + 2 w(M - 1)]` and `F < (u + 1) b^2 <= M b^2`. So with
`K = w(M) / b^2 < M`, `F / b^2` lies in `[K, K + 2 rho_M K)`, an interval
of length below `2 rho_M M <= 1`, and `u = floor(F / b^2)` takes at most
two values.

This leaves the shape `(M, u, v)`. Its equation is

    w(u) + w(v) - u b - v = Theta,    Theta = M b^2 - w(M).

Let `T` be the largest digit with `w(T) <= 2 M (b + 1)`. For two solutions
`(u, v)` and `(u', v')` of this shape, the difference of the left sides is
`(u - u') b + (v - v')`, below `M (b + 1)` in absolute value. If the
multisets `{u, v}` and `{u', v'}` differed in a digit above `T`, let `d` be
the largest digit whose count differs. The difference of the weight sums
would be at least `w(d) - 2 w(d - 1) >= w(d) / 2 > M (b + 1)`. So all
solutions of this shape share the digits above `T`.

- Two digits above `T`: the multiset `{u, v}` is fixed. Both orders would
  give `(u - v)(b - 1) = 0`. At most 1 solution.
- One digit `L` above `T`: `(L, v)` fixes `g(v)`, and `(u, L)` fixes
  `h_b(u)`. At most 3 solutions.
- No digit above `T`: then `w(u) + w(v) <= 2 w(T) <= 4 M (b + 1)` and
  `u b + v <= M (b + 1)`, so `|Theta| <= 5 M (b + 1)`. Since
  `Theta = M (b^2 - M^(M-1))`, this gives `|b^2 - M^(M-1)| <= 5 (b + 1)`
  and `|b - M^((M-1)/2)| <= 6`. Each `u < M` gives at most one `v`, so
  there are at most `M` solutions.

So each `M` gives at most `12 + 3 = 15` solutions, or `12 + M` in the
exceptional bases, and two values of `M` give at most 30, or `2M + 24`.
For a fixed `M` the exceptional bases are the at most 13 integers within 6
of `M^((M-1)/2)`.

This is a constant bound for all bases outside a set of at most about
`26 ln X / ln ln X` bases up to `X`, against the power of `log b`
of Proposition 4.1. It does not reach 2. The weak point is the shape
`(M, u, v)`, where each solution is an exact coincidence and nothing
elementary stops several of them in one base.

### 25.3.3 Bases of the families

Proposition 25.16 (proven). A base has at most one 3-digit power-identity
member.

Proof. Let `(p, q, x)` and `(p', q', x')` be members in base `b`, with
`x <= x'`. If `x = x'`, then `lam = lam'` (1 for even `x`, the squarefree
part of `x` for odd `x`), and `c b + e = c' b + e'` with `0 <= e, e' < b`,
so the members agree. If `x < x'`, then `p b^2 <= w(x)` and
`w(x') < (p' + 1) b^2`, so `w(x') / w(x) < p' + 1`. But
`w(x') >= w(x) x'^(x' - x) >= x' w(x)`, so `x' <= p'`, while
`x' >= w(p') + 1 > p'`.

Proposition 25.17 (proven). Let `(p, q, x)` be a member in base `b`. Every
other 3-digit solution of base `b` is either `(p, x, r)` with

    (E1)  g(r) = (x - q) b - w(p) - lam e^2,

or `(p, q', x)` with `q' != q` and

    (E2)  h_b(q') = h_b(q),  that is  w(q') - w(q) = (q' - q) b.

Each of (E1) and (E2) has at most one solution. So base `b` has at most 3
three-digit solutions.

Proof. Here `w(x) = lam (c b + e)^2 = p b^2 + q b + lam e^2`, so
`K = w(x) / b^2` lies in `[p, p + 1/2)`. By Lemma 25.13 the largest digit
`M` of another solution has `b^2 / 3 <= w(M) < (M + 1) b^2`. `M >= x + 1`
fails, since `w(x + 1) >= 2 (x + 1) w(x) >= (x + 2) b^2`. `M <= x - 1`
fails, since `w(x - 1) <= w(x) / (2x) < (p + 1) b^2 / (2x) < b^2 / 3`,
because `2x > 3 (p + 1)`. So `M = x`. If
`x` occurs three times, the leading digit is `x = floor(3K) <= 3p + 1`,
but `x >= w(p) + w(q) >= p^p + 4 > 3p + 1`. If it occurs twice, `F / b^2` lies in
`[2p, 2p + 3/2)`, so the leading digit is `2p` or `2p + 1`, not `x`. The
string is `(u, x, x)`, and its equation
`(u - 2p) b^2 + (x - 2q) b + x - 2 lam e^2 - w(u) = 0` fails: for
`u = 2p` the middle term is at least `b` and the rest is smaller, and for
`u = 2p + 1` every term but `- 2 lam e^2 - w(u)` is positive and `b^2`
exceeds that. If `x` occurs once, `F / b^2` lies in `[p, p + 1)`, so the
leading digit is `p`, and `x` is the middle or the last digit. These give
(E1) and (E2), using `w(x) = p b^2 + q b + lam e^2` and
`x = w(p) + w(q) + lam e^2`. `g` is injective, and `h_b` takes each value
at most twice.

Computed (`r5f_members3.py`). For each of the 80 members with
`x < 10^300`, the script finds the only candidate `r` for (E1) and `q'`
for (E2) from high-precision logarithms, with one neighbour on each side,
and tests the equations modulo 24 primes above `10^9`. Every candidate
fails modulo some prime. So in these 80 bases, among them
`46666^23333 - 3`, the member is the only 3-digit solution.

### 25.3.4 The answer

- Proven: the largest digit takes at most two values per base
  (Corollary 25.14); at most 30 solutions in every base outside at most 13
  bases per value of `M`, and at most `2M + 24` in those (Theorem 25.15); at
  most one family member per base, and at most 3 solutions in a base with
  a member (Propositions 25.16 and 25.17).
- Computed: every base up to `10^3301` has at most two 3-digit
  solutions, and base 4 is the only one with two (Theorem 25.11). Of the
  bases with a 2-digit solution, base 25 is the only one up to `10^3301`
  with a 3-digit solution, and it has one. The 80 family bases with
  `x < 10^300` have exactly one.
- Heuristic: a base with three 3-digit solutions needs three independent
  coincidences. Beyond `10^3301` the expected number of 3-digit solutions
  in all bases together is below `10^-3000` (Heuristic 25.12 with
  `M > 2000`), so the expected number of bases with three is smaller
  still. The families do not change this: a family base has at most two
  further candidates, (E1) and (E2), and each is a coincidence of the same
  kind.
- Open: "at most two" for every base. The method of Theorem 15.7 fails at
  the shape `(M, u, v)`, where a base near `M^((M-1)/2)` gives an equation
  in two free digits.

## 25.4 Errors and imprecisions in existing chapters

- Chapter 22, summary row "3, completeness", and section 22.4.4: "the
  nearest in base `10^108942` (3 digits) and `10^(3.9 * 10^13)` (4
  digits)". The nearest known 4-digit solution beyond the lists is
  `(8, 0, 0, 16777218)` in base about `10^(4.04 * 10^7)` (Theorem 25.5).
  The table of section 22.3.2 is also not the smallest for 5 and 6 digits
  (Table 25.1.6). Section 22.3.2 states that its search leaves out other
  shapes, so the table is not wrong, but the summary claim is.
- README and chapter 2, section 2.5: "the next 3-digit one is
  `(1,6,46666)`". In context this means the next family member, and that
  is correct (Theorem 25.10). Read as "the next 3-digit solution" it is
  heuristic, with the computed range of Theorem 25.11. A word such as
  "member" would remove the ambiguity.
- Chapter 3, section 3.5, says the 3-digit list is complete up to
  `10^51.5`. That is correct; Theorem 25.11 extends it to `10^3301`.
- Section 22.4.2 lists the self-paying digits, Theorem 22.6 and the
  families of section 19.2 as the structures the root heuristic cannot
  see. Theorem 25.5 is one more. Its `c = 1` case is the family
  `(1, 0, 0, x)` of section 19.2, which misses `D = 0` only because
  `c = 1`.

No mathematical error was found in Theorem 8.3, the corrected Corollary
8.4, Theorem 15.7, Proposition 22.8 or the proof of Corollary 22.7.

## Files

| script | output |
|---|---|
| `r5f_identities.py` | `data/r5f_identities.txt`: the census of power identities for `k = 3` to 7, and the family of Theorem 25.5 |
| `r5f_members3.py` | `data/r5f_members3.txt`: every 3-digit member with `x < 10^6605.8`, in order of base, and the checks (E1), (E2) |
| `r5f_sieve3.c`, `r5f_sieve3.py` | `data/r5f_sieve3.txt`: the 3-digit sieve of Theorem 25.11 |
| `r5f_bounds.py` | `data/r5f_bounds.txt`: the inequalities of Theorem 25.7 and section 25.3.1 |

## New questions

- Prove that the shape `(M, u, v)` of Theorem 25.15 has at most two
  solutions per base. This would give an absolute bound near 26 and,
  with more care, perhaps 2.
- Close the gap of Theorem 25.11: all 3-digit strings with two digits in
  `[201, 46700]`. A sieve over pairs of large digits with the third digit
  determined by size could make this about `10^10` tests instead of
  `10^14`.
- Is there an identity family with nonlinear `A`, that is a
  parametrized `A` for which `A(b) = x^(x/j)` is solvable by structure?
  Proposition 25.6 reduces this to values of polynomials at perfect powers,
  where the Schinzel-Tijdeman theorem bounds the exponent for each fixed
  `A`.
