# 32. The basic questions revisited

This chapter returns to three questions from the start of the project:

1. Which digit strings are never a solution, in any base?
2. Which bases have no solution at all?
3. How can the search be made faster?

The main new result answers part of the first question. It uses a tool the library
has not used before for this purpose: Baker's theory of linear forms in
logarithms, in its 2-adic form.

## Summary

| basic question | result | status |
|---|---|---|
| 1 | For fixed digits `p, q` with `p` not a square and `x` even, the strings `(p, q, x)` and `(p, x, q)` are solutions for only finitely many `x`, with an explicit bound `X0(p, q)` | proven (Theorem 32.2) |
| 1 | The bound is uniform: `x <= C B^(3/2) (log 3B)^4` when `p, q <= B` | proven, `C` effective (Theorem 32.5) |
| 1 | For `p, q <= 20` no such string is a solution in any base, under either convention; the same holds when `x >= 9` is an odd square | proven and computed (Theorem 32.3, Proposition 32.7) |
| 1 | Every 3-digit solution in any base with two digits at most 20 and the third digit even and not leading is in the lists of chapter 3 or a member of the binomial family | proven and computed (Corollary 32.4) |
| 1 | The three regimes: `N` a square (elementary), the square class of `N` fixed (Baker), the class varying (open; finite in the last position by chapter 36) | proven for the first two (section 32.1.6) |
| 2 | What counting can and cannot prove about empty bases, and what the families add | discussion (section 32.2) |
| 3 | Searching by multisets across bases saves at most about 2.1x on a sweep, and nothing on one base | proven bound, heuristic gain (section 32.3) |

## 32.1 Strings that are never solutions

### 32.1.1 Setting

Chapter 1 shows that a string is a solution in at most one base
(Proposition 1.3), and chapter 11 that a string whose polynomial `Q_s` has no
root modulo some prime is a solution in no base (Proposition 11.1). So each
single string is decided by a finite computation. The question is about
infinite families: which families of strings contain no solution, or only
finitely many?

Two kinds of argument were known.

- Local: a covering. A finite set of moduli excludes every member of the
  family (Theorem 15.13, `(2, 1, x)` is never a solution).
- Archimedean: a gap. The size of the terms leaves no room for a solution
  (Theorem 25.7 (ii), where `N` is a perfect square).

This section adds a third kind, which is global: a bound from transcendence
theory, followed by a finite sieve. It excludes infinite families that have
no known covering. Each member of these families is excluded by some prime,
and heuristically no finite set of primes excludes them all.

Fix the convention `m` and write `w(0) = m`, `w(d) = d^d` for `d >= 1`.
Take a 3-digit string with leading digit `p >= 1`, a second small digit
`q >= 0`, and an even digit `x >= 2`, in one of the two positions

    last:    (p, q, x),   p b^2 + q b + x = w(p) + w(q) + x^x,
    middle:  (p, x, q),   p b^2 + x b + q = w(p) + x^x + w(q).

Multiply by `4p` and complete the square. Write `p = n f^2` with `n`
squarefree. Since `x` is even, `x^x = (x^(x/2))^2`, and

    U^2 - n V^2 = R,    V = 2 f x^(x/2),

where

    last:    U = 2 p b + q,   R = q^2 + 4 p (w(p) + w(q) - x),
    middle:  U = 2 p b + x,   R = x^2 + 4 p (w(p) + w(q) - q).

This is the equation of Theorem 25.7 (iii) with `N = n V^2`. If `n = 1`,
Theorem 25.7 (i) and (ii) decide everything. So let `n > 1`. Then `R != 0`,
since `R = 0` would make `n` a rational square.

The point is that `n` does not depend on `x`. As `x` runs over the even
numbers, all these Pell equations live in one field, `K = Q(sqrt n)`. Write
`O_K` for its ring of integers and `eta > 1` for its fundamental unit.

### 32.1.2 The tool

Linear forms in two `p`-adic logarithms (primer). For algebraic numbers
`a_1, a_2` and integers `b_1, b_2`, the number `a_1^(b_1) - a_2^(b_2)` is
not zero unless `a_1, a_2` are multiplicatively dependent. Baker's theory
says more: it cannot be very small, in the real sense or in the `p`-adic
sense, unless the heights of `a_1, a_2` or the exponents are large. We use
the `p`-adic form with `p = 2`, in the version of Bugeaud and Laurent:

Theorem 32.1 (Bugeaud and Laurent; stated as Theorem 2.1 of M. A. Bennett and
Y. Bugeaud, Acta Arith. 155 (2012) 259-269, simplifying Theoreme 3 of
Y. Bugeaud and M. Laurent, J. Number Theory 61 (1996) 311-342). Let `p` be
a prime, `a_1, a_2` multiplicatively independent algebraic numbers with
`v_p(a_1) = v_p(a_2) = 0`, `D = [Q(a_1, a_2) : Q]`, and `g` the least
positive integer with `v_p(a_i^g - 1) > 0` for both `i` (so `g <= p^D - 1`).
Let `log A_i >= max(h(a_i), (log p)/D)` and
`b' = b_1 / (D log A_2) + b_2 / (D log A_1)`. Then for positive integers
`b_1, b_2`,

    v_p(a_1^(b_1) - a_2^(b_2))
      <= 24 p g / ((p-1) (log p)^4) * D^4
         * max(log b' + log log p + 0.4, 10 (log p)/D, 10)^2
         * log A_1 * log A_2.

Here `v_p` is normalized by `v_p(p) = 1` and `h` is the absolute logarithmic
height.

### 32.1.3 The theorem

Theorem 32.2 (proven). Let `p = n f^2` with `n > 1` squarefree, let `q >= 0`,
and let `x` be even. If `(p, q, x)` or `(p, x, q)` is a solution in some
base, under either convention, then

    x/2 + 2 - log2 |R| <= 9991 * max(log b' + 0.0335, 10)^2
                          * log(|R| eta) * max(log eta, 0.347),

with `b' = 1/(2 max(log eta, 0.347)) + M / (2 log(|R| eta))` and
`M = (log(4 f sqrt n) + (x/2) log x + 1e-6) / log eta + 1/2`. Since the left
side grows like `x` and the right side like `(log x)^3`, this bounds `x`.
`analysis/r6b_pell_bound.py` computes the bound `X0(p, q)` for every
position and convention.

Proof. Let `beta = U - V sqrt n`. Then `beta` is in `Z[sqrt n]`, which lies
in `O_K`, its norm is `R`, and its conjugate is `beta' = U + V sqrt n`.
Fix the real embedding in which `sqrt n > 0`. Then `U > 0` gives
`|beta| = |R| / (U + V sqrt n) <= |R| / (V sqrt n)`.

Step 1: an associate of small height. Choose the integer `m` such that
`delta = beta eta^(-m)` satisfies

    |R|^(1/2) eta^(-1/2) < |delta| <= |R|^(1/2) eta^(1/2).

The norm of `delta` is `+-R`, so `|delta'| = |R| / |delta|` lies in the same
range. `delta` is an algebraic integer, so
`h(delta) <= (1/2) log(|R| eta)`. Also

    |m| log eta = log|delta| - log|beta| <= log(2 V sqrt n + 1) + (1/2) log eta

once `V sqrt n >= |R|` (then `U <= V sqrt n + 1`). This gives `|m| <= M`.
If instead `V sqrt n < |R|`, then `|R| > 2 x^(x/2)`, so
`log2 |R| > x/2 + 1` for `x >= 2`, the left side of the claim is below 1, and
the claim holds trivially.

Step 2: the 2-adic closeness. Let `v` be the 2-adic valuation on an
algebraic closure of `Q_2`, with `v(2) = 1`, restricted to `K` through one
embedding. Then `beta' - beta = 2 V sqrt n` and `V = 2 f x^(x/2)` with `x`
even, so `v(beta' - beta) >= 2 + x/2`. Also `beta beta' = R` with both
factors integral, so `v(beta) <= v(R) <= log2 |R|`. Hence

    v(beta'/beta - 1) >= x/2 + 2 - log2 |R|.

Now `beta'/beta = (delta'/delta) (eta'/eta)^m`, and `eta' = N(eta)/eta`
with `N(eta) = +-1`. Put `a_1 = N(eta)^m delta'/delta`. Then
`beta'/beta = a_1 eta^(-2m)`, and since `eta` is a unit,

    v(a_1 - eta^(2m)) >= x/2 + 2 - log2 |R|.                      (*)

Step 3: Baker. If `v(a_1) != 0`, then the left side of (*) is at most 0,
so `x/2 + 2 <= log2 |R|`, which is far stronger than the claim. If `a_1` and
`eta` are multiplicatively dependent, then `a_1` is a unit with
`eta^(-1) < |a_1| < eta`, so `a_1 = +-1`. Then (*) bounds
`v(eta^(2m) -+ 1) <= v(eta^(4m) - 1) <= v(eta^(12m) - 1)`. For `z = eta^3`
we have `v(z - 1) > 0` (the residue field has at most 4 elements), and two
squarings give `v(eta^12 - 1) >= 2 > 1`, so
`v(eta^(12m) - 1) = v(eta^12 - 1) + v_2(m)`. This gives
`x/2 + 2 - log2|R| <= v(eta^12 - 1) + log2 M`, again a much smaller bound.
If `m = 0` then `|beta| = |delta| > (|R| eta^(-1))^(1/2)`, and with
`|beta| <= |R| / (V sqrt n)` this forces `V sqrt n < (|R| eta)^(1/2)`, so `x`
is tiny. `r6b_pell_bound.py` checks that both side bounds lie below `X0`.

Otherwise apply Theorem 32.1 with `p = 2`, `a_1` as above, `b_1 = 1`,
`a_2 = eta^2` and `b_2 = m` if `m > 0`, or `a_2 = eta^(-2)` and `b_2 = -m`
if `m < 0`. Here `D = 2`, `g <= 3`,
`h(a_1) <= 2 h(delta) <= log(|R| eta)`, and `h(eta^(+-2)) = log eta`. The
constant is `24 * 2 * 3 / (log 2)^4 * 2^4 = 9991` (rounded up), and
`log log 2 + 0.4 = 0.0335`. Together with (*) this is the inequality.

Remarks.

- The proof replaces `|R|` by the upper bound `q^2 + 4p (w(p) + w(q) + x)`
  (last) or `x^2 + 4p (w(p) + w(q) + q)` (middle) in the script. This is
  allowed: `log A_1` may be any upper bound for the height, and `log2|R|`
  enters with a minus sign.
- The argument is the one Bennett and Bugeaud use for `||xi b^n||` with a
  quadratic `xi` (their Theorem 1.2). The difference is that here the base of
  the power, `x`, varies together with the exponent. This costs nothing,
  because only the 2-adic valuation of `V`, at least `x/2`, enters, and the
  height of `delta` grows only like `log x`.
- I know of no covering of these families, and a heuristic says there is
  none: each odd prime `l` leaves about `(l + 1)/(2l)` of the residues, the
  first five leave about 7% of even `x` (the wheel of `r6b_sieve.c`), and the
  joint period of any finite set of primes is fixed while `x` is unbounded.
  Each member is excluded by some prime; the family as a whole is excluded
  by the bound.

### 32.1.4 The computation

Theorem 32.3 (proven and computed). Let `p <= 20` be a non-square, let
`q <= 20`, and let `x >= 2` be even. Then neither `(p, q, x)` nor
`(p, x, q)` is a solution in any base, under either convention.

Method. `r6b_pell_bound.py 10 10` gives `X0` for each of the 168 cases
(family, position, convention for `q = 0`). The largest is
`X0 = 717,115,282`, for `n = 7`, whose unit `8 + 3 sqrt 7` is large.
`r6b_sieve.c` tests every even `x <= X0`: the string is a solution exactly
when `D = U^2` is a perfect square, and `D` must be a square modulo each odd
prime. The sieve uses 150 odd primes, with tables of period `l (l-1)` for
`x^x mod l`. For `p, q <= 10` it tested `2.48 * 10^10` values of `x` in about 15
minutes on 6 threads (`data/r6b_sieve10.txt`). Three values passed every
prime:
`(3,1,2)`, `(3,2,2)` and `(3,2,2)` with `x` in the middle, all with
`D = U^2` and root `b = 3`. In base 3 the digit 3 is not allowed, so none
is a solution. (They are the strings of section 12.4 with an integer root
at most the largest digit.)

Validation. For `p, q <= 12`, both positions and even `x <= 80`, the sieve
survivors agree exactly with an exact test of `D` for squareness in Python.
Known family members survive: `(1,2,6)` and `(1,6,46666)`.

The 536 further cases with `p, q <= 20` have bounds up to
`X0 = 2,448,584,564` (for `n = 19`, whose unit `170 + 39 sqrt 19` is large).
The sieve tested `1.73 * 10^11` values of `x` in about 3 hours on 5 shared
threads, and no value passed every prime (`data/r6b_sieve20.txt`). In total
704 cases and `1.98 * 10^11` values of `x`.

Corollary 32.4 (proven and computed). Let `s` be a 3-digit solution in some
base, under either convention, whose leading digit and one other digit are
at most 20, and whose third digit `x` is even and not leading. Then `s` is
in the complete 3-digit lists of chapter 3, or `s = (c^2, 2ce, x)` with
`x = w(c^2) + w(2ce) + e^2` and `x^x = (c b + e)^2`: case (i) of Theorem
25.7, the binomial family of Theorem 22.6 with `j = 2`.

Proof. If `p` is not a square, Theorem 32.3 applies. Let `p` be a square. If
`x < 44`, then `p b^2 <= F < 2 * 20^20 + 42^42`, so `b < 2 * 10^34`, inside
the lists of chapter 3 (every 3-digit solution in bases up to `10^51`, both
conventions). If `x >= 44 = 2 * 20 + 4`, Theorem 25.7 applies with
`B = 20`. Theorem 25.7 is stated under `0^0 = 1`, but for `x` in the middle
or last position its proof uses only the algebra of `R` and the bound
`w(d) <= B^B` for the small digits, so it holds under `0^0 = 0` as well; in
case (i) the value `e = 0` is then allowed, with `x = w(c^2) = c^(2c^2)`
(the zeros weigh nothing).
`N = 4 p x^x` is a square, so case (iii) is empty, case (ii) has no solution,
and case (i) is the family.

Of the known 3-digit solutions only `(1,2,6)` in base 215 has this shape
(under `0^0 = 1`), and it is the first family member.

### 32.1.5 A bound uniform in the small digits

Theorem 32.5 (proven, with an effective constant `C`). Let `s = (p, q, x)` or
`(p, x, q)` be a 3-digit solution with `p, q <= B`, `B >= 2`, `x` even and
`p` not a square. Then `x <= C B^(3/2) (log 3B)^4`.

Proof sketch. Use Theorem 32.2 with explicit bounds for its terms.

- The regulator. With `Delta <= 4n <= 4B` the discriminant of `K`, the class
  number formula gives `log eta <= h log eta = (sqrt(Delta)/2) L(1, chi)`.
  Partial summation with `|sum_(k <= t) chi(k)| <= Delta` gives
  `L(1, chi) <= log Delta + 2`. So `log eta <= sqrt(B) (log 4B + 2)`.

  Correction (chapter 36, 2026-10-19). With `|sum chi(k)| <= Delta`,
  partial summation from `N = Delta` gives only `log Delta + 3`. The
  stated `log Delta + 2` holds because the partial sums are at most
  `Delta/2` in absolute value (the sum over a period is 0; Lemma 36.2).
  The theorem is unaffected.
- The constant term. `|R| <= x^2 + 4B (2 B^B + x + B)`, so
  `log |R| <= 2 log x + (B + 1) log B + 4`.
- The exponent. `log b' <= 2 log x` for `x >= 10`.

The inequality becomes
`x/2 <= c (log x)^2 (log x + B log B + sqrt(B) log 3B) sqrt(B) log 3B`
plus lower-order terms. If `log x <= B log B` this gives
`x <= c' B^(3/2) (log 3B)^2 (log x)^2`, hence the claim. If
`log x > B log B`, it gives `x <= c'' (log x)^3 sqrt(B) log 3B`, which
contradicts `log x > B log B` for large `B` and bounds `x` for small `B`.

So a 3-digit solution whose even large digit sits behind a non-square
leading digit cannot be much larger than the small digits. Together with
Theorem 25.7: every 3-digit solution with an even, non-leading digit
`x > C B^(3/2) (log 3B)^4` is a member of the binomial family, where `B` is
the larger of the other two digits.

### 32.1.6 Three regimes, and where the frontier is

For a 3-digit string with one large digit `x` and small digits at most `B`,
Theorem 25.7 reduces everything to `U^2 - n V^2 = R` with `V` a power of `x`
times a constant and `n` the squarefree part of `N = 4 l x^x`, where `l` is
the leading digit.

| regime | when | method | result |
|---|---|---|---|
| `N` a square | `x` odd and leading; `x` even with a square leading digit | the gap of Theorem 25.7 (ii) | no solution except the family |
| `n` fixed in `x` | `x` even and not leading, `p` not a square | 2-adic Baker (Theorem 32.2) | finitely many, explicit |
| `n` fixed on a class | `x` in a fixed square class: odd, not leading, `x = lam t^2`; or even and leading, `x = lam t^2` | real Baker (Matveev), Proposition 32.6 | finitely many in each class |
| `n` varies, last position | odd `x` last, over all classes | the imaginary field `Q(sqrt R)`: Lehmer numbers, Matveev (chapter 36) | finitely many for each `p, q`, effective (Corollary 36.10) |
| `n` varies, other positions | odd `x` in the middle, even `x` leading, over all classes | none known | open |

Correction (chapter 38, 2026-10-20). The last row is now split as well.
Even `x` leading is finite for every pair of small digits, with an
effective bound (Theorem 38.6: the ideal of norm `x` is generated by
`(q + sqrt R)/2` up to the primes of `Aq`, and the S-unit lattice of
`Q(sqrt R)` has covolume `O(sqrt(x) log x)`); the family
`b (xb + 1) = x^x + 1` has no solution (Corollary 38.8). Odd `x` in the
middle remains open, except that in the 25 families with `pA` a square
prime powers `x` are effectively bounded (Theorem 38.2, Corollary 38.3).

Proposition 32.6 (proven). Fix `p, q`, the position of `x`, and a squarefree
`lam`. Then only finitely many `x` with squarefree part `lam` make the string
a solution, and their number is effectively bounded.

Proof sketch. In each case `n` is the squarefree part of `p lam` (not
leading) or of `lam` (leading), so `K` is fixed. `V` is a constant times a
power of `t` and `lam`. The associate `delta` of Step 1 has height
`O(log x)`. The real linear form
`log(2 sqrt(n) V) - log delta - m log eta` has absolute value at most
`|R| / V^2`, about `x^(-x)`. It has four logarithms with heights
`O(1), O(log x), O(log x), O(1)` and coefficients `O(x log x)`. Matveev's
theorem gives a lower bound `exp(-c (log x)^3)`, which beats `x^(-x)` for
large `x`. If `x` is odd, `V` has no factor 2, so the 2-adic argument is not
available. The real one is, but with a worse constant: about `10^17` in place
of `10^9`.

Proposition 32.7 (proven and computed). Let `p <= 20` be a non-square,
`q <= 20`, and `x = t^2` with `t >= 3` odd. Then neither `(p, q, x)` nor
`(p, x, q)` is a solution in any base, under either convention.

Proof. Here `x^x = (t^x)^2`, so `V = 2 f t^x` and the field is `Q(sqrt n)`
again, with `n` the squarefree part of `p`. With `beta' = U + V sqrt n` and
the associate `delta'` of Step 1 of Theorem 32.2,

    Lambda = log(4 f sqrt n) + x log t - log|delta'| + m log eta
           = log|1 - beta/beta'|,

so `log|Lambda| <= log(2|R|) - log(4 f^2 n) - 2x log t`, and `Lambda != 0`.
Matveev's theorem (E. M. Matveev, Izv. Math. 64 (2000) 1217-1269,
Corollary 2.3) for four logarithms in a real field of degree `D = 2` gives

    log|Lambda| > -1.4 * 30^7 * 4^4.5 * D^2 (1 + log D) (1 + log B)
                  * A_1 A_2 A_3 A_4

with `B = max(x, |m|)`, `A_1 = log(16 f^2 n)`, `A_2 = 2 log t`,
`A_3 = log(|R| eta)` and `A_4 = log eta` (each at least 0.16). The two
bounds meet at `t <= T0(p, q)`, at most `2.4 * 10^9` for `p, q <= 10` and
`3.94 * 10^9` for `p, q <= 20` (`r6b_pell_bound.py 20 20 sq`), so
`x = t^2 < 1.6 * 10^19` still fits in 64 bits. The sieve in mode `sq` tested
every odd `t <= T0`: `1.18 * 10^11` values for `p, q <= 10`, in about 3.5
hours on 5 shared threads (`data/r6b_sieve_sq10.txt`), and `4.88 * 10^11`
more for the 536 families with `p > 10` or `q > 10`, in about 4 hours on 3
shared threads (`data/r6b_sieve_sq20.txt`). For `p, q <= 10` The only survivors have `t = 1`, that
is `x = 1`: the invalid strings `(2,1,0)`, `(3,0,1)`, `(3,1,2)` and the known
solutions `(3,1,3)`, `(5,1,3)`, `(6,1,5)` (`0^0 = 1`) and `(5,0,1)`,
`(7,0,1)` (`0^0 = 0`). For the larger families the only survivors are
`(p, 0, 1)` at the end, `0^0 = 0`, for `p = 11, 13, 15, 17, 19`. These are
solutions: `p b^2 + 1 = p^p + 1` with `b = p^((p - 1)/2)`, the same family as
`(5,0,1)` and `(7,0,1)`. For square `p`, `N` is a square and Theorem 25.7
decides, as in Corollary 32.4.

So Corollary 32.4 holds for `p, q <= 20` with "`x` even" replaced by "`x`
even or an odd square".

So the open part of the 3-digit problem has a precise shape: Pell equations
`U^2 - n V^2 = R` in which the field `Q(sqrt n)` changes with `x`. The
regulator of `Q(sqrt(p x))` can be as large as `sqrt(x) log x`, and then
every Baker bound is too weak by a power of `log x`. This is the obstacle of
direction A7 of `questions-round5.md` (the field `Q(sqrt(x^2 + 4c))` for
`b (b + x) = x^n + c`), now seen to be the only obstacle for three digits.
A uniform treatment of a family of real quadratic fields, for example
through results on `y^2 = a x^n + c` that are uniform in `n`, would settle
the 3-digit case up to a finite computation.

Correction (chapter 36, 2026-10-19). "Now seen to be the only obstacle for
three digits" is wrong for the last position. The regulator is an obstacle
of the Pell form only. For `(p, q, x)` with `x` odd and
`x > W + q^2/(4p)` the same equation reads `U^2 + D = 4p x^x` with
`D > 0`, and in the imaginary field `Q(sqrt(-D))` there are no units of
infinite order and `x^x` is an `x`-th power. Primitive divisors of Lehmer
numbers (Theorem 36.5) and Matveev's bound for three logarithms with a
reduced lattice basis (Theorem 36.9) bound `x` by about `10^39` to
`10^40` for `p <= 20`, uniformly in `q`. So the last position is finite
for each pair of small digits, of either parity (Corollary 36.10), and the
row "`n` varies" of the table above is split. The middle position with
`x` odd and the leading position with `x` even remain open; there the
field of `R` is real and its regulator enters every height (section
36.4.3).

The abc conjecture would close every regime at once, but only in the
completed-square form. Written as `x^x = p b^2 + q b + (x - C)`, the
radical contains `b`, about `x^(x/2)`, and abc says nothing. Written as
`U^2 = N + R` with `N = 4 l x^x`, the radical of the three terms (after
removing their common factor, which divides `R`) is at most
`|R| * 4 l x * U`, about `x^(x/2 + 3) B^B`, while `U^2` is about `x^x`.
The quality tends to 2, so abc bounds `x` for each `B`, in all positions
and for both parities. This is question 102. Theorem 32.2 and
Proposition 32.6 prove parts of this unconditionally.

Update (chapter 33). Theorem 33.16 proves this. Under abc every 3-digit
string with two digits at most `B` and `R != 0` has
`x <= (2 + O(eps)) B + C_eps`, for every position of `x`, both parities and
both conventions. The row "`n` varies" of the table is therefore finite
under abc. With the explicit form `c < rad(abc)^(7/4)` the bound is
about `x <= 10.5 B` for `10 <= B <= 1000` (Table 33.4.1). Every 3-digit
solution under `0^0 = 1` with two digits at most 200 is then one of the six
known ones or a family member (Corollary 33.18).
Under abc the open part is two comparable large digits (Proposition 33.20).

### 32.1.7 Four or more digits

The same method applies when the polynomial is a perfect power up to a small
remainder in a fixed field. For `k` digits with the large digit last and
`k - 1` dividing `x`, completing the power works only when the prefix has
the binomial shape. For example, `q^2 = 3 p r` for `(p, q, r, x)`. Then
`u^3 - 27 p^2 X^3` is small with `X = x^(x/3)`, a Thue equation in the fixed
field `Q(p^(1/3))`, and the 2-adic argument works with `D = 6`. Otherwise the
equation defines a curve of genus at least 1 that changes with `x`, and Baker's
method for such curves needs more. This leaves question 64 open for `k >= 4`
outside these shapes.

## 32.2 Bases without solutions

The library proves nothing about bases without solutions beyond single
computations (bases 19, 27 and 35 up to 41), and chapter 8 explains why. Here
is what I see after revisiting the question.

What counting proves. A base `b` has a `k`-digit solution only if some string
of `k` digits, each at most `X_k(b)`, is a solution there (Proposition 1.2),
and each string has at most one base (Proposition 1.3). Up to `B` there are
about `(k ln B / ln(k ln B))^k` such strings. This is less than `B` exactly
while `k < (1 - eps) ln B / ln ln B`, which is Theorem 20.3. Counting cannot
go further, since beyond that range there are more strings than bases. Any
stronger statement must show that most strings fail, which is the
equidistribution question of the random model.

What the families add. The bases with a 3-digit solution are now better
known. Under `0^0 = 1` they are 4, 25, 91, 215, 904, the bases of the
binomial family, and possibly bases above `10^3301` with two large digits
(Theorem 25.11). Theorem 32.3 removes from that last set every solution with
an even, non-leading large digit and the two other digits at most 20. So the
set of bases with a solution of length 3 is known except for strings with
two large digits or odd ones.

Where a proof of "infinitely many empty bases" would have to come from. A base
is empty when none of about `C(2b, b)` multisets has the right digits. The
only multiset-level invariant is `n mod (b - 1)` (Proposition 10.2), and it
removes a fraction `1/(b-1)` at best. So an emptiness proof for infinitely
many bases must use the size and the digits together, as Theorem 25.7 (ii)
does for 3 digits. For long strings no such structure is known, and the
model says that none should exist: the per-base events look independent with
probability about `e^(-E)`. I regard the second question as out of reach in the
present state of knowledge.

A model case shows how hard it is. For two-digit narcissistic numbers
(weights `x^2`), base `b` has exactly `tau(b^2 + 1) - 2` of them, and an
even base has none exactly when `b^2 + 1` is prime (Theorem 30.12 and
Corollary 30.13). So "infinitely many empty bases" is Landau's problem on
primes of the form `n^2 + 1` in that toy world, one of the oldest open
problems in number theory. The Munchausen question has the same shape with
a far less tractable weight. The useful targets are its pieces with a
fixed shape, as in section 32.1.

## 32.3 Faster search

Searching by multisets across bases. Proposition 1.3 suggests sharing work
across bases: enumerate multisets once and test each in every base where it
could fit. The gain is small.

- A multiset of length `L` with largest digit `M` and sum `N` has the right
  length in base `b` when `b^(L-1) <= N < b^L`. This window has relative
  width `N^(1/(L(L-1)))`, about `1 + ln(M)/M`, so it contains about `ln b`
  consecutive bases. A full-length multiset (`L = M + 1`) fits only base
  `M + 1`, by Proposition 1.6. So the sharing factor is at most about `ln b`,
  and only for shorter lengths.
- The pruning of the tree depends on the base: a node survives when the
  leading base-`b` digits of its partial sum fit its counts. Surviving in
  base `b` and in base `b + 1` are separate coincidences. A shared tree keeps
  the union of the per-base trees, and these overlap only near the root.
- The cost of a sweep of bases is dominated by its largest base. With
  growth `1.89x` per base, a sweep `b_0..b_1` costs about
  `1/(1 - 1/1.89) = 2.1` times the last base alone, so even perfect sharing
  saves at most 2.1x on a sweep and nothing on a single base.

The short-length engine `kdigit` already works by strings across all bases,
which is where this idea pays.

What remains. Chapter 31 assembles the library's results into pruning
rules for the engine. From the basic question I take one point: the exact
tree grows like `1.89^b`, tending to `2^b`, and the model floor for every
top-down search is `1.638^b`. The gap comes from the worst-case bound on
the remaining digits at each node. A bound that uses the digits of `F`
already fixed (each fixed digit value below the current one is a lower
bound on its count, and the number of remaining free slots shrinks
accordingly) can be iterated to a fixed point at each node. Section 31.3
measures it: the engine already iterates this bound, the iteration saves a
constant factor 1.46 in nodes, and the interval it reaches is the exact
hull of the reachable sums (Lemma 31.4). So it does not narrow the gap in
the growth rate.

## Files

| file | contents |
|---|---|
| `analysis/r6b_pell_bound.py` | the bound `X0(p, q)` of Theorem 32.2 for every family, with the side cases |
| `analysis/r6b_sieve.c` | the sieve over even `x <= X0` |
| `analysis/data/r6b_sieve10.txt` | the run for `p, q <= 10` |
| `analysis/data/r6b_sieve20.txt` | the run for `p, q <= 20` |
| `analysis/data/r6b_sieve_sq10.txt` | the odd squares `x = t^2`, `p, q <= 10` |
| `analysis/data/r6b_sieve_sq20.txt` | the odd squares, the 536 further families with `p, q <= 20` |

## New questions

These are questions 129 to 132 of `questions.md`.

1. (Answered in chapter 36 for the last position: in the field
   `Q(sqrt(-D))` of `R` the bound is uniform in `q`, Theorem 36.9. The
   middle position remains.) Uniformity over fields. Is there a bound for the solutions of
   `U^2 - n V^2 = R` with `V = x^(x/2)`-type powers that is uniform over the
   fields `Q(sqrt(p x))`, `x` odd? This would close the 3-digit problem up to
   computation. Lead: the results on `y^2 = a x^n + c` uniform in `n`.
2. (Answered in chapter 36 for the last position: every class at once,
   Corollary 36.10. The middle position remains.) Other square classes. Proposition 32.6 gives finiteness for odd `x` in
   any fixed square class `x = lam t^2`, and Proposition 32.7 closes
   `lam = 1`. For `lam > 1` the linear form has five logarithms and the
   bound on `t` is about `10^10`. Is there a better route, for example a
   `l`-adic bound at a prime `l` dividing `lam`?
3. Four digits with a binomial prefix. Carry out section 32.1.7 for
   `(p, q, r, x)` with `q^2 = 3 p r` and `x` even, `3 | x`: a Thue equation
   in `Q(p^(1/3))` with a 2-adic bound.
4. (Answered in section 31.3.2: the engine already iterates to the fixed
   point, which saves 1.46 to 1.47 times the nodes in bases 20 to 33.) A
   fixed-point bound for the exact tree. Measure how many nodes the
   iterated interval of section 32.3 removes at bases 25 to 35.
