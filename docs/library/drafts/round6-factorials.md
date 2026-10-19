# Round 6: factorials against x^x

DRAFT. This file answers questions 97, 98, 96, 102 and 99 of
`questions-round6.md` (workload 2). The common thread: the weight `x!` is
divisible by every prime up to `x` and is almost never a power, while `x^x`
is a power on whole progressions. The first fact gives local obstructions
for factorions, the second gives identity families for `x^x`. Where neither
helps, Brocard's problem and the abc conjecture take over.

Each statement carries one label: Theorem, Proposition, Lemma or Corollary
(proved here, or proved and then completed by a stated computation),
Heuristic, Conjecture, or "conditional" with the hypothesis named. Scripts
are `analysis/r6f_*`, data `analysis/data/r6f_*`. The runs used one thread.

Notation. A factorion in base `b` is a digit string, most significant digit
first, whose value in base `b` equals the sum of the weights of its digits,
`w(x) = x!`, with `w(0) = m`, `m = 1` (the usual `0! = 1`) or `m = 0`. For
`x^x` the notation is that of chapter 25. For a 3-digit string
`(d2, d1, d0)` completing the square gives

    U^2 = M + K,   U = 2 d2 b + d1,

where `M = 4 l w(x)` holds the weight of the large digit `x` (`l = d2` is the
leading digit) and `K` is the rest. For factorions with one large digit:

| position | string | `M` | `K` |
|---|---|---|---|
| last | `(p, q, x)` | `4p x!` | `q^2 + 4p (w(p) + w(q) - x)` |
| middle | `(p, x, r)` | `4p x!` | `x^2 + 4p A`, `A = w(p) + w(r) - r` |
| leading | `(x, q, r)` | `4x x!` | `q^2 + 4x A`, `A = w(q) + w(r) - r` |

In chapter 25 the same split is `U^2 = N + R` with `N = 4 l x^x`.

## Summary

| question | result | status |
|---|---|---|
| 97 | For fixed small digits, a 3-digit factorion with large last or middle digit `x` has `x` below an explicit bound; uniform bounds in the small digits `B` (Table 1.6). With `x` leading, the same holds unless `q^2 + 4Ax = s^2`, and then the equation is `4x x! + s^2 = U^2`, of Brocard type. | Theorem 1.5, unconditional |
| 97 | With two digits at most 10 (both conventions, all positions) every 3-digit factorion is one of the 7 known ones (8 under `w(0) = 0`), or is a leading-`x` Brocard case with `x > 4,103,641` | Theorem 1.7, proved and computed |
| 97 | Under abc, or under the explicit form `c < rad(abc)^(7/4)`, the Brocard cases are finite; under the explicit form the list for digits up to 10 is complete | Corollary 1.8, conditional |
| 97 | Two large digits: under GRH everything reduces to Brocard-type equations; unconditionally the method reaches `v < u^1.1` and `v > (u!)^0.45` | Proposition 1.9, conditional on GRH; section 1.8 |
| 98 | Under GRH, a `k`-digit factorion with fixed small digits and a large last digit has `x <= C_k (B log B)^2 (log B)^2` unless the polynomial `G_x` has a root modulo every prime; for `k <= 5` that means a rational root, which leaves a thin set of about `X^(1/(k-1))` values of `x`, each a Brocard-type equation | Theorem 2.2, conditional on GRH |
| 98 | `k = 2`: infinitely many factorions, `(1, x)` in base `x! - x + 1`. `k = 3`: Theorem 1.5. `k >= 4`: GRH alone does not give finiteness. abc gives finiteness for each fixed prefix, and with Theorem 4.4 a bound `x <= C_k max(2, B)` for every position | Proposition 2.1; Theorem 2.2; Theorem 4.4, conditional on abc |
| 98 | Check: 4-digit prefixes up to 6, `x <= 1500`: no factorion; every `x >= 76` without an obstructing prime has `G_x` with a rational root; the least obstructing prime is at most 101 | computed |
| 96 | A sufficient condition for identity families of every length, for any weight (Theorem 3.1). Under abc, for weights with `rad(w(x)) = w(x)^(o(1))`, every solution with one dominant digit is a power-identity member, so families exist exactly when `w(x)` lies in `lam` times the `j`-th powers on the values the construction produces (Corollary 3.4). `x!` meets this set only below `2 lam` (Bertrand). | Theorem 3.1; Proposition 3.2; Corollary 3.4, conditional |
| 96 | Census with 5 weights: `x^x` and `x^(x+1)` have members of length 3 and 4, `x^3` of length 3 only, `x^2` and `x!` none | computed |
| 102 | abc implies: every 3-digit solution of `x^x` (either convention, any position and parity) with `R != 0` has `x <= (2 + O(eps)) B + C_eps`. Under `c < rad^(7/4)`: `x <= 10.5 B` for `B <= 1000`, and every 3-digit solution under `0^0 = 1` with two digits at most 200 is one of the six known or a member of case (i) of Theorem 25.7 | Theorem 4.1, Corollary 4.3, conditional |
| 102 | Two large digits `u >= v`: abc leaves exactly the range `v log v >= (1/2 - eps) u log u` (about `v >= u/2`); the 7/4 form leaves `v >= u/14` roughly. Neither Fermat-Catalan nor the `n`-conjecture covers the rest | Proposition 4.5, conditional; discussion |
| 99 | The constructions of Theorem 15.14 need one exact coincidence each. Those with a one-step chain are finitely many and the only one is the 11-digit solution of base 64. Search to `t = 10^5` (`r <= 7`) and `t = 20000` (`r <= 40`): nothing else. Length grows like `c` with `|L - c| = O(log b)` | Proposition 5.2, proved and computed; Heuristic 5.3 |
| library | Section 1.6 of `drafts/round6-basics.md` says abc does not help for 3 digits; it does (Theorem 4.1). Four smaller problems in the questions file | section 6 |

## 1. Three-digit factorions (question 97)

### 1.1 Two lemmas

Lemma 1.1 (proved). Let `U^2 = M + K` with integers `U, M` and `K != 0`, and
let `l` be a prime with `v_l(M) > v_l(K) + 2 v_l(2)`. Then `K` is a square in
`Q_l`.

Proof. `U^2 = K (1 + M/K)` and `v_l(M/K) >= 1` for odd `l`, `>= 3` for
`l = 2`. Then `1 + M/K` is a square in `Z_l` by Hensel's lemma (for `l = 2`,
a unit `== 1 (mod 8)` is a square). So `K = U^2 / (1 + M/K)` is a square in
`Q_l`.

So a prime `l` at which `K` is not a local square, and which divides `M`
often enough, excludes the equation. For factorions `M = c x!` with
`v_l(x!) >= floor(x/l)`, so every prime up to about `x` is available. For
`x^x`, `M = 4 l x^x` is divisible only by the primes of `x` and `l`; this is
why the argument has no analogue there (compare Proposition 16.8).

Write `K = f^2 D` with `D != 1` squarefree, `Delta` the discriminant of
`Q(sqrt D)` (`D` or `4D`), `chi` the Kronecker symbol `(Delta / .)`, and
`l0(Delta)` the least inert prime, the least `l` with `chi(l) = -1`.

Lemma 1.2 (proved). Let `U^2 = c x! + K` with `c >= 1`, `x >= 4`, and `K`
not a perfect square. Let `l0 = l0(Delta)`.

- (a) If `l0` does not divide `f` and `l0 <= x`, there is no solution.
- (b) If `l0` divides `f`, then `|Delta| <= 4|K| / l0^2`, and there is no
  solution if `x > l0 (log|K| / log l0 + 3)`.
- (c) For any prime `l` with `chi(l) != 1`, there is no solution if
  `x > l (log|K| / log l + 3)`.

Proof. If `chi(l) = -1` and `l` does not divide `f`, then `v_l(K) = 0` and
`K` is not a square in `Q_l` (for `l = 2`, `K == 5 (mod 8)`); Lemma 1.1 with
`v_l(c x!) >= 1` (`>= 3` for `l = 2`, `x >= 4`) gives (a). If `chi(l) = 0`,
`l` ramifies, and `K` is again not a square in `Q_l` (odd valuation, or for
`l = 2` a unit part `== 3 (mod 4)`). In (b) and (c),
`v_l(c x!) >= x/l - 1 > log_l |K| + 2 >= v_l(K) + 2 v_l(2)`. The bound on
`Delta` in (b) is `|D| <= |K| / f^2`.

### 1.2 The least inert prime

Lemma 1.3 (cited, and computed). Let `Delta` be a fundamental discriminant.

- (a) Computed (`r6f_inert.py`, `data/r6f_inert.txt`): for
  `1 < |Delta| <= 4 * 10^6`, `l0(Delta) <= 79` for `Delta > 0` and
  `l0(Delta) <= 71` for `Delta < 0`. The record holders are listed; for
  example `l0 = 31` at `Delta = 1596` and `l0 = 37` at `3705`, which are the
  known exceptions of the bounds in (b).
- (b) E. Trevino, The least inert prime in a real quadratic field, Math.
  Comp. 81 (2012) 1777-1797: for `Delta > 1596`, `l0(Delta) <= Delta^0.45`.
  (This improves `sqrt(Delta)/2` for `Delta > 3705`, A. Granville, R. A.
  Mollin and H. C. Williams, Canad. J. Math. 52 (2000) 369-380.)
- (c) For `Delta < 0`, `q = |Delta| > 4 * 10^6`: `chi` is primitive and odd
  modulo `q`. By C. Pomerance, Remarks on the Polya-Vinogradov inequality,
  Integers 11A (2011), Article 19 (as quoted by D. A. Frolenkov,
  arXiv:1107.0381), `|sum_(n <= y) chi(n)| <= S(q) = sqrt(q) (log q / (2 pi)
  + log log q / pi + 1)`. If no prime up to `y` were inert, `chi(n)` would be
  1 for every `n <= y` prime to `q`, so the sum would be at least
  `y phi(q)/q - 2^omega(q)`. With `q / phi(q) < e^gamma log log q + 2.50637 /
  log log q` (Rosser and Schoenfeld, Illinois J. Math. 6 (1962) 64-94,
  Theorem 15) and `omega(q) <= 1.3841 log q / log log q` (G. Robin, Acta
  Arith. 42 (1983) 367-389) this gives an explicit `Lam(q)` of size
  `sqrt(q) (log q)^2` with `l0 <= Lam(q)`.
- (d) Under GRH: for a non-principal character modulo `m >= 10^8`, the least
  prime `l` with `chi(l) != 1` satisfies `l < (1.17 log m - 6.36)^2`
  (E. Bach, Math. Comp. 55 (1990) 355-380, in the form stated as Theorem 3.1
  by K. J. McGown, arXiv:1102.2043). For `4 * 10^6 < m < 10^8` the script
  uses `(1.17 log m + 15.2)^2`: view `chi` as a character modulo
  `m P` with `P = 100000007` prime; the bound for `m P >= 10^8` is below
  `P`, so the prime it gives is not `P`.

Only (b) and (c) are used beyond the table, and (d) only for statements
marked GRH.

### 1.3 One large digit

Theorem 1.4 (proved; the bounds are explicit). Fix the convention, the
position of the large digit `x`, and the two other digits. Let `K(x)` be as
in the notation table.

- (a) Last, `(p, q, x)`. `K(x)` is a square for at most
  `sqrt(q^2 + 4p (w(p) + w(q)))` values of `x`, all with
  `x <= w(p) + w(q) + q^2/(4p)`. For every other `x`, Lemma 1.2 with
  Lemma 1.3 excludes `x` once `x >= X0`, where `X0` is computed from
  `|K| <= q^2 + 4p (w(p) + w(q) + x)` and both signs of `Delta`.
- (b) Middle, `(p, x, r)`. `K(x) = x^2 + 4pA` with `A >= 1`. It is a square
  only for `x = (e - d)/2` with `d e = 4pA`, `d < e`, so for `x < 2pA`. Every
  other `x >= X0` is excluded, with `|K| <= x^2 + 4pA` and `Delta > 0`.
- (c) Leading, `(x, q, r)`, `A >= 1`. If `K(x) = q^2 + 4Ax` is not a square,
  `x >= X0` is excluded (`Delta > 0`, `|K|` linear in `x`). If
  `K(x) = s^2`, the string is a factorion exactly when
  `4x x! + s^2 = U^2` with `U == q (mod 2x)` and `b = (U - q)/(2x) > x`.
  These `x` form the union of the progressions `x = (s^2 - q^2)/(4A)`, an
  infinite set.
- (d) Leading with `A = 0`. This happens only for `w(0) = 0`, `q = 0` and
  `r in {0, 1, 2}`; then `K = 0` and `4x x!` would be a square. For `x >= 4`
  a prime in `(x/2, x)` divides `x x!` exactly once (Bertrand), so there is
  no factorion.

Proof. (a) For `x` beyond `w(p) + w(q) + q^2/(4p)`, `K < 0`, so it is not a
square; below, `K = t^2` fixes `x = (c0 - t^2)/(4p)`. For non-square `K`,
Lemma 1.2 (a) needs `Lam(4|K|) <= x`, and (b) needs
`x > l (log_l |K| + 3)` for every prime `l <= Lam(4|K| / l^2)`. Since
`|K| = O(x)` in (a) and (c) and `O(x^2)` in (b), and
`Lam(q) <= max(79, q^0.45, c sqrt(q) (log q)^2)`, both hold for large `x`:
in (b) `Lam(4|K|)` is about `1.9 x^0.9`, and in case (b) of the lemma
`l0 <= (4|K|)^(0.45/1.9)`, about `x^0.47`. `r6f_factorion3.py` finds `X0` by
stepping `x` by factors 1.1 up to `10^30` (`10^250` for Table 1.6) and
testing each interval with `|K|` at its right end and `x` at its left end;
beyond that range the margins only grow. (b), (c), (d) are the same
computation.

Remark. In (a) the K-square values are finitely many, so the last position
is finite outright. The middle position is finite too. Only the leading
position keeps infinitely many candidates, and only through `K = s^2`. This
is the "Brocard case" of question 97: `4x x! + s^2 = U^2`, or
`(U - s)(U + s) = 4x x!`, two divisors of `4x x!` at distance `2s`, with
`s` about `2 sqrt(Ax)`. It contains Brocard's equation in spirit: for
`n! + 1 = m^2` the divisors `m - 1, m + 1` of `n!` differ by 2. Whether it
has infinitely many solutions is open for the same reasons. A. Dabrowski,
On the Diophantine equation x! + A = y^2, Nieuw Arch. Wisk. (4) 14 (1996)
321-324, treats `x! + A = y^2` with fixed `A`; for `A` not a square the
argument is the case of Lemma 1.2 with a fixed prime. Our `K(x)` moves with
`x`, so a bound for the least inert prime is needed in place of one fixed
prime.

Theorem 1.5 (proved, uniform bounds). Let the two small digits be at most
`B`. Then beyond `X0(B)` of Table 1.6 a 3-digit factorion with one large
digit `x` has `K(x)` a perfect square: in the last position also
`x <= 2 B! + B`, in the middle `x < 4B B!`, and in the leading position
`4x x! + s^2 = U^2`. Under GRH the second column applies.

Table 1.6 (computed, `r6f_factorion3.py`, part 1a). `X0(B)`, unconditional
and under GRH (the smaller of the two).

| `B` | last | last, GRH | middle | middle, GRH | leading | leading, GRH |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 64 | 64 | 1,218 | 1,218 | 48 | 48 |
| 5 | 60,640 | 241 | 1,340 | 1,340 | 137 | 137 |
| 10 | `1.28 * 10^6` | 2,158 | 17,560 | 2,158 | `4.42 * 10^6` | 4,626 |
| 20 | `3.0 * 10^12` | 23,380 | `3.8 * 10^9` | 23,380 | `2.1 * 10^16` | 37,650 |
| 50 | `1.9 * 10^36` | `6.0 * 10^5` | `3.1 * 10^30` | `6.0 * 10^5` | `1.1 * 10^54` | `6.6 * 10^5` |
| 100 | `3.9 * 10^83` | `6.5 * 10^6` | `4.6 * 10^72` | `6.5 * 10^6` | `3.4 * 10^130` | `7.1 * 10^6` |

Unconditionally `X0(B)` grows like a power of `B!` (from `Delta^0.45` and
Polya-Vinogradov). Under GRH it grows like `(B log B)^2 (log B)^2`, a
polynomial in `B`. The middle column for `B = 2` is large because the table
bound 79 is crude for small `|K|`.

### 1.4 The computation for digits up to 10

Theorem 1.7 (proved and computed). Let `s` be a 3-digit factorion under
either convention whose two digits other than some digit `x` are at most 10.
Then `s` is one of

    (1,4,4) base 5, (1,4,5) base 10, (6,6,1) and (6,6,2) base 15,
    (7,2,5) base 27, (1,6,6) base 35, (2,4,10) base 1346,

and also `(6,6,0)` in base 15 under `w(0) = 0`; or `s = (x, q, r)` with
`q, r <= 10`, `x > 4,103,641`, `q^2 + 4x (w(q) + w(r) - r) = s'^2` and
`4x x! + s'^2` a perfect square.

Method (`r6f_factorion3.py 10`, `data/r6f_factorion3.txt`). For each of the
679 cases (convention, position, two digits; 3 cases with `A = 0` are
Theorem 1.4 (d)):

- `X0` as in Theorem 1.4. The largest is `4.42 * 10^6` (leading, `q = r =
  10`); for the last position `1.28 * 10^6`, for the middle `17,564`.
- Every `x <= 400`: exact test (`U^2 = M + K` an integer square with the
  right `b`).
- Every `x` from 401 to `X0` with `K` not a square: a prime `l < 300`, `l <= x`,
  with `K` a nonzero non-residue modulo `l`; the few `x` left get a full
  search over primes up to `x` with exact valuations (Lemma 1.1). No `x` was
  left undecided.
- Every `x` with `K(x)` a square: exact test for `x <= 3000`, and the sieve
  `r6f_brocard.c` above: `c x! + s^2` must be a square modulo each of the 40
  primes above the largest `x`, where `x!` is a unit. There were 211,668
  such `x` (90,576 last, 3,109 middle, 117,983 leading, the leading ones up
  to `x = 4,103,641`); none passed (`data/r6f_brocard.txt`, 40 s). The sieve
  was validated on `4! + 1`, `5! + 1`, `7! + 1`.

The list is the one of `r6p_factorion3.py` (digits up to 150), which is
complete for bases up to `10^131`. So the new content is that no large third
digit, in any base, adds a factorion. `(2,4,10)` is the K-square case of the
last position: `K(10) = 144`, and `10!/2 + 9 = 1347^2`.

### 1.5 The Brocard case under abc

Corollary 1.8 (conditional).

- (a) Assume the abc conjecture. Then for fixed `q, r` the leading-position
  factorions of Theorem 1.4 (c) are finitely many; more precisely
  `x <= max(C_eps, (2 + O(eps)) B)` (Theorem 4.1).
- (b) Assume `c < rad(abc)^(7/4)` for coprime `a + b = c`. S. Laishram and
  T. N. Shorey, Baker's explicit abc-conjecture and applications, Acta
  Arith. 155 (2012) 419-429, derive this from A. Baker's explicit abc
  conjecture. Then a leading-position factorion with `q, r <= 10` has
  `x <= 4,103,641`, so with Theorem 1.7 the list of Theorem 1.7 is complete.

Proof of (b). Put `N = 4x x!`, `R = s^2`, `g = gcd(N, R)`. The coprime
triple `N/g + R/g = U^2/g` gives
`N/g <= U^2/g < (rad(N) U R / g)^(7/4)`, so `N < (rad(N) U R)^(7/4)`, and
`U^2 <= 2N` gives `log N < 7 log 2 + 14 log(rad(N) R)`. Here
`rad(N) = prod_(p <= x) p < e^(1.01624 x)` (Rosser and Schoenfeld) and
`R <= 100 + 8x 10!`. `r6f_factorion3.py` finds the largest `x` for which the
inequality can hold: 4,103,641 (`log x` about 15.2, where `x log x - x` meets
`14.23 x`).

Brocard's own equation is open, finite under abc (M. Overholt, Bull. London
Math. Soc. 25 (1993) 104), and has no solution beyond `n = 7` up to `10^9`
(B. C. Berndt and W. F. Galway, Ramanujan J. 4 (2000) 41-42). The leading
case here is of the same kind: Corollary 1.8 is as far as current methods
go.

### 1.6 Two large digits

Let the digits be `u <= v` (large) and `s <= B` (small), in some order.
Two choices of `M` are available:

- (A) `M = 4 d2 (u! + v!)`, divisible by every prime up to `u`; then
  `K_A = 4 d2 w(s) + d1^2 - 4 d2 d0`, a polynomial in `u, v` of size
  `O(v^2 + v B!)`.
- (B) `M = 4 d2 v!`; then `K_B = K_A + 4 d2 u!`, of size about `4 d2 u!`.

Proposition 1.9 (conditional on GRH). For 3-digit factorions with two large
digits `u <= v` and one digit at most `B`, all but finitely many have `K_A` a
perfect square (when `v <= u^3`, roughly) or `K_B` a perfect square (when
`v > u^3`). Each such case is an equation `U^2 - t^2 = 4 d2 (u! + v!)` or
`U^2 - t^2 = 4 d2 v!`, of Brocard type.

Proof sketch. Lemma 1.2 (c) with Lemma 1.3 (d). Choice (A) needs
`u >= c (log v + log B!)^3`, choice (B) needs
`v >= c (u log u + log B!)^2 u log u`. If (A) fails, `u` is at most a power
of `log v`, so (B) holds for large `v`. Explicit constants come from Lemma
1.3 (d) as in Table 1.6.

Unconditionally (Lemma 1.3 (b), (c)) choice (A) works while `v` is below
about `u^1.1` (positive `K_A`) or `u^2` (negative `K_A`), and choice (B) once
`v > (4 d2 u!)^0.45`, up to logarithms. The range in between is out of
reach. Under abc, the `K_A`-square case with `u log u > (1/2 + eps) v log v`
is finite (the radical of `u! + v! = u! (1 + (u+1) ... v)` is at most
`e^(1.02 u) v^(v-u)`), and Theorem 4.4 gives `v <= C u` in all cases. So
under GRH and abc together the 3-digit problem reduces to
`U^2 - t^2 = 4 d2 (u! + v!)` with `K_A = t^2` and `2u <~ v <= C u`.

## 2. Factorions of every length (question 98)

### 2.1 Two digits

Proposition 2.1 (proved). For every `x >= 3`, `(1, x)` is a factorion in
base `x! - x + 1`, under either convention. So there are infinitely many
2-digit factorions.

Proof. `1 * b + x = x! + 1 = w(1) + w(x)`, and `b = x! - x + 1 > x`.

So the hope of question 98 that factorions are "the first world where every
length has finitely many solutions" fails at `k = 2`, exactly as for `x^x`
(chapter 2).

### 2.2 A large last digit under GRH

Fix `k >= 3` and a prefix `t = (t_0, ..., t_(k-2))` of digits at most `B`,
`t_0 >= 1`. With `F(t)` the sum of their weights, `(t, x)` is a factorion in
base `b` exactly when

    G_x(b) = x!,   G_x(r) = r P_t(r) + x - F(t),

a polynomial of degree `d = k - 1` with leading coefficient `t_0`. Call `G`
intersective if it has a root modulo every prime (equivalently, by
Chebotarev, every element of its Galois group fixes a root).

Theorem 2.2 (conditional on GRH). There are effective constants `c_k` such
that if `x >= c_k (log x + B log B)^2 (log log x + log B)^2` and `G_x` is not
intersective, then `(t, x)` is not a factorion in any base. In particular
this holds if `G_x` is irreducible of degree at least 2. For `k <= 5`,
`G_x` is intersective exactly when it has a rational root; this happens only
for `x` in

    R(t) = { F(t) - rho P_t(rho) : rho = -u/v rational, v | t_0 },

a set with `O(X^(1/(k-1)))` elements up to `X`. For `k = 3`, `R(t)` is
finite, and Theorem 1.4 (a) is the unconditional form.

Proof sketch. Let `L` be the splitting field of the monic polynomial
`t_0^(d-1) G_x(r / t_0)`, `n = [L : Q] <= d!`, and `C` the set of elements
of `Gal(L/Q)` that fix no root, a nonempty union of conjugacy classes. The
ramified primes divide `t_0 disc(G_x)`, whose logarithm is
`O_k(log x + B log B)` since the coefficients are at most `x + k B!`. Hensel's
bound `v_p(d_L) <= n - 1 + n v_p(n)` (J.-P. Serre, Publ. Math. IHES 54
(1981) 123-201, section 1.4) gives `log d_L = O_k(log x + B log B)`. Under
GRH, Lagarias and Odlyzko (in: Algebraic Number Fields, ed. A. Frohlich,
Academic Press 1977, 409-464, Theorem 1.1) count the primes `l <= X` with
Frobenius in `C` as `(|C|/|G|) Li(X)` up to an error
`O(sqrt(X) log(d_L X^n))`. For `X` of the stated size this exceeds the
number of primes dividing `t_0 disc(G_x)`, so some `l <= X` not dividing it
has Frobenius in `C`. Then `G_x` has no root modulo `l`, while `l <= x`
divides `x!`: a contradiction. (An explicit form is the bound
`(4 log d_L + 2.5 n + 5)^2` of E. Bach and J. Sorenson, Math. Comp. 65 (1996)
1717-1735, as quoted by J. Thorner and A. Zaman, Algebra Number Theory 11
(2017); it gives the least such prime but does not exclude the primes
dividing the discriminant.)

For `d <= 4`: an irreducible factor of degree at least 2 has a
fixed-point-free element (Jordan's theorem), and a product of two
irreducible quadratics has one too (if the two quadratic fields agree, the
non-trivial element moves all four roots; if not, take the element that is
non-trivial on both). A linear factor is a rational root `rho`, and the
rational root theorem gives `rho = -u/v` with `v | t_0`. Then
`x = F(t) - rho P_t(rho)`, which for `k = 3` is at most
`F(t) + q^2/(4p)`, and for `k >= 4` is a polynomial of degree `d` in `u`.

What remains for `k = 4, 5` under GRH: for `x in R(t)`, `G_x = (v r + u) H(r)`
with `H in Z[r]`, and the factorion is `(v b + u) H(b) = v x!`, again two
factors of a factorial in a fixed proportion, Brocard type. For `k >= 6`,
intersective polynomials without rational roots exist (degree 5: a cubic
times the quadratic over its discriminant field), so `R(t)` grows by such
`x`.

Computed (`r6f_kdigit4.py`, `data/r6f_kdigit4.txt`). All prefixes
`(p, q, s)` with digits up to 6, both conventions, `2 <= x <= 1500`
(881,412 strings): no 4-digit factorion. The least prime `l <= x` at which
`G_x` has no root is at most 101, and falls off fast (2, 3, 5 settle 65% of
the strings that have one). Every `x >= 76` without such a prime has `G_x`
with a rational root, as Theorem 2.2 says; the 2,496 exceptions (no rational
root, no obstructing prime) all have `x <= 75`, where the primes up to `x`
are too few. The GRH bound is far from tight here: the least obstructing prime
behaves like a random variable with a geometric tail, not like
`(log x)^2`.

### 2.3 The answer to question 98

- `k = 2`: infinitely many factorions (Proposition 2.1).
- `k = 3`: finitely many with one large digit, except the leading Brocard
  case; this is unconditional (Theorem 1.4). With two large digits, GRH
  reduces to Brocard-type equations (Proposition 1.9).
- `k >= 4`, fixed prefix, large last digit: GRH leaves the thin set `R(t)`;
  abc makes it finite (Theorem 4.4, whose proof covers `x!` and every
  position). GRH alone does not give finiteness.
- Every `k >= 3`, under abc: every `k`-digit factorion has its largest digit
  at most `C_k` times `max(2, second largest digit)` (Theorem 4.4 with
  Proposition 3.2).

Conjecture 2.3. For each `k >= 3` there are finitely many `k`-digit
factorions.

Heuristic. A `k`-digit string with largest digit `M` is a factorion with
chance about `(M!)^(-(k-2)/(k-1))` (the root heuristic of section 3.5 with
`P'(b)` about `b^(k-2)`), and there are about `M^(k-1)` strings with largest
digit `M`. The sum over `M` converges very fast. Unlike `x^x`, no identity
family can make a sum diverge (Proposition 3.2).

## 3. Which weights have identity families (question 96)

### 3.1 A sufficient condition

Theorem 3.1 (proved). Let `w` be a weight on the nonnegative integers and
`j >= 2`. Suppose there is an integer `M >= 1` such that, for all large
`x == 0 (mod M)`:

- (S1) `w(x) = y(x)^j` for an integer `y(x)` divisible by `M`;
- (S2) `M | w(d)` for every `d >= 1` with `M | d`;
- (S3) `y(x) > M (x + x^(1/j)) + 1`.

Then for every large `u`, with `t_i = M^(j-i) C(j, i) (M u)^i`
(`0 <= i < j`) and `x = (M u)^j + sum w(t_i)`, the string
`(t_0, ..., t_(j-1), x)` is a `(j+1)`-digit solution in base
`b = (y(x) - M u)/M`, under either value of `w(0)`. So every length `j + 1`
for which such an `M` exists has infinitely many solutions.

Proof. As Corollary 22.7 with `c = M`, `e = M u`. Every `t_i` is a positive
multiple of `M`, so `x == 0 (mod M)` by (S2). Then (S1) gives `w(x) = y^j`
with `M | y - M u`. The digits are positive, so `F = sum w(t_i) + w(x)` and
`P(b) = (M b + M u)^j - (M u)^j + x = y^j - (M u)^j + x = F`. (S3) and
`M u <= x^(1/j)` give `b > x >= t_i`.

Examples. `x^x`: `M = j`, `y = x^(x/j)` (Corollary 22.7). `x^(x+t)` with
`j | t`: `M = j`, `y = x^((x+t)/j)`. `x^d` with `j | d`, `j < d`: `M = j`,
`y = x^(d/j)`. For `x^(x+t)` with `j` not dividing `t`, (S1) holds on
`x == -t (mod j)` instead; the census below finds members for every `t` it
tried, for example `(1, 3, 3, 164)` for `x^(x+1)` (`164^165` is a cube).
For `x!`, (S1) fails for every `j`, by the next proposition.

### 3.2 Factorials

Proposition 3.2 (proved). Let `x! = lam y^j` with `j >= 2`, `y` rational
and `lam` a positive rational. Then every prime in `(x/2, x]` divides the
numerator or the denominator of `lam`; so `x < 2 P(lam)`, where `P(lam)` is
the largest such prime. In particular, for a string `(t, x)` whose last digit
`x` carries a linear power identity `r P_t(r) + C = lam (c r + e)^j`
(Corollary 25.3), a factorion forces `x < 2 t_0`, which is impossible for
`t_0 >= 3`, since `x = F(t) + lam e^j >= t_0! >= 2 t_0`.

Proof. By Bertrand's postulate `v_l(x!) = 1` for a prime `l` in `(x/2, x]`,
which exists for `x >= 2`; `v_l(lam y^j) == v_l(lam) (mod j)`. In the
identity, `lam c^j = t_0`, so `lam <= t_0`.

So the set `S_j(lam) = {x : w(x) in lam Q^(*j)}` is finite for `x!`, and it
is all of the progression `x == 0 (mod j)` (with `lam = 1`) for `x^x`. That
is the difference behind question 96.

### 3.3 The criterion, under abc

The converse direction (no identity, so finitely many solutions) cannot be
proved for all solutions: strings whose digits are all of one size are
outside every method here. For strings with one dominant digit it follows
from abc.

Theorem 3.3 (conditional on abc). Let `w` be a weight with
`log rad(w(x)) = o(log w(x))` and `log w(x) / x -> infinity`, for example
`x^x`, `x^(x+t)` or `x!`. Fix `k >= 3`. There is `C_k` such that every
`k`-digit solution whose largest digit `x` exceeds `C_k max(2, B)`, where `B`
is the second largest digit, has a power identity: the digits other than
`x` are the coefficients of `lam (c r + e)^(k-1)` up to a constant term,
`x` is last, and `w(x) = lam y^(k-1)` with `y = c b + e`. Under `w(0) = 0` the
self-paying shapes `(x, 0, ..., 0, s)` with `w(s) = s` are also possible.

This is Theorem 4.4 below.

Corollary 3.4 (conditional on abc). For weights as in Theorem 3.3 and each
`k >= 3`: infinitely many `k`-digit solutions with one dominant digit exist
if and only if, for some `lam`, the set `S_(k-1)(lam)` contains infinitely
many of the values `x = F(t) + lam e^(k-1)` with `t` of binomial shape and
`c | y - e`. For `x!` the set is finite (Proposition 3.2), so there are
finitely many such factorions of each length; for `x^x` it is a whole
progression.

This is the conjecture of question 96, proved under abc in the
dominant-digit range, with "compatible with the constructions" made precise
as "the values `F(t) + lam e^j` meet `S_j(lam)` infinitely often, with the
congruence `c | y - e`".

### 3.4 The census

`r6f_identities.py` (`data/r6f_identities.txt`) takes the linear shapes
`r P_t(r) + C = lam (c r + e)^(k-1)` of `r5f_identities.py` (prefix digits up
to 60 for `k = 3`, 20 for `k = 4`) and tests each weight:

| weight | `k = 3`: `w(x) = lam y^2` / members | `k = 4`: `w(x) = lam y^3` / members |
|---|---:|---:|
| `x^x` | 38 / 31 | 3 / 2 |
| `x^(x+1)` | 73 / 65 | 14 / 14 |
| `x!` | 0 / 0 | 0 / 0 |
| `x^2` | 83 / 0 | 19 / 0 |
| `x^3` | 62 / 62 | 4 / 0 |

Notes. For `x^2` the base `b` is at most `x`, as Theorem 3.1 predicts
(`j < d` is needed). For `x^3` and `k = 3` the members are mostly
`(a, 0, a^3)` in base `a^4` (`w(0) = 0`): `x = w(a)` is a cube by
construction, so the "thin set of perfect powers" of question 96 is hit on
purpose. For `k = 4`, `x^3` needs `j = 3 < 3`, which fails. `x!` has no shape
with `x! = lam y^j` at all.

## 4. The abc conjecture and the 3-digit list (question 102)

### 4.1 One large digit

abc, in the form used here: for every `eps > 0` there is `K_eps` such that
coprime positive `a + b = c` satisfy `c <= K_eps rad(abc)^(1 + eps)`.

Theorem 4.1 (conditional on abc). Let `s` be a 3-digit string, under either
convention, with two digits at most `B` and a third digit `x >= 2B + 4`, in
any position and of any parity, and let `U^2 = N + R` be as in Theorem 25.7.
If `R != 0` and `s` is a solution, then

    (1 - eps)/2 * log N <= log K_eps + (1 + eps) log(rad(N) |R|) + log 2.

With `log N >= x log x`, `rad(N) <= 2 l x` and `|R| <= 9 x^2 B^B`:

    x log x <= 2 (1 + eps)/(1 - eps) * (B log B + 5 log x + log 18)
               + (2/(1 - eps)) (log K_eps + log 2),

so `x <= (2 + O(eps)) B + C_eps`. The same holds for factorials with
`log N >= x log x - x`, `rad(N) <= e^(1.01624 x)` and `w(B) = B!`: then
`x <= max(C'_eps, (2 + O(eps)) B)`.

Proof. Let `g = gcd(N, R)`, which divides `U^2`. If `R > 0` the coprime
triple is `N/g + R/g = U^2/g`; if `R < 0` it is `U^2/g + |R|/g = N/g`. In
both cases the largest term is at least `N/g`, and the radical of the
product is at most `rad(N) * U * |R|/g` (`rad(U^2/g) <= U`,
`rad(|R|/g) <= |R|/g`). abc gives
`N/g <= K_eps (rad(N) U |R| / g)^(1+eps)`, so
`N <= K_eps (rad(N) U |R|)^(1+eps)`. Since `|R| < sqrt(N)` (Theorem 25.7),
`U^2 <= 2N`, and the inequality follows. For the bounds on `|R|` and `rad(N)`
see Theorem 25.7: `l <= B` or `l = x`, and `rad(4 l x^x) <= 2 l x`.

`R = 0` is case (i) of Theorem 25.7: the family members. So:

Corollary 4.2 (conditional on abc). For every `eps > 0` there is `B_eps`
such that every 3-digit solution of `x^x`, under either convention, whose
largest digit exceeds `(2 + eps) max(B_eps, B)` (`B` the second largest
digit) is a member of case (i) of Theorem 25.7. In particular all but
finitely many 3-digit solutions with one digit larger than `3 B` are family
members. This is Conjecture 25.8 (a) for 3 digits in the dominant-digit
range.

### 4.2 The explicit form

With `c < rad(abc)^(7/4)` (Laishram and Shorey, from Baker's explicit abc
conjecture) the same proof gives

    log N < 7 log 2 + 14 log(rad(N) |R|),

with the exact `|R|` bounds of Theorem 25.7 in each position.

Table 4.1 (computed, `r6f_abc3.py`, `data/r6f_abc3.txt`). Largest `x`
allowed when the two other digits are at most `B`.

| `B` | 1 | 2 | 5 | 10 | 20 | 50 | 100 | 200 | 500 | 1000 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `x^x`, last | 37 | 42 | 62 | 105 | 196 | 481 | 974 | 1,991 | 5,130 | 10,484 |
| `x^x`, middle | 45 | 47 | 62 | 105 | 196 | 481 | 974 | 1,991 | 5,130 | 10,484 |
| `x^x`, leading | 38 | 43 | 64 | 105 | 194 | 477 | 970 | 1,986 | 5,124 | 10,478 |
| `x!`, all | `4.10 * 10^6` | | | `4.10 * 10^6` | | | `4.11 * 10^6` | `4.12 * 10^6` | | `4.19 * 10^6` |

For `x^x` the ratio `x/B` is about 10 for `B` up to 1000 and tends to 14
slowly. For `x!` the bound is about `e^15.2`, almost independent of `B`: the
radical of `x!` is `e^(1.016 x)`, so abc can only beat `x!` once
`log x > 14 * 1.016 + 1`.

Corollary 4.3 (conditional on `c < rad(abc)^(7/4)`). Every 3-digit solution
under `0^0 = 1` with two digits at most 200 is one of the six known
solutions (`(1,3,1)`, `(3,1,3)` base 4; `(5,1,3)` base 25; `(6,1,5)` base 91;
`(1,2,6)` base 215; `(1,7,1)` base 904) or a member of case (i) of Theorem
25.7.

Proof. By Table 4.1, `x <= 1991` when `R != 0`. Theorem 25.11 (a) decided
every string with digits up to 2000. The members of case (i) are those with
`R = 0`.

This removes the base restriction from Theorem 25.11 (b) (two digits up to
200, bases below `46666^23333 - 3`), at the price of the hypothesis.

### 4.3 Every length

Theorem 4.4 (conditional on abc). Let `w` be `x^x` or `x!` (either
convention), or another weight as in Theorem 3.3. For each `k >= 3` there is
`C_k` such that every `k`-digit solution whose largest digit `x` exceeds
`C_k max(2, B)`, `B` the second largest digit, has `E = 0` below: a power
identity with `x` last (or, under `w(0) = 0`, a self-paying shape).

Proof sketch (`x` last; the other positions are the same with coefficients
that are polynomials in `x`). Let `d = k - 1`, `p = t_0`, `q = t_1`,
`Y = d p b + q` and `C = d^d p^(d-1)`. Then `C b P_t(b) = Y^d + Q(Y)` with
`deg Q <= d - 2` (Tschirnhaus), so the solution is

    Y^d + E = C w(x),   E = Q(Y) + C (x - F(t)).

If `E != 0`, abc for the triple (after dividing by
`g = gcd(Y^d, E)`, as in Theorem 4.1) gives
`Y^d <= K_eps (Y |E| C rad(w(x)))^(1+eps)`. Now
`|E| <= B^(O(d)) Y^(d-2) + C (x + k w(B))` and `Y^d` is about `C w(x)`. If
the first term of `|E|` dominates, `Y^(1 - (d-1) eps) <= K_eps (B^(O(d))
rad(w(x)))^(1+eps)`, which bounds `log w(x)` by `O(d^2 log B)` plus
`o(log w(x))`. If the second dominates,
`w(x)^((d-1)/d - O(eps)) <= w(B)^(1+eps) w(x)^(o(1))`, so
`log w(x) <= (d/(d-1) + O(eps)) log w(B)`, and `x <= C_k B`. If `E = 0` and
`Q` is not constant, then `|Q(Y)|`, about `Y^(deg Q)` up to a factor
`(dp)^(-d)`, exceeds `C (x + k w(B))`
for `x > C_k B`; so `Q` is constant, `r P_t(r) + x - F(t)` is
`p (r + q/(dp))^d`, a linear power identity.

This also proves the per-prefix finiteness asked in question 98 for
factorions: for fixed `t`, `w(x) = x!` and `E = 0` force `C x! = Y^d`, which
Proposition 3.2 rules out for large `x`.

### 4.4 Two large digits

Proposition 4.5 (conditional on abc). Let a 3-digit solution of `x^x` have
digits `u >= v` (large) and `s <= B`. If `R != 0` after moving `4 l v^v`
into `R`, then

    (1/2 - eps) u log u <= (1 + eps) v log v + O(B log B + log u),

so `v log v >= (1/2 - O(eps)) u log u`, that is `v >= (1/2 - O(eps)) u`
for large `u` (with `c < rad^(7/4)`: `u log u < 14 (v log v + B log B) +
O(log u)`, about `v >= u/14`).

Proof. Theorem 4.1 with `|R'| <= 9 u^2 B^B + 4 l v^v`.

What remains. The range `u/2 <~ v <= u` is a genuine 4-term equation
`U^2 = 4l u^u + 4l v^v + R`. abc does not apply to 4 terms. The
`n`-conjecture of Browkin and Brzezinski (Math. Comp. 62 (1994) 931-939)
gives `max <= rad^(2n - 5 + eps)`, exponent 3 for 4 terms, and
`rad(U^2 u^u v^v R)` is about `u^(u/2)`, so `rad^3` is far above `U^2`.
Fermat-Catalan statements need pure powers with zero remainder; here
`R != 0` and `u^u + v^v` is not a perfect power for structural reasons. This
is the 3-digit form of the case `a^a ~ c^c` that Theorem 15.10 leaves out
for 2 digits. So the residue of the 3-digit problem under abc is precisely
the comparable pair `u/2 <~ v <= u`, the range of Theorem 25.11 with "two
digits above 200".

Correction to `drafts/round6-basics.md`, section 1.6 (last paragraph): "The
abc conjecture does not help here, unlike for `(1, x, 1)` ... the radical of
the right side contains `b` ... so the abc inequality is satisfied." That
remark used the triple `x^x = p b^2 + q b + (x - C)`. The completed square
`U^2 = N + R` has `rad(U^2) <= U`, about `x^(x/2)`, and gives Theorem 4.1. So
the regime "`n` varies" of its table 1.6 is settled under abc (and the
other regimes too), and the open part under abc is the two-digit range of
Proposition 4.5.

## 5. Long structured solutions under `0^0 = 1` (question 99)

### 5.1 The shape of Theorem 15.14

Base `b = r^t`, chain `u_0 -> ... -> u_j = 0`, leading weight left over
`c = r^(u_0)` at position 0, and a set `S` of self-paying digits. Let `T`
be the top position. The zero count gives

    T + 1 = L = c + j + |S|.

Proposition 5.1 (proved). In such a solution `|S| <= v_top`, the exponent of
the largest self-paying digit used, and `v_top <= log_r(t T) + 1`. So
`L = c + O(log b)`: the length is fixed by the last digit `c` up to
`O(log b)`, and a solution needs a position (of a chain digit or a
self-paying digit) within `O(log b)` of `c`.

Proof. A self-paying digit `r^v` at position `v (r^v - 1)/t <= T` has
`r^v <= t T + 1`. Distinct digits in `S` have distinct `v`.

Proposition 5.2 (proved and computed). The solutions of Theorem 15.14 with a
one-step chain (`j = 1`) are finitely many, and the only one is the 11-digit
solution of base 64.

Proof. `j = 1` means `t | u_0 r^(u_0)`, and the digit 1 sits at
`P_1 = u_0 c / t < c`. So the top is a self-paying digit `r^v` with
`v (r^v - 1)/t = c + k`, `k = |S| >= 1`. Put `t = u_0 c / P_1`:
`v (r^v - 1) P_1 = u_0 c (c + k)`. If `v <= u_0` the left side is below
`u_0 c * c`, a contradiction, so `v > u_0`, and reducing modulo `c` gives
`c | v P_1`; with `n = v P_1 / c < v`,
`u_0 k = n r^v - n - u_0 c >= c (n r^(v-u_0) - u_0) - n`. The left side is
positive, so `n r^(v - u_0) - u_0 >= 1` and `k >= (c - v)/u_0`. With
`k <= v` (Proposition 5.1) this gives `c <= (u_0 + 1) v`, and
`r^v <= u_0 c (c + v) + 1 <= 2 u_0 (u_0 + 1)^2 v^2`. These two inequalities
allow only `u_0 <= 7` for `r = 2`, smaller `u_0` for larger `r`, and
`r <= 2 v (u_0 + 1)` with `v` below 25; then `t <= u_0 r^(u_0) < 1000`. All
these bases are inside the search below (bases `r^t` with `r` a perfect
power are the same constructions with the root of `r`). The search finds
only base 64.

Computed (`r6f_chains.py`; `data/r6f_chains.txt`, `data/r6f_chains_1e5.txt`).
All chains and all admissible `S` with positions up to `10^6`, for
`r <= 40` (not a perfect power) and `t <= 20,000`, and for `r <= 7` and
`t <= 10^5`: one configuration, the base 64 solution, `L = 11`,
`L / ln b = 2.64`. The search agrees with section 15.5 on its range
(`t <= 300`).

### 5.2 Heuristic

Heuristic 5.3. For given `(r, t, u_0)` the chain must end at 0, which needs
`t | u_i r^(u_i)` at its last step, and some position must land in a window
of width `O(log b)` at `c`. The first condition puts all of `t` outside the
primes of `r` into `u_(j-1)`; the second has chance about
`log b / (c log r)` per candidate position. Summed over `t` and `u_0` this
converges, so the expected number of these solutions beyond the searched
range is small, and an infinite family would need an identity that makes a
position equal `c + j + |S| - 1` exactly. Proposition 5.2 shows that no such
identity exists for one-step chains. Note that one solution of this kind has
length far beyond `log b`: `L` is about `c`, and `c` can be large compared
with `t log r`. Base 64 already has `L = 2.64 ln b`.

Answer to question 99: no infinite family found; Theorem 15.14 cannot
produce one with a one-step chain; for longer chains each solution is a
coincidence of the type above (heuristic). The families of fixed length
(Corollary 22.7, Theorem 25.5) have `ln b` about `x ln x / j`, far above
their length. Two chains sharing a last digit (the second attack of the
question) do not help: the zero count `c - 1` is paid once, but each chain
must still end at 0 and land within `O(log b)` of `c`.

## 6. Problems found

1. `drafts/round6-basics.md`, section 1.6, last paragraph: the claim that
   abc does not help for 3-digit strings is wrong; see section 4.4. The
   table there ("`n` varies: none known, open") should add "finite under
   abc".
2. `questions-round6.md`, question 97 ("Why"): a proof "would be the
   library's first unconditional finiteness theorem for a family of short
   strings with a free digit, in any world". Theorem 15.13 (coverings: a
   prefix that makes the last digit impossible in every base) and Theorem
   1.2 of `drafts/round6-basics.md` came first.
3. `questions-round6.md`, question 97: the Dabrowski reference is A.
   Dabrowski, On the Diophantine equation x! + A = y^2, Nieuw Arch. Wisk.
   (4) 14 (1996) 321-324. Secondary sources describe it in two ways
   (finiteness for non-square `A`; and finiteness under abc for every `A`);
   I could not see the paper itself. The non-square case follows from one
   fixed prime `l` with `(A/l) = -1`, as in Lemma 1.2.
4. `questions-round6.md`, question 98: "Factorions would then be the first
   world of the library where every length provably (under GRH) has finitely
   many solutions." Length 2 has infinitely many (Proposition 2.1), and GRH
   alone leaves the rational-root set `R(t)` for `k >= 4` (Theorem 2.2).
5. `questions-round6.md`, question 96: "The weights `x^d` give only the thin
   set of perfect powers." For `k = 3` the weight `x^3` has the infinite
   family `(a, 0, a^3)` in base `a^4` (`w(0) = 0`), because the large digit is
   itself a weight. The thin set is hit by construction (section 3.4).

## Files

| file | contents |
|---|---|
| `analysis/r6f_inert.py` | least inert primes of quadratic fields, `|Delta| <= 4 * 10^6`, record holders (Lemma 1.3 (a)) |
| `analysis/data/r6f_inert.txt` | its output |
| `analysis/r6f_factorion3.py` | bounds `X0` (Table 1.6), the check of Theorem 1.7, the K-square candidates |
| `analysis/data/r6f_factorion3.txt` | its output (679 cases, both conventions) |
| `analysis/r6f_brocard.c` | sieve for `c x! + s^2` a square, primes above `x` |
| `analysis/data/r6f_brocard_cand.txt` | the 211,668 K-square candidates with `x > 3000`; written by `r6f_factorion3.py 10 all <path>`, not committed (6.6 MB) |
| `analysis/data/r6f_brocard.txt` | sieve output: no survivor |
| `analysis/r6f_kdigit4.py` | 4-digit factorions with a large last digit, obstructing primes, rational roots |
| `analysis/data/r6f_kdigit4.txt` | its output |
| `analysis/r6f_identities.py` | identity census for five weights |
| `analysis/data/r6f_identities.txt` | its output |
| `analysis/r6f_abc3.py` | explicit abc bounds (Table 4.1) |
| `analysis/data/r6f_abc3.txt` | its output |
| `analysis/r6f_chains.py` | constructions of Theorem 15.14 ranked by length |
| `analysis/data/r6f_chains.txt`, `r6f_chains_1e5.txt` | its output |

## New questions

1. The leading Brocard case. Is `4x x! + s^2 = U^2` with
   `s^2 = q^2 + 4Ax` solvable for any `x > 10`? Push the sieve of section 1.4
   to `x = 10^9` (as Berndt and Galway did for Brocard), which would also
   reach the Laishram-Shorey bound for digits up to about `10^6`.
2. Sharper unconditional bounds. For `|K|` linear in `x` the bound
   `Delta^0.45` is far from the truth (the least inert prime up to
   `4 * 10^6` is at most 79). An explicit Burgess bound for imaginary
   quadratic characters would cut `X0(B)` of the last position from a power
   of `B!` to about `(B!)^(1/4)`.
3. Two large digits in the factorion world. Run the GRH reduction of
   Proposition 1.9 as a computation for `u, v <= 10^4`: how many pairs have
   `K_A` or `K_B` a square, and do any survive a sieve?
4. The comparable range for `x^x`. Proposition 4.5 leaves `u/2 <~ v <= u`.
   Is there a conditional statement (a 4-term abc with a better exponent for
   this special shape, or Vojta's conjecture for the surface
   `U^2 = 4l (u^u + v^v) + R`) that covers it?
5. Intersective polynomials for `k >= 6`. Are there prefixes `t` for which
   `G_x` is intersective without a rational root for infinitely many `x`?
6. Theorem 15.14 with cycles. Proposition 5.2 used only self-paying digits.
   Do swaps (2-cycles of `phi`) allow a family with a one-step chain?
