# Round 3 number theory: multisets, x^x - x, and b(b+x) = x^n + c

This draft answers, fully or in part, questions 45, 46, 52, 51 and 53 of
`questions-round3.md`, in that order. Every statement is marked:

- proven: the proof is here;
- cited: a published theorem, used without proof, with a reference;
- computed: an exact computation found it, and the range is stated;
- heuristic: an argument that is not a proof.

Scripts are in `analysis/` with names starting `r3nt_`. Their output is in
`analysis/data/r3nt_*`. Chapter numbers such as "Proposition 15.17" refer to
the library chapters.

## Summary

SUMMARY-TABLE

## 1. Counting multisets (question 45)

A `k`-digit solution `n = F(c)` is fixed by its digit multiset `c`: the
multiset gives `n`, and `n` and the base give the string. Theorem 11.2 and
Proposition 10.4 count strings. This section counts multisets and doubles the
range of Theorem 11.2.

Notation. `L = ln B`. `X_k(B)` is the largest `X` with `X^X < B^k`; by
Proposition 1.2 every digit of a `k`-digit solution in a base `b <= B` is at
most `X_k(B)`. `S(c)` is the digit sum of `c`, `M` its largest digit, and
`H_k = 1 + 1/2 + ... + 1/k`. "Solution" means a nontrivial solution with at
least 2 digits, under a fixed convention.

### 1.1 The window

Lemma 1.1 (proven). Let `n` be a solution in base `b` with `k >= 2` digits,
leading digit `p` and largest digit `M`. Then

    p b^(k-1) <= n < p b^(k-1) + (M + 1) b^(k-2),

and so

    b <= (n / p)^(1/(k-1)) < b + (M + 1) / (p (k - 1)).

Proof. The digits after the second one are at most `b - 1`, so they add at
most `b^(k-2) - 1`. The second digit is at most `M`. So
`n - p b^(k-1) <= M b^(k-2) + b^(k-2) - 1`. For the second claim put
`u = (M + 1) / (p b)`. Then `n / p < b^(k-1) (1 + u)`, and
`(1 + u)^(1/(k-1)) <= 1 + u / (k - 1)` (Bernoulli).

The proof uses only that the second digit is at most `M`. It does not matter
where the largest digit stands. Proposition 15.17 is the same statement with
`X >= M` in place of `M`, where `X` is the largest integer with `X^X <= n`. So
Proposition 15.17 is correct as stated, also when the leading digit is not
the largest digit. The window `(Y - h, Y]` with `Y = (n/p)^(1/(k-1))` and
`h = (M + 1)/(p (k-1))` holds at most `floor(h) + 1 <= M + 2` integers, as
the question says.

Computed (`analysis/r3nt_multiset.py`, `data/r3nt_multiset.txt`):

- all 3,135 known solutions with at least 2 digits (bases 2 to 41 and 43, both
  conventions, and the lists `k2.txt` to `k7.txt`) satisfy both inequalities
  exactly. In 1,745 of them the leading digit is not the largest digit. The
  largest relative position of `Y` in the window is 0.984, so the window is
  close to sharp;
- a search that runs over multisets and tests only the bases in the windows
  reproduces the complete lists:

| `k` | digits up to | multisets | window bases | with `b - 1 \| F(c) - S(c)` | solutions, `0^0 = 1` | solutions, `0^0 = 0` |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 40 | 12,341 | 76,600 | 107 | 6 | 52 |
| 4 | 22 | 14,950 | 66,914 | 163 | 2 | 18 |
| 5 | 12 | 6,188 | 17,368 | 314 | 6 | 9 |
| 6 | 9 | 5,005 | 8,512 | 569 | 1 | 2 |
| 7 | 7 | 3,432 | 2,031 | 342 | 1 | 2 |

The column with `b - 1 | F(c) - S(c)` is for `0^0 = 1`. It uses the
congruence `n == S(c) (mod b - 1)` of section 1.6; section 1.4 uses it.

### 1.2 The count

Proposition 1.2 (proven). Let `k >= 2` and `X = X_k(B)`. Under a fixed
convention, the number of bases `b <= B` with a `k`-digit solution is at most

    C(X + k, k) * ( (X + 1) H_k / (k - 1) + k ).

Proof. Map a base with a `k`-digit solution to the triple (digit multiset
`c`, leading digit `p`, base `b`). Different bases give different triples.
The multiset has `k` digits from `{0, ..., X}`, so there are at most
`C(X + k, k)` of them. The leading digit is one of the at most `k` distinct
nonzero digits of `c`. By Lemma 1.1, given `c` and `p`, the base lies in a
window with at most `(X + 1)/(p (k - 1)) + 1` integers. The sum of `1/p` over
at most `k` distinct positive integers is at most `H_k`.

For both conventions together the bound doubles.

### 1.3 The range

Theorem 1.3 (proven). Let `L = ln B`, and count bases `b <= B` with a
solution of `k` digits for some `2 <= k <= K`, under a fixed convention.

- (a) For fixed `alpha < 1` and `K = alpha L / ln L`, the count is at most
  `B^(alpha + o(1))`.
- (b) For fixed `delta > 0` and
  `K = (L / ln L) (1 + (ln ln L + ln 2 - 1 - delta) / ln L)`, the count is at
  most `B exp(-(delta + o(1)) L / ln L)`.
- (c) So almost all bases `b` have no solution with `k` digits for
  `2 <= k <= (ln b / ln ln b) (1 + (ln ln ln b + ln 2 - 1 - delta) / ln ln b)`.
  In particular this holds for `k <= (1 - eps) ln b / ln ln b`, twice the
  range of Theorem 11.2.
- (d) For `K = (L / ln L) (1 + (ln ln L + ln 2 - 1 + delta) / ln L)` the
  bound of Proposition 1.2 for `k = K` alone exceeds `B`. So the count of
  multisets cannot reach further.

Proof. Let `K = kappa L / ln L` with `kappa` bounded, and `X = X_K(B)`.

Step 1, the size of `X`. From `X^X < B^K <= (X+1)^(X+1)` we get
`X ln X = K L + O(ln X)`. Then `ln X = 2 ln L - ln ln L - ln ln X + O(1)`,
`ln ln X = ln 2 + ln ln L + O(ln ln L / ln L)`, and

    ln (X / K) = ln L - ln ln X + o(1/K) = ln L - ln ln L - ln 2 + O(ln ln L / ln L).

In particular `X ~ kappa L^2 / (2 (ln L)^2)`, so `K^2 / X` is bounded.

Step 2, the binomial. Stirling's formula and `K^2 / X = O(1)` give
`ln C(X + K, K) = K ln(X / K) + K + O(ln K)`. With step 1,

    ln C(X + K, K) = kappa L (1 - a / ln L + O(ln ln L / (ln L)^2)),   a = ln ln L + ln 2 - 1.

Step 3, the other factors. The window factor of Proposition 1.2 is at most
`(X + 1) H_K + K`, and the sum over `k <= K` adds a factor `K`, because the
terms grow with `k`. Together these are `exp(O(ln L))`, which is
`exp(o(L / ln L))`.

For (a), `kappa = alpha` gives `alpha L (1 + o(1))`. For (b),
`kappa = 1 + (a - delta)/ln L` gives
`kappa (1 - a / ln L) = 1 - delta / ln L + O((ln ln L)^2 / (ln L)^2)`, so the
logarithm of the count is at most `L - (delta - o(1)) L / ln L`. For (d) the
same computation with `+ delta` gives `L + (delta - o(1)) L / ln L`. For (c),
the bases up to `sqrt B` are at most `sqrt B`, and for `sqrt B < b <= B` the
length bound in (c) is at most the `K` of (b), because it increases with `b`.
The correction term `(ln ln ln b + ln 2 - 1 - delta) / ln ln b` tends to 0,
so the bound in (c) exceeds `(1 - eps) ln b / ln ln b` for large `b`.

Computed (`r3nt_multiset.py`, part 4). The bounds of Proposition 10.4 summed
over `2 <= k <= K` (strings) and of Proposition 1.2 (multisets), as powers of
`B`, at `B = 10^96`, where `L / ln L = 40.95`:

| `K` | `alpha = K ln L / L` | strings | multisets |
|---:|---:|---:|---:|
| 8 | 0.195 | `B^0.207` | `B^0.182` |
| 16 | 0.391 | `B^0.458` | `B^0.343` |
| 24 | 0.586 | `B^0.725` | `B^0.502` |
| 32 | 0.781 | `B^1.003` | `B^0.659` |
| 40 | 0.977 | `B^1.289` | `B^0.816` |
| 48 | 1.172 | `B^1.582` | `B^0.973` |

The string count stays below `B` up to `K = 31`, the multiset count up to
`K = 49`. At `K = 16` (`alpha = 0.4`) the string bound is the `B^0.46` of
section 11.6, and the multiset bound is `B^0.34`. At finite `B` both counts
reach beyond their asymptotic `alpha` (1/2 and 1) because of the second-order
term in (b). The largest `K` with a multiset bound below `B`, against the
formula of (b) with `delta = 0`:

| `B` | largest `K` | `L / ln L` | formula |
|---:|---:|---:|---:|
| `10^100` | 51 | 42.3 | 53.1 |
| `10^1000` | 362 | 297.4 | 364.3 |
| `10^10000` | 2,765 | 2,292.4 | 2,748.9 |
| `10^(10^6)` | 184,385 | 157,177.9 | 182,687.2 |
| `10^(10^10)` | 1,088,827,070 | 965,044,571.6 | 1,080,937,272.3 |

### 1.4 Fixed length

The question expected the multiset count to sharpen Proposition 10.4 for every
fixed `k`. As it stands it does not. For fixed `k` and `B -> infinity`, the
bound of Proposition 1.2 is about `X^(k+1) H_k / (k! (k - 1))`, which is larger
than the `X^k` of Proposition 10.4 by a factor of order `X`. The windows have
about `X / (p k)` integers each, and that loses what the multisets gain. A
divisibility condition repairs this.

Lemma 1.4 (proven). Let `m >= 1`, `h >= 1` and `Y - h >= 1`, and let
`d_1 < ... < d_r` be divisors of `m` in the interval `(Y - h, Y]`. Then
`m > (Y - h)^r / h^(r (r-1) / 2)`.

Proof. For each prime `q`, write `e_i = v_q(d_i)`, sorted so that
`e_1 >= e_2 >= ...`. Then the sum over `i < j` of `min(e_i, e_j)` is
`sum of (j - 1) e_j`, which is at least `e_2 + ... + e_r`. So
`v_q(lcm) = e_1 >= sum e_i - sum over i < j of min(e_i, e_j)`, and
`lcm(d_1, ..., d_r) >= prod d_i / prod over i < j of gcd(d_i, d_j)`. Each
`gcd(d_i, d_j)` divides `d_j - d_i < h`. And `m` is a multiple of the lcm.

Proposition 1.5 (proven). Let `k >= 3`, and let `b_k` be the largest real `Y`
with `Y <= 2^k (k ln Y / (k - 1))^(k(k-1)/2)`. Under a fixed
convention, the number of bases `b <= B` with a `k`-digit solution is at most

    b_k + k (k - 1) C(X + k, k),    X = X_k(B).

This is `X^k / (k - 2)! (1 + o(1))` as `B -> infinity`, smaller than
Proposition 10.4 by the factor `(k - 2)!`.

Proof. Fix a multiset `c` with `n = F(c)` and a leading digit `p`. Let
`Y = (n/p)^(1/(k-1))` and `h = (M + 1)/(p (k - 1))`. A base `b` of a
solution with these data lies in `(Y - h, Y]` (Lemma 1.1), and `b - 1`
divides `m = n - S(c)` (section 1.6). For `k >= 3`, `m >= 1`: all weights
satisfy `w(d) >= d`, with equality for every digit only if all digits are 0 or
1, and then `n <= k < 2^(k-1) <= b^(k-1)`. Suppose `k` such bases exist. Lemma
1.4 with the divisors `b - 1` in `(Y - 1 - h, Y - 1]` gives
`p Y^(k-1) = n > m > (Y - h - 1)^k / h^(k(k-1)/2)`. If `Y >= 2 (h + 1)`, this
gives `Y < 2^k p h^(k(k-1)/2) <= 2^k ((M + 1)/(k - 1))^(k(k-1)/2)`, since
`p >= 1`. Now `M^M <= n < b^k <= Y^k` gives `M ln M < k ln Y`, so
`M + 1 <= k ln Y` for `Y >= 42` (for `M <= 2` directly, for `M >= 3` from
`M < k ln Y / ln 3`). Then `2 (h + 1) <= 2 (M + 1) <= 2 k ln Y <= Y` for
`Y > b_k`, and the inequality above contradicts `Y > b_k`. (One checks
`b_k > 42` for `k >= 3`.) So a window with `Y > b_k` holds at most
`k - 1` bases, and every base `b <= b_k` is counted by the first term. There
are at most `k C(X + k, k)` pairs `(c, p)`.

For `k = 3` this gives `X^3 (1 + o(1))`, the same as Proposition 10.4. For
`k = 4` it gives `X^4 / 2`, with `b_4` about `1.5 * 10^10`. So the gain for
fixed `k` is the factor `(k - 2)!`, a constant.

### 1.5 Beyond alpha = 1

Proposition 11.1 is a test on strings. Given a multiset `c` and a base `b`, the
string is fixed, and a window base is a single integer to test. So local tests
on strings cannot bring the number of candidate pairs below the number of
multisets, which is `B^(alpha + o(1))`. At the level of multisets the only
congruence is `n == S(c) (mod b - 1)` (Proposition 10.2), and the table of
section 1.1 shows how strongly it filters: for `k = 3` and digits up to 40, 107
of 76,600 window bases pass.

Heuristic. If `F(c) - S(c)` behaved like a random integer modulo each `b - 1`
near `(F(c)/p)^(1/(k-1))`, the test would keep about one window base in `b`,
and the count of Proposition 1.2 would lose a further factor of about `B`.
The range would then reach the `K` where the number of multisets is about
`B^2`, that is `alpha` near 2. A proof needs an equidistribution statement for
the integers `F(c) - S(c) = sum of (d^d - d)` over multisets, in residue classes
modulo integers in short windows that depend on `F(c)` itself. I know no
method for this. The number of multisets already exceeds `B` at `alpha = 1`, so
any argument that counts candidates one by one stops there. This is the
obstacle.

## 2. The 3-adic and 5-adic laws of x^x - x (question 46)

Let `f(x) = x^x - x` and `T(q) = { f(x) mod q : x >= 1 }`. For `q = p^e`, the
value `f(x) mod q` depends only on `x mod p^e (p - 1)` once `x >= e`.

### 2.1 Lifting

Lemma 2.1 (proven). For every prime `p` and `e >= 1`, `T(p^e)` contains every
multiple of `p`.

Proof. For `x == 0 (mod p)` with `x >= e`, `f(x) == -x (mod p^e)`.

Lemma 2.2 (proven). Let `p` be odd and `x_0` prime to `p` with
`x_0^(x_0) != 1 (mod p)`. As `x` runs over the integers with
`x == x_0 (mod p (p - 1))`, `f(x) mod p^e` runs over the whole class
`f(x_0) + p Z` modulo `p^e`, for every `e >= 1`.

Proof. On this class `f(x) mod p` is constant, because it depends on
`x mod p` and `x mod (p - 1)`. Let `x' = x + d` with
`d = p^(j+1) (p - 1) s` and `j >= 0`. Then `x'^(x') = x'^x x'^d`. Since
`x'^(p-1) == 1 (mod p)` and `p` is odd, `x'^d == 1 (mod p^(j+2))`. By the
binomial theorem `x'^x = x^x (1 + d/x)^x == x^x (1 + d) (mod p^(j+2))`,
because `v_p(d) = j + 1` and the terms with `(d/x)^i`, `i >= 2`, have valuation
at least `2 (j + 1) >= j + 2`. So

    f(x') == f(x) + p^(j+1) (p - 1) (x^x - 1) s   (mod p^(j+2)),

and `x^x == x_0^(x_0) != 1 (mod p)`. So the step `s` moves `f` through all
residues of the next `p`-adic digit. Induction on `j` gives every residue of
`f(x_0) + p Z` modulo `p^e`.

Modulo `p`, `x^x == u^j` with `u = x mod p` and `j = x mod (p - 1)`, and these
are independent. So `f(x) == g - u (mod p)` with `g` in the cyclic group
generated by `u`. Call a residue `r != 0` good if `r = g - u` with `g != 1`.
By Lemmas 2.1 and 2.2, `T(p^e)` contains the full classes of 0 and of every
good residue.

Theorem 2.3 (proven). For every prime `p >= 7` and every `e >= 1`,
`T(p^e) = Z / p^e`.

Proof. Let `r != 0`. For a primitive root `u`, the residue `g = u + r` lies in
the group generated by `u` unless `g = 0`, and `g != 1` unless `u = 1 - r`. So
`r` is good if some primitive root avoids `-r` and `1 - r`. For `p >= 11`,
`phi(p - 1) >= 4`, so this holds. For `p = 7` the primitive roots are 3 and 5,
and `{-r, 1 - r} = {3, 5}` has no solution (`r = 4` gives `{3, 4}`, `r = 2`
gives `{5, 6}`).

Lemma 2.4 (proven). For `p = 5` the good residues are 1, 2 and 4. The residue
3 arises only from `x == 3 (mod 5)` with `x^x == 1`, that is `x == 8 (mod 20)`.
For `p = 3` there is no good residue. The residue 2 arises only from
`x == 2 (mod 6)`, and 1 never arises.

Proof. A direct check of the pairs `(u, g)`. For `p = 5`: `r = 1` from
`(3, 4)`, `r = 2` from `(2, 4)`, `r = 4` from `(3, 2)`; `r = 3` needs
`g - u = 3` with `g` a power of `u`, and the only pair is `(u, g) = (3, 1)`.
For `p = 3` see Lemma 15.12.

### 2.2 The classes with a vanishing derivative

On the classes of Lemma 2.4, `x^x == 1 (mod p)`, so the step in Lemma 2.2 is
0 and the class does not lift. A power series describes it.

Lemma 2.5 (proven, with standard facts on the p-adic exponential). Let `p` be
odd, `zeta` in `Z_p` a root of unity of order `t | p - 1`, and `x` an integer
with `x == zeta (mod p)` and `t | x`. Write `x = zeta e^a` with
`a = log(x / zeta)` in `p Z_p`. Then

    f(x) = sum over n >= 0 of c_n a^n,    c_n = (S_n - zeta) / n!,
    S_n = sum over m = 0..n of C(n, m) zeta^m m^(n-m)    (0^0 = 1).

Proof. For `y` in `1 + p Z_p` and an integer `x`, `y^x = exp(x log y)`, and
`exp`, `log` are inverse bijections between `p Z_p` and `1 + p Z_p` for odd
`p` (cited: F. Q. Gouvea, p-adic Numbers, 2nd ed., Springer 1997, section 4.5).
Since `t | x`, `x^x = zeta^x (e^a)^x = exp(x a) = exp(zeta a e^a)`. Expand
`exp(zeta a e^a) = sum over m, l of zeta^m m^l a^(m+l) / (m! l!)`; the terms
tend to 0 because `v_p(a^n / (m! l!)) >= n - n/(p - 1)`, so the double series
may be regrouped by `n = m + l`. Subtract `x = zeta sum a^n / n!`.

For `zeta = -1`: `c_0, c_1, ... = 2, 0, 0, 1/2, 5/12, 1/24, -47/360, ...`. For
`zeta = i`, a square root of -1: `c_0 = 1 - i`, `c_1 = 0`, `c_2 = (i - 1)/2`
(computed exactly in `r3nt_tq.py`).

Theorem 2.6 (the 3-adic law, proven). For `e >= 4`,

    T(3^e) = { v : v == 0 (mod 3) }  together with  { v : v == 2 (mod 27), v != 56 (mod 81) }.

So `|T(3^e)| = 29 * 3^(e-4)` and the density of `T(3^e)` is `29/81`. For
`e <= 3`, `T(3^e)` is as in Lemma 15.12. Every `T(3^e)` with `e >= 5` is the
full preimage of `T(81)`.

Proof. By Lemma 2.4 only the class `x == 2 (mod 6)` remains. Take `zeta = -1`
and `a = 3 w` with `w` in `Z_3`. The integers `x == 2 (mod 6)` are dense in
`2 + 3 Z_3 = -exp(3 Z_3)`: the condition `x` even is free 3-adically. So the
values `f(x) mod 3^e` on this class are the values of
`2 + 27 G(w) mod 3^e` for `w` in `Z_3`, where

    G(w) = sum over n >= 3 of c_n 3^(n-3) w^n.

The coefficient `c_n 3^(n-3)` has valuation at least
`n - 3 - v_3(n!) >= (n - 5)/2`. The exact values are `1/2` for `n = 3`,
`5/4` for `n = 4`, `3/8` for `n = 5` and `-47 * 3^3 / 360` (valuation 1) for
`n = 6`; for `n >= 7` the bound gives valuation at least 1. So `G` has
coefficients in `Z_3` tending to 0, and modulo 3

    G(w) == (1/2) w^3 + (5/4) w^4 == -(w^3 + w^4) (mod 3).

Its values mod 3 are 0 at `w == 0`, 1 at `w == 1` and 0 at `w == 2`. So
`G(w)` is never `2 (mod 3)`, which excludes `v == 56 (mod 81)`. The derivative
is `G'(w) == -w^3 (mod 3)`, a unit at `w == 1` and `w == 2`. Modulo any
`3^e` the series `G` agrees on `Z_3` with a polynomial with coefficients in
`Z_3`, because its coefficients tend to 0. Hensel's lemma for that polynomial
shows that `G` maps `1 + 3 Z_3` onto `1 + 3 Z_3` and `2 + 3 Z_3` onto `3 Z_3`
modulo every `3^e`. So the values of `G` modulo `3^e` are exactly the `g` with
`g != 2 (mod 3)`.

Theorem 2.7 (the 5-adic law, proven). Let `i` be the square root of -1 in
`Z_5` with `i == 3 (mod 5)`, and `A = 1 - i`, so `A == 8 (mod 25)`. For
`e >= 2`,

    T(5^e) = { v : v != 3 (mod 5) }  together with  { A (1 - 25 s / 2) mod 5^e : s a square in Z_5 }.

The class `3 (mod 5)` holds exactly `sq(e - 2)` elements of `T(5^e)`, where
`sq(k)` is the number of squares modulo `5^k`: `(5^(k+1) + 7)/12` for `k`
even, `(5^(k+1) + 11)/12` for `k` odd. That is 1, 3, 11, 53, 261, 1303 for
`e = 2, ..., 7`. The density of `T(5^e)` tends to `4/5 + 1/60 = 49/60`.

Proof. By Lemmas 2.1, 2.2 and 2.4 only the class `x == 8 (mod 20)` needs
work, and it gives the residues `== 3 (mod 5)`. Take `zeta = i` (order 4,
and `4 | x`) and `a = 5 w`. As in Theorem 2.6, these `x` are dense in
`3 + 5 Z_5 = i exp(5 Z_5)`, so the values are those of `A + 25 G(w)` with

    G(w) = sum over n >= 2 of c_n 5^(n-2) w^n,   c_2 = -A/2.

For `n >= 3` the coefficient has valuation at least
`n - 2 - v_5(n!) >= 1`. So `G(w) = -(A/2) w^2 U(w)` with `U(w)` in
`1 + 5 Z_5` for every `w` in `Z_5`. Every element of `1 + 5 Z_5` is a square,
so `G(Z_5)` lies in `-(A/2)` times the squares. Conversely let `s = t^2`. If
`t = 0`, take `w = 0`. Otherwise `t = 5^j u` with `u` a unit, and the
function `g(w_1) = w_1^2 U(5^j w_1)` satisfies `g(u) == u^2 (mod 5)` and
`g'(u) == 2u (mod 5)`, a unit. Hensel's lemma gives `w_1` with `g(w_1) = u^2`,
and `w = 5^j w_1` gives `G(w) = -(A/2) s`. Finally `A + 25 G = A (1 - 25 s/2)`,
and its residue mod `5^e` depends on `s mod 5^(e-2)`; the squares of `Z_5`
reduce to all squares modulo `5^(e-2)`. The count of squares modulo `p^k` is
classical.

Computed (`analysis/r3nt_tq.py`). The laws agree with a direct computation of
`T(3^e)` for `e <= 10`, `T(5^e)` for `e <= 7`, and `T(2^e)` (even residues) for
`e <= 12`. `T(p^e) = Z/p^e` for `p = 7` (`e <= 5`), 11 and 13 (`e <= 4`),
17, 19 and 23 (`e <= 3`), and every prime `7 <= p < 100` at `e = 2`. Lemma
2.2 holds class by class for `(p, e) = (3, 6), (5, 5), (7, 4), (11, 3), (13, 3)`.
The leads of the question are all confirmed: the residues prime to 3 are `{2}`
mod 27, `{2, 29}` mod 81 and `2 + 27 j`, `j` in `{0, 1, 3, 4, 6, 7}` mod 243;
`T(5^e)` misses 4 of the 5 classes `== 3` mod 25, 22 of 25 mod 125 and 114 of
125 mod 625.

### 2.3 Coverings with 81 and 125

Write `A(r) = sum s_i r^(k-i)` and `F_0` for a prefix
`(s_1, ..., s_(k-1))`, as in Theorem 15.13.

Corollary 2.8 (proven). If for every residue `r mod 81`, `A(r) - F_0` is not
in `T(81)`, then no string `(s_1, ..., s_(k-1), x)` with `x >= 1` is a
solution in any base, under either convention, and under `0^0 = 0` also for
`x = 0`. For a single modulus `3^e`, the modulus 81 is the last one that adds
anything: `T(3^e)` is the preimage of `T(81)` for `e >= 5`.

Proof. As for Theorem 15.13, with Theorem 2.6.

Example. For `(8, 7, x)`, `A(r) - F_0 = 8 r^2 + 7 r - 8^8 - 7^7` is never
`0 (mod 3)`, and it is `2 (mod 27)` only for `r == 8 (mod 9)`, where it is
`56 (mod 81)`. So 81 excludes `(8, 7, x)` for every `x`, and 27 does not.
Checked directly for `x <= 1500` (`analysis/r3nt_cover_examples.py`).

Proposition 2.9 (proven). If a single modulus `5^e` excludes every last digit
of a prefix, then `F_0 == 2 (mod 5)`, and `A(r) == 0` and `A'(r) == 0 (mod 5)`
for every `r`. So either every `s_i` is divisible by 5 (possible only under
`0^0 = 1`, with the number of zero digits `== 2 (mod 5)`), or the polynomial
`A mod 5` is a nonzero multiple of `(r^5 - r)^2` and the prefix has at least 10
digits.

Proof. `T(5^e)` contains every `v != 3 (mod 5)`, so `A(r) - F_0 == 3 (mod 5)`
for all `r`. At `r = 0` this gives `F_0 == 2`, and then `A(r) == 0` for all
`r`. If `A'(r_0)` is a unit for some `r_0`, then `t -> A(r_0 + 5t)` maps onto
the class `A(r_0) + 5 Z` modulo `5^e`, which meets `T(5^e)`. A polynomial over
`F_5` that vanishes with its derivative at every point is divisible by
`(r^5 - r)^2`. `A` has degree `k - 1` and no constant term.

So the 5-adic law matters only jointly with other moduli, as in the 11 sets of
section 15.4.4 that contain 5 or 25.

Computed (`analysis/r3nt_cover_density.py`, `data/r3nt_cover_density.txt`;
20,000 random prefixes per length, digits in `[3, 10^6]`, the sampling of
section 15.4.4). Share of prefixes whose last digit is excluded:

| length | 27 | 81 | 25 | 125 | 16, 27, 25, 7 | 16, 81, 125, 7 |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 0.1124 | 0.1161 | 0 | 0 | 0.1124 | 0.1161 |
| 4 | 0.0717 | 0.0736 | 0 | 0 | 0.0717 | 0.0736 |
| 5 | 0.0790 | 0.0807 | 0 | 0 | 0.0819 | 0.0837 |
| 6 | 0.0840 | 0.0853 | 0 | 0 | 0.0859 | 0.0873 |

The modulus 81 adds 0.2 to 0.4 percentage points to the 8% of section 15.4.4,
and 125 adds nothing alone, as Proposition 2.9 predicts. Small prefixes
(`analysis/data/r3nt_cover_examples.txt`): with digits `1..40` and `k = 3`, 27
excludes 204 of 1,600 prefixes and 81 excludes 210; with `k = 4` and digits
`1..12`, 131 and 134 of 1,728; with `k = 5` and digits `1..7`, 168 and 169 of
2,401. No prefix in these ranges is excluded by 125.

For question 47 this means: 81 is worth adding to the sieve of `kdigit`, and
`3^5` and higher are not, as single moduli. Powers of 5 above 25 are useful
only in combination.

SECTION-3

SECTION-4

SECTION-5

SCRIPTS
