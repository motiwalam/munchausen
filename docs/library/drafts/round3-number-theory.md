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

| question | what is now known | status |
|---|---|---|
| 45, window | Proposition 15.17 is correct, also when the leading digit is not the largest: only the second digit enters | proven (Lemma 1.1), checked on 3,135 solutions |
| 45, range | almost all bases have no solution with `2 <= k <= (1 - eps) ln b / ln ln b` digits, and in fact up to `(ln b / ln ln b)(1 + (ln ln ln b + ln 2 - 1 - delta)/ln ln b)`; counting multisets cannot go further | proven (Theorem 1.3) |
| 45, `B = 10^96` | the multiset bound stays below `B` up to 49 digits, the string bound up to 31; at 16 digits `B^0.34` against `B^0.46` | computed |
| 45, fixed `k` | the multiset count alone is weaker than Proposition 10.4; with `b - 1 \| F(c) - S(c)` it gains the factor `(k-2)!` | proven (Proposition 1.5) |
| 45, beyond `alpha = 1` | needs equidistribution of `F(c) - S(c)` in short windows of moduli; open | heuristic |
| 46, `p >= 7` | `T(p^e) = Z/p^e` for every `e` | proven (Theorem 2.3) |
| 46, `p = 3` | `T(3^e) = 3Z u {v == 2 (mod 27), v != 56 (mod 81)}` for `e >= 4`; 81 is the last useful single 3-power | proven (Theorem 2.6) |
| 46, `p = 5` | `T(5^e)` misses exactly the `v == 3 (mod 5)` outside `A (1 - 25 s/2)`, `s` a square, `A = 1 - sqrt(-1)`; counts 1, 3, 11, 53, 261, 1303 | proven (Theorem 2.7) |
| 46, coverings | 81 raises the covered share from 11.2% to 11.6% (3 digits) and 8.4% to 8.5% (6 digits); a single 5-power covers only special prefixes | proven (Corollary 2.8, Proposition 2.9), computed |
| 52 | `(gamma) = Q^(a n - 2) B^n`; `Q^j` is not principal for `j <= log2 x - 3`; the linear form has three logarithms, so Laurent and Proposition 18.4 do not apply; Matveev gives `n < 4.1 * 10^12 (d+1)^2 (log x)^2 (1 + log n)`; a bound of `x` by `n` only in one pure configuration (`x < 2^(2n+1)`) | proven (section 3) |
| 52, small `x` | no solution with `n >= 5` for `x <= 10^4` (all `n`), nor with `5 <= n <= 15` for `x <= 10^8` | computed (Theorem 3.5) |
| 51, `(1, 2, x)` | a solution only for `x = 6` (base 215) | proven (Proposition 4.1) |
| 51, `c = 25` | `sqrt D - 10` generates `P^2`, so Propositions 18.4 and 18.6 have analogues; `(1, x, 3)` is a solution for no prime power `x`; for odd prime powers `x` the solutions with `n >= 3` are `(5, 3)`, `(7, 3)`, `(3, 6)` | proven, with computations (Theorems 4.7, 4.8, Corollary 4.9) |
| 51, `c = 3` | no explicit generator; the regulator of `Z[theta]` is not bounded by `log x`, so the analogue of Theorem 18.10 fails even for prime `x`; every prime factor of `x` is `+-1 (mod 12)` | proven (Lemma 4.2, Proposition 4.10) |
| 51, computed | `(1, x, 2)` and `(1, x, 3)`: no solution for `x <= 10^9`; all `n` for odd `x <= 1001`: none for `c = 3`, only `(7, 3)` and `(3, 6)` for `c = 25` | computed (Theorem 4.11) |
| 53 | `d \| x` occurs (from `x = 15`, `d = 3`, up to `d = 34,333` at `x = 514,995`); the share of such `x` falls like `6.7 x^(-0.54)`; the class group conditions of Corollary 18.11 are expected to hold for infinitely many `x` | computed (GRH), heuristic |

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
can be regrouped by `n = m + l`. Subtract `x = zeta sum a^n / n!`.

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

## 3. The even case x == 0 (mod 8) (question 52)

The equation is (1) of chapter 18, `b (b + x) = x^n + 1`. By Proposition 18.1
the open even cases have `x = 2^a m` with `a >= 3`, `m` odd, `x` not a square
and `n >= 5` odd. Theorem 18.8 settles `m = 1`. Here `m > 1`.

### 3.1 Setting

Put `V = b + x/2` and `E = (x/2)^2 + 1`. Then `V^2 - E = x^n`, `V` is odd, and
`E == 1 (mod 16)`. Let `K = Q(sqrt E)`, `R = Z[(1 + sqrt E)/2]` (an order of
`K` whose conductor is odd), and

    gamma = (V + sqrt E) / 2 = (b + eps) / 2,    eps = x/2 + sqrt E,

so `gamma` is in `R`, `N(gamma) = x^n / 4 = 2^(a n - 2) m^n`, and
`gamma - gamma' = sqrt E`. The unit `eps` has norm -1, and
`Lam0 = log(gamma / gamma') < tau_n` with the `tau_n` of (2) in chapter 18,
because `gamma / gamma' = (b + eps) / (b + eps')`.

Lemma 3.1 (proven). The prime 2 splits in `R`, and the ideals `(gamma)` and
`(gamma')` of `R` are coprime. So

    (gamma) = Q^(a n - 2) B^n,

with `Q` one of the two primes above 2 and `B` a product over `p^c || m` of
`q_p^c`, `q_p` one of the two primes above `p`. All these ideals are prime to
the conductor, so they are invertible and factor uniquely.

Proof. `E == 1 (mod 8)`, so 2 splits. A common prime of `(gamma)` and
`(gamma')` divides `sqrt E` and `x^n`, but `E == 1 (mod p)` for every `p | x`.
If both primes above 2 divided `gamma`, one of them would divide `gamma'`
too. The same argument applies to each odd `p | m`, which splits because `E`
is a nonzero square mod `p`.

This is where Lemma 18.3 breaks: the exponent `a n - 2` of `Q` is not a
multiple of `n`.

### 3.2 The class of Q

Lemma 3.2 (proven). `Q^j` is not principal in `R` for
`1 <= j <= log2(x) - 3`. So the order `t` of the class of `Q` satisfies
`t >= floor(log2 x) - 2`. In particular `Q^2` is not principal for `x >= 32`.

Proof. Suppose `Q^j = (pi)` with `pi = (u + v sqrt E)/2` in `R`. No rational
prime divides `pi`, because `Q^j` is divisible neither by `(2) = Q Q'` nor by
an odd prime. If `u, v` are even, then `pi = u' + v' sqrt E` with
`gcd(u', v') = 1` and `u'^2 - E v'^2 = +-2^j`. If `u, v` are odd, then
`gcd(u, v) = 1` and `u^2 - E v^2 = +-2^(j+2)`. In both cases
`|u^2 - E v^2| <= 2^(j+2) < sqrt E`, because `sqrt E > x/2 >= 2^(j+2)`. A
coprime solution of `|u^2 - E v^2| < sqrt E` comes from a convergent of
`sqrt E` (cited: I. Niven, H. S. Zuckerman, H. L. Montgomery, An
Introduction to the Theory of Numbers, 5th ed., Theorem 7.24). Since
`E = (x/2)^2 + 1`, `sqrt E = [x/2; x, x, x, ...]`, and every convergent has
norm `+-1`. This contradicts `j >= 1`.

The bound is sharp for `x = 2^a`, where `Q^(a-2)` is principal. Computed
(`analysis/r3nt_even_q.gp`, `data/r3nt_even_q.txt`): for the 446 values
`x == 0 (mod 8)` up to 4000 with `E` squarefree, `t >= floor(log2 x) - 2`
holds, with equality in some cases.

Proposition 3.3 (proven). Let `b` be a solution, `C = Q^a B`, and `d` the
order of the class of `C` in the class group of `R`. (Parts (b) and (c), and
Theorem 3.4 below, hold with the same proofs in the maximal order, which the
computations use.) Then:

- (a) `n [C] = 2 [Q]`, so `d >= t / 2 >= (floor(log2 x) - 2) / 2`;
- (b) write `n = n0 + d j` with `0 <= n0 < d`. Then
  `gamma = +-eta0^k rho eta^j`, where `eta0` is the fundamental unit,
  `(rho) = C^(n0) Q^(-2)` and `(eta) = C^d`, and

        0 < Lam0 = | 2 k mu0 + lam + j th | < tau_n,    lam = log|rho / rho'|,  th = log|eta / eta'|;

- (c) if `m` is a prime power `p^c`, write `(delta) = Q^(a-2) P_m` with
  `delta = (eps + 1)/2` (the analogue of `P = (eps + 1)` in chapter 18). If
  `B = P_m` and `(gamma)` is divisible by the same `Q` as `delta` (the "pure"
  case), then `t | 2 (n - 1)`, and so `x < 2^(2n + 1)`. If `B = P_m` and
  `(gamma)` is divisible by the other prime above 2, then
  `t | 2 ((a - 1) n - 1)`.

Proof. (a) Lemma 3.1 gives `(a n - 2)[Q] + n [B] = 0`. Multiplying
`n [C] = 2 [Q]` by `d` gives `2 d [Q] = 0`, so `t | 2 d`. (b) `C^n Q^(-2)` is
principal and equals `C^(n0) Q^(-2) (C^d)^j`. (c) `N(delta) = x/4` and
`delta - delta' = sqrt E`, so `(delta) = Q^(a-2) P_m` for one prime `Q`. In the
first case `(gamma) = (delta)^n Q^(2n - 2)`. In the second `(gamma) = Q'^(a n - 2)
P_m^n` and `[P_m] = -(a - 2)[Q]`, `[Q'] = -[Q]`, which gives
`(2 (a - 1) n - 2) [Q] = 0`. In the first case Lemma 3.2 gives
`floor(log2 x) - 2 <= t <= 2 n - 2`.

So the first pure configuration has an analogue of Corollary 18.5, but
exponential: `x < 2^(2n+1)` in place of `x < 11 n`. The second gives only
`m < 2^(2 (a-1) n)`, which bounds the odd part of `x` by its 2-part and `n`.

Why there is no analogue of Proposition 18.4. In chapter 18 the fixed factor
is trivial, so the linear form has two terms and the explicit generator
`eps + 1` gives the lower bound `n log z >= mu0 - tau_n`. Here
`rho` generates `C^(n0) Q^(-2)`, which is never the unit ideal (its norm is
`x^(n0) / 4`), and `Q^2` itself is not principal (Lemma 3.2). So `lam` is a
fixed real number of size up to `mu0` that need not lie in
`Z th + 2 mu0 Z`.
The form in (b) has three logarithms with coefficients `2k`, `j` and 1.
Laurent's two-logarithm theorem does not apply, and an inhomogeneous form
gives no lower bound for `j`: `j th + lam` can be close to a multiple of
`2 mu0` for small `j`. This is the obstacle at 2.

### 3.3 A bound for n

Matveev's theorem (cited: E. M. Matveev, Izv. Math. 64 (2000) 1217-1269; in
the form of Y. Bugeaud, M. Mignotte, S. Siksek, Ann. of Math. 163 (2006),
Theorem 9.4). Let `alpha_1, ..., alpha_r` be positive real numbers in a
number field of degree `Dg`, `b_1, ..., b_r` integers with
`Lam = sum b_i log alpha_i != 0`, `B >= max |b_i|`, and
`A_i >= max(Dg h(alpha_i), |log alpha_i|, 0.16)`. Then

    log |Lam| > -1.4 * 30^(r+3) r^4.5 Dg^2 (1 + log Dg) (1 + log B) A_1 ... A_r.

For `r = 3` and `Dg = 2` the constant is `CM = 9.70 * 10^11`.

Theorem 3.4 (proven, with Matveev's theorem). In the setting of
Proposition 3.3, with `|lam|, |th| <= mu0` after multiplying `rho` and `eta`
by units,

    (n/2) log x < log(2 sqrt(x^2 + 4)) + 0.01 + CM (1 + log B) (2 mu0) (d log x + mu0) (n0 log x + log 4 + mu0),

with `B = max(j, |k|) <= n`. Since `mu0 <= log eps < log(x + 1)` and `n0 < d`,
this gives `n < 4.1 * 10^12 (d + 1)^2 (log x)^2 (1 + log n)` for `x >= 24`.

Proof. Apply Matveev's theorem to `alpha_1 = eta0^2`, `alpha_2 = |eta / eta'|`,
`alpha_3 = |rho / rho'|` with `b = (k, j, 1)`. For `alpha_1`, `Dg h = 2 mu0`.
For `alpha_2 = eta^2 / |N(eta)|`, a root of
`|N(eta)| T^2 - Tr(eta^2) T + |N(eta)|` with `|N(eta)| = x^d`, `Dg h <= d log x + |th|`.
For `alpha_3`, use `4 rho` in place of `rho`: it generates the integral ideal
`C^(n0) Q'^2` of norm `4 x^(n0)`, and `alpha_3` does not change. From (b),
`2 |k| mu0 <= j |th| + |lam| + 1`, so `|k| <= j + 1`. Compare with
`log Lam0 < log tau_n <= log(2 sqrt(x^2 + 4)) - (n/2) log x` for `n >= 5`.

This is the analogue of Theorem 18.10 with three logarithms: the bound has
`d^2 (log x)^2` in place of `d log x`, and a constant 60 million times larger.

### 3.4 Computations

Theorem 3.5 (computed). Let `x == 0 (mod 8)` have an odd prime factor and not
be a square.

- (a) For `x <= 10^8` there is no solution with `n` in {5, 7, ..., 15}
  (`fast/target/r3nt_sieve`, `data/r3nt_sieve_even_n5-15_1e8.txt`; the
  exact check `analysis/r3nt_even_direct.py` confirms `x <= 10^5`).
- (b) For `x <= 10^4` there is no solution with any odd `n >= 5`
  (`analysis/r3nt_even.gp`, `data/r3nt_even_1e4.txt`: 1,219 values of `x`,
  6,794 configurations `(Q, B, n0)`, every one reduced, no candidate).

The method of (b), `analysis/r3nt_even.gp`. For each `x` the script builds
`K` with a certified class group (`bnfcertify`), and for each of the two
primes `Q` above 2 and each of the `2^omega(m)` choices of `B` it computes `d`,
every `n0` with `n0 [C] = 2 [Q]`, and generators `rho`, `eta` in compact
form. Theorem 3.4 then bounds `j` by `J` (at most `1.5 * 10^19`). The reduction
lemma of Dujella and Petho (cited: A. Dujella, A. Petho, Quart. J. Math.
Oxford 49 (1998) 291-306, Lemma 5a) with a convergent `p/q` of
`th / (2 mu0)`, `q > 6 J`, and `eps_1 = ||q lam/(2 mu0)|| - J ||q th/(2 mu0)|| > 0`
leaves only `j < log(A_0 q / eps_1) / log B_0`, with
`A_0 = 2 sqrt(x^2 + 4) x^(-n0/2) / mu0` and `B_0 = x^(d/2)`. Those few
exponents are checked exactly, and so is every odd `n <= 301`. As a test,
the same script with `n >= 3` and `x = 2^a` allowed finds the known
solution `(x, n) = (8, 3)`.

### 3.5 What remains

For `x == 0 (mod 8)` with an odd prime factor and `n >= 5` odd, a solution
must have `x > 10^4`, and `x > 10^8` if `n <= 15`, and also `x > 10^9` for
`n = 7, ..., 15` and `x > 10^10` for `n = 5` (section 18.1.7). The open part
is a uniform bound: Theorem 3.4 bounds `n` by `x` and `d`, but nothing bounds
`x` by `n` except in the pure configuration of Proposition 3.3(c). The abc
conjecture still gives finiteness (Proposition 18.13).

## 4. The equations b(b+x) = x^n + 3 and x^n + 25 (question 51)

Under `0^0 = 1`, `(1, x, r)` is a solution in base `b` exactly when
`b (b + x) = x^x + c` with `c = w(r) - r + 1`: `c = 3` for `r = 2` and
`c = 25` for `r = 3`. Put `D = x^2 + 4c`, `U = 2b + x`, so that
`U^2 = 4 x^n + D`, and `theta = (x + sqrt D)/2`, of norm `-c`. Then
`N(b + theta) = b^2 + b x - c`, so the equation says `N(b + theta) = x^n`.
Work in the order `R = Z[theta]` of discriminant `D`.

### 4.1 Elementary cases

Proposition 4.1 (proven). `(1, 2, x)` is a solution in some base exactly for
`x = 6`, in base 215, under either convention.

Proof. The condition is `(b + 1)^2 = x^x + 6 - x`. For odd `x`, `x^2 == 1
(mod 8)` gives `x^x == x (mod 8)`, so the right side is `6 (mod 8)`, not a
square. For even `x >= 8`, `(x^(x/2) - 1)^2 < x^x + 6 - x < (x^(x/2))^2`. For
`x = 6` the right side is `6^6 = 216^2`. The cases `x = 0, 1, 2, 4` fail by
hand.

Lemma 4.2 (proven). Let `c` be 3 or 25 and `n >= 2`.

- (a) If `n >= 4` is even, or `n >= 5` and `x` is a square, there is no
  solution once `x^2 + 4c < 4 x^(n/2) + 1`. For `c = 3` this holds for all
  `x >= 2`. For `c = 25` it holds for `x >= 6`, and a direct check of `x <= 5`
  leaves one solution, `(x, n, b) = (3, 6, 26)`, where
  `x^2 + 100 = 4 x^3 + 1` and `U = 2 x^3 + 1`. So the families need `x` odd
  and not a square.
- (b) `c = 3`: `x` is prime to 3, every odd prime `p | x` has
  `p == +-1 (mod 12)`, and an even `x` has `x == 2 (mod 4)`.
- (c) `c = 25`: an even `x` has `x == 0 (mod 8)`; if `5 | x` then `5 | b`.
- (d) `n = 2`: no solution for `c = 3` (`U^2 = 5 x^2 + 12` is impossible mod 5);
  for `c = 25` every solution has `5 | x`.

Proof. (a) As Proposition 18.1(a), (b): `x^n` is a square `Y^2` and
`(2Y)^2 < U^2 < (2Y + 1)^2`. (b) If `3 | x`, then `b^2 + b x == 3 (mod 9)`
forces `3 | b` and then `b^2 + bx == 0 (mod 9)`. Modulo `p | x`,
`U^2 == D == 12`, so 3 is a square mod `p`. For even `x` put `V = U/2`:
`V^2 = x^n + (x/2)^2 + 3` is `7 (mod 8)` if `x == 4 (mod 8)` and `3 (mod 16)` if
`8 | x`. (c) With `V` as before, `V^2 == 2 (mod 4)` if `x == 2 (mod 4)` and
`5 (mod 8)` if `x == 4 (mod 8)`; and `b^2 == 25 - b x == 0 (mod 5)`. (d) For
`c = 25`, `5 | U`, then `5 | x`.

Computed (`analysis/r3nt_n3.sage`, `data/r3nt_n3.txt`). For `n = 3` the
equation is the elliptic curve `Y^2 = X^3 + X^2 + 64 c` with `X = 4x`,
`Y = 4U`. Its integral points give: no solution for `c = 3` (conductor 3891,
rank 1); the solutions `(x, b) = (5, 10), (7, 16), (656, 16477), (1600, 63205)`
for `c = 25` (conductor 54005, rank 2). For `c = 1` the same script gives the
list of chapter 16.

### 4.2 c = 25: an explicit generator

Lemma 4.3 (proven). Let `x` be odd and prime to 5, and `c = 25`. The
conductor of `R` is prime to `10 x`, so the ideals below are invertible and
factor uniquely.

- (a) 5 splits in `R`, and `(theta) = q^2` for a prime `q` above 5.
- (b) `(theta - 5) = q P` with `N(P) = x`. Then `(theta' - 5) = q' P'`,
  `P P' = (x)`, and `P`, `P'` are coprime.
- (c) `P^2 = (pi)` with `pi = sqrt D - 10 = (theta - 5)^2 / theta`.
- (d) For a solution, `(b + theta) = B^n` with `B` a product over `p^a || x`
  of `q_p^a`, `q_p` a prime above `p`, and `B != B'`. If `x` is a prime power,
  then `B` is `P` or `P'`.

Proof. `D == x^2 (mod 5)` is a nonzero square and `D` is odd and prime to
`x`. `theta theta' = -25` and `theta - theta' = sqrt D` is prime to 5, so
`(theta)` is the square of one prime above 5. `(theta - 5)(theta' - 5) = -5 x`
and the difference is `sqrt D`, prime to `5 x`; `theta - 5 == -5 (mod q)`, so
`q | theta - 5`. Then `(theta - 5)^2 = q^2 P^2 = (theta) P^2`, and
`(theta - 5)^2 / theta = theta - 10 + 25/theta = theta - 10 - theta' = sqrt D - 10`.
(d) is the argument of Lemma 18.3.

Call a solution pure if `B` is `P` or `P'`. Let `mu0` be the logarithm of the
fundamental unit of `R`. Every unit `e > 1` of `R` is `(u + v sqrt D)/2` with
`u, v >= 1` and `u^2 - D v^2 = +-4`, so `e > sqrt(D - 4) > x` and
`mu0 > log x`.

Proposition 4.4 (proven). Let `x` be odd, prime to 5, `n >= 5` odd, and `b` a
pure solution of `b (b + x) = x^n + 25`. Put `l = arcsinh(10/x)`. Then there
is an integer `s >= 1` with

    | n l - s mu0 | = Lam0 < tau_n = sqrt D / (x^(n/2) - x/2 - 25),

where `Lam0 = log((b + theta)/(b + theta'))` (for `x = 3` assume `n >= 7`, so
that the denominator is positive). In particular
`n > (mu0 - tau_n) / l > (mu0 - tau_n) x / 10`.

Proof. If `B = P`, Lemma 4.3 gives `(b + theta)^2 = u pi^n` with `u` a unit
of `R`, `u = +-eta0^k`. Then `|pi / pi'| = (sqrt D - 10)/(sqrt D + 10) = e^(-2l)`,
because `(sqrt D + 10)/x = sqrt(1 + 100/x^2) + 10/x`. So
`2 Lam0 = 2 k mu0 - 2 n l`. For `B = P'` the sign of `n l` changes. In both
cases `Lam0 = |n l - s mu0|` for some integer `s`. The bound `tau_n` is that of
(2) in chapter 18 with `c = 25`: `b + theta' = b - 25/theta > b - 25` and
`b > x^(n/2) - x/2`. If `s <= 0`, then `Lam0 >= n l > 10 n / sqrt D > tau_n`;
the last inequality is `10 n (x^(n/2) - x/2 - 25) > x^2 + 100`, true in the
range stated.

This is the analogue of Proposition 18.4, with `l = arcsinh(10/x)` in place of
`log z = 2 artanh(1/eps)`. The generator `pi` of `P^2` plays the role of
`eps + 1`; `(1, x, 3)` gets it because `c = 25` is a square, so that `theta - 5`
has norm `-5 x`.

Proposition 4.5 (proven). For odd `x >= 22,027` prime to 5, the equation
`b (b + x) = x^x + 25` has no pure solution.

Proof. Take `n = x` in Proposition 4.4. Then `x l = x arcsinh(10/x) < 10`, so
`s mu0 < 10 + tau_x`, while `mu0 > log x >= log 22027 > 10 + 10^-5 > 10 + tau_x`.
So `s < 1`, a contradiction.

The analogue of Proposition 18.6 is thus easier: the unit of `R` is never
small. (Without the order `R`, with the fundamental unit of the maximal
order, the same conclusion needs the gap computation of `analysis/r3nt_c25.py`,
part 2: the numbers `s mu` with `mu` in
`{arcsinh(y/2)} u {arccosh(y/2)}` and `s >= 1` stay at least `2.1 * 10^-5` away
from 10, while `10 - x l < 1000/(6 x^2)`. That gives `x < 2808` for pure
solutions, by a different route.)

Proposition 4.6 (proven). For `x = 5^e` with `e >= 3` odd, the equation
`b (b + x) = x^n + 25` has no solution with `n >= 3` odd. For `x = 5` the only
solution with `n >= 3` is `n = 3`, `b = 10`.

Proof. By Lemma 4.2(c), `b = 5 g`, and with `y = x/5 = 5^(e-1)` the equation
becomes `g^2 + g y - 1 = 5^(e n - 2)`, that is `N(g + eps_y) = 5^(e n - 2)` with
`eps_y = (y + sqrt(y^2 + 4))/2` in `R_1 = Z[eps_y]`, whose conductor is prime
to 5. For `x = 5`, `(2g + 1)^2 = 4 * 5^(n-2) + 5` forces `5 | 2g + 1` and then
`5 g'^2 = 4 * 5^(n-3) + 1` with `2g + 1 = 5 g'`, impossible for `n >= 4`; `n = 3`
gives `g = 2`. Now let `e >= 3`. As in Lemma 18.2, 5 splits in `R_1` and
`(g + eps_y) = p^(e n - 2)` for a prime `p` above 5, while
`(eps_y + 1)` has norm `y` and equals `p^(e-1)` or `p'^(e-1)`. So the order
`t` of the class of `p` divides `e - 1` and `e n - 2`. If `p^j = (pi)` with
`1 <= j <= e - 2`, write `pi = (u + v sqrt(y^2 + 4))/2`; then
`|u^2 - (y^2 + 4) v^2|` is `4 * 5^j` or `5^j`, below `sqrt(y^2 + 4)`, so `u/v`
is a convergent of `sqrt(y^2 + 4)` (as in Lemma 3.2). The continued fraction is
`[y; (y-1)/2, 1, 1, (y-1)/2, 2y]`: the complete quotients are
`(sqrt D_1 + y)/4`, `(sqrt D_1 + y - 2)/y`, `(sqrt D_1 + 2)/y`,
`(sqrt D_1 + y - 2)/4` and `sqrt D_1 + y`, with `D_1 = y^2 + 4`. The norms of
the convergents are `+-1`, `+-4` and `+-y`, none of the form `5^j` or
`4 * 5^j` with `1 <= j <= e - 2`. So `t = e - 1`, which is even, while `e n - 2`
is odd. This contradicts `t | e n - 2`.

Theorem 4.7 (proven, with the sieve below). `(1, x, 3)` is a solution in no
base for any prime power `x`, under `0^0 = 1`.

Proof. Even `x` and squares: Lemma 4.2(a). `x = 5^e`: Proposition 4.6 (for
`x = 5`, `n = x = 5 >= 4`). Odd `x = p^e`, `p != 5`, `e` odd: every solution
is pure (Lemma 4.3(d)), so `x < 22,027` by Proposition 4.5, and the sieve
excludes every `x <= 10^9`.

Theorem 4.8 (proven for `x > 507,211`; computed for smaller `x`). Let `x` be odd and
prime to 5, and `n >= 5` odd. Then `b (b + x) = x^n + 25` has no pure
solution.

Proof for large `x`. Apply Laurent's theorem (section 18.1.4) to
`alpha1 = eta0`, `alpha2 = zeta = e^(2l) = (sqrt D + 10)/(sqrt D - 10)`,
`b1 = 2 s`, `b2 = n`: `|n log zeta - 2 s log eta0| = 2 Lam0`. Here `eta0` is the
fundamental unit of the maximal order and `s` is replaced by `s` times the
index of the unit groups; Proposition 4.4 holds with that `mu0` as well.
`zeta` is a root of `x^2 T^2 - 2 (x^2 + 200) T + x^2`, which is primitive since
`gcd(x, 10) = 1`, so `h(zeta) = log x + l`, and `zeta` is not a unit, hence
independent of `eta0`. Take `log A1 = max(mu0, 1)/2` and
`log A2 = log x + l`. For `x >= 10^5`, `l < 10.0001/x`, `tau_5 < 10^-8`, and
as in Part A of Theorem 18.7 Laurent's bound gives
`nu = n / max(mu0, 1) < 2 + 403.3 M^2` with
`M = max(log(1.0001 nu) + 0.38, 5)`, so `nu < 50,721`
(`analysis/r3nt_c25.py`, part 3; the exact bound is 50,720.6). With
`n > (mu0 - 10^-8) x / 10.0001` and `mu0 >= 1` (the fields `Q(sqrt 5)` and
`Q(sqrt 2)`, the only ones with a unit below `e`, need `5 | x` or `x` even),
`x <= 507,211`.

Computed part (`analysis/r3nt_pure25.gp`, `data/r3nt_pure25_507211.txt`).
For each of the 202,603 odd `x <= 507,211` prime to 5 and not a square, the
script computes `mu0` with `quadregulator` (continued fractions, no GRH),
bounds `n` by Laurent's theorem (largest bound `3.0 * 10^10`), and tests the
convergents of `l / mu0` (Legendre, since `2 n tau_n < mu0` for `n >= 17`).
No candidate with `n >= 17` appears. The exponents `5 <= n <= 15` are covered
by the sieve for all `x <= 10^7` (`data/r3nt_sieve_c25_n5-15_1e7.txt`).

Corollary 4.9 (proven, with computations). For an odd prime power `x`, the
solutions of `b (b + x) = x^n + 25` with `n >= 3` are exactly
`(x, n, b) = (5, 3, 10)`, `(7, 3, 16)` and `(3, 6, 26)`.

Proof. `n = 3`: the elliptic curve. `n >= 4` even, or `x` a square: Lemma
4.2(a). `x = 5^e`: Proposition 4.6. Otherwise every solution is pure: `n <= 15`
by the sieve (`x <= 10^7`), `n >= 17` by Theorem 4.8.

So the method of chapter 18 does not need a unit of norm -1. It needs a fixed
power of the ideal `P` of norm `x` with an explicit generator whose logarithm
is about `C / x`; then Proposition 18.4 has an analogue, and the unit enters
only through the lower bound `mu0 > log x`, which every order `Z[theta]` has.

### 4.3 c = 3: where the method stops

For `c = 3`, `theta` itself generates a prime above 3, and `(theta - 3)` has
norm `6 - 3x`, not a multiple of `x`. No element `u + v theta` has a norm of the
form `+-x^j 3^i 2^h` for all `x` at once: that would need a square root of 3
modulo `x` given by a polynomial in `x`. So no power of `P` has a known
generator, and only the analogue of Theorem 18.10 remains. Its proof goes
through unchanged with `D = x^2 + 12`: for `B^d = (eta)`,
`|2 k mu0 + (n/d) th| < tau_n`, and Laurent's theorem gives

    log tau_n >= -403.2 M^2 (max(mu0, 1)/2) ((d log x + mu0)/2).

In chapter 18, `mu0 <= log eps`, about `log x`, because `eps` is a unit; this
turned the inequality into `n < 6.4 * 10^4 d log x`. For `c = 3` no unit of
size `x` exists in general: `x^2 + 12` is of Richaud-Degert type only when
`12 | 4x`, that is `3 | x`, which Lemma 4.2(b) excludes. Heuristic: as for
most real quadratic fields, `mu0` is then typically of size `sqrt D`, about
`x`, and the inequality allows `n` up to about `x^2 / log x`.

Proposition 4.10 (proven). Let `x` be a prime, `x > 10^6`, and let `b` solve
`b (b + x) = x^x + 3`. Let `p` be the prime of `R` with `(b + theta) = p^x`.
Then either the class of `p` has order exactly `x`, so the class number of `R`
is a multiple of `x`, or `p = (eta)` is principal and

    mu0 (log x + mu0) > x log x / (202 M^2),   M = max(log(2x) + 0.38, 5).

Proof. The order of `[p]` divides the prime `x`. If it is 1, apply the
inequality above with `d = 1`, `n = x` and `-log tau_x > (x/2 - 1.01) log x`,
and use `mu0 > log x > 1`. Then `b' <= (x + 1)/log x + x / log x <= 2 x`.

So for prime `x` the family `(1, x, 2)` would need either a class group with an
element of order `x` in a field of discriminant about `x^2`, or a principal
`p` with a regulator `mu0 > sqrt(x log x) / (21 M)`. (If `mu0 <= log x`, the
inequality gives `mu0 > x / (404 M^2)`, which is larger than `log x`; so
`mu0 > log x` and `2 mu0^2 > x log x / (202 M^2)`.) The class
number formula makes the first case implausible: with `mu0 > log x`,
`h(R) mu0` is about `sqrt D L(1, chi) / 2` with `L(1, chi)` of size
`log x`, so `h(R)` is at most about `x / 2` (heuristic; I did not write out the
explicit constants). The second case is the generic one. Computed
(`analysis/r3nt_c3_primes.gp`, `data/r3nt_c3_primes.txt`, GRH): of the 1,121
primes `x == +-1 (mod 12)` up to `2 * 10^4`, 621 have a principal prime above
`x`, and all 621 have a regulator above the bound of Proposition 4.10 (median
`mu0 / sqrt x` = 27); no class of order `x` occurs (largest order 56). This is the
obstacle for `c = 3`: the regulator of `Z[theta]` is not bounded by `log x`.

The question suggested the case `3 | x`, where `x^2 + 12` is of
Richaud-Degert type with the unit `1 + (x/3) theta = theta^2 / 3`. By Lemma
4.2(b) that case has no solution at all, so it gives no foothold.

For a fixed `x` the method still works, because it only needs `mu0`.

Theorem 4.11 (computed). For odd `x <= 1001`:

- `b (b + x) = x^n + 3` has no solution with `n >= 2`;
- `b (b + x) = x^n + 25` with `x` prime to 5 has, for `n >= 2`, only the
  solutions `(x, n, b) = (7, 3, 16)` and `(3, 6, 26)`.

Proof. `n = 2` and even `n`: Lemma 4.2. `n = 3`: the elliptic curves.
`n = 5, ..., 15`: the sieve (`x <= 10^7`,
`data/r3nt_sieve_c3_n5-15_1e7.txt`, `data/r3nt_sieve_c25_n5-15_1e7.txt`).
`n >= 17`: `analysis/r3nt_allnc.gp` (`data/r3nt_allnc_c3_1001.txt`,
`data/r3nt_allnc_c25_1001.txt`), the method of Theorem 18.12 with `theta` in
place of `eps`, certified class groups, and the bound of Laurent with the
true `mu0`. For `c = 3`, 228 of the 323 values of `x` fail Lemma 4.2(b). The
other 95 have 224 ideals `B` (78 not principal); Laurent allows `n` up to
`2.1 * 10^9`. For `c = 25` there are 388 values and 1,306 ideals (658 not
principal), with `n` up to `4.6 * 10^9`. No candidate appears. With the
threshold lowered to `n >= 3` the same script finds `(7, 3)` for `c = 25` and
`(7, 7)` and `(119, 3)` for `c = 1`.

Computed (sieves, `fast/target/r3nt_sieve`):

- `(1, x, 2)`: `4 x^x + x^2 + 12` is not a square for `2 <= x <= 10^9`
  (`data/r3nt_sieve_1x2_1e9.txt`; no survivor, primes up to 127 suffice);
- `(1, x, 3)`: `4 x^x + x^2 + 100` is not a square for `2 <= x <= 10^9`
  (`data/r3nt_sieve_1x3_1e9.txt`; primes up to 131 suffice);
- `b(b + x) = x^n + 3` for `n = 5, ..., 15` and `x <= 10^7`: only
  `(x, n, b) = (2, 5, 5)`; for `c = 25` none.

What remains. For `(1, x, 3)`: composite `x` with a mixed ideal `B` (as for
`(1, x, 1)` in Corollary 18.11, but without the bound `mu0 <= log x`, so the
analogue of Theorem 18.10 bounds `n` only in terms of `mu0`), and composite
`x` divisible by 5. For `(1, x, 2)`: every `x > 10^9` whose prime factors are
`== +-1 (mod 12)`, including primes, because of the regulator.

## 5. Orders of mixed ideal classes (question 53)

Corollary 18.11 leaves one case of `b (b + x) = x^x + 1` open: `x > 4 * 10^9`
odd, composite, not a prime power, with a mixed ideal `B` of norm `x` in
`Q(sqrt(x^2 + 4))` whose class has order `d | x` and `x / d < 3.3 * 10^4 log x`.
Below `10^6`, `3.3 * 10^4 log x > x / 3`, so there the condition is simply
`d | x` with `d > 1`.

Computed (`analysis/r3nt_mixed_orders.gp`, `data/r3nt_mixed_orders.txt`;
`bnfinit` under GRH, which is enough for statistics; `analysis/r3nt_mixed_stats.py`
for the tables). All odd `x` in `[3, 200001]`, and five windows near `2.5`, `4`, `5.5`, `7` and `8.5 * 10^5` (the runs there were stopped early; each window is complete). For each odd non-square `x` with at least two prime
factors the script lists the order `d` of every mixed ideal, one per
conjugate pair (`B` and `B'` have inverse classes).

| range of `x` | values | mixed pairs | pairs with `d \| x` | `x` with some `d \| x` | with `d >= x/100` | with `d >= x/1000` | largest `d/x` | largest `h/x` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `[3, 10^4)` | 3,712 | 6,560 | 337 (5.1%) | 241 (6.5%) | 59 | 193 | 0.200 | 0.200 |
| `[10^4, 10^5)` | 36,520 | 82,464 | 1,000 (1.2%) | 689 (1.9%) | 27 | 228 | 0.110 | 0.118 |
| `[10^5, 2 * 10^5]` | 41,539 | 103,123 | 546 (0.53%) | 417 (1.0%) | 5 | 74 | 0.094 | 0.102 |
| `[2, 2.58] * 10^5` | 24,252 | 62,332 | 264 (0.42%) | 191 (0.79%) | 1 | 24 | 0.085 | 0.094 |
| `[3.5, 4.04] * 10^5` | 22,934 | 61,188 | 213 (0.35%) | 145 (0.63%) | 2 | 18 | 0.083 | 0.090 |
| `[5, 5.52] * 10^5` | 21,879 | 59,905 | 175 (0.29%) | 120 (0.55%) | 1 | 10 | 0.081 | 0.089 |
| `[6.5, 6.99] * 10^5` | 20,871 | 58,163 | 116 (0.20%) | 88 (0.42%) | 0 | 8 | 0.077 | 0.088 |
| `[8, 8.49] * 10^5` | 21,012 | 59,426 | 105 (0.18%) | 78 (0.37%) | 0 | 6 | 0.081 | 0.087 |

Only `x = 15` has `d >= x/10`.

Observations:

- `d | x` happens. The smallest case is `x = 15`, `d = 3`. The largest `d`
  found is `d = 34,333 = h` at `x = 514,995 = 15 * 34,333`, so `x / d = 15`.
  A pattern such as "d never divides x" does not hold, and no proof can rest
  on one.
- When `d | x`, `d` is usually small: the median of `log(x/d) / log x` is
  about 0.74 in every range, so a typical such `d` is about `x^(0.26)`.
- The share of `x` with some mixed `d | x` falls like `6.7 x^(-0.54)` (least squares over the ranges). The share of
  `x` with some `d | x` and cofactor `x/d <= G` is close to `c(G) / x`, with
  `c(1000)` about 0.27 * 1000 and `c(10^4)` about 0.11 * 10^4, stable across
  the ranges (`data/r3nt_mixed_stats.txt`).
- The largest `d / x` is about 0.08 near `10^6`, just below the largest
  `h / x`. Both fall slowly, like `h ~ x L(1, chi) / (2 log x)` predicts
  for these fields, whose regulator is about `log x`.

Heuristic. Extrapolate `c(G)` with the growth seen between `G = 1000` and
`10^4`, `c(G) ~ 270 (G / 1000)^0.65`. At `x = 4 * 10^9` the loophole needs
`x / d < G(x) = 3.3 * 10^4 log x`, about `7.3 * 10^5`, so `c(G(x))` is about
`2 * 10^4`. About half of all integers are odd and composite, so the expected
number of `x` in `(4 * 10^9, X]` that pass every class-group condition of
Corollary 18.11 is about `10^4 ln(X / (4 * 10^9))`. It is unbounded. So the
class group alone cannot close the loophole, and the Diophantine condition
must do it: such an `x` still needs `|q th - 2 p mu0| < tau_x` for a
convergent, a chance of order `x^(-x/2)` in the model of section 18.1.8. The
expected number of solutions beyond `4 * 10^9` stays far below 1.

## Scripts and data

| file | content |
|---|---|
| `analysis/r3nt_multiset.py` | question 45: the window on all known solutions, the multiset search, the bounds at `B = 10^96` and beyond: `data/r3nt_multiset.txt` |
| `analysis/r3nt_tq.py` | question 46: `T(p^e)` against Theorems 2.3, 2.6, 2.7 and Lemma 2.2 |
| `analysis/r3nt_cover_density.py` | question 46: covered prefixes with 81 and 125: `data/r3nt_cover_density.txt` |
| `analysis/r3nt_cover_examples.py` | question 46: small prefixes excluded by 81 or 125, direct checks: `data/r3nt_cover_examples.txt` |
| `analysis/r3nt_even_q.gp` | question 52: the order of the class of `Q` (Lemma 3.2): `data/r3nt_even_q.txt` |
| `analysis/r3nt_even.gp` | question 52: all `n` for `x == 0 (mod 8)` (Theorem 3.5): `data/r3nt_even_1e4.txt` |
| `analysis/r3nt_even_direct.py` | question 52: exact check for `n <= 15`, `x <= 10^5`: `data/r3nt_even_direct.txt` |
| `analysis/r3nt_sieve.c` | questions 51, 52: sieve for `A x^e + B x^2 + C x + D` a square: `data/r3nt_sieve_*.txt` |
| `analysis/r3nt_n3.sage` | question 51: `n = 3` for `c = 1, 3, 25`: `data/r3nt_n3.txt` |
| `analysis/r3nt_c25.py` | question 51: identities, gaps and the Laurent constant for `c = 25`; continued fractions for `x = 5^e` |
| `analysis/r3nt_pure25.gp` | question 51: pure solutions for `c = 25`, `x <= 507,211` (Theorem 4.8): `data/r3nt_pure25_507211.txt` |
| `analysis/r3nt_allnc.gp` | question 51: all `n` for `c = 3, 25`, odd `x <= 1001` (Theorem 4.11): `data/r3nt_allnc_c3_1001.txt`, `data/r3nt_allnc_c25_1001.txt` |
| `analysis/r3nt_mixed_orders.gp` | question 53: class orders of mixed ideals: `data/r3nt_mixed_orders.txt` |
| `analysis/r3nt_mixed_stats.py` | question 53: the statistics of section 5: `data/r3nt_mixed_stats.txt` |
| `analysis/r3nt_c3_primes.gp` | question 51: principal primes and regulators for `c = 3`: `data/r3nt_c3_primes.txt` |

Build the sieve with `cc -O2 -o fast/target/r3nt_sieve analysis/r3nt_sieve.c`.
For example `fast/target/r3nt_sieve 4 1 0 100 0 1000000000` sieves
`(1, x, 3)` and `fast/target/r3nt_sieve 4 1 0 4 5 100000000 8 8 0` the
exponent 5 with `x == 0 (mod 8)`. Run the PARI scripts as their headers say,
for example `(echo 'c=3; X=1001;'; cat analysis/r3nt_allnc.gp) | gp -q`.
