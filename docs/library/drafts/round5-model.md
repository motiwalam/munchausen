# Round 5 model: theorems about the model

DRAFT. This file answers questions 81, 82, 80, 83 and 84 of
`questions-round5.md` (Theme XIII). Questions 81, 82 and 80 ask for proofs
about the probabilistic model of chapter 5 and its variants. Questions 83
and 84 ask for two corrected models, one in `F_q[T]` and one in the
factorial system. Each statement is marked proved (a proof is here),
computed (an exact computation, with its range), heuristic (a model, or a
judgment from data) or conjecture.

## Summary

| question | answer | status |
|---|---|---|
| 81, length shares | Theorem 1.1: in the basic model, `E_(b-j)(b) -> s_j` for every fixed `j`, with `|E_(b-j) - s_j| <= ((j+1)^2 + 1)/b + (j+2)/floor(sqrt b)!` for `b >= b_0(j)`. The limits are explicit sums: 8.03%, 55.18%, 23.25%, 8.55%, 3.15%, 1.16%. The total over all lengths tends to 1 (Corollary 1.6). The first correction is `c_j / b` with `c_0 = -1/(4e)` (Proposition 1.7). | proved; computed check |
| 82, `k(B)` | Theorem 2.3 and Corollary 2.4: `k(B) = omega(B-1)` whenever some irreducible factor of `B - 1` has degree prime to `e - 1`; so always when `e - 1` is a prime power. Theorem 2.5: in every case `k(B) <= omega(B-1) + 1`, with an exact criterion for the extra dimension; it never occurs for non-squarefree `B - 1`, nor for squarefree `B - 1` with `q <= e - 2`. Together with Remark 2.6 this proves `k = omega` for all `e <= 10` and for every census base. No counterexample among 110,654 bases and 379,700 polynomials of the open factor types. | proved for the cases listed; conjecture in general (first open type: `e = 11`, factors of degrees 5 and 6, `q >= 11`) |
| 80, Assumption R | Assumption R as stated is false for short strings (Lemma 3.1); Lemma 13.10 only needs `d >= b/2`. Theorem 3.2 removes the conditioning on `G_d` and reduces R to one number per base, `rho(b)`. Computed: `rho(b) <= 0.82` for `10 <= b <= 6000`, so the refined Corollary 13.11 holds unconditionally there, with `kappa <= |H_0| + 5`, and `kappa <= |H_0| + 0.0005` for `100 <= b <= 6000`. The Poisson rate over all odd prime powers `q | b-1`, `b <= 20,000`, is at least 0.2143 (0.2308 for `b >= 10`); for `b - 1 = p` prime the sums show square-root cancellation. Proposition 3.6 proves the spread modulo every prime `p <= b^(2/3 - eps)`. No `o(p)` bound for the complete sums is in the literature I found. | proved; computed; conjecture for `b > 6000` |
| 83, Frobenius-block model | Keeping the blocks of Corollary 24.3 and the residue modulo `B - 1`, and drawing each `p_j` uniformly among digits of its degree, predicts the census within 17% for 16 of the 21 factor types, against 5 of 21 for the refined model. Totals: 31.6, 73.5, 58.7 against census 34.4, 76.3, 60.5 (refined 26.2, 64.8, 45.4). The irreducible quartic of `(5, 4)`: 8.8 against 10.0 (refined 4.9). The per-orbit Pearson statistic drops from 749 to 187 on 160 orbits for `(5, 4)`. | computed; heuristic |
| 84, factorial system | A model that keeps the true top digits of `F` over the positions where the largest digit must sit (Lemma 5.1) closes about half the lengths. Open for `L <= 33`: 8, 10, 13, 14, 15, 18, 19, 20, 24, 26, 28, 29, 30, 32; for `34 <= L <= 100`: 11 to 14 lengths, among them 35 and 40. It closes all 8 lengths in 10..26 without near-solutions (plain model: 81 expected) and keeps open all 5 with them. It expects 3.85 solutions below `34!` (plain 4.6); with the cluster calibration from near-solutions the empty census has probability 0.22 to 0.39. Beyond `34!`: 0.29 expected up to `L = 40`, 2.5 up to `L = 100`. The census extension to `L = 40` was not run. | computed; heuristic |

## 1. The length shares as a theorem (question 81)

### 1.1 The model

Fix a base `b >= 3` and a convention `m` in `{0, 1}`. Let `w(x) = x^x` for
`x >= 1` and `w(0) = m`. A random `d`-digit string `n` has its leading
digit uniform on `{1, ..., b-1}` and its other `d - 1` digits uniform on
`{0, ..., b-1}`, all independent. Let `F(n) = sum of w(x)` over the digits.
Section 5.1 defines the expected number of `d`-digit solutions as

    E_d(b) = P( b^(d-1) <= F(n) < b^d ).

This is the model of `analysis/model.py`. Write `N_x` for the number of
copies of the value `x` in `n`, and `y_0 = min{ y >= 1 : N_(b-y) >= 1 }`,
the distance of the largest digit from `b`.

For `y >= 1` let `gamma(y) = (e^y - floor(e^y)) / e^y`, which is positive
because `e^y` is irrational. For `j >= 0` let
`gamma_j = min{ gamma(y) : y in {j, j+1}, y >= 1 }`. The values are
`gamma_0 = 0.264`, `gamma_1 = 0.0527`, `gamma_2 = gamma_3 = 0.00426`,
`gamma_4 = 0.00278`, `gamma_5 = 0.00106`.

Define the event, for independent counts,

    A_j = { y_0 = j and N_(b-j) < e^j }  union  { y_0 = j+1 and N_(b-j-1) > e^(j+1) },

where the first part is empty for `j = 0`, and the limit

    s_j = sum over 1 <= k < e^j of e^(-j) / k!  +  sum over k > e^(j+1) of e^(-(j+1)) / k!.

So `s_0 = e^(-1) (e - 5/2)`. Numerically (`analysis/r5m_shares.py`):

| `j` | 0 | 1 | 2 | 3 | 4 | 5 | `>= 6` |
|---|---:|---:|---:|---:|---:|---:|---:|
| `s_j` | 0.080301 | 0.551823 | 0.232540 | 0.085548 | 0.031471 | 0.011578 | 0.006738 |

These are the shares of section 5.2. The second sum in `s_j` is the case
"the largest digit is `b - j - 1` and it occurs more than `e^(j+1)` times";
it adds `3.8 * 10^-6` to `s_1` and less elsewhere. Section 5.2 and
`model.limit_terms` leave it out, which does not change any printed digit.

### 1.2 The theorem

**Theorem 1.1** (proved). Fix `j >= 0` and let

    b_0(j) = max( e^(j+2), j + 1 + 2 (j+1)^2 / gamma_j, 64 / gamma_j^2 ).

For every `b >= b_0(j)`, in the basic model under either convention,

    | E_(b-j)(b) - s_j |  <=  ((j+1)^2 + 1) / b  +  (j+2) / floor(sqrt b)!.

In particular `E_(b-j)(b) -> s_j` as `b -> infinity`.

The constant `b_0(j)` is crude (`b_0(0) = 919`, `b_0(1) = 23,000`). The
proof needs it only to keep the threshold `e^y` away from the integers.
The exact computation of section 1.4 shows the convergence already at
`b = 30`.

The proof has three steps: the weights, the localization of the event to
the top `j + 2` counts, and the Poisson coupling.

**Lemma 1.2** (weights, proved). For `0 <= y < b`,

    e^(-y) b^(b-y)  <=  w(b - y)  <=  e^(-y) b^(b-y) exp( y^2 / (2 (b - y)) ).

Proof. Put `t = y/b`. Then `ln w(b-y) - (b-y) ln b = b (1-t) ln(1-t)`,
and `(1-t) ln(1-t) = -t + sum over k >= 2 of t^k / (k (k-1))`, a series with
positive terms after the first. So the logarithm is at least `-y` and at
most `-y + (y^2 / (2b)) sum over m >= 0 of t^m = -y + y^2 / (2 (b-y))`.

**Lemma 1.3** (coupling, proved). Let `d = b - j` and `K = j + 1`. Let
`P_b` be the law of `(N_(b-1), ..., N_(b-K))` for the random `d`-digit
string, and `Q` the law of `K` independent Poisson(1) variables. Then

    d_TV(P_b, Q) <= (1 + K + K j) / b = ((j+1)^2 + 1) / b.

Proof. Three steps, each bounded in total variation.

1. Replace the leading digit by a uniform digit on `{0, ..., b-1}`. The
   two laws of the string differ by `1/b` in total variation.
2. For `d` independent uniform digits, the total `M` of the `K` counts is
   Binomial(`d`, `K/b`), and given `M` the counts are multinomial with
   equal cells. For `K` independent Poisson(`d/b`) variables the total is
   Poisson(`dK/b`), and given the total the counts are the same
   multinomial. So the distance equals the distance between the totals,
   which is at most `K/b` by the Barbour-Hall bound
   `d_TV(Bin(n, p), Poi(np)) <= p`.
3. The same conditioning argument compares Poisson(`d/b`) counts with
   Poisson(1) counts: the distance is
   `d_TV(Poi(Kd/b), Poi(K)) <= 1 - e^(-Kj/b) <= Kj/b`.

**Lemma 1.4** (localization, proved). Let `b >= b_0(j)`, `d = b - j` and
`M = floor(sqrt b)`. Let `H` be the event that `N_(b-y) <= M` for
`y = 1, ..., j+2`. On `H`,

    F(n) has exactly d digits   if and only if   A_j holds.

Moreover `P(not H) <= (j+2) / M!`.

Proof. All terms of `F` are nonnegative. Fix `y` in `{j, j+1}` with
`y >= 1` and suppose `y_0 = y` and `N_(b-y) = k`. Write `F = k w(b-y) + R`,
where `R` collects the digits below `b - y`. On `H`, the digit `b - y - 1`
contributes at most `M w(b-y-1) <= M b^(b-y) / b` by Lemma 1.2, the other
at most `b` digits contribute at most `b w(b-y-2) + b <= 2 b^(b-y) / b`.
So

    k e^(-y)  <=  F / b^(b-y)  <=  k e^(-y) e^eps + M/b + 2/b,   eps = y^2 / (2 (b-y)).

If `k > e^y`, then `F > b^(b-y)`. If `k < e^y`, then
`k e^(-y) <= 1 - gamma_j`, and `b >= b_0(j)` gives `eps <= gamma_j / 4`,
`M / b <= gamma_j / 8` and `2/b <= gamma_j / 32`, so
`F / b^(b-y) <= (1 - gamma_j)(1 + 2 eps) + 5 gamma_j / 32 < 1`. Also
`F >= e^(-y) b^(b-y) >= b^(b-y-1)` because `b >= e^(j+2)`. So, with
`y_0 = y`, `F` has `b - y + 1` digits if `k > e^y` and `b - y` digits if
`k < e^y`. Now go through the cases.

- `y_0 <= j - 1`: `F >= e^(-y_0) b^(b-y_0) >= b^(b-j)`, since
  `b^(j-y_0) >= b >= e^(y_0)`. So `F` has more than `d` digits.
- `y_0 = j`: by the above, `F` has `d` digits exactly when `k < e^j`.
- `y_0 = j + 1`: `F` has `d` digits exactly when `k > e^(j+1)`. (Then also
  `F <= b w(b-j-1) + b < b^d`.)
- `y_0 >= j + 2` or no value above `b - j - 2`: then
  `F <= M w(b-j-2) + b w(b-j-3) + b < b^(d-1)` on `H`, so `F` has fewer
  than `d` digits.

These cases give exactly `A_j`. For the bound on `H`, a fixed value occurs
at most once in the leading position, so
`P(N_x > M) <= P(Bin(d-1, 1/b) >= M) <= C(d-1, M) b^(-M) <= 1/M!`.

Proof of Theorem 1.1. By Lemma 1.4, `|E_(b-j) - P_b(A_j)| <= P(not H)`.
The event `A_j` depends only on the `K = j + 1` counts of Lemma 1.3. Under
`Q`, `P(y_0 = y, N_(b-y) = k) = (e^(-1))^(y-1) e^(-1) / k! = e^(-y) / k!`,
so `Q(A_j) = s_j`. Lemma 1.3 bounds `|P_b(A_j) - Q(A_j)|`.

### 1.3 The total

**Theorem 1.5** (tails, proved). For `b >= 21` and `J >= 1`,

    sum over b/2 <= d <= b - J of E_d(b)  <=  5.6 e^(-J/3),

and `sum over d < b/2 of E_d(b) <= C / sqrt(b)` with an absolute constant
`C`.

Proof. Let `d = b - j` with `J <= j <= b/2`. On the event that `F` has `d`
digits, every digit `x >= 1` has `x^x < b^d`. The proof of Lemma 13.10
shows that then `x < b - theta j` with `theta = ln b / (1 + ln b)`, which is
at least 0.75 for `b >= 21`. So each of the `d - 1 >= 0.45 b` non-leading
digits avoids at least `theta j - 1` values, and

    E_(b-j) <= (1 - (theta j - 1)/b)^(d-1) <= exp(-0.45 (0.75 j - 1)).

Summing over `j >= J` gives at most `e^0.45 e^(-0.3375 J) / (1 - e^(-0.3375))
<= 5.6 e^(-J/3)`. For `d < b/2`: if a digit `x >= sqrt(b)` occurs, then
`(x/2) ln b <= x ln x < d ln b`, so `x < 2d`. Hence every digit is below
`X_d = max(2d, sqrt b)` and `E_d <= (X_d / (b-1))^d`. The sum over
`d <= b/4` is at most `2/sqrt(b)` plus `O(1/b)`. For `b/4 < d < b/2`,
every digit `x >= b/4` satisfies `x < d ln b / (ln b - ln 4)`, which is
below `0.6 b` for large `b`, and these terms are exponentially small.

**Corollary 1.6** (proved). `sum over d = 1..b of E_d(b) -> 1`. So the
basic model expects one nontrivial-length solution per base and convention
in the limit, as section 5.2 says, and the shares of the lengths are the
`s_j`.

Proof. `F(n) < b^b` always, so only `d <= b` count. The events `A_j`,
`j >= 0`, partition the Poisson outcomes with `y_0` finite: an outcome with
`y_0 = y` and `N_(b-y) = k` lies in `A_y` if `k < e^y` and in `A_(y-1)` if
`k > e^y`. So `sum of s_j = 1`. Combine Theorem 1.1 for `j < J` with
Theorem 1.5 and let `b`, then `J`, tend to infinity.

### 1.4 The first correction

**Proposition 1.7** (proved, with the expansion sketched below; checked by
computation). For fixed `j`,

    E_(b-j)(b) = s_j + c_j / b + O_j(1/b^2),
    c_j = sum over (y, k) in A_j of (e^(-y)/k!) delta_j(y, k),
    delta_j(y, k) = (j+1)(y - k) + y k + k - k(k-1)/2 - y^2/2 - y.

In particular `c_0 = -1/(4e) = -0.0920`, and `c_1 .. c_5` are `+0.0919`,
`+0.2813`, `+0.3173`, `+0.2269`, `+0.1356`.

Sketch. For `b >= b_0(j)` the event is `A_j` up to `P(not H)`, which is
smaller than any power of `b`. The exact probability that `y_0 = y` and
`N_(b-y) = k` is

    ((b-1-y)/(b-1)) C(n, k) b^(-k) (1 - y/b)^(n-k)  +  (1/(b-1)) C(n, k-1) b^(-(k-1)) (1 - y/b)^(n-k+1),

with `n = b - j - 1`. Expanding each factor to first order in `1/b`
uniformly for `k <= sqrt b` gives `(e^(-y)/k!)(1 + delta_j(y,k)/b +
O(k^4/b^2))`, and the weights `1/k!` make the sum of the errors
`O(1/b^2)`. For `j = 0` the sums `sum k/k!`, `sum k(k-1)/k!`, `sum 1/k!`
over `k >= 3` are `e - 2`, `e - 1`, `e - 5/2`, which give `-1/(4e)`.

Table 1.1 (computed, `analysis/r5m_shares.py`, `analysis/data/r5m_shares.txt`).
`E_(b-j)` from the exact law of the top counts, and `b (E_(b-j) - s_j)`.

| `b` | `E_b` | `E_(b-1)` | `E_(b-2)` | `E_(b-3)` | `b(E-s)`, `j = 0..3` |
|---:|---:|---:|---:|---:|---|
| 30 | 0.07735 | 0.55501 | 0.24203 | 0.09693 | -0.089, +0.096, +0.285, +0.341 |
| 100 | 0.07939 | 0.55275 | 0.23536 | 0.08879 | -0.091, +0.093, +0.282, +0.324 |
| 1000 | 0.08021 | 0.55191 | 0.23282 | 0.08587 | -0.092, +0.092, +0.281, +0.318 |
| 100000 | 0.08030 | 0.55182 | 0.23254 | 0.08555 | -0.092, +0.092, +0.281, +0.317 |

A Monte Carlo of `analysis/model.py` itself (400,000 strings per length)
agrees within 1.5 standard errors at `b = 30` and `b = 100`, for example
`E_(b-1)(100) = 0.5515 +- 0.0008` against 0.5527. The section 5.6 values
for base 100 (0.55, 0.24, 0.09, 0.08) are these numbers.

So the shares are a theorem about random strings. Every later use of
"about one per base" in the basic model rests on Corollary 1.6. The
refined model adds the residue factor of section 5.3; section 3 below
deals with that.

## 2. The free residue dimension `k(B)` (question 82)

### 2.1 Setting

Let `q` be a prime power, `B` in `F_q[T]` of degree `e >= 2`, and
`M = B - 1`. Let `R = F_q[T]/(M)`, `t` the class of `T`, and
`phi(x) = x^q` the Frobenius of `R`, an `F_q`-linear ring endomorphism.
Let `W_j` be the span of `1, t, ..., t^j`. A digit sum `D_j` of degree at
most `j` reduces to an element of `W_j`, and `D_j(T^(q^j))` reduces to
`phi^j(D_j)`. So the map of section 21.1.4 has image

    J = sum over j = 1..e-1 of (phi^j - 1) W_j,

and `k(B) = e - dim J` (the term `j = 0` vanishes). Let
`I = (phi - 1) R` and let `omega` be the number of distinct monic
irreducible factors of `M`. Write `M = prod P_i^(a_i)` with `f_i = deg P_i`
and `R = prod R_i`, `R_i = F_q[T]/(P_i^(a_i))`.

**Lemma 2.1** (proved).

1. `ker(phi^j - 1)` on `R_i` has dimension `gcd(j, f_i)`. In particular
   `dim ker(phi - 1) = omega` and `I` has codimension `omega` (Berlekamp).
2. `Im(phi^j - 1)` on `R_i` contains the nilradical `N_i` and equals the
   preimage of `ker(Tr : F_(q^f_i) -> F_(q^gcd(j, f_i)))`.
3. If `S` is a set of positive integers with `gcd(S, f_i) = 1`, then the
   sum over `j` in `S` of `Im(phi^j - 1)` on `R_i` is `I_i`, the image of
   `phi - 1` on `R_i`.
4. `J` is contained in `I`, so `k(B) >= omega` (Theorem 21.6).

Proof. (1) A solution of `x^(q^j) = x` in the local ring `R_i` reduces to
a root of `X^(q^j) - X` in the residue field `F_(q^f_i)`; these roots form
`F_(q^gcd(j, f_i))`, and each lifts uniquely because the derivative of
`X^(q^j) - X` is `-1` (Hensel). (2) `phi` maps `N_i` into itself and is
nilpotent there (`x^(q^r) = 0` once `q^r >= a_i`), so `phi^j - 1` is
invertible on `N_i`. Hence `N_i` lies in the image, and the image is the
preimage of its reduction, which is the image of `phi^j - 1` on the field.
On a finite field `L` over `K = F_(q^g)`, `g = gcd(j, f)`, that image is
the kernel of the trace `L -> K` (Hilbert 90, additive form, by
dimension). (3) Under the trace form of `L` over `F_q` the annihilator of
`ker Tr_(L/K)` is `K`. So the annihilator of a sum of such kernels is the
intersection of the fields `F_(q^gcd(j, f))`, which is `F_q` when
`gcd(S, f) = 1`; then the sum is `ker Tr_(L/F_q) = I` on the field, and
(2) lifts this to `R_i`. (4)
`phi^j - 1 = (phi - 1)(1 + phi + ... + phi^(j-1))`.

### 2.2 A good factor decides

Call an irreducible factor `P` of `B - 1` good if `gcd(deg P, e - 1) = 1`,
and bad otherwise.

**Theorem 2.3** (proved). If `B - 1` has a good factor, then
`k(B) = omega(B - 1)`.

Proof. The term `j = e - 1` has `W_(e-1) = R`, so
`J >= (phi^(e-1) - 1) R`, which is the direct sum over `i` of the images on
`R_i`. On a good `R_i` this image is `I_i` (Lemma 2.1 (3) with
`S = {e-1}`). So `J` contains `I_good + 0`. Let `E` be the total degree of
the bad part `R_bad`, the product of the bad `R_i`. There is a good
factor, so `E <= e - 1`. For `j >= E - 1` the projection of `W_j` onto
`R_bad = F_q[T]/(M_bad)` is onto, since polynomials of degree below `E`
represent every class. So the projection of `J` onto `R_bad` contains
`sum over j = max(E-1, 1)..e-1 of (phi^j - 1) R_bad`. This range holds two
consecutive integers, because `E - 1 <= e - 2`, so by Lemma 2.1 (3) the
sum is `I_bad`. Since `J <= I = I_good + I_bad` and `J >= I_good + 0`,
`J` is `I_good` plus its projection to `R_bad`, which is `I_bad`. So
`J = I`.

**Corollary 2.4** (proved). If `e - 1` is a prime power `r^s`, then
`k(B) = omega(B - 1)` for every `B` of degree `e`. This covers
`e = 2, ..., 6, 8, 9, 10, 12, 14, 17, 18, 20, ...`.

Proof. If every factor is bad, `r` divides every `f_i`, hence
`e = sum a_i f_i`. But `r` divides `e - 1`.

The first degrees where all factors can be bad are `e = 7`
(types `3 + 4`, `2 + 2 + 3`, `2^2 + 3`), `e = 11`, `13`, `15`, `16`.

### 2.3 At most one extra dimension

Let `ell : R -> F_q` be the coefficient of `t^(e-1)` (in the basis
`1, ..., t^(e-1)`). The pairing `(x, y) -> ell(x y)` is nondegenerate, and
the functionals vanishing on `W_j` are the `ell(h .)` with
`deg h <= e - 2 - j`. In particular `W_(e-2)` is the kernel of `ell`.

**Theorem 2.5** (proved).

1. `k(B) <= omega(B - 1) + 1`.
2. `k(B) = omega(B - 1) + 1` holds if and only if
   (a) `Lambda_(e-2) = 0`, where `Lambda_j = sum over i = 0..j of ell o phi^i`;
   (b) `Lambda_j` vanishes on `W_j` for `1 <= j <= e - 3`;
   (c) `ell` vanishes on the fixed ring `R^phi`.
3. If `B - 1` is not squarefree, `k(B) = omega(B - 1)`.
4. Let `B - 1` be squarefree and `e >= 5`. If `k(B) = omega + 1`, then
   `D = M'^(1-q) mod M` has degree at most 1 and is not constant. If
   moreover `q <= e - 2`, this is impossible, so `k(B) = omega`.

Proof. Work with the dual. A functional `lambda` vanishes on `J` exactly
when `lambda o phi^j = lambda` on `W_j` for `j = 1..e-1`. Put
`delta_j = lambda o phi^j - lambda`. Then `delta_j` vanishes on `W_j`,
`delta_(e-1) = 0` because `W_(e-1) = R`, and
`delta_(a+b) = delta_b + delta_a o phi^b`.

(1) `delta_(e-2)` vanishes on `W_(e-2)`, so `delta_(e-2) = c ell` for some
`c` in `F_q`. From `0 = delta_(e-1) = delta_1 + delta_(e-2) o phi` we get
`delta_1 = -c ell o phi`. The map `lambda -> delta_1` sends the annihilator
of `J` into the line spanned by `ell o phi`, and its kernel is the set of
`phi`-invariant functionals, the annihilator of `I`, of dimension `omega`.

(2) If `c != 0`, then `delta_j = sum over i < j of delta_1 o phi^i =
-c (Lambda_j - ell)`. For `j = e - 2` this equals `c ell`, which is (a).
For `j <= e - 3`, `delta_j` vanishes on `W_j` and so does `ell`, which is
(b). And `delta_1 = -c ell o phi` must lie in the image of
`lambda -> lambda o phi - lambda`, which is the annihilator of
`ker(phi - 1) = R^phi`; since `ell(phi(x)) = ell(x)` on `R^phi`, this is
(c). Conversely, given (a) to (c), choose `lambda` with
`lambda o phi - lambda = ell o phi` (possible by (c)). Then
`delta_j = Lambda_j - ell`, which vanishes on `W_j` for `j <= e - 3` by (b),
equals `-ell` for `j = e - 2` by (a), and is 0 for `j = e - 1`, because
`Lambda_(e-1) = ell + Lambda_(e-2) o phi = ell`. And `lambda` is not
invariant, since `ell o phi != 0` (from (a), `ell o phi^(e-1) = ell`).

(3) From (a), `Lambda_(e-2) o phi - Lambda_(e-2) = ell o phi^(e-1) - ell =
0`. If `R` has a nonzero nilradical `N`, then `phi^(e-1)` kills `N`
(nilpotency index at most `e <= q^(e-1)`), so `ell` vanishes on the ideal
`N`, and nondegeneracy gives `N = 0`, a contradiction.

(4) For squarefree `M`, `ell(x) = sum over roots beta of x(beta) / M'(beta)`
(Euler). Write `ell o phi^i = ell(c_i .)` with `c_i` in `R`; then
`c_(e-1) = 1` by `ell o phi^(e-1) = ell`. Use (a) to rewrite (b):
`sum over i <= j of c_i = - sum over m = 1..e-2-j of c_(e-1-m)`. With
`u_m = c_(e-1-m)` the roots give `u_m = M'^(1 - q^m)`, so
`u_1 = D` and `u_(m+1) = u_1 phi(u_m)`, and (b) says that
`P_k = u_1 + ... + u_k` has degree at most `k` for `1 <= k <= e - 3`.
`k = 1`: `deg D <= 1`. If `D` is a constant `alpha`, then `u_m = alpha^m`;
reduction modulo each factor gives `u_(f_i) = 1`, so `alpha^(f_i) = 1`,
hence `alpha^e = 1`, and (a) with `phi^(e-1)`-invariance gives
`alpha^(e-1) = 1`, so `alpha = 1`. Then (a) reads `e - 1 = 0` in `F_q`, and
(c) reads `f_i = 0` in `F_q` for every orbit, so `p` divides both `e - 1`
and `e`, which is impossible. If `D = alpha + beta t` with `beta != 0`,
then `P_2 = D + D phi(D)` contains `beta^2 t^(q+1)`. When `q + 1 <= e - 1`
the polynomial is already reduced, of degree `q + 1 >= 3`, against
`deg P_2 <= 2` (needs `e >= 5`).

**Remark 2.6** (proved). Conditions (a) and (c) also give, for every orbit
of size `f` with `r = (e - 1) mod f`, the relation
`sum over m < r of u_m(beta) = 0`. So `r = 1` is impossible, and `r = 2`
forces `D == -1` modulo that factor, hence `D = -1`, which the constant
case excludes. This kills the types `2 + 2 + 3` and `3 + 4` of `e = 7` for
every `q` by hand: for `3 + 4`, the quartic has `r = 6 mod 4 = 2`; for
`2 + 2 + 3`, the quadratics have `r = 0` and (c) gives `1 + D(beta) = 0`
on them, so `D = -1`.

More generally, a squarefree type with a factor of degree 2, or with a
factor of degree `f` and `(e - 1) mod f` in `{1, 2}`, never has an extra
dimension. With Corollary 2.4 and Theorem 2.5 (3), (4), this settles every
`e <= 10`.

### 2.4 Computations

All computations use `analysis/r5m_kB.py` (all bases of a degree) and
`analysis/r5m_kB_types.py` (only the types with every factor bad).
`omega` is computed as the corank of `phi - 1` (Lemma 2.1 (1)), and checked
against PARI/GP `factormod` for the types.

- Census (computed, `analysis/r4f_census_q*e*m0.txt`, 1,111 orbits of all
  14 cases up to `(17, 3)`, `(5, 4)`, `(3, 5)`, `(2, 7)`): the stored `k`
  equals the recomputed `k` and `omega` in every orbit.
- All monic `B` (computed, `analysis/data/r5m_kB_scan.txt`): `q = 2`,
  `e = 3..13`; `q = 3`, `e = 3..8`; `q = 5`, `e = 3..6`; `q = 7`,
  `e = 3..5`; `q = 11`, `e = 4`; `q = 13`, `e = 3, 4`. 110,654
  polynomials, `k = omega` in each. Scaling `B` changes neither number.
- All-bad types (computed, `analysis/data/r5m_kB_types.txt`): `q = 2`,
  `e = 11, 13, 15, 16, 19, 21, 22`; `q = 3`, `e = 11, 13`; `q = 5`,
  `e = 7`; and `q = 7`, `e = 7` in full. 379,700 polynomials (some types
  of the first runs capped at 20,000), `k = omega` in each. For `q = 7`,
  `e = 7`, 42 of the 65,856 squarefree polynomials of type `3 + 4` have
  `deg D <= 1`; Remark 2.6 excludes them by hand.
- Open types, random samples (computed, `analysis/r5m_kB_sample.py`,
  `analysis/data/r5m_kB_sample.txt`): `e = 11`, type `5 + 6`, 20,000
  polynomials each for `q = 11` and `q = 13`; `e = 13`, `q = 13`, types
  `4 + 9` and `3 + 4 + 6`, 5,000 each. `k = omega` in all, and `deg D` is
  never below 6. These samples cannot reach the rare `M` with
  `deg D <= 1`, which is where an exception would have to be.

The `(2, 7)` census has 8 polynomials of the all-bad types (6 of type
`3 + 4`, 2 of type `2^2 + 3`); Remark 2.6 and Theorem 2.5 (3) cover them.
So every base of every census has `k(B) = omega(B - 1)` by proof, not only
by computation.

### 2.5 Verdict

`k(B) = omega(B - 1)` is proved for every `B` with a good factor, for every
non-squarefree `B - 1`, for squarefree `B - 1` with `q <= e - 2`, and for
`e <= 10`. The computations find no exception anywhere.

**Conjecture 2.7.** `k(B) = omega(B - 1)` for every `B`.

The open cases need a squarefree `M` all of whose factors are bad, no
factor of degree 2, no factor with `(e - 1) mod deg P` in `{1, 2}`,
`q >= e - 1`, and `M'^(q-1) (alpha + beta T) == 1 (mod M)`, plus the
conditions of Theorem 2.5 (2). The first such type is `5 + 6` in degree
`e = 11`, with `q >= 11`.

Section 24.4.5 shows that `kappa(B)` can exceed `k(B)`. That is a
different map (`phi^(e-1) - 1` alone), and nothing above contradicts it.

## 3. Assumption R (question 80)

### 3.1 What Lemma 13.10 needs

Let `m = b - 1` and `g(x) = x^x - x` for `x >= 1`, `g(0) = 0`. The refined
model of section 13.2.1 uses the residue `sum c_x g(x) (mod m)`: the
string `Y_u + c_1` is congruent to `V(u) + c_1`, and the ones cancel, so
`0^0` plays no role. Let `H_0` be the set of `h` modulo `m` with
`h g(x) == 0` for every digit `x`. Since every `g(x)` is even and
`g(2) = 2`, `H_0 = {0, m/2}` for even `m` and `{0}` for odd `m`.

**Lemma 3.1** (proved; a correction to section 13.2.3). Assumption R as
stated, "for every `d`", is false. Example: `b = 10`, `d = 2`. A string of
one digit whose `V` has 2 digits must be the digit 3 (`3^3 = 27`), so the
share of the residue `g(3) = 24 == 6 (mod 9)` is 1, not at most
`kappa / 9` for any `kappa < 9`. For fixed `d` and large `b` the same
happens: the allowed digits number about `d ln b / ln(d ln b)`.

Lemma 13.10 uses Assumption R only for `d >= ell >= b/2`. The statement
should be restricted to these `d`. The theorem below needs even less.

### 3.2 Removing the conditioning

For `L <= b` let `psi_L(h) = (1/L) sum over x < L of e(h g(x) / m)`, and

    rho(b) = max over ceil(b/2) <= L <= b and h not in H_0 of |psi_L(h)|.

**Theorem 3.2** (proved). Let `b >= 12` and `ell = ceil(b/2)`. In the
refined coupled model, Lemma 13.10 and Corollary 13.11 hold with

    kappa(b) = |H_0| + (b - 1) rho(b)^(ell - 2).

Proof. Lemma 13.10 bounds the refined `E[T]` by the sum over `d >= ell` of
`(1/b) (b - 1) P(G_d and S == r_d)`, where `S` is the residue of the top
`d - 1` digits of a uniform `d`-digit string. Its proof shows that on
`G_d`, `d = b - j`, every digit is below `b - theta j`. Let `A_j` be this
event. It is a product event: given `A_j`, the leading digit is uniform on
`{1, ..., L - 1}` and the other `d - 2` digits are independent and uniform
on `{0, ..., L - 1}`, with `L = L_j` in `[ell, b]`. So

    P(G_d and S == r) <= P(A_j) P(S == r | A_j)
                     <= P(A_j) (1/m) sum over h of |E e(hS/m) | A_j|
                     <= P(A_j) (1/m) ( |H_0| + m rho(b)^(d-2) ),

because the leading digit contributes a factor of modulus at most 1, each
other digit a factor `psi_L(h)`, and `h` in `H_0` gives modulus 1. Now
`d - 2 >= ell - 2`, and the sum of `P(A_j)` over `j` is the quantity that
Lemma 13.10 bounds by 7.1.

So the conditioning on the length is harmless: one can replace `G_d` by
a product event that contains it. Assumption R reduces to one number per
base, `rho(b)`, and it suffices that `1 - rho(b) >= 3 ln b / b`.

### 3.3 Computations

Table 3.1 (computed, `analysis/r5m_rho.c`, all `b` from 4 to 6000, every
`L` in `[ceil(b/2), b]` and every `h` modulo `b - 1`;
`analysis/data/r5m_rho_b6000.txt`, `r5m_rho_report.txt`).

| bases | max `rho(b)` | where | `kappa(b) - |H_0|` at most |
|---|---:|---|---:|
| 12 to 19 | 0.8197 | `b = 13, 16`, `L = 8`, `h = m/3` | 4.6 |
| 20 to 49 | 0.7954 | `b = 22`, `L = 14`, `h = 7` | 2.7 |
| 50 to 99 | 0.7807 | `b = 52` | 0.134 |
| 100 to 999 | 0.7725 | `b = 100`, `L = 50`, `h = 33` | 0.00041 |
| 1000 to 6000 | 0.7646 | `b = 1000`, `h = 333` | `10^-55` |

**Corollary 3.3** (proved, computer-assisted). For every `b` with
`12 <= b <= 6000`, the refined case of Corollary 13.11 holds without
Assumption R, with `kappa <= |H_0| + 5`, and with
`kappa <= |H_0| + 0.0005` for `100 <= b <= 6000`. So `kappa` is 1 in even
bases and 2 in odd bases up to `5 * 10^-4`, the factor of section 5.3.

For `100 <= b <= 6000` the worst `h` is `m/3` or `m/6` in every one of
the 1,967 bases with `3 | b - 1`, and `rho(b) <= 0.537` in the other 3,934
bases (maximum at `b = 113`). The cause is Lemma 15.12 (3): modulo 3,
`g(x)` is 2 for `x == 2 (mod 6)` and 0 otherwise.

**Proposition 3.4** (proved). If `3 | b - 1` and `h = m/3`, then
`psi_L(h) -> 5/6 + (1/6) e(2/3)` as `L -> infinity`. Its modulus is
`sqrt(7/12) = 0.7638` and `1 - Re psi = 1/4`.

Proof. A share `1/6 + O(1/L)` of the `x < L` has `x == 2 (mod 6)`.

So the computed `rho(b)` approaches 0.7638 from above, and the
conjecture below has a reason in the 3-adic law, not only in data.

The quantity of the question. Table 3.2 (computed,
`analysis/r5m_cosmin.py`, `analysis/data/r5m_cosmin_b20000.txt`,
`r5m_cos_report.txt`): for every `b <= 20,000` and every odd prime power
`q | b - 1` (45,534 pairs), the Poisson rate
`c_pois = min over h != 0 (mod q) of (1/b) sum over x < b of (1 - cos(2 pi h g(x)/q))`
and the fixed-length rate `c_mult = min of 1 - |phi(h)|`, by one FFT of
the histogram of `g(x) mod q`.

| `q` | pairs (`b >= 10`) | min `c_pois` | where | min `c_mult` |
|---|---:|---:|---|---:|
| all, `b >= 3` | 45,534 | 0.2143 | `b = 7`, `q = 3` | 0.2046 |
| `3^k` | 9,994 | 0.2308 | `b = 13`, `q = 3` | 0.2193 |
| `5^k` | 4,994 | 0.4762 | `b = 21`, `q = 5` | 0.4684 |
| `7^k` | 3,331 | 0.4270 | `b = 29`, `q = 7` | 0.4259 |
| `p >= 11` | 27,211 | 0.4477 | `b = 27`, `q = 13` | 0.4452 |
| primes `p >= 101` | 14,082 | 0.7574 | `b = 104`, `p = 103` | 0.7177 |

The lead of question 80 (minimum 0.23) holds from `b = 10` on; bases 7
(0.2143) and 4 are below it. For primes `p >= 101` the worst cases are
`b - 1 = p` (the 8 worst all are), and the minimum grows with `p`: 0.757
for 3-digit `p`, 0.907 for 4-digit, 0.967 for 5-digit. For
`b - 1 = p` prime with `1000 <= p <= 20,000` (2,094 primes),
`max over h of |sum over x < b of e(h g(x)/p)|` lies between 0.84 and
1.40 times `sqrt(p ln p)`, mean 1.00. This is the size of the maximum of
`p` random sums of `p` unit vectors.

**Conjecture 3.5.** `rho(b) <= 0.77` for every `b >= 100`. More
precisely, for `b - 1 = p` prime, `max over h != 0 of
|sum over x <= p of e(h (x^x - x)/p)| = O(sqrt(p log p))`.

Either statement, or even `1 - rho(b) >= 3 ln b / b`, makes Corollary
13.11 unconditional with `kappa = |H_0| + o(1)`.

### 3.4 What is proved for large bases

**Proposition 3.6** (proved). Let `p` be an odd prime dividing `b - 1`, let
`3p <= L <= b`, and `h` not divisible by `p`. Then

    | (1/L) sum over x < L of e(h g(x) / p) |  <=  3 (1 + tau(p-1)) / sqrt(p)  +  p^(3/2) (1 + ln p) / L,

where `tau` counts divisors. So for primes `p <= b^(2/3 - eps)` the
residue of `g` modulo `p` is close to uniform, and a sum of `b/2` digits
is uniform modulo `p` up to `exp(-c b)`.

Proof. Write `x = u + k p` with `0 <= u < p`. Since `p == 1 (mod p - 1)`,
`x == u + k (mod p - 1)`, so `x^x == u^(u+k) (mod p)` for `u != 0`, and
`g(x) == 0` for `u = 0`. Hence the sum is
`K_0 + sum over u != 0 of e(-hu/p) sum over k < K_u of e(a_u u^k / p)`
with `a_u = h u^u` prime to `p` and `K_u <= K = ceil(L/p)`. Let `t` be the
order of `u`. Two classical facts:

- For a subgroup `G` of `F_p^*` and a character `chi` of `G`,
  `|sum over y in G of chi(y) e(a y / p)| <= sqrt p` (expand the indicator
  of `G` in multiplicative characters; each Gauss sum has modulus
  `sqrt p`).
- Completion: `|sum over k < N of e(a u^k / p)| <= sqrt(p) (1 + ln t)` for
  `N <= t`, from the first fact and
  `sum over c mod t of |sum over k < N of e(ck/t)| <= t (1 + ln t)`.

So the inner sum is at most `min(K, sqrt(p) (K/t + 1 + ln p))`. Group the
`u` by their order: `phi(t)` of them have order `t`. The orders `t <= p^(1/4)`
contribute at most `K sqrt p`, the others at most
`sqrt(p) K tau(p-1) + p^(3/2) (1 + ln p)`. Divide by `L >= (K - 1) p`
and use `(K + 1)/(K - 1) <= 2` for `K >= 3`.

This does not cover the joint residue modulo all of `b - 1`, and it says
nothing for a prime `p > b^(2/3)`, which is the case of question 80. At
most one prime factor of `b - 1` exceeds `b^(2/3)`.

### 3.5 The literature

I searched for nontrivial bounds on `sum over x <= p - 1 of e(a x^x / p)`.

- Balog, Broughan and Shparlinski (Acta Arith. 148, 2011) bound the number
  `J(p; lambda)` of `x <= p - 1` with `x^x == lambda (mod p)` by
  `p^(12/13 + o(1))`, uniformly in `lambda` (as quoted in arXiv
  2608.01781; I did not see the paper itself), and
  `J(p; 1) < p^(1/3+o(1))` (as quoted by Cilleruelo and Garaev).
- Cilleruelo and Garaev (Proc. AMS 144, 2016, arXiv 1503.02730) improve
  `J(p; 1)` to `p^(27/82 + o(1))` and bound the number of collisions
  `x^x == y^y` with `x, y <= p - 1` by `p^(23/12 + o(1))`, using
  Shkredov's and Shteinikov's bounds for sums over subgroups.
- The collision bound is a mean square: summed over `a`,
  `|sum e(a x^x/p)|^2` totals `p I(p) <= p^(35/12 + o(1))`. So at most
  `p^(11/12 + 2 delta + o(1))` values of `a` can have a sum above
  `p^(1 - delta)`. It does not exclude a single bad `a`, which is what
  `rho(b)` needs.

I found no pointwise `o(p)` bound for the complete sum, for `x^x` or for
`x^x - x`. The needed statement is weaker than `o(p)`: the sum must stay
below `p - 3 ln p` (in the normalization of Theorem 3.2), uniformly in `a`
and for every initial segment of length at least `p/2`. I found no result
of that kind either.

## 4. A model that keeps the Frobenius blocks (question 83)

### 4.1 The model

By Corollary 24.3, `F(x)` is assembled from `e` digits:
`p_(e-1) = D_(e-1)`, `p_j = sigma(p_(j+1)) + D_j`, `p_0 = sigma(p_1) + D_0`
(under `0^0 = 0`). The digits of `F(x)` are `p_0` at position 0 and the
digits of `Phi^j(p_j)` at the positions `[q^(j-1), q^j)`. So the class sums
of `F(x)` are `class(p_0) + sum over j >= 1 of K_j(p_j)`, with one table
`K_j` per base. The map `x -> (p_0, ..., p_(e-1))` is a bijection.

Block model. Keep the block maps `K_j` and replace each `p_j` by a uniform
digit of the same degree (zero stays zero). Let `delta(x)` be the tuple of
degrees of the `p_j`. The model solution count is

    E_block = sum over x of P( class sums of F(p~) = x ),   p~ uniform with delta(p~) = delta(x),

and the bijection turns it into a sum over the true values:

    E_block = sum over x' of [ delta(X(x')) = delta(x'), F(x') has >= 2 digits ] / #{x : delta(x) = delta(x')},

where `X(x')` is the vector of class sums of `F(x')`.

Refined block model. As in section 5.3, also keep `F mod (B - 1)` exact:
`p~` is uniform among the tuples of the same degrees whose `F` has the same
residue modulo `B - 1`. Then

    E_ref = sum over x' of [ delta(X) = delta(x'), r(X) = r(x'), F(x') has >= 2 digits ] / C(delta(x'), r(x')),

with `r(x) = F(x) mod (B - 1)` and `C` the number of `x` with that degree
tuple and residue. A model solution then satisfies the identity of
Proposition 21.5, as a true solution does.

`analysis/r5m_block.py` computes both for every base orbit, from the tables
`K_j`, in 1 second for `(5, 3)`, 11 seconds for `(7, 3)` and 24 seconds per
orbit for `(5, 4)`. It also counts the exact solutions from the same tables:
they match the census in all 25, 63 and 160 orbits.

The basic block model gives 1.3 to 1.5 solutions per base on average (0 to
3.75 by type), like the basic model, because it ignores the identity. The refined block model is the one
to compare. Its mass is not the census in disguise: the exact solutions
themselves contribute 1% to 2% of it (`block_res_self` in the data files).

### 4.2 Results

Table 4.1 (computed, `0^0 = 0`, per base; `analysis/data/r5m_block_q*.txt`,
`analysis/r5m_block_report.py`). Type of `B - 1`: degrees and
multiplicities of its irreducible factors.

`(q, e) = (5, 3)`:

| type | bases | census | refined | block | census/refined | census/block |
|---|---:|---:|---:|---:|---:|---:|
| root, quadratic | 200 | 36.00 | 27.94 | 35.83 | 1.29 | 1.00 |
| irreducible cubic | 160 | 7.50 | 3.91 | 6.67 | 1.92 | 1.12 |
| double root, root | 80 | 40.00 | 23.46 | 29.68 | 1.70 | 1.35 |
| three roots | 40 | 140.00 | 123.87 | 127.50 | 1.13 | 1.10 |
| triple root | 20 | 0 | 3.46 | 5.00 | 0 | 0 |
| all | 500 | 34.40 | 26.23 | 31.62 | 1.31 | 1.09 |

`(q, e) = (7, 3)`:

| type | bases | census | refined | block | census/refined | census/block |
|---|---:|---:|---:|---:|---:|---:|
| root, quadratic | 882 | 78.00 | 52.17 | 71.10 | 1.49 | 1.10 |
| irreducible cubic | 672 | 7.88 | 5.86 | 6.26 | 1.34 | 1.26 |
| double root, root | 252 | 35.00 | 47.56 | 42.30 | 0.74 | 0.83 |
| three roots | 210 | 352.80 | 339.05 | 350.84 | 1.04 | 1.01 |
| triple root | 42 | 0 | 5.56 | 0 | 0 | - |
| all | 2058 | 76.29 | 64.81 | 73.49 | 1.18 | 1.04 |

`(q, e) = (5, 4)`:

| type | bases | census | refined | block | census/refined | census/block |
|---|---:|---:|---:|---:|---:|---:|
| root, cubic | 800 | 41.50 | 24.89 | 40.91 | 1.67 | 1.01 |
| irreducible quartic | 600 | 10.00 | 4.93 | 8.83 | 2.03 | 1.13 |
| two roots, quadratic | 400 | 164.50 | 125.71 | 156.28 | 1.31 | 1.05 |
| double root, quadratic | 200 | 24.00 | 25.10 | 26.11 | 0.96 | 0.92 |
| two quadratics | 180 | 45.56 | 25.71 | 47.74 | 1.77 | 0.95 |
| two roots, double root | 120 | 133.33 | 124.77 | 137.58 | 1.07 | 0.97 |
| root, triple root | 80 | 30.00 | 24.81 | 25.70 | 1.21 | 1.17 |
| square of a quadratic | 40 | 0 | 4.93 | 5.96 | 0 | 0 |
| two double roots | 40 | 60.00 | 24.81 | 28.75 | 2.42 | 2.09 |
| four roots | 20 | 620.00 | 624.84 | 620.00 | 0.99 | 1.00 |
| fourth power of a root | 20 | 0 | 4.81 | 0 | 0 | - |
| all | 2500 | 60.48 | 45.41 | 58.68 | 1.33 | 1.03 |

Per orbit, in units of the families of `q(q-1)` solutions (Lemma 24.8),
the Pearson statistic `sum (c - E)^2 / E`:

| `(q, e)` | orbits | refined | refined block |
|---|---:|---:|---:|
| (5, 3) | 25 | 26.5 | 6.6 (23 orbits with `E > 0`) |
| (7, 3) | 63 | 48.5 | 13.8 (43) |
| (5, 4) | 160 | 749.1 | 186.9 (155) |

### 4.3 Verdict

Heuristic 4.1. Keeping the forced structure exactly and randomizing the
rest is enough in `F_q[T]` for most of the gap. The refined block model
cuts the total error from 18% to 33% down to 3% to 9%, and the per-orbit
misfit by a factor of 4. It needs no `kappa(B)`: the larger kernel of
Proposition 24.13 is built in, because the generic cell keeps its
degrees. The irreducible quartic of `(5, 4)` (ratio 2.0 against the
refined model, unexplained in Heuristic 24.14) comes out at 1.13. The
types with `kappa > k` (root and quadratic, root and cubic) go from 1.29 to
1.67 down to 1.00 to 1.10.

What the block model still misses are the types with a repeated factor:
"two double roots" of `(5, 4)` at 2.09, "double root, root" at 1.35 for
`(5, 3)` and 0.83 for `(7, 3)`, and two types without solutions (the
triple root of `(5, 3)` and the square of a quadratic of `(5, 4)`), where
it predicts 5 and 6. For
`(5, 4)` the Pearson value 187 on 155 orbits is about 1.8 standard
deviations above a Poisson fit, so the block model is close to a complete
description. The repeated factors are where the remaining structure sits:
for them `R` has a nilradical, and the identity behaves differently on it
(compare Theorem 2.5 (3)).

So in a world where the forcing is strong, "keep the forced digits,
randomize the rest" works when the forcing is kept in full: all `e`
generating digits and their degrees, not only the top digit. This is the
`F_q[T]` counterpart of the forced-top-digit correction of section 23.5,
and it supports using the same recipe for the factorial system (section 5).

## 5. Open lengths in the factorial system (question 84)

### 5.1 A model with the top digits kept

The question asks to fix the top digits of `F` from the large counts, as
the search of `r3t_factorial.rs` does. A first attempt did exactly that:
`analysis/r5m_fact_open.py` ports the first levels of the search tree to
exact integers and runs it to a fixed depth. It does not separate lengths.
At depth 3 to 10 almost every length keeps surviving nodes, and their
number grows with `L` like the census node counts. For example, at depth
5 the tree keeps 382 nodes for `L = 26`, which has near-solutions, and 656
for `L = 25`, which has none. Consistency of the top digits with a few
large counts is too weak a test, because the counts of zero for the
largest values always survive. So I built the model
the other way: keep the true top digits of `F` and randomize the rest.

Window `W = [L!, (L+1)!)`; a member has digits `d_i <= i` at positions
`i = 1..L` and `d_L >= 1`. The plain model of section 21.5.3 is
`E_L = P(F(n) in W)` for `n` uniform in `W`. For a multiset `c` with
`F(c)` in `W`, let `T` be the top `K` factorial digits of `F(c)`, and treat
only the digits at positions `1..L-K` as uniform. Then

    P(digits of F(c) form c) = 1(T in c) A(c - T, L - K) / prod over i <= L-K of (i + 1),

where `A(c, N)` counts the placements of a multiset of `N` digits into
positions `1..N` with the value `u` only at positions `>= u`. The board is
a Ferrers board, so `A` is a product of binomials: place the values from
the largest down, each into the free positions at or above it.

**Lemma 5.1** (proved). Summed over `c`, the top-`K` model gives

    E_L(K) = E_n [ 1(F(n) in W) P(top K digits of a random arrangement of c(n) = T) / P_W(top K digits = T) ],

with `n` uniform in `W`. `E_L(0)` is the plain model and `E_L(L)` is the
exact number of solutions in `W`.

Proof. The plain model is the sum over `c` with `F(c)` in `W` of
`#arr(c) / |W|`, where `#arr(c)` counts the members of `W` with multiset
`c`; so a sum over `c` equals `E_n[ g(c(n)) |W| / #arr(c(n)) ]`. The ratio
`A(c - T, L - K) / #arr(c)` is the chance that a random arrangement of `c`
has top digits `T`, and `|W| / prod over i <= L - K of (i + 1)` is
`1 / P_W(top K = T)`. For `K = L` the indicator says that the digits of
`F(c)` are `c`.

The adaptive version keeps the positions where the largest digit `v` of `n`
can sit, `K = L - v + 1`. This is the forcing of section 21.5.3: these
positions hold all copies of `v`, and the large counts fix their digits.
`analysis/r5m_fact_model.py` estimates `E_L(K)` for `K <= 8` and the
adaptive `EA_L` by sampling `n`, with exact integers for `F`:
`3 * 10^6` strings per length under `0^0 = 0`, `10^6` under `0^0 = 1`,
`L = 3..100`.

### 5.2 Open lengths

Call `L` open when `EA_L > 0.01` (computed, `analysis/data/r5m_fact_model_m*.txt`,
`analysis/r5m_fact_report.py`, `analysis/data/r5m_fact_report.txt`).

- `L <= 33`, both conventions: 8, 10, 13, 14, 15, 18, 19, 20, 24, 26, 28,
  29, 30, 32. Fourteen of 31 lengths.
- `34 <= L <= 100`: 34 (only under `0^0 = 0`, 0.012), 35, 40, 43, 47, 48,
  55, 56, 58, 59, 64, 67, 75, 77 under `0^0 = 0`; 35, 40, 43, 47, 48, 56,
  58, 75, 77, 78, 81 under `0^0 = 1`.
- No sampled string gives a nonzero term for 45 (`0^0 = 0`) and 52
  (`0^0 = 1`) of the 98 lengths. The closed lengths include all the
  lengths where the plain model is already 10 times smaller
  (7, 12, 17, 22, 27, 33, 39, 45, ...).

Table 5.1 (computed). Near-solutions at the offsets `D = 1000 j`,
`j = 1..100` (section 21.5.3, `analysis/data/r3t_factorial_near1000.txt`),
against 100 times the model. The offsets are below `9!`, so they leave the
top digits of `F + D` unchanged except near a carry; the table uses the
model at `D = 0`.

| `L` | near, `0^0 = 0` (offsets hit) | near, `0^0 = 1` | 100 `E_L` plain | 100 `EA_L` |
|---:|---:|---:|---:|---:|
| 10 | 30 (10) | 26 (12) | 22.1 | 14.1 |
| 11 | 0 | 0 | 18.9 | 0 |
| 12 | 0 | 0 | 3.1 | 0 |
| 13 | 10 (3) | 16 (6) | 19.3 | 80.1 |
| 14 | 0 | 0 | 18.7 | 16.4 |
| 15 | 38 (12) | 52 (19) | 17.9 | 15.7 |
| 16 | 0 | 0 | 15.6 | 0 |
| 17 | 0 | 0 | 2.3 | 0 |
| 18 | 0 | 0 | 15.8 | 6.6 |
| 19 | 0 | 0 | 15.5 | 7.6 |
| 20 | 2 (1) | 8 (3) | 15.0 | 15.4 |
| 21 to 23, 25 | 0 | 0 | 41.8 | 0 |
| 24 | 0 | 0 | 13.3 | 9.7 |
| 26 | 138 (30) | 161 (51) | 11.5 | 65.1 |
| total | 218 | 263 | 230.7 | 230.8 |

The model closes 8 of the 17 lengths, and all 8 are empty, where the plain
model expects 81 near-solutions. Every length with near-solutions is open.
Four open lengths (14, 18, 19, 24) are empty, against 40 expected; the
near-solutions come in clusters (section 21.5.3 and the round 5 evidence
draft, Lemma 1.3), so a few empty open lengths are ordinary. The totals
agree within 6%.

Heuristic 5.2. The top-digit model explains where the coincidences of the
factorial system can happen: a length is open when the true top digits of
`F`, over the positions where the largest digit must sit, can be digits of
the multiset. This is the "all or nothing" of section 21.5.3 in numbers.
About half of the lengths are open, not "5 of 17".

### 5.3 Calibration and prediction

Expected solutions (the model mean; computed, with sampling errors):

| range | plain `E0` | `EA`, `0^0 = 0` | `EA`, `0^0 = 1` |
|---|---:|---:|---:|
| `3 <= L <= 33` | 4.6 / 4.8 | 3.85 +- 0.05 | 3.90 +- 0.08 |
| `34 <= L <= 40` | 0.59 | 0.29 +- 0.07 | 0.28 +- 0.11 |
| `34 <= L <= 100` | 3.4 | 2.5 +- 0.7 | 2.4 +- 0.9 |

The means hardly move: the model shifts mass between lengths, it does not
remove it. Under a Poisson law the census (no solution with
`3 <= L <= 33`) has probability `e^(-3.85) = 0.021`, against 0.010 for the
plain model.

The clusters change this. The near-solutions show how often an offset
carries at least one hit: 56 of the 1,700 offset-length pairs under
`0^0 = 0` and 91 under `0^0 = 1`, against model means of 231 and 233. So
the chance that an offset carries a coincidence is 0.24 to 0.39 times the
model mean, the rest being repeats of the same multiset. Calibrated this
way (heuristic), the chance of no solution for `3 <= L <= 33` is
`exp(-0.24 * 3.85) = 0.39` and `exp(-0.39 * 3.90) = 0.22`. The census is
then an ordinary outcome.

Predictions (heuristic). For `34 <= L <= 40` the model expects 0.29 and
0.28 solutions, so at least one with probability about 0.07 to 0.10 after
calibration; the open lengths there are 35 and 40. For `34 <= L <= 100`,
2.5 and 2.4 expected, at least one with probability 0.45 to 0.6. Beyond
`L = 50` the estimates rest on fewer than 100 nonzero terms per length, so
they are uncertain by a factor of 2. Like the plain model, the top-digit
model expects finitely many solutions, but it says nothing on finiteness
that a proof could use.

The census extension to `L = 40` was not run. The model predicts no
solution there (0.3 expected), and the extension needs wider integers in
`r3t_factorial.rs` (`u128` stops at `L = 33`) and, extrapolating the node
counts of `L = 28..33` (growth about 1.6 per length), a few `10^8` tree
nodes per length near `L = 40`.

## Library corrections

- Section 13.2.3, Assumption R: "for every `d`" is false (Lemma 3.1,
  `b = 10`, `d = 2`). Lemma 13.10 needs it only for `d >= ell >= b/2`, and
  Theorem 3.2 replaces it by the number `rho(b)`.
- Section 13.2.6, "The limits of the means ... A proof would turn that
  computation into a theorem": done (Theorem 1.1, Corollary 1.6).
- Section 5.2 describes the length `b - j`, `j >= 2`, as "no digit above
  `b - j` and at least one copy of `b - j`". The exact condition also needs
  fewer than `e^j` copies, plus the case of more than `e^(j+1)` copies of
  `b - j - 1` (section 1.1). The table is right to its printed precision.
- Question 80's lead "the minimum is at least 0.23" holds for `b >= 10`;
  base 7 has 0.2143 (Table 3.2).
- Section 21.1.4: "`k(B) = omega(B - 1)` for every one of the 4,426 bases
  of the census (computed)" can now cite Theorem 2.3, Corollary 2.4 and
  Theorem 2.5 (3): every census base is covered by proof.

## Files

- Question 81: `analysis/r5m_shares.py`; data
  `analysis/data/r5m_shares.txt`.
- Question 82: `analysis/r5m_kB.py`, `analysis/r5m_kB_types.py`,
  `analysis/r5m_kB_sample.py`; data `analysis/data/r5m_kB_sample.txt`,
  `analysis/data/r5m_kB_scan.txt`, `r5m_kB_types.txt`.
- Question 80: `analysis/r5m_rho.c` (build:
  `gcc -O2 -fopenmp -o r5m_rho r5m_rho.c -lm`), `analysis/r5m_rho_report.py`,
  `analysis/r5m_cosmin.py`, `analysis/r5m_cos_report.py`; data
  `analysis/data/r5m_rho_b6000.txt`, `r5m_rho_report.txt`,
  `r5m_cosmin_b20000.txt`, `r5m_cos_report.txt`.
- Question 83: `analysis/r5m_block.py`, `analysis/r5m_block_report.py`;
  data `analysis/data/r5m_block_q5e3.txt`, `r5m_block_q7e3.txt`,
  `r5m_block_q5e4.txt`.
- Question 84: `analysis/r5m_fact_model.py`, `analysis/r5m_fact_report.py`,
  and the depth-limited search `analysis/r5m_fact_open.py` (the approach of
  section 5.1 that does not separate lengths); data
  `analysis/data/r5m_fact_model_m0.txt`, `r5m_fact_model_m1.txt`,
  `r5m_fact_report.txt`.

The draft is not yet in `lean/` or `docs/exposition/`. Theorem 1.1,
Theorem 2.3, Corollary 2.4 and Theorem 2.5 (1), (3) are the natural
candidates for formalization.

## New questions

1. The case left by Theorem 2.5: squarefree `B - 1` whose factors all
   share a divisor with `e - 1`, no factor of degree 2, `q >= e - 1`.
   Does condition (b) of Theorem 2.5 (2) for `k = 2, 3` already force a
   contradiction, as the degree count does for `q <= e - 2`? The first
   test is `e = 11`, factors of degrees 5 and 6, `q = 11, 13`.
2. Conjecture 3.5: is `max over h != 0 of |sum over x <= p of
   e(h (x^x - x)/p)| = O(sqrt(p log p))`? A weaker target that suffices for
   Corollary 13.11: the sum is below `p - 3 ln p` for every `h` and every
   initial segment of length at least `p/2`. Can the method of
   Cilleruelo and Garaev (sums over subgroups along `x = u + kp`) give it
   for `p` close to `b`?
3. The joint residue. Proposition 3.6 handles one prime at a time. Is
   there a proof of `rho(b) < 1 - c` for composite `b - 1` all of whose
   prime factors are below `b^(1/2)`, where every digit range covers full
   periods of `x mod p(p-1)`?
4. The refined model's first-order term. Proposition 1.7 gives the basic
   model as `s_j + c_j / b`. What is the analog with the residue factor of
   section 5.3, and does `sum over j of c_j` (1.1046 numerically) have a
   closed form?
5. The block model of section 4 misses the types with repeated roots
   (ratio 2.09 for two double roots in `(5, 4)`) and predicts 5 solutions
   for the triple root and the square of a quadratic, which have none. Is
   there an exact obstruction on the nilradical, like Theorem 2.5 (3)?
6. Factorial system: why is `L = 13` open with the largest model mean
   (0.80) but only 3 to 6 offsets with near-solutions? A finer model would
   keep the top digits over the positions of the two largest values.
7. Factorial system: the top-digit model needs a variance reduction
   beyond `L = 50`, where fewer than 100 strings per length carry the
   whole estimate. Importance sampling on the largest digit and its count
   is the obvious route.
