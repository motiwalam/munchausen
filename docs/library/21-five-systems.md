# 21. Five more number systems

This chapter answers the twist questions 59 to 63 of `questions-round3.md`.

Each statement carries one mark:

- proven: a proof is in this chapter;
- cited: a published result, with its source;
- computed: an exact search, with its range;
- heuristic: the model of chapter 5, adapted to the number system.

In the tables, "model" or `E` always means the refined model of section 5.3
for that number system, computed with the exact weights. "Basic" means the
model without the digit-sum identity. "Near" is the mean number of
near-solutions `n = F(n) + D` per offset `D`, for offsets in the residue
class of 0 that the identity allows (section 11.1). Near-solutions are
further draws of the same coincidence, so they measure the true rate
without the model.

The sections are in the order of payoff: first the world with exact
structure (61), then the three sharp tests of the parity law (60, 63, 59),
then the world where the model fails (62).

## Summary

| question | world | answer | basis |
|---|---|---|---|
| 61 | `F_q[T]`, base `B` of degree `e`, `w(d) = d^(q^deg d)` | `F` depends only on the sums `D_j` of the digits of each degree, so the problem is finite and linear. Solutions come in families of `q`. For `e = 2` there are exactly `q(q-1)` solutions if `B - 1` has two roots in `F_q`, else none. For `e >= 3` the count depends on `B` through `k(B)`, the number of irreducible factors of `B - 1`: a free residue factor `q^k(B)` replaces the parity factor 2. | proven; computed for 4,426 bases |
| 60 | rational bases `p/q` (AFS) | `q N == digit sum (mod p - q)`. When `p, q` are odd, the identity is free mod 2 under `0^0 = 0`, and near-solutions double: 2.2 per base and offset in 9 odd/odd bases against 1.1 in 20 others, as the model predicts. Solutions: 14 in the odd/odd bases against 19.8 expected (P = 0.11). | proven; computed for all bases with `p <= 10`, and `11/2` to `11/7`, `11/9` |
| 63 | Eisenstein bases `-n + omega` | The identity modulus `n^2 + 3n + 3` is odd, and nothing doubles: near-solutions per offset 1.03 and 1.27 under `0^0 = 0` against 1.07 and 1.13 under `0^0 = 1`. The Gaussian control `-2+i` doubles (2.57 against 1.07). | proven; computed for `n` = 1, 2, 3 (`n = 3` to 25 digits, 90% of the model) |
| 59 | Pisot base `(x + sqrt(x^2+4))/2` | Expansions have at most `2 log N + 2` digits. `N == digit sum (mod x)`. Even `x` double under `0^0 = 0`: 31 solutions against 9 for odd `x` (x = 2 to 12), near-solutions 2.65 against 1.43 per offset. Twins exist; the model fits. | proven; computed for `x` = 1 to 12 |
| 62 | factorial number system | No residue identity exists. The only solutions up to `34!` are 1, 4, 5 (`0^0 = 0`) and 1, 2, 5 (`0^0 = 1`), all built from two self-paying digits. The plain model expects 4.5 more per convention by `34!` and fails. The reason: a digit `v` can only sit at a position `>= v`, so large digits sit in the top positions, which the large counts fix. Coincidences come in rare clusters. Finiteness stays open. | proven (structure); computed (census); heuristic (model failure) |

## The common frame

Every world below has a digit set, a unique representation, and a weight
`w(d) = d^d` (or its analog) with `w(0) = m`, the convention `0^0 = m`. A
solution has at least 2 digits unless the text says otherwise.

The model is the one of section 5.1, with the windows of the world. Split
the integers into windows `W` (for example all integers with `L` digits).
Assume that `F(c)` is a random integer of its window. Then the expected
number of solutions is

    E = sum over windows W of  P( F(N) in W ),   N uniform in W.

The refined model adds the digit-sum identity modulo `M`: a string can only
be a solution when `sum (w(d) - d) == 0 (mod M)`, and then it is `M` times
as likely. The parity doubling of section 5.3 appears when `M` is even and
`w(d) == d (mod 2)` for every digit, so the identity holds for free modulo 2
under `0^0 = 0`.

## 21.1 A function-field analogue

### 21.1.1 Definitions

Let `q` be prime (the proofs work for prime powers; the programs use primes)
and `B in F_q[T]` of degree `e >= 2`, with any nonzero leading coefficient.
The digits are the `q^e` polynomials of degree below `e`. Every polynomial
`n` has exactly one expansion `n = sum d_i B^i` (proven: repeated division
with remainder). The weight of a digit is `w(d) = d^|d|` with
`|d| = q^(deg d)`, and `w(0) = m`. A nonzero constant `c` has `|c| = 1`, so
`w(c) = c`. The `q - 1` constants are the one-digit solutions, and no other
digit is one, since `deg w(d) = j q^j > j` for `deg d = j >= 1`.

### 21.1.2 Linearity

Proposition 21.1 (proven). For `deg d = j`, `w(d) = d(T^(q^j))`. Hence

    F(n) = sum_{j=0..e-1} D_j(T^(q^j)) + m z,

where `D_j` is the sum of the digits of degree exactly `j` and `z` is the
number of zero digits.

Proof. In characteristic `p` the map `x -> x^q` is additive, and it fixes
the coefficients, which lie in `F_q`. So `d^(q^j) = d(T^(q^j))`, and this is
linear in `d`.

Corollary 21.2 (proven). `n` is a solution exactly when its class sums
`(D_0, ..., D_(e-1), z mod p)` are a fixed point of

    (D, z) -> class sums of  sum_j D_j(T^(q^j)) + m z.

So there are at most `q^(e(e+1)/2)` solutions (times `q` if `m = 1`). They
have degree at most `(e-1) q^(e-1)`, so at most `(e-1) q^(e-1)/e + 1`
digits. In this world the length bound has no factor "number of digits",
because the degree of a sum is at most the largest degree.

The base-`B` expansion is `F_q`-linear, because the digits form a vector
space and no carries occur (proven). So the digits of `F(D, z)` are a
linear function of `(D, z)`, and only the split of the digits into degree
classes is nonlinear. This is the form of the question: for a fixed pattern
of digit degrees, the solutions form an affine space minus the strings where
a digit drops in degree. `fast/src/bin/r3t_ffield.rs` enumerates the group
of class sums and updates the digit vector linearly. A second mode
enumerates all digit multisets with weights computed by real powering. The
two modes give the same solutions and the same model sums for every base
with `(q, e)` = (2, 2..4), (3, 2..3), (5, 2), both conventions (computed).

### 21.1.3 Families and self-paying digits

Proposition 21.3 (translates, proven). Under `0^0 = 0`, if `n` is a
solution, then so is `n + c` for every constant `c`. So solutions come in
families of exactly `q`, which differ only in the last digit.

Proof. `w(d + c) = w(d) + c` for every digit `d`: if `deg d = j >= 1` then
`deg(d + c) = j` and `(d + c)^(q^j) = d^(q^j) + c`; if `d` is a constant or
0, both sides are `d + c` (with `w(0) = 0`). Adding `c` to `n` changes only
the last digit, from `d_0` to `d_0 + c`, so `F` grows by `c` as well.

This replaces the twins of Proposition 2.1: every constant weighs itself, so
the last digit can take all `q` constant shifts. The census confirms it:
every family found has exactly `q` members (computed, all bases below).

Proposition 21.4 (self-paying digits, proven). A digit `d` of degree
`j >= 1` pays for itself at position `k` when `w(d) = d B^k`, that is
`d^(q^j - 1) = B^k`. In base `T^e` and for `d = c T^j` this happens exactly
when `e` divides `j (q^j - 1)`, at `k = j (q^j - 1)/e`. Under `0^0 = 0` such
a digit can be placed at any zero position of a solution, as in
Proposition 2.3. Example: `q = 2`, base `T^3`, the digit `T^2` at position
2, since `(T^2)^4 = T^8 = T^2 (T^3)^2`.

The census finds such digits in 2 of 8 bases for `(q, e) = (2, 3)`, in 18 of
162 for `(3, 4)`, and in 20 of 500 for `(5, 3)`
(`analysis/r3t_ffield_structure.py`).

### 21.1.4 The identity and the free residues

Proposition 21.5 (proven). Every `n` satisfies `n == sum d_i (mod B - 1)`.
So a solution satisfies

    sum_j ( D_j(T^(q^j)) - D_j ) + m z == 0   (mod B - 1).

The residues modulo the divisors of `B - 1` are the only ones that the digit
multiset fixes, for numbers with at least 3 digits: swapping the last two
digits `x, y` with `x - y = 1` changes `n` by `B - 1` (proven, as in
Proposition 14.4; here every digit can sit at every position).

Theorem 21.6 (free residues, proven). Let `P` be an irreducible factor of
`B - 1`, and let `Tr` be the trace from `F_q[T]/(P)` to `F_q`. Then for all
class sums `D`,

    Tr( sum_j (D_j(T^(q^j)) - D_j)  mod P ) = 0.

So under `0^0 = 0` the identity holds for free on a subspace of codimension
at least `omega(B - 1)`, the number of distinct irreducible factors.

Proof. Let `theta` be a root of `P` and `sigma` the Frobenius of
`F_q(theta)`. Then `D_j(theta^(q^j)) = sigma^j(D_j(theta))`, because `D_j`
has coefficients in `F_q`, and `Tr(sigma^j y) = Tr(y)`. The factors give
independent conditions by the Chinese remainder theorem.

For a linear factor `T - a` the statement reads `D(a^(q^j)) = D(a)`: every
weight agrees with its digit at `a`, like `x^x == x (mod 2)`. In the
integers this happens only at the prime 2. Here it happens at every prime of
`B - 1`.

Write `k(B)` for the codimension of the image of the map
`D -> sum_j (D_j(T^(q^j)) - D_j) mod (B - 1)`. Then `k(B) >= omega(B - 1)`
(proven), and `k(B) = omega(B - 1)` for every one of the 4,426 bases of the
census (computed, `analysis/r3t_ffield_summary.py`). The refined model then
predicts about `q^k(B)` times the basic count (heuristic).

Under `0^0 = 1` the trace of the constant `z` is `z deg P`. So a factor of
`B - 1` with degree prime to `p` forces `z == 0 (mod p)`: the analog of the
even number of zeros in odd bases (proven).

### 21.1.5 Degree 2: the exact count

Theorem 21.7 (proven). Let `e = 2` and `0^0 = 0`. Base `B` has exactly
`q (q - 1)` nontrivial solutions if `B - 1` has two distinct roots in
`F_q`, and none otherwise. They are the numbers `c + beta T^q` with
`beta != 0`, in `q - 1` families of `q`.

Proof. Write `D_1 = alpha + beta T` and `c = D_0 + alpha`. Then
`F = c + beta T^q`. If `beta = 0`, `F` is a constant, with one digit. So
`beta != 0`, and the identity (Proposition 21.5) gives
`(B - 1) | beta (T^q - T)`. Since `T^q - T` is the product of all `T - a`,
`B - 1` must have two distinct roots in `F_q`.

Conversely, let `T^q - T = (B - 1) Q` and write `Q = sum q_i B^i` in base
`B`. Then `(B - 1) Q = sum_i (q_(i-1) - q_i) B^i`, with digits of degree at
most 1, and

    F = (c + beta (T - q_0)) + sum_{i >= 1} beta (q_(i-1) - q_i) B^i

is the base-`B` expansion of `F`. Its digit sum is `c + beta T`
(telescoping). The digits of degree 1 carry all the `T`-coefficients, so
their sum has `T`-coefficient `beta`, as `D_1` requires. Hence `F` is a
solution exactly when the constant coefficient of the sum of its degree-1
digits equals `alpha`; then `D_0` matches as well. Let `gamma` be the
constant coefficient of the sum of the degree-1 digits at positions
`i >= 1`; these digits do not depend on `c`. If the last digit
`c + beta (T - q_0)` is a constant, the condition reads `gamma = alpha`: it
fixes `alpha` and leaves `D_0` free. If the last digit has degree 1, the
condition reads `gamma + c - beta q_0(0) = alpha`, that is
`D_0 = beta q_0(0) - gamma`: it fixes `D_0` and leaves `alpha` free. Either
way each `beta` gives exactly `q` values of `c`, and distinct `(beta, c)`
give distinct `F`. `F` has degree `q >= 2`, so it has at least 2 digits.

The census agrees in all 3,654 bases of degree 2 with `q` = 2, 3, 5, 7, 11,
13 (computed). The refined model gives the same numbers, 0 or `q(q-1)`,
because for `e = 2` the identity decides everything. Under `0^0 = 1` the
count is `q (q - 2)` on average over the bases with two roots for `q` = 5, 7,
11, 13, 5 for `q = 3`, 2 for `q = 2`, and 0 otherwise (computed). Correction:
this is an average, not a per-base count. Each such base has 0 or `q(q-1)`
solutions under `0^0 = 1`, and the square bases `lambda (T - c)^2` have none
(Corollary 24.12).

### 21.1.6 The census for `e >= 3`

All bases of degree `e` (any nonzero leading coefficient), both conventions
(`analysis/data/r3t_ffield_frob.txt`). The model sums are exact, not
sampled. Families are counted under `0^0 = 0` (solutions divided by `q`).

| `q` | `e` | bases | `0^0 = 0`: solutions | families | basic | refined | `0^0 = 1`: solutions | refined |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 3 | 8 | 12 | 6 | 5.1 | 14.3 | 8 | 11.7 |
| 2 | 4 | 16 | 38 | 19 | 14.8 | 51.1 | 30 | 42.7 |
| 2 | 5 | 32 | 120 | 60 | 33.1 | 130.3 | 68 | 101.9 |
| 3 | 3 | 54 | 444 | 148 | 51.3 | 349.9 | 222 | 295.7 |
| 3 | 4 | 162 | 2340 | 780 | 161.0 | 1597.0 | 612 | 1300.0 |
| 5 | 3 | 500 | 17200 | 3440 | 495.5 | 13115.1 | 5920 | 11669.0 |

The basic model gives about one solution per base, between 0.64 and 1.04
for every `(q, e)`, and the same for every base of a given `(q, e)`. The
free residues then multiply it. Split by `k(B)`, under `0^0 = 0`, per base:

| `q` | `e` | `k(B)` | bases | observed | refined | basic times `q^k` |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 5 | 1 | 8 | 3.00 | 1.92 | 2.07 |
| 2 | 5 | 2 | 20 | 3.00 | 4.07 | 4.14 |
| 2 | 5 | 3 | 4 | 9.00 | 8.40 | 8.29 |
| 3 | 4 | 1 | 48 | 4.88 | 2.81 | 2.98 |
| 3 | 4 | 2 | 90 | 13.20 | 9.11 | 8.95 |
| 3 | 4 | 3 | 24 | 38.25 | 26.76 | 26.84 |
| 5 | 3 | 1 | 180 | 6.67 | 3.86 | 4.96 |
| 5 | 3 | 2 | 280 | 37.14 | 26.66 | 24.78 |
| 5 | 3 | 3 | 40 | 140.00 | 123.87 | 123.88 |

So the count depends on `B`, not only on `e`, and mostly through `k(B)`:
each factor of `B - 1` multiplies the count by about `q` (computed and
heuristic). The refined model tracks this factor over a range of 30.

The model is not exact, though. For the odd `q` of the table below, `(3, 3)`,
`(3, 4)` and `(5, 3)`, it is 1.25 to 1.47 times too low under `0^0 = 0` and
1.4 to 2.1 times too high under `0^0 = 1`. Chapter 24 extends the census to
`q = 17`. There the ratio under `0^0 = 0` is 1.03 to 1.47 and moves toward 1
for large `q`, and the ratio under `0^0 = 1` falls to 0.025 (Statement
24.3.1). Near-solutions `n = F(n) + (B - 1) g`, with `g` running over the
nonzero polynomials of small degree, settle whether this is chance
(`analysis/data/r3t_ffield_near.txt`, at least 3 digits):

| `q` | `e` | offsets `g` | `0^0 = 0`: solutions | near, summed over bases | refined | `0^0 = 1`: solutions | near | refined |
|---:|---:|---|---:|---:|---:|---:|---:|---:|
| 2 | 4 | deg < 4 (15) | 38 | 47.6 | 50.6 | 30 | 36.1 | 42.2 |
| 2 | 5 | deg < 4 (15) | 116 | 133.1 | 126.5 | 64 | 68.5 | 98.5 |
| 3 | 3 | deg < 2 (8) | 432 | 364.5 | 346.2 | 210 | 231.0 | 292.0 |
| 3 | 4 | deg < 2 (8) | 2340 | 2097.0 | 1597.0 | 612 | 541.5 | 1300.0 |
| 5 | 3 | constants (4) | 17200 | 17200.0 | 12960.2 | 5920 | 5680.0 | 11520.6 |

The solutions match their near-solutions within 15% in every row, and the
near-solutions share the deviation from the model. So the solutions are
ordinary draws, as in section 11.1, and the model misses a factor near 1.3
under `0^0 = 0` and near 0.5 under `0^0 = 1` for these odd `q` (computed).
Chapter 24 traces the gap to the digits of `F`, which are not independent. One
candidate is the length law: 63% of the solutions with `(q, e) = (3, 4)` have
the maximal 21 digits, so the top degree class is almost always present, and
the model's law for the number of zeros is then off.

Correction (chapters 24 and 26). The conclusion that "the solutions are
ordinary draws" is withdrawn. The offsets `(B - 1) g` in the table above
map most solutions to near-solutions one to one (Lemmas 24.9 and 24.10).
So these near-solutions were mostly the solutions again, not independent
draws: for `q = 5`, `e = 3` the near count 17,200 equals the solution count.
Offsets that perturb 5 low digits bring the near count down to the model
(section 24.4.3). The table of section 26.4 lists the claim as withdrawn.
The model gap itself stands. Chapter 24 traces it to the additive `F`.

### 21.1.7 Contrast: the weight `d^(deg d)`

With `w(d) = d^(deg d)` the weights are no longer linear (nonzero constants
weigh 1). The degree of `F` is at most `(e-1)^2`, so solutions are short:
at most 3 digits for `e = 4`. A multiset search over all bases
(`analysis/data/r3t_ffield_deg.txt`) gives:

| `q` | `e` | bases | `0^0 = 0`: solutions | basic | refined | `0^0 = 1`: solutions | refined |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 16 | 20 | 14.5 | 33.4 | 16 | 30.4 |
| 2 | 5 | 32 | 40 | 29.8 | 93.2 | 36 | 86.3 |
| 3 | 3 | 54 | 72 | 48.5 | 74.8 | 72 | 73.4 |
| 3 | 4 | 162 | 660 | 148.1 | 656.6 | 612 | 644.3 |
| 5 | 3 | 500 | 800 | 448.4 | 554.8 | 800 | 548.4 |

There are no families of `q`: `w(d + c) != w(d) + c`. Free residues
remain in part, because `x^k = x` holds in `F_2` for all `k >= 1` and in
`F_3` for odd `k`, so some degree classes still satisfy the identity at the
roots of `B - 1`. Without Frobenius the world looks like a short-solution
regime of the integers.

### 21.1.8 What this world shows

- The "one per base" law survives exactly: the basic model gives 0.6 to 1.0
  per base, independent of `B` (computed, exact sums).
- The parity factor generalizes to a factor `q` per prime of `B - 1`
  (Theorem 21.6), and the counts follow it (computed).
- Twins become families of `q`, and self-paying digits exist (proven).
- With additive weights the problem is finite and its solutions are the
  fixed points of an explicit map on a group of size `q^(e(e+1)/2)`. In
  degree 2 the count is a formula (Theorem 21.7). The coincidence model
  still describes `e >= 3` within a factor 2.

## 21.2 Parity in rational bases

### 21.2.1 Definitions and the identity

Base `p/q` with `gcd(p, q) = 1` and `1 <= q < p`. Every `N >= 1` has exactly
one expansion `N = sum (a_i / q) (p/q)^i` with digits `0 <= a_i < p`, from
`q N_i = p N_(i+1) + a_i`, `N_0 = N` (cited: Akiyama, Frougny and
Sakarovitch, Israel J. Math. 168 (2008)). The base `p/1` is the integer base
`p`. Section 16.5 found the first solutions with `alg_afs.c`.

Proposition 21.8 (identity, proven). Every `N` satisfies
`q N == sum a_i (mod p - q)`. A solution satisfies
`sum (q w(a) - a) == 0 (mod p - q)`.

Proof. Modulo `p - q`, `p == q`, so `q N_i == q N_(i+1) + a_i`. Summing
over `i` gives `q N_0 == q N_L + sum a_i`, and `N_L = 0`. Since
`gcd(q, p - q) = 1`, `N = F` turns into the second form.

If `p` and `q` are odd, `p - q` is even and `q w(a) - a == w(a) - a == 0`
(mod 2) under `0^0 = 0`. So the identity is free modulo 2 and the model
doubles (heuristic). Under `0^0 = 1` each zero adds `q`, which is odd, so a
solution has an even number of zeros (proven). If `p` or `q` is even,
`p - q` is odd and no factor 2 arises. Proposition 16.16 (no twins for
`q > 1`) still holds.

### 21.2.2 The search

The expansion of `N` is that of its parent `(q N - a_0)/p` followed by `a_0`.
So the integers form a tree, and a walk from the root carries
`F(N) = F(parent) + w(a_0)` at constant cost per node.
`fast/src/bin/r3t_afs.rs` walks it with one pruning rule.

Proposition 21.9 (pruning, proven). Let `r = p/q` and `W = (p-1)^(p-1)`.
The descendants of `N` at depth `t` lie in `[N r^t, (N+1) r^t)`, and their
sums are at most `F(N) + t W`. So the subtree holds no solution when
`g(t) = N r^t - F(N) - t W > 0` for every `t >= 1`. The function `g` is
convex, so it suffices to check it at `t = 1` and at the integers next to
its minimum.

Proof. A child of `M` is `(p M + a)/q >= M r`, and `< (M + 1) r`. Each step
adds one digit weight, at most `W`.

The tree has about `2 W / ln r` nodes, so the cost grows like `(p-1)^(p-1)`
and is worst for `q` near `p`. Base `11/7` takes `6.5 * 10^10` nodes;
`11/8` and `11/10` (about `10^11` and `2.5 * 10^11`) were not run. The engine
reproduces every solution of `analysis/data/alg_afs_8.txt` (computed).

### 21.2.3 The model

Lengths are nondecreasing in `N` (the parent map is monotone, proven), so
the windows are the integers of each length. `r3t_afs model` samples
400,000 integers per window (`analysis/data/r3t_afs_model.txt`).

### 21.2.4 The census against the model

All bases with `p <= 11` except `11/1`, `11/8` and `11/10`, both
conventions (`analysis/data/r3t_afs_search.txt`). "near" is the mean count
of `N = F(N) + j (p - q)` over `j = 1..30`.

| base | `p - q` | `p, q` odd | `0^0 = 0` | `E_0` | near | `0^0 = 1` | `E_1` | near |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| 3/2 | 1 | | 1 | 1.19 | 1.10 | 2 | 1.72 | 1.20 |
| 4/3 | 1 | | 1 | 1.26 | 1.27 | 0 | 1.27 | 1.23 |
| 5/2 | 3 | | 0 | 1.18 | 1.20 | 2 | 1.09 | 0.97 |
| 5/3 | 2 | yes | 1 | 2.37 | 3.17 | 1 | 1.07 | 1.33 |
| 5/4 | 1 | | 0 | 1.17 | 0.87 | 0 | 1.17 | 1.10 |
| 6/5 | 1 | | 1 | 1.12 | 1.70 | 2 | 1.12 | 1.70 |
| 7/2 | 5 | | 0 | 1.11 | 1.57 | 1 | 1.20 | 1.37 |
| 7/3 | 4 | yes | 3 | 2.25 | 2.63 | 1 | 1.16 | 1.17 |
| 7/4 | 3 | | 0 | 1.11 | 0.83 | 1 | 1.21 | 1.37 |
| 7/5 | 2 | yes | 2 | 2.25 | 2.53 | 2 | 1.12 | 1.20 |
| 7/6 | 1 | | 0 | 1.09 | 1.13 | 2 | 1.09 | 1.03 |
| 8/3 | 5 | | 1 | 1.32 | 0.93 | 0 | 1.24 | 1.23 |
| 8/5 | 3 | | 1 | 1.08 | 0.83 | 2 | 1.08 | 0.83 |
| 8/7 | 1 | | 1 | 1.08 | 1.03 | 1 | 1.08 | 1.37 |
| 9/2 | 7 | | 1 | 1.66 | 0.90 | 1 | 1.70 | 0.97 |
| 9/4 | 5 | | 0 | 1.11 | 1.00 | 1 | 1.10 | 1.37 |
| 9/5 | 4 | yes | 1 | 2.23 | 1.50 | 1 | 1.11 | 0.80 |
| 9/7 | 2 | yes | 0 | 2.13 | 1.53 | 1 | 1.06 | 1.00 |
| 9/8 | 1 | | 2 | 1.05 | 1.13 | 2 | 1.05 | 1.50 |
| 10/3 | 7 | | 2 | 1.32 | 1.37 | 0 | 1.33 | 1.20 |
| 10/7 | 3 | | 1 | 1.05 | 1.07 | 0 | 1.06 | 1.23 |
| 10/9 | 1 | | 3 | 1.05 | 1.20 | 1 | 1.05 | 1.13 |
| 11/2 | 9 | | 1 | 1.24 | 1.10 | 2 | 1.26 | 1.13 |
| 11/3 | 8 | yes | 4 | 2.33 | 2.33 | 1 | 1.25 | 1.17 |
| 11/4 | 7 | | 2 | 1.09 | 0.83 | 1 | 1.09 | 1.03 |
| 11/5 | 6 | yes | 3 | 2.10 | 1.83 | 2 | 1.06 | 0.87 |
| 11/6 | 5 | | 2 | 1.07 | 0.83 | 1 | 1.07 | 1.33 |
| 11/7 | 4 | yes | 0 | 2.09 | 2.30 | 1 | 1.05 | 1.23 |
| 11/9 | 2 | yes | 0 | 2.08 | 2.10 | 1 | 1.04 | 1.00 |

Totals over these bases with `q > 1` (computed; model heuristic):

| group | bases | `0^0 = 0`: solutions | refined | basic | near, summed | `0^0 = 1`: solutions | refined | near, summed |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `p, q` odd | 9 | 14 | 19.8 | 10.0 | 19.9 | 11 | 9.9 | 9.8 |
| others | 20 | 20 | 23.4 | 23.3 | 21.9 | 22 | 24.0 | 24.3 |

Answer: yes, the count doubles in the bases with `p` and `q` odd. The
near-solutions show it best: 2.2 per offset and base against 1.1, under
`0^0 = 0` only, exactly as the model predicts (19.8 against the basic 10.0).
The solutions themselves, 14 in 9 bases, fall a little short of 19.8
(`P(X <= 14) = 0.11`), while their near-solutions (19.9) do not. The lead of section 16.5 (6 against 6 for `p <= 8`)
was a small sample: with `p <= 11` the odd/odd bases have 1.6 solutions
each, the others 1.0. The integer bases `p/1` confirm the old law: odd `p`
have near-solution rates 2.2 to 3.7, even `p` 0.9 to 1.5.

Base 11/9 took `1.2 * 10^11` nodes (30 minutes on 3 threads).

The identity modulus `p - q` has nothing to do with the digit range `p`.
The doubling follows it all the same, which makes this the cleanest test of
the parity law in the library.

## 21.3 Eisenstein bases

### 21.3.1 Definitions and the identity

Let `omega^2 + omega + 1 = 0` and `beta = -n + omega`, `n >= 1`. Then `beta`
is a root of `t^2 + (2n+1) t + (n^2 + n + 1)`, and a quadratic
`t^2 + B t + C` is a canonical number system base exactly when
`-1 <= B <= C` and `C >= 2` (cited: Katai and Kovacs, Acta Sci. Math. 42
(1980); Gilbert, Canad. J. Math. 1981). Here `B = 2n + 1 <= n^2 + n + 1 = C`.
So every element of `Z[omega]` has exactly one expansion with digits 0 to
`n^2 + n`. These are the only quadratic CNS bases of `Z[omega]` up to
conjugation, since `B^2 - 4C = -3` forces `B` odd and `C = (B^2+3)/4`
(proven).

The last digit of `a + b omega` is `(a + n b) mod (n^2 + n + 1)`, because
`omega == n (mod beta)`.

Proposition 21.10 (proven). `beta - 1 = -(n+1) + omega` is primitive of norm
`M = n^2 + 3n + 3`. So a rational integer solution satisfies
`sum (w(x) - x) == 0 (mod M)`. `M = n(n+3) + 3` is odd for every `n`, so the
parity doubling never applies (heuristic consequence).

The length bound of Proposition 14.10 carries over with
`|z|^2 = a^2 - ab + b^2`: lengths at most 19, 20 and 30 for `n` = 1, 2, 3
(proven with a finite computation, in the program).

### 21.3.2 The census

`fast/src/bin/r3t_eisen.rs` is `gauss.rs` with the Eisenstein digit map, a
switch to run the Gaussian base as a control, and near-solution counts at
offsets `j M`, `j = 1..30`. It reproduces the census of `-2+i` from
section 14.5 (computed).

| base | `M` | `0^0` | lengths searched | solutions (lengths) | model, searched lengths | model, all lengths | near per offset |
|---|---:|---:|---|---|---:|---:|---:|
| -1+w | 7 | 0 | 2..19 (complete) | none | 0.79 | 0.79 | (offsets too large) |
| -1+w | 7 | 1 | 2..19 (complete) | none | 1.49 | 1.49 | (offsets too large) |
| -2+w | 13 | 0 | 2..20 (complete) | 1 (15) | 1.22 | 1.22 | 1.03 |
| -2+w | 13 | 1 | 2..20 (complete) | 1 (15) | 1.19 | 1.19 | 1.07 |
| -3+w | 21 | 0 | 2..25 of 30 | 2 (12, 25) | 0.95 | 1.07 | 1.27 |
| -3+w | 21 | 1 | 2..25 of 30 | 2 (23, 25) | 0.95 | 1.06 | 1.13 |
| -2+i (control) | 10 | 0 | 2..16 (complete) | 1 (8) | 2.22 | 2.22 | 2.57 |
| -2+i (control) | 10 | 1 | 2..16 (complete) | none | 1.05 | 1.05 | 1.07 |

The solutions (digits from the top):

- `-2+w`, `0^0 = 0`: `(1,4,5,6,6,3,0,2,1,2,6,4,3,4,6)`.
- `-2+w`, `0^0 = 1`: `(1,4,5,6,6,4,4,6,0,6,4,0,0,1,4)`.
- `-3+w`, `0^0 = 0`: `(2,6,3,1,2,2,7,0,0,4,0,3)` and the 25-digit
  `(2,5,3,10,3,2,9,7,12,2,4,3,2,1,7,11,11,9,10,1,2,0,6,12,8)`.
- `-3+w`, `0^0 = 1`: the 23-digit `(1,5,8,6,0,5,2,7,4,2,8,11,9,4,9,6,7,10,4,5,10,9,7)`
  and the 25-digit `(2,5,2,6,1,3,2,8,0,12,12,1,4,4,7,2,5,5,1,9,7,0,6,1,11)`.

For `n = 3` the lengths 27 and 28 hold 11% of the model (sampled,
`analysis/data/r3t_eisen3_mc.txt`); a search of length 27 would take about
`3 * 10^10` leaves, which I did not run. Base `-4+w` has digits up to 20 and
its model mass sits near 40 digits, out of reach for this enumeration, as
`-4+i` was in section 14.5.

Answer: no doubling. Under `0^0 = 0` the two Eisenstein bases have
near-solution rates 1.03 and 1.27 per offset, against 1.07 and 1.13 under
`0^0 = 1` and a model of 1.1 to 1.2 for both. The Gaussian control with an
even modulus doubles in the same test: 2.57 against 1.07. The solution
counts, 3 under each convention in `n = 2, 3`, match the model's 2.2 for
each convention. So the second law of section 14.6.3 holds in the sharpest form: the
factor 2 follows the parity of the identity modulus, not the shape of the
base (computed and heuristic).

### 21.3.3 Lengths of positive integers

As in section 14.5.1, positive integers skip some lengths
(`analysis/r3t_eisen_lengths.py`, all integers up to `10^6`, and 3,000
random ones per decade from `10^4` to `10^30`):

| base | `pi / (pi - arg beta)` | lengths up to 40 that never occur |
|---|---:|---|
| -1+w | 6.00 | all but 1, 4, 6, 8, 11, 13, 16, 18, 20, 23, 25, 28, 30, 32, 35, 37, 40 |
| -2+w | 9.42 | 2, 3, 5, 7, 14, 16, 18, 23, 25, 27, 32, 34, 36 |
| -3+w | 12.95 | 2, 3, 5, 7, 9, 16, 18, 20, 22, 29, 31, 33, 35 |
| -4+w | 16.52 | 2, 3, 5, 7, 9, 11, 20, 22, 24, 26, 28, 37, 39 |

The runs switch parity about every `pi / (pi - arg beta)` digits, the
heuristic of section 14.5.1. For `-1+w`, `beta^2 = -3 omega` and
`beta^12 = 729`, so the set of lengths is closed under adding 12 (proven),
which the table obeys. The model has zero mass exactly at the missing
lengths, and every solution found has an allowed length.

The first version of this table missed lengths near `10^6` to `10^7`
because it sampled only from `10^7` on, as `wld_gauss_lengths.py` does. A
denser rerun of the Gaussian table of section 14.5.1 confirms it unchanged.

## 21.4 The Pisot base `eps_x`

### 21.4.1 Definitions

Let `x >= 1` and `eps = (x + sqrt(x^2 + 4))/2`, the dominant root of
`t^2 - x t - 1`, a Pisot unit with conjugate `-1/eps`. Since
`1 = x/eps + 1/eps^2`, the expansion of 1 is `d(1) = x1`, and the greedy
(beta-) expansions are exactly the digit strings over 0 to `x` in which every
digit `x` is followed by a 0, unless it is the last digit (cited: Parry,
Acta Math. Hungar. 11 (1960), with `d*(1) = (x0)^infinity`). Every positive
integer has a finite greedy expansion (cited: Frougny and Solomyak, Ergodic
Theory Dynam. Systems 12 (1992), property (F), since `d(1) = x1` has
nonincreasing digits). The digit string of `N` runs from its top position
`k` down to position 0, or to its last nonzero digit after the point.

`fast/src/bin/r3t_pisot.rs` works exactly in `Z[eps]` with pairs
`a + b eps`. The sign of `a + b eps` follows from the sign of the conjugate
`a - b/eps` and of the norm `a^2 + x a b - b^2`.

### 21.4.2 Length and identity

Proposition 21.11 (proven). An integer `N >= 1` with `T` digits in base
`eps` has `T <= 2 log_eps N + 2`.

Proof. Let the expansion run from position `k` to `-m`. Then
`N >= eps^k`, so `k <= log_eps N`. If `m >= 1`, the algebraic integer
`A = N eps^m` has the shifted expansion `a_(k+m) ... a_0` with `a_0 >= 1`.
Its conjugate is `N (-1/eps)^m`. On the other hand the conjugate equals
`a_0 + sum_{j >= 1} a_j (-1/eps)^j`. Here `a_1 <= x - 1`, since a digit `x`
must be followed by 0 and `a_0 != 0`. So the conjugate is at least
`1 - (x-1)/eps - x (eps^-3 + eps^-5 + ...) = 1 - (x-1)/eps - 1/eps^2 = 1/eps`,
using `eps^3 - eps = x eps^2` and `1 - 1/eps^2 = x/eps`. Hence
`N eps^-m >= 1/eps`, `m <= 1 + log_eps N`, and `T = k + 1 + m` gives the
bound.

The bound is attained: `max (T - 2 log_eps N) = 2.000` for all `N <= 3 * 10^5`
and `x` = 1, 2, 3, 5, 8, 12 (computed). Only `N = 1, ..., x` have no digits
after the point (computed, same range). So a solution has `N = F <= T x^x`
and `T <= 2 log_eps(T (x^x + 1)) + 2`, which bounds `T`: 11 for `x = 2`, 24
for `x = 10`, 28 for `x = 12` (proven, with the arithmetic in the program).

Proposition 21.12 (identity, proven). `eps - 1` has norm `-x`, so
`Z[eps]/(eps - 1) = Z/x`, and `eps == eps^-1 == 1` modulo `eps - 1`. Hence
`N == sum d_i (mod x)`, and a solution has `sum (w(d) - d) == 0 (mod x)`.
For even `x` and `0^0 = 1`, a solution has an even number of zeros.

Proposition 21.13 (twins, proven). Under `0^0 = 0`, if `N` is a solution
whose digit at position 0 is 0, and the digit at position 1 is not `x`, then
`N + 1` is a solution, with the 0 replaced by 1. For `x = 1` the digit at
position -1 must also be 0. The new string is admissible, so it is the
greedy expansion of `N + 1`, and `F` grows by `w(1) - w(0) = 1`.

There are no self-paying digits: a digit at position `k != 0` adds an
irrational amount to the value.

### 21.4.3 The search and the census

`r3t_pisot search` enumerates every digit multiset of every length `T` up
to the bound, keeps those with every `x` followed by a 0
(`c_x <= c_0 + 1`), filters by Proposition 21.12, and compares the expansion
of `F` exactly. It needs `F` in `[eps^((T-2)/2), eps^T)`, which Proposition
21.11 justifies. It agrees with a direct expansion of every `N` up to the
bound for `x` = 1 to 7 (computed). The model samples integers in each window
`eps^k <= N < eps^(k+1)`.

All solutions with `x` = 1 to 12 (`analysis/data/r3t_pisot_search.txt`,
`r3t_pisot_search12.txt`; digits from the top, the point marks position -1):

| `x` | `0^0 = 0` | `0^0 = 1` |
|---:|---|---|
| 1 | 2 = `1,0.0,1` | 9, 12 |
| 2 | 3 = `1,0.1,1`, 4 = `1,1.1,1`, 5 = `2,0.0,1` | 4, 8, 11, 14 |
| 3 | none | 7 = `2,0.1,1`, 37 |
| 4 | 9, 10, 54, 55, 84, 138, 312 | 10, 138 |
| 5 | 40, 370 | 40, 370 |
| 6 | 877, 3423, 3475, 6615, 6616, 7031, 50349 | 877, 3423, 3475, 6616, 7031 |
| 7 | 3933, 106077, 917942, 917943 | 3933, 870775, 917943 |
| 8 | 96959, 96960, 917915, 923417, 1787625, 2520454, 2564464, 17697718 | none |
| 9 | 405944671 | none |
| 10 | 310, 421798810, 877154544, 1600837696, 1956350341, 1956350342 | 1956350342 |
| 11 | 10405164675, 10405164721 | 1971580245, 10405164675, 10405164721 |
| 12 | none | none |

Check of the first: `eps + eps^-2 = 2` for the golden ratio, and
`w(1) + w(1) = 2`. The pairs `(N, N+1)` under `0^0 = 0` are the twins of
Proposition 21.13: 3/4, 9/10, 54/55, 6615/6616, 917942/917943,
96959/96960, 1956350341/1956350342.

### 21.4.4 Against the model

`x = 1` is degenerate (modulus 1, weights 0 and 1). For `x >= 2`:

| `x` | `0^0 = 0` | twin pairs | `E_0` | basic | near | `0^0 = 1` | `E_1` | near |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 3 | 2 | 3.55 | 1.78 | 2.27 | 4 | 1.78 | 1.37 |
| 3 | 0 | 0 | 0.73 | 1.49 | 0.77 | 2 | 1.68 | 1.17 |
| 4 | 7 | 2 | 3.32 | 1.40 | 2.77 | 2 | 2.08 | 1.60 |
| 5 | 2 | 0 | 1.07 | 1.19 | 1.10 | 2 | 1.16 | 1.00 |
| 6 | 7 | 1 | 2.21 | 1.27 | 2.57 | 5 | 1.71 | 2.10 |
| 7 | 4 | 1 | 1.25 | 1.22 | 1.47 | 3 | 1.21 | 1.10 |
| 8 | 8 | 1 | 2.87 | 1.24 | 3.07 | 0 | 2.03 | 1.53 |
| 9 | 1 | 0 | 1.23 | 1.17 | 2.13 | 0 | 1.17 | 1.83 |
| 10 | 6 | 1 | 2.39 | 1.20 | 2.13 | 1 | 1.93 | 1.93 |
| 11 | 2 | 0 | 1.15 | 1.14 | 1.67 | 3 | 1.14 | 1.63 |
| 12 | 0 | 0 | 2.67 | 1.15 | 3.10 | 0 | 2.03 | 1.40 |

| `x` from 2 to 12 | bases | `0^0 = 0` | twin pairs | `E_0` | basic | near per base | `0^0 = 1` | `E_1` | near per base |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| even | 6 | 31 | 7 | 17.0 | 8.0 | 2.65 | 12 | 11.6 | 1.66 |
| odd | 5 | 9 | 1 | 5.4 | 6.2 | 1.43 | 10 | 6.4 | 1.35 |

"near" counts `N = F(N) + j x`, `j = 1..30` (`j = 1..10` for `x = 12`).

Answer: about one coincidence per base before the identity (basic 1.1 to
1.8), and the identity modulo `x` doubles even `x` under `0^0 = 0`, as
predicted: near-solutions 2.65 against 1.43 per offset, solutions 31
against 9. The solutions exceed the model in even bases (31 against 17.0),
but 7 twin pairs account for 7 of them, and the near-solutions (2.65) match
the model (2.8 per base). Odd `x` with `3 | x` lose part of the mass
(`E_0 = 0.73` for `x = 3`), because `d^d - d (mod 3)` is biased. Under
`0^0 = 1` the even bases gain a smaller factor, since the number of zeros
must be even (Proposition 21.12), as in section 5.3. The first non-integer
base of the library therefore follows both universal laws.

Update (chapter 26). For even `x` under `0^0 = 0` the offsets `j x` mix two
classes: even `j` carry 1.4 to 2.4 times as many near-solutions as odd `j`.
Calibrated in the class of 0 modulo `2x`, even `x` have 25 solutions against
14.8 expected (P about 0.05). See section 26.6.

## 21.5 The factorial number system

### 21.5.1 Definitions and structure

Every `n >= 1` has exactly one expansion `n = sum_{i=1..L} d_i i!` with
`0 <= d_i <= i` and `d_L >= 1`, so `L! <= n < (L+1)!` (proven: mixed-radix
division). A solution is `n = sum w(d_i)`.

Proposition 21.14 (no invariant residue, proven). No modulus `M >= 2` makes
`n mod M` a function of the digit multiset on numbers with 3 or more
digits. Proof: `(1,0,1) = 7` and `(1,1,0) = 8` have the same multiset.

So the model has no residue factor and no parity doubling. Residues that
depend on positions, like `n == d_1 (mod 2)`, do not give a factor
(heuristic: the condition holds for about half of the arrangements of a
multiset).

Proposition 21.15 (self-paying digits, proven). A digit `a` at position `i`
pays for itself when `a * i! = a^a`, that is `a^(a-1) = i!`. The only cases
are `(a, i) = (1, 1)` and `(2, 2)`.

Proof. For `i >= 3`, take a prime `p >= 3` with `i/2 < p <= i`: for
`i = 3` take `p = 3`, and for `i >= 4` Bertrand's postulate gives a prime in
that range, and every prime above `i/2 >= 2` is at least 3. It divides `i!`
exactly once. Then `p | a`, and `a^(a-1)` holds `p` at least
`a - 1 >= p - 1 >= 2` times. (An earlier version allowed `p = 2` for
`i = 3`, where the last step fails; the Lean formalization found this.) For `i <= 2`,
`i!` is 1 or 2, so `a = 1` or `a = 2`.

Under `0^0 = 0` the solutions 1 = `(1)`, 4 = `(2,0)` and 5 = `(2,1)` are the
nonempty combinations of these two digits, and 4, 5 are twins (the digit at
position 1 is 0 or 1, proven as in Proposition 2.1). Under `0^0 = 1` the
solutions are 1, 2 = `(1,0)` and 5 = `(2,1)`.

### 21.5.2 The search

`fast/src/bin/r3t_factorial.rs` fixes `L` and decides the digit counts from
the largest value down, as `fast` does. The numbers with fixed digits at
positions `>= j` form an interval of length `j!`, so the top digits shared by
both ends of the range of `F` are digits of every candidate. A digit `u` can
only sit at a position `>= u`, so the counts must satisfy
`#(digits >= u) <= L - u + 1`. A brute force over all `n < 10!` agrees on
solutions and on the near-solutions with `D = 1..5`
(`analysis/r3t_factorial_check.py`, computed).

Computed (`analysis/data/r3t_factorial_census.txt`): for `L <= 33`, that is
`n < 34!` (about `3 * 10^38`), the only solutions are the six above. The
whole census takes `1.4 * 10^8` tree nodes per convention. `u128` stops at
`L = 33`.

### 21.5.3 The model, and why it fails

`E_L = P(F(n) in [L!, (L+1)!))` for `n` uniform in the same window. Only the
largest digit `v` decides whether `F` can land there (`v^v <= F <= L v^v`),
so `analysis/r3t_factorial_model.py` computes `P(max digit = v)` exactly and
samples the rest (`analysis/data/r3t_factorial_model.txt`).

The model predicts `sum_{L=3..33} E_L = 4.5` per convention, and
`E_L` decays only slowly: 0.10 at `L = 40`, 0.03 at `L = 100`, 0.014 at
`L = 170` (heuristic). In the model the large digits must avoid the top
`L - v ~ L / ln L` positions, which costs about `exp(-L / (2 ln^2 L))`, so
the sum converges and the model predicts finitely many solutions. But it
expects about 5.7 more per convention between `34!` and `301!`
(`E_L = 0.004` at `L = 300`), and more beyond.

The census refutes the model's rate: no solution for `3 <= L <= 33` where it
expects 4.5 (`P = 0.011` per convention). Near-solutions confirm that this
is not chance. With offsets `D = 1..100` there is none for
`7 <= L <= 29` except one cluster at `L = 26` (126 near-solutions under
`0^0 = 0`, in one cluster of 35 consecutive offsets), where the model
expects about 310 spread over all lengths. With offsets `D = 1000 j`, `j = 1..100`, and
`10 <= L <= 26`, the hits sit in 5 of the 17 lengths (10, 13, 15, 20, 26)
and in clusters of 10 to 50 offsets
(`analysis/data/r3t_factorial_near1000.txt`).

The diagnosis (`analysis/r3t_factorial_diag.py`, all `n` with 7 to 9 digits
whose sum has as many digits): let `v` be the largest digit of `n`. The
model assumes that the digits of `F(n)` look like those of a random integer
in the window. They do not:

| `L` | `E_L` | largest digit of `F` equals `v`: `F` / random | digit `v` occurs as often as in `n`: `F` / random |
|---:|---:|---|---|
| 7 | 0.051 | 0.000 / 0.279 | 0.000 / 0.053 |
| 8 | 0.254 | 0.297 / 0.255 | 0.297 / 0.257 |
| 9 | 0.238 | 0.046 / 0.237 | 0.004 / 0.239 |

The reason is structural (heuristic, with this evidence). A digit `v` can
only sit at a position `>= v`, and the large digits have `v` close to `L`.
So they sit in the few top positions. The top digits of `F` are fixed by
the counts of the large digits, `F ~ c_v v^v + c_(v-1) (v-1)^(v-1)`, which
take only a few values. At a given `L` either these few values can place
the digit `v` in a top position or they cannot, for all multisets at once.
The coincidences are therefore all or nothing per length: rare lengths like
`L = 8` or 26 carry clusters, and most lengths carry nothing. In integer
bases a large digit can sit at any position, mostly among the random low
digits, so this effect is absent.

Answer: the six small solutions are the only ones below `34!` (computed).
Finiteness is not proven and I see no route: no size argument works, and
there is no residue to exploit. The plain model predicts finitely many but
is wrong in this world. Its mean may be about right (the near-solutions
at `D = 1000 j` total 218 and 263 against its 231), but the variance is far larger
than Poisson. A model that fixes the top digits from the large counts, as
the search tree does, is the natural correction; with it the expected
number of large solutions depends on how often a length is "open", which
the data put at about 5 lengths in 17.

## What is universal

| feature | integers | 61 `F_q[T]` | 60 `p/q` | 63 Eisenstein | 59 `eps_x` | 62 factorial |
|---|---|---|---|---|---|---|
| about one coincidence per window family | yes | yes, 0.6 to 1.0 exactly | yes | yes | yes | no: clustered |
| identity modulus | `b - 1` | `B - 1` | `p - q` | `n^2+3n+3` | `x` | none |
| free residue factor | 2 if `b` odd | `q^k(B)`, `k` = factors of `B-1` | 2 if `p, q` odd | none (odd) | 2 (or more) if `x` even | none |
| twins | 2 under `0^0 = 0` | families of `q` | none for `q > 1` | not studied | yes | yes, at position 1 |
| self-paying digits | in perfect-power bases | yes | no | no | no | only `(1,1)`, `(2,2)` |
| length bound | `b` digits | `(e-1)q^(e-1)/e + 1` | finite per base | Proposition 14.10 | `2 log N + 2` | none |

- Universal (computed in all six worlds with a residue identity): the free
  residue factor follows the identity modulus and the residues of the
  weights. Doubling appears exactly when the modulus is even (60, 63, 59),
  and in `F_q[T]` it becomes `q` per prime of `B - 1`, because Frobenius
  makes the weights agree with the digits at every prime.
- Universal where digits can move: about one coincidence per base and
  convention, and solutions behave like near-solutions (sections 11.1,
  21.1.6, 21.2.4).
- Not universal: the coincidence model itself. It needs a digit value to be
  free to appear at many positions. The factorial system confines large
  digits to the top, where the sum is not random, and the model fails there.

## Status

| question | answer | status |
|---|---|---|
| 61 | class-sum linearity, families of `q`, self-paying digits, free factor `q^k(B)` with `k(B) >= omega(B-1)`; exact count for `e = 2`; census of 4,426 bases | proven; computed; model off by a factor 0.5 to 1.5 for odd `q` here; chapter 24 traces the gap to the digits of `F` |
| 60 | doubling in odd/odd bases | proven identity; computed `p <= 11` except `11/1, 11/8, 11/10` |
| 63 | no doubling, as the odd modulus predicts; Gaussian control doubles | proven identity; computed `n <= 3` (`n = 3` to 25 digits) |
| 59 | length bound, identity, twins; even `x` double | proven; computed `x <= 12` |
| 62 | only 1, 4, 5 and 1, 2, 5 below `34!`; model fails for a structural reason | proven structure; computed census; finiteness open |

Open questions raised here:

- `F_q[T]`: is `k(B) = omega(B - 1)` always? Why is the model 1.3 times
  too low under `0^0 = 0` and 2 times too high under `0^0 = 1` for odd `q`?
  (Answered in chapter 24: the digits of `F` are not independent, and
  Proposition 24.11 accounts for the whole gap under `0^0 = 1`.)
- Factorial system: a model with top digits fixed by the large counts, and
  a search past `34!` with wider integers. Is the set finite?
- Rational bases `11/8` to `11/10` and `p >= 12` need a better pruning
  bound; the tree has about `2 W / ln(p/q)` nodes.
- Eisenstein `-3+w` at lengths 27 and 28, and `-4+w`.

## Files

- `fast/src/bin/r3t_ffield.rs`, `analysis/r3t_ffield_summary.py`,
  `analysis/r3t_ffield_structure.py`; data `analysis/data/r3t_ffield_frob.txt`,
  `r3t_ffield_near.txt`, `r3t_ffield_deg.txt`.
- `fast/src/bin/r3t_afs.rs`, `analysis/r3t_afs_summary.py`; data
  `analysis/data/r3t_afs_search.txt`, `r3t_afs_model.txt`.
- `fast/src/bin/r3t_eisen.rs`, `analysis/r3t_eisen_summary.py`,
  `analysis/r3t_eisen_lengths.py`; data `analysis/data/r3t_eisen12.txt`,
  `r3t_eisen3_m0.txt`, `r3t_eisen3_m1.txt`, `r3t_eisen3_mc.txt`,
  `r3t_gauss2_offsets.txt`, `r3t_eisen_lengths.txt`.
- `fast/src/bin/r3t_pisot.rs`, `analysis/r3t_pisot_summary.py`; data
  `analysis/data/r3t_pisot_search.txt`, `r3t_pisot_search12.txt`,
  `r3t_pisot_model.txt`.
- `fast/src/bin/r3t_factorial.rs`, `analysis/r3t_factorial_check.py`,
  `analysis/r3t_factorial_model.py`, `analysis/r3t_factorial_diag.py`; data
  `analysis/data/r3t_factorial_census.txt`, `r3t_factorial_near1_m0.txt`,
  `r3t_factorial_near1_m1.txt`, `r3t_factorial_near1000.txt`,
  `r3t_factorial_model.txt`, `r3t_factorial_diag.txt`.
