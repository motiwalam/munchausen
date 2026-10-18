# Round 3 research questions in detail

A reading of chapters 11 to 18 produced these 19 questions, numbered
45 to 63 after the 44 of `questions.md`. Each question cites the result that
raised it. Each has a line "Why" (what raised it and what an answer would
change), a line "Attack" (a concrete first step) and a line "Kind" (proof,
computation or twist). The last section groups ten of them into two agent
workloads.

A few leads come from quick checks by the questioner. Their scripts were
throwaway runs in a scratch directory and are not in the repo. Their numbers
are leads, not results.

## Theme VII. Short solutions: counting and local structure

### 45. Count multisets, not strings

A `k`-digit solution `n = F(c)` is fixed by its digit multiset `c`. For each
choice of leading digit, Proposition 15.17 puts its base in a window of at
most `X + 2` integers. Does this prove that almost all bases have no solution
with at most `(1 - eps) ln b / ln ln b` digits, twice the range of
Theorem 11.2? How far beyond that can a counting argument go?

Why: Theorem 11.2 and Proposition 10.4 count strings, `X (X+1)^(k-1)` of
them. Multisets number `C(X+k, k)`, smaller by about `k!`. At
`k = alpha ln B / ln ln B` we have `ln X ~ 2 ln ln B` and `ln k! ~ alpha ln B`,
so my sketch gives at most `K^2 (X+2) C(X+K, K) = B^(alpha + o(1))` bases up
to `B` with a solution of at most `K` digits. That is below `B` for every `alpha < 1`. The same count sharpens
Proposition 10.4 for every fixed `k`.

Attack: Write the proof. Check the window of Proposition 15.17 when the
second digit is the largest. Evaluate the new bound at `B = 10^96` next to
the `B^0.46` of section 11.6. Then ask whether Proposition 11.1, applied to
multisets, can push `alpha` past 1.

Kind: proof.

### 46. The 3-adic and 5-adic laws of `x^x - x`

Describe `T(q) = { x^x - x mod q : x >= 1 }` for every prime power `q`. Prove
that `T(p^e)` is all of `Z/p^e` for `p >= 7`, and find the rules for
`3^e` and `5^e`.

Why: Lemma 15.12 stops at 27 and only computes `T(25)`. Theorem 15.13 shows
that the gaps in `T(q)` are what make coverings, and question 38 asks which
moduli coverings need. Lead (computed): the residues of `T(3^e)` prime to 3
are `{2}` mod 27, `{2, 29}` mod 81 and `2 + 27 j` with
`j` in `{0, 1, 3, 4, 6, 7}` mod 243. `T(5^e)` misses only residues
`== 3 (mod 5)`: 4 of the 5 such classes mod 25, 22 of 25 mod 125, 114 of 125
mod 625. `T(p^2)` is everything for `7 <= p <= 47`. A 5-adic rule would give a
second covering theorem next to 15.13, and new moduli for question 47.

Attack: Find the classes of `x` modulo `lcm(5^e, 4 * 5^(e-1))` with
`x^x - x == 3 (mod 5)`. Expand `x^x` around them as in part 3 of the proof
of Lemma 15.12. For `p >= 7`, lift part 2 of that proof with Hensel's lemma.
Then add 81 and 125 to `analysis/dyn_cover_density.py` and remeasure the
8% of section 15.4.4.

Kind: proof.

### 47. Prime powers in the sieve of `kdigit`

Add the moduli 4, 8, 16, 9, 27, 81, 25 and 125 to the root test of
`fast/src/bin/kdigit.rs`. How much do they cut the survivors and the run
time, and which set of 18 moduli is best?

Why: `kdigit` tests the 18 primes up to 61 (section 11.5). The primes 2 and 3
are weak: 98.8% and 80% of 3-digit strings pass them. Theorem 15.13 shows that
27 makes the last digit hopeless for about 8% of prefixes, and the test mod 3
cannot see this. The mask method works for any modulus `q`, because
`Q_s(r) mod q` depends only on `r mod q`. A faster sieve pushes 7 digits past
digit 26 (bases up to `10^5.5`) and starts 8 digits, which also bears on
question 29.

Attack: Turn `PRIMES` into a list of moduli up to 128 with 128-bit masks.
Check that k = 3 to 6 reproduce the lists of chapter 3. Count survivors per
modulus in the order applied. Choose 18 moduli greedily by the share each one
removes per unit of cost.

Kind: computation.

### 48. p-adic local factors in the root heuristic

In the heuristic of section 11.4, replace the root count `rho_s(p)` mod `p`
by the p-adic density `lim #roots mod p^e / p^(e-1)` for `p` = 2, 3 and 5. Do
the predictions move toward the observed 6 three-digit, 2 four-digit and 6
five-digit solutions?

Why: The heuristic predicts 5.09, 1.39 and 2.42. The 5-digit count is 2.5
times too high, which is the largest gap left in the short lists. A root mod 3
that does not lift to 27 still counts as a root today, and Lemma 15.12 shows
that this happens often. The same heuristic gives the completeness estimates
of section 11.4, so a better factor changes how far the lists can be trusted.

Attack: Change `analysis/root_local.py` to count roots modulo `2^6`, `3^4` and
`5^3`. Check that the corrected factor still averages near 1 over random
strings. Redo the table of section 11.4.

Kind: computation.

### 49. A defect spectrum for short solutions

For k = 4 and 5, count the pairs `(s, b)` with `Q_s(b) = D` and `b > max(s)`
for a few hundred offsets `D`. Is the count of short solutions, like that of
long ones, a Poisson draw with the mean of its offsets?

Why: Section 11.1 did this for long solutions and showed that they are
ordinary draws. Short solutions follow another heuristic (section 11.4), and
it rests on 2 and 6 data points. Hundreds of offsets calibrate it to about 5%.
They decide whether the 5-digit excess (6 against 2.42) is luck or a missing
factor. Offsets `D = j L` with `L = 2^4 * 3^3 * 5^2 * 7 = 75600` keep the roots
of `Q_s` modulo these prime powers. Offsets `D = j` test the local factors
themselves.

Attack: Add `--offset D` to `kdigit`: subtract `D` from the constant term in
the masks and in the exact root step. Run k = 4 with `M = 150` and k = 5 with
`M = 60` for `j = 1` to 200. Compare with `root_local.py` applied to
`Q_s - D`.

Kind: computation.

### 50. At most two 3-digit solutions per base

Under `0^0 = 1`, does every base have at most two 3-digit solutions? Base 4
has two, `(1,3,1)` and `(3,1,3)`. Every other base below `10^51` has at most
one (section 18.2).

Why: Theorem 15.7 settled two 2-digit solutions with elementary inequalities.
The method of `analysis/r2nt_two_three.py` shows that in one base each leading
digit `p` allows at most two values of the largest digit `M`. If `M` is the
middle or the last digit, at most two strings remain. Only `M = p` leaves up
to `p` strings. An absolute bound would replace the power of `log b` of
Proposition 4.1 for k = 3. A per-base 3-digit search could then stop after two
hits.

Attack: Follow the four steps of Theorem 15.7. In the case `M = p`, write
`q b - g(q) = p^p - p b^2 + g(r)` with `g(x) = w(x) - x`. Use the concavity of
the left side in `q` to bound the number of `q`. Check the inequalities on a
grid, as section 15.2 did.

Kind: proof.

## Theme VIII. The equation `b(b+x) = x^n + c`

### 51. The families `(1, x, 2)` and `(1, x, 3)`

Under `0^0 = 1`, `(1, x, r)` is a solution exactly when
`b(b+x) = x^x + c` with `c = w(r) - r + 1`. That is `c = 3` for `r = 2` and
`c = 25` for `r = 3`. Does the method of chapter 18 solve
`b(b+x) = x^n + c` for these `c`, at least for prime powers `x`?

Why: Five of the six 3-digit solutions have an algebraic factor pair
(section 16.1.5). The family `(1, x, 1)` is solved for prime powers
(Theorem 18.8). The case `r = 0` is easy: `x^x + 2` is odd for odd `x`, and a
square plus 2 for even `x`. For `c = 3, 25` the number
`theta = (x + sqrt(x^2 + 4c))/2` has norm `-c` and is not a unit. The answer
shows whether chapter 18 depends on the unit `eps` of norm -1. The same
question applies to `(1, 2, x)`, which needs `(b+1)^2 = x^x + 6 - x` and
contains `(1,2,6)` in base 215.

Attack: Sieve `4 x^x + x^2 + 4c` as in `alg_sieve171.c`. Run the convergent
method of `r2nt_allnx.gp` with `theta` in place of `eps`, for odd prime `x` up
to 1000. When `3 | x`, `x^2 + 12` is of Richaud-Degert type with an explicit
unit. Look there for an analogue of Proposition 18.6.

Kind: proof.

### 52. The even case `x == 0 (mod 8)`

Solve `b(b+x) = x^n + 1` for `x == 0 (mod 8)` with an odd prime factor and odd
`n >= 5`. At least prove an analogue of Proposition 18.4 that bounds `x` in
terms of `n`.

Why: Proposition 18.1 leaves these `x` open, and Theorem 18.8 handles only
`x = 2^a` (Szalay). They are the last even case of question 32 (section
18.1.9, question 2). With `V = b + x/2` and `E = (x/2)^2 + 1`, the equation
reads `V^2 - E = x^n`. Since `E == 1 (mod 8)`, 2 splits in `Q(sqrt E)`. The
2-part of `(V + sqrt E)/2` has exponent `a n - 2`, which is not a multiple of
`n`, so Lemma 18.3 fails as it stands.

Attack: As ideals, `((V + sqrt E)/2)` is `C^n` divided by the square of a
prime above 2. Carry this fixed factor through Proposition 18.4 and
Laurent's bound, as one more algebraic number in the linear form. Check every `x = 8m` up to `10^5` and
`n <= 15` directly first.

Kind: proof.

### 53. Orders of mixed ideal classes

For odd composite non-square `x` up to `10^5` or `10^6`, compute the order `d`
of the class of each mixed ideal `B` of norm `x` in `Q(sqrt(x^2 + 4))`. How
often does `d` divide `x`, and how does `d / x` behave?

Why: Corollary 18.11 leaves one loophole for `(1, x, 1)`: a mixed `B` whose
class order `d` divides `x`, with `x / d < 3.3 * 10^4 log x`. So the class
group needs an element of order about `x / log x`. Since `h R` is about
`sqrt(D) L(1, chi)` and `R` is about `log x`, the class number allows this.
Statistics of `d` give a Cohen-Lenstra estimate of the expected number of such
`x` above `4 * 10^9`. A pattern, such as `d` never dividing `x`, would point
to a proof.

Attack: Use PARI `bnfinit` (GRH is fine for statistics) and `bnfisprincipal`
on the ideals above the primes of `x`. Record `d`, `gcd(d, x)` and the largest
`d` per `x`. Fit the share of `x` with `d | x` and `d > x / C` against `x`.

Kind: computation.

## Theme IX. The model and complexity

### 54. A proof of Assumption R

Prove Assumption R of section 13.2.3 with an explicit `kappa`, at least when
`b - 1` is prime to 6. This would make the refined case of Corollary 13.11
unconditional.

Why: Assumption R is the only gap in the Poisson theorem of chapter 13
(section 13.2.6). It is also the factor 1 for odd primes in section 5.3. The
data of section 11.1 say that counts are Poisson draws with the refined means.
Lemma 15.12 and question 46 show where uniformity can fail: modulo `3^e` and
`5^e` the values of `x^x - x` are thin.

Attack: Write the share as `(1/q) sum over h of E[e(h S / q) | G_d]`. Without
the condition, Poisson counts give
`|E e(hS/q)| = exp(-sum over x of (1 - cos(2 pi h (x^x - x) / q)))`. Show that
the sum over `x < b` is at least `c b`, with Lemma 15.12 part 2 for primes.
Then show that the condition `G_d` on the length, which the top digits decide,
is nearly independent of the residue.

Kind: proof.

### 55. Hardness with long solutions

Is GEN still NP-complete on weight tables whose every solution has at least
`b - C` digits, or at least `b / 2`?

Why: Section 13.1.6 leaves this open. The hard instances of Corollary 13.4
have solutions with at most `b/2` digits. Real solutions have about `b - 1`
digits, and Theorem 10.1 is about that regime. If hardness survives, the
barrier covers every regime the search meets. If it fails, the algorithm for
long-solution tables is a new search idea.

Attack: Pad the reduction of Theorem 13.3 with filler digit values. Give them
weights that force a fixed number of copies through an unused high block of
positions. Check small instances with `analysis/thy_reduction.py`.

Kind: proof.

### 56. The length tail in perturbed worlds

Count solutions by `J = b - k`, for `J` from 0 to 15, in many perturbed worlds
at bases 20 to 40. Does the tail of section 10.5 appear? Beyond
`J = ln b + 1` it is about 3 times the `e^-J` limit, with dips at some `J`.

Why: Conjecture 10.3, the window `ln k + ln ln k`, rests on this tail. The
real data have only three long exceptions. Perturbed weights keep the size of
`x^x`, so they test the mechanism, the digit `b - J + 1` becoming possible,
with hundreds of independent worlds. The window also decides which
`--min-digits` and `--max-digits` settings a search needs.

Attack: Run `fast search --perturb <seed> --max-digits <b-4>` for 200 seeds
at bases 20, 24, 28 and 32. Measure the cost first, since short lengths use
smaller digits. Compare with `analysis/length_law.py` run on the same
perturbed weights.

Kind: computation.

### 57. The factorion shortfall in a narrower offset class

Repeat the offset test of section 17.4 for factorions in the odd bases 15 to
35, with offsets `D = j b (b-1)`. These keep both `n mod (b-1)` and `n mod b`.
Does the shortfall at `D = 0` appear in this narrower class too?

Why: The offsets `j (b-1)` of section 17.4 move the last digit of `n` by
`-j`. For `x!` the low digits of `F` are fixed by the small digit counts.
Section 11.2 used `2 j b (b-1)` for `x^x` for this reason. If the narrow class
is short too, the cause is the last digit, which `wgt_lowdigits.py` missed. If
not, the shortfall is chance, and question 41 can close without bases 47 and
49 (1 and 3 hours). Lead (from `analysis/data/wgt_factorial.txt`): the 7 long
factorions of odd bases 14 to 36, counted per convention, sit in bases 17
(4), 23 (1) and 27 (2). Prime and composite bases look alike.

Attack: Run `fast search --factorial --offset D` for `j = 1` to 30 in the odd
bases 15 to 35. Compare per base with the table of section 17.4 and with
`analysis/data/wgt_offsets_factorial.txt`.

Kind: computation.

## Theme X. Twists

### 58. Narcissistic numbers as a model test

Narcissistic numbers use the weights `x^d`, with `d` the length. Their counts
per base are a published dataset (OEIS A010353). Does the refined model
predict them per base and per length, with the exact factor that the residues
of `x^d mod (b-1)` give at each `d`?

Why: Section 17.2 showed that forced residues multiply the count by `b - 1`.
Here the residues change with `d`. If `d == 1 (mod lambda(b-1))`, then
`x^d == x` for every digit, and the identity holds for free, as under
`--set-residue 0`. Other `d` give other factors. Also `x^d == x (mod 2)`, so
odd bases gain a factor 2 at every length. These are sharp predictions on
data nobody tuned. Lead (computed): bases 3 to 7 have 3, 8, 13, 25 and 53
narcissistic numbers with at least 2 digits. With the one-digit numbers this
matches A010353.

Attack: Extend `analysis/wgt_model.py` to weights that depend on the length.
Enumerate multisets per length for bases up to 12, or give `fast` a weight
table per length. Compare the counts per length with the model.

Kind: twist.

### 59. The Pisot base `eps_x`

Let `eps_x = (x + sqrt(x^2 + 4))/2`, the unit of section 18.1.2. Every
positive integer has a finite greedy expansion in base `eps_x` with digits 0 to
`x` (Frougny and Solomyak). Which integers equal the sum of the weights of
their digits?

Why: `Z[eps]/(eps - 1)` is `Z/x`, because `N(eps - 1) = -x`, and every power
of `eps`, negative ones included, is 1 modulo `eps - 1`. So
`N == digit sum (mod x)`. The universal laws of section 14.6.3 then predict
about one solution per base and convention, doubled under `0^0 = 0` when `x`
is even. This is the first non-integer base in the library, and the same unit
`eps` controls the family `(1, x, 1)`. Equivalently, `Q_s(eps_x) = 0` for a
string with a radix point, which is two integer equations.

Attack: Implement greedy expansions exactly in `Z[eps]`, as pairs of integers.
Bound the number of digits after the radix point first. Enumerate multisets
for `x` = 2 to 12 under both conventions. Compare the counts with a model
that samples valid expansions.

Kind: twist.

### 60. Parity in rational bases

In the base `p/q` of Akiyama, Frougny and Sakarovitch, the recursion
`q N_i = p N_(i+1) + a_i` gives `q N == digit sum (mod p - q)`. When `p` and
`q` are both odd, `x^x == x (mod 2)` makes this free under `0^0 = 0`. Does the
count double in those bases?

Why: Section 14.6.3 predicts parity doubling whenever the digit-sum modulus is
even. In AFS bases this modulus is `p - q`, unrelated to the digit range, so
the test is new. Lead (section 16.5): under `0^0 = 0` the three bases with odd
`p` and `q` (5/3, 7/3, 7/5) have 6 Munchausen numbers. The 11 other bases with
`p <= 8` have 6 together.

Attack: Run `analysis/alg_afs.c` for `p` up to 12 or 14, timing it first. Build
the model by sampling `N` in each length window and reading its digits,
because the AFS language is not regular. Compare odd/odd bases with the rest,
under both conventions.

Kind: twist.

### 61. A function-field analogue

In `F_q[T]` with a base `B` of degree `e >= 2`, the digits are the polynomials
of degree below `e`. Give a digit `d` the weight `d^|d|`, with `|d| = q^deg d`,
the analogue of `x^x` with the norm as exponent. What are the solutions of
`n = F(n)`, and what structure do they have?

Why: Frobenius gives `d^(q^j) = d(T^(q^j))`, which is `F_q`-linear in `d`. So
for a fixed pattern of digit degrees, the solutions form a linear space minus
the strings where some digit drops in degree. Exact linear algebra replaces
the coincidence model. That shows what the "one per base" law becomes when
the weights are additive. It also shows whether analogues of twins and
self-paying digits (`d^(|d| - 1) = B^k`) appear.

Attack: In Sage, take `q` = 2 and 3 and bases `T^e` and irreducible `B` of
degree 2 to 4. The degrees give a length bound: `deg F <= (e-1) q^(e-1)`. Solve
the linear system for each degree pattern. Check whether the count depends
only on `e` or on `B` too. Repeat with the weight `d^(deg d)` for contrast.

Kind: twist.

### 62. The factorial number system

Write `n = sum d_i i!` with `0 <= d_i <= i`, and ask for `n = sum w(d_i)`. Are
there finitely many solutions?

Why: Every base `b` has finitely many solutions because of the length bound
of section 1.2. Here no size argument bounds the length: the top weights
`L^L` exceed `(L+1)!`. So finiteness must come from the model alone, as in
the conjectures of sections 7.2 and 10.3. There is also no digit-sum modulus.
Swapping two adjacent digits changes `n` by a multiple of `i * i!`, which
depends on the position. Lead (computed): below `10!` the only solutions are
1, 4, 5 under `0^0 = 0` and 1, 2, 5 under `0^0 = 1`.

Attack: Build the model: the chance that a random admissible string of length
`L` has `F` in `[L!, (L+1)!)` with matching digits. Sum it over `L`. Fixed top
digits still give an interval, so a prefix tree like `fast` can search to
`20!` or `25!`.

Kind: twist.

### 63. Eisenstein bases

In `Z[omega]`, `beta = -n + omega` is a canonical number system base for
`n >= 1`, with digits 0 to `n^2 + n`. Its identity modulus
`N(beta - 1) = n^2 + 3n + 3` is always odd. Do these bases show no parity
doubling under `0^0 = 0`, unlike the Gaussian bases `-n + i` with even `n`?

Why: Section 14.6.3 claims two universal laws: about one solution per base
and convention, and doubling exactly when the identity modulus is even.
Eisenstein bases are a family where the second law predicts no doubling for
any `n`. A census also tests the gaps in lengths of section 14.5.1, now with
`arg(beta) = pi - arctan(sqrt(3) / (2n + 1))`.

Attack: Adapt `fast/src/bin/gauss.rs` to `Z[omega]`. The last digit of
`a + b omega` is `(a + n b) mod (n^2 + n + 1)`, because `omega == n`. Port the
length bound of Proposition 14.10. Run `n` = 2 to 4 under both conventions
and sum the model exactly.

Kind: twist.

## Proposed workloads

Two workloads of five questions, each ranked by expected payoff.

Workload 1: number theory (PARI/GP, Sage, Python).

1. Question 45. A short proof that doubles the range of Theorem 11.2. Very
   likely to succeed.
2. Question 46. Likely provable, and it feeds question 47 and the coverings
   of chapter 15.
3. Question 52. Closes the last even case of question 32, or isolates the
   obstacle at 2.
4. Question 51. Tests whether chapter 18 needs the unit of norm -1, and
   reaches two new 3-digit families.
5. Question 53. A heuristic count for the one loophole of Corollary 18.11.
   Lower payoff, but the run is mechanical.

Workload 2: computation and model tests (Rust `kdigit` and `fast`, Python).

1. Question 47. A direct speedup of `kdigit` and longer short-solution lists.
   It can use the computed `T(q)` of question 46 without waiting for the proof.
2. Question 49. Calibrates the short-solution heuristic with hundreds of
   draws. It needs the same `kdigit` changes as question 47.
3. Question 48. A cheap model fix that might explain the 5-digit excess.
4. Question 58. A sharp test of the model on outside data.
5. Question 57. Settles the factorion shortfall cheaply, or sharpens it.

Left for a later agent: questions 50, 54 and 55 (proofs), 56 (a long
computation), and the twists 59 to 63. The twists form a natural third
workload.
