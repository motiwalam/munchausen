# A library of facts about Munchausen numbers

These notes collect what is known about Munchausen numbers: numbers equal to
the sum of their digits, each raised to its own power, in some base `b`. Every
statement is marked by its source:

- proven: a proof is in the chapter;
- computed: an exhaustive search found it, and the range is stated;
- model: the probabilistic model of chapter 5 predicts it.

## Chapters

| chapter | contents |
|---|---|
| [1. Basics](1-basics.md) | notation, length bound, balance, one base per digit string, the two conventions, congruences, `b`-digit solutions |
| [2. Constructions](2-constructions.md) | twins, self-paying digits, swaps, all 2-digit solutions, solutions of every length under `0^0 = 0` |
| [3. Fixed length](3-lengths.md) | every short solution in every base up to huge bounds; which lengths occur; finitely or infinitely many |
| [4. Counts per base](4-counts.md) | bounds on the number of solutions, the data for bases 2 to 41, bases with exactly `n` solutions, empty bases |
| [5. Probabilistic model](5-model.md) | the expected number of solutions, the parity effect, the `(b-1)`-digit excess, predictions |
| [6. Cost of search](6-search.md) | why the exhaustive search grows like `1.87^b`, ideas that do not help, base 100 |
| [7. Open problems](7-open.md) | conjectures with their evidence |
| [8. Barriers](8-barriers.md) | what is settled, partial finiteness proofs, and why the rest needs new mathematics |
| [9. Inexact search and counts](9-inexact.md) | a faster search with a measured miss rate, empty bases, bases with many solutions, length against base |
| [10. Limits of randomized search](10-limits.md) | growth rates of the exact and likely trees, a lower bound for tree searches, the `--zscore` rule, failed routes to a larger speedup, the sharpened length window |
| [11. Near-solutions and local obstructions](11-local.md) | the defect spectrum `n - F(n) = D`, empty bases and missing `b`-digit solutions explained, local obstructions for short strings, a sieved search 150 times faster, almost all bases have no short solution |
| [12. The Munchausen polynomial](12-polynomial.md) | Galois groups of `Q_s`, completeness of the local test, Munchausen numbers in negative bases |
| [13. Complexity and a Poisson law](13-complexity.md) | the general problem with arbitrary weights is NP-complete; a Chen-Stein Poisson theorem in the model |
| [14. Other number systems](14-other-bases.md) | negative, imaginary and Gaussian bases; factorions; what is universal |
| [15. Dynamics and nonexistence](15-dynamics.md) | cycles of `n -> F(n)`, bases with two 2-digit solutions, coverings, constructions, integers with many bases |
| [16. Algebra of the polynomial](16-algebra.md) | Aurifeuillian factors and base 904, the equation `b(b+x) = x^x + 1`, reducibility, Galois groups, rational bases |
| [17. Other weights](17-weights.md) | a general weight table in the engine; forced residues multiply the count by `b-1` as predicted; `0^0 = m`; universality of the laws |
| [18. The equation b(b+x) = x^n + 1 and more](18-number-theory.md) | `b(b+x) = x^n + 1` solved for prime powers and odd `x <= 1001`; the M/L series in general; bases with 2- and 3-digit solutions; integers with three bases; signs of roots; powers as weights |
| [19. A faster sieve and short-string spectra](19-sieve-spectra.md) | prime powers in the `kdigit` sieve (11x faster); defect spectra for 4 and 5 digits; p-adic local factors; narcissistic numbers as a model test; the factorion shortfall is chance |
| [20. Multisets and the residues of x^x - x](20-multisets-residues.md) | almost all bases have no solution with up to about `ln b / ln ln b` digits; the 3-adic and 5-adic laws of `x^x - x`; `b(b+x) = x^n + c` for `x == 0 (mod 8)` and `c = 3, 25`; mixed ideal classes |
| [21. Five more number systems](21-five-systems.md) | function fields `F_q[T]`, rational bases, Eisenstein bases, a Pisot base, the factorial system; the residue factor follows the identity modulus everywhere; the model fails in the factorial system |
| [22. Self-paying blocks and binomial families](22-blocks-families.md) | infinitely many solutions of every length under `0^0 = 1`; self-paying blocks; the 5-digit excess recalibrated to about 9x and still unexplained |
| [23. Factorions, empty negative bases, cycles and scatter](23-factorions-negative.md) | base 47 factorions; negative census to -38; near-2-cycles; lengths in base -1+i proven; where the per-base scatter comes from |
| [24. Why the model misses in F_q[T]](24-ffield-gap.md) | Frobenius blocks make the digits of `F` far from uniform; the exact channel under `0^0 = 1`; short solutions counted for every degree; small effects on the integer model |
| [25. Identity families and 3-digit solutions](25-identity-families.md) | where the large digits of an identity sit; a second infinite family `(c^j, 0, ..., 0, x)`; no other 3-digit solution up to `10^3301`; at most 30 three-digit solutions in almost every base |
| [26. Near-solutions as evidence](26-near-solutions-evidence.md) | the swap lemma: near-solutions cluster across offsets; a corrected calibration; every chance verdict revisited; a pooled test across worlds |
| [27. Limits of search](27-limits-of-search.md) | constraint solvers lose to the tree; the entropy floor holds for every order; certificates of emptiness; bottom digits do not pay; the law of work-unit sizes |
| [28. A sharper z-score rule, length windows and the GPU](28-zscore-gpu.md) | `--zlaw cond` fixes the variance of the z-score test (1.1 to 1.3x fewer nodes at equal miss rate); length windows do not pay; the GPU runs the inexact search and shards |
| [29. Theorems about the model](29-model-theorems.md) | the length shares of the basic model proven; `k(B) = omega(B - 1)` in `F_q[T]` for every `e <= 10`; Assumption R reduced to one number per base and checked up to base 6000; a block model for `F_q[T]`; open lengths in the factorial system |
| [30. Connections to other fields](30-applications.md) | anti-concentration proves the refined Poisson law in the limit; Assumption R as a collision bound for `x^x - x`; 2-digit solutions as fixed points of `x -> x^x mod p`; `tau(b^2 + 1) - 2` two-digit narcissistic numbers, so empty bases are Landau's problem; analogies |
| [Open questions](questions.md) | 123 research questions in eight rounds, with priorities and answers; [round 5 directions](questions-round5.md); [round 6 directions](questions-round6.md) |

## Main results

Proven:

- Each digit string is a solution in at most one base (Proposition 1.3).
- Under `0^0 = 0`, solutions ending in 0 and 1 come in twins (Proposition 2.1).
- A digit `a` with `a^(a-1) = b^k` pays for itself at position `k`. These
  digits exist only in perfect-power bases, and under `0^0 = 0` they combine
  freely with any solution (Propositions 2.2 and 2.3).
- `(a, c)` is a 2-digit solution exactly when `a | w(c) - c`, in base
  `(a^a + w(c) - c) / a` (Proposition 2.6).
- Under `0^0 = 0`, every length has infinitely many bases with a solution of
  that length (Proposition 2.7).
- Under `0^0 = 0`, the number of solutions per base is unbounded. Base `2^60`
  has at least 32,766 (Proposition 4.2).
- For a fixed length `k`, a base has at most a power of `log b` many
  `k`-digit solutions (Proposition 4.1).
- In an odd base, every solution under `0^0 = 1` has an even number of zeros
  (section 1.6).
- Self-paying digits never occupy adjacent positions, and under `0^0 = 1` the
  only solutions made of zero-balance placements are `(a, 1)` (section 8.3).
- Under `0^0 = 1`, every length `k >= 3` has infinitely many solutions
  (Corollary 22.7). The digits are the coefficients of `(c r + e)^(k-1)`
  without the constant term, then one digit `x` with `x^x` a `(k-1)`-th
  power. The smallest is `(1,2,6)` in base 215; the next 3-digit member is
  `(1,6,46666)` in base `46666^23333 - 3`. This refutes the finiteness
  conjecture of chapters 3 and 7 and corrects Corollary 8.4.
- A second family, `(c^j, 0, ..., 0, x)` with `x = c^(j c^j) + j - 1`, gives
  smaller solutions of 4 to 6 digits, such as `(8,0,0,16777218)` in base
  `16777218^5592406 / 2`. In every power identity the large digit is last
  (Theorems 25.2, 25.5).
- Short solutions under `0^0 = 1` with a large leading digit are finite in
  the square class, with an explicit bound (Theorem 8.3).
- Base `n^(n-1)` has at least `2^(n-1) - 2` solutions under `0^0 = 0`, and
  at most `X^(1/(c+1))` bases up to `X` have `c` self-paying digits
  (section 9.8).
- In the model, every search that walks the digit tree from the top needs
  about `1.638^b` nodes, exact or not (Theorem 10.1). The only residue that
  the digit multiset determines is `n mod (b-1)` (Proposition 10.2).
- Up to `B`, at most a power of `ln B` bases have a solution with a fixed
  number of digits (Proposition 10.4).
- Almost all bases have no solution with fewer than `(1 - eps) ln b / ln ln b`
  digits (Theorem 20.3, doubling the range of Theorem 11.2).
- A digit string whose polynomial `Q_s` has no root modulo some prime is not a
  solution in any base (Proposition 11.1). If `Q_s` is irreducible, this
  happens for a positive density of primes (Proposition 12.1).
- Munchausen numbers in negative bases have an odd number of digits
  (Proposition 12.2); 3-digit solutions with `s_1 | s_2` have a partner in a
  negative base (Proposition 12.3).
- Under `0^0 = 1`, base 3 is the only base with two 2-digit solutions
  (Theorem 15.7).
- The Aurifeuillian factors `L < M` of `x^x + 1` satisfy `M / L -> e^2`
  (Theorem 16.2). This explains `(1,7,1)` in base 904 and why no larger `x`
  works the same way; `b(b+x) = x^x + 1` has no further solution for `x` up to
  `4 * 10^9`, and the abc conjecture would rule them out entirely.
- For `x` a prime power, the only solutions of `b(b+x) = x^n + 1` with
  `n >= 2` are `(x, n) = (3,2), (8,2), (3,3), (5,3), (8,3), (64,3), (7,7)`
  (Theorem 18.8). There are none with `n >= 4` even. So `(1,x,1)` with `x`
  an odd prime power is a solution only for `x = 3, 7`; any other `x` must be
  composite, above `4 * 10^9`, with a non-principal ideal class (Corollary 18.11).
- For every Aurifeuillian pair of `Phi_m(s y^2)`, `log(M/L)` is an exact
  series with a twisted Ramanujan sum, and `M/L` tends to `e^(2/y)` or 1
  (Theorem 18.20).
- With arbitrary weights in place of `x^x`, deciding whether a solution exists
  is NP-complete and counting them is #P-complete (chapter 13). Any fast
  algorithm for real Munchausen numbers must use the arithmetic of `x^x`.
- The residues of `x^x - x` cover everything modulo `p^e` for `p >= 7`; modulo
  powers of 3 and 5 they follow explicit laws (Theorems 20.8, 20.11, 20.12).
  Beyond 81, single powers of 3 give no new coverings.
- Infinitely many digit strings are excluded in every base by covering
  congruences with moduli `3^e` and `2^e`; `(2,1,x)` is never a solution
  (chapter 15).
- In the model, every order of revealing digit counts, fixed or adaptive,
  needs at least the top-down entropy, so the `1.638^b` floor holds for all
  orders (Theorem 27.2). In an oracle model the exact tree is optimal up to
  a factor about linear in `b`, computed up to base 21 (section 27.3).
- In the basic model, the expected number of solutions with `b - j` digits
  tends to an explicit share `s_j` (8.0%, 55.2%, 23.3%, 8.6%, ...) with
  error `O(1/b)`, and the sum over all lengths tends to 1 (Theorem 29.1,
  Corollary 29.6). The proof couples the top digit counts with independent
  Poisson variables.
- In `F_q[T]`, the free residue dimension `k(B)` equals `omega(B - 1)`
  whenever some factor of `B - 1` has degree prime to `e - 1`, so for every
  `e` with `e - 1` a prime power (Theorem 29.9, Corollary 29.10). It is never
  more than `omega(B - 1) + 1`, and equal to `omega(B - 1)` for every
  `e <= 10` and every census base (Theorem 29.11, Remark 29.12).
- Assumption R of chapter 13 is false as stated for short strings. The
  refined Poisson theorem needs only one number per base, an exponential sum
  `rho(b)` of `x^x - x` modulo `b - 1` (Theorem 29.15).
- The refined coupled model of chapter 13 has its bivariate Poisson law in
  the limit for every base, without Assumption R (Theorem 30.5). The proof
  is a Littlewood-Offord argument: the weights of the small digits grow so
  fast that their sum fixes their counts (Lemma 30.2, Theorem 30.3). The
  rate is weak, `exp(-c ln b / ln ln b)`.
- Assumption R for prime `b - 1` follows from a bound `O(p)` on the
  collisions `x^x - x == y^y - y (mod p)` (Corollary 30.8).
- A 2-digit string `(a, c)` with `c >= 1` is a solution exactly when `c` is
  a fixed point of `x -> x^x` modulo `a`. So for almost all primes `p` some
  `(p, c)` with `2 <= c < p` is a solution, and none is when
  `p == 3 (mod 8)` and `(p-1)/2` is prime (Corollary 30.11, from Kurlberg,
  Luca and Shparlinski).
- Base `b` has exactly `tau(b^2 + 1) - 2` two-digit narcissistic numbers
  (Theorem 30.12). Every odd base has some. An even base has none exactly
  when `b^2 + 1` is prime, so whether infinitely many bases have none is
  Landau's problem. The mean over odd bases is twice the mean over even
  bases, `(4/pi) ln X` against `(2/pi) ln X` (Proposition 30.14).
- Deciding whether a base has a solution is an NP problem on a tally language.
  So a proof that no fast algorithm exists would prove P != NP, and NP-hardness
  would prove P = NP (section 8.1).

Computed:

- All solutions in bases 2 to 41, both conventions (`output/`). Bases 2 to 35
  agree with OEIS A166623.
- Every solution with 3, 4, 5 or 6 digits in every base up to `10^51`,
  `10^18`, `10^8` and `10^4` respectively (chapter 3).
- Under `0^0 = 1` there are exactly two 4-digit solutions in all these bases:
  3435 in base 10 and `(6,5,3,4)` in base 20.
- Under `0^0 = 1` the only 4-digit solutions in all bases up to `10^186` are
  3435 and `(6,5,3,4)`; the 5-digit list is complete up to `10^30.9`, the
  6-digit one up to `10^11` (section 11.5).
- Base -10 has 404201091 = `(4,0,5,8,1,9,1,1,1)` and two more solutions
  under `0^0 = 1` (section 12.3).
- Under `0^0 = 1` no base up to 100,000 has a 9-digit solution, and no base up
  to 10,000 has one with 18, 21, 22, 24, 26 or 28 digits.
- Under `0^0 = 1`, base 25 is the only base below `10^51` with both a
  2-digit and a 3-digit solution: `(1,3)` and `(5,1,3)` (section 18.2).
- Under `0^0 = 1` no new 7-digit solution exists in bases up to `10^7.2`,
  nor an 8-digit one up to base 23,364 (section 19.1.5).
- Under `0^0 = 1` no base up to `10^3301` has a 3-digit solution other than
  the six known ones, and every such base has at most two (Theorem 25.11,
  section 25.3).
- `rho(b) <= 0.82` for every base from 12 to 6000. So the refined Poisson
  theorem of chapter 13 holds without assumption in that range (Corollary
  29.16, computer-assisted).
- `k(B) = omega(B - 1)` in all 110,654 monic bases of the scanned degrees and in
  379,700 polynomials of the factor types that the proofs leave open
  (section 29.2.4).
- For every prime `11 <= p < 10^5`, the shifted map `x^x - x` has about
  `2 (p - 1)` collisions, like a random map, while `x^x` follows the
  Holden-Moree prediction, about `2.64 (p - 1)` (Table 30.2.1).
- The conjecture "no `b`-digit solution" is false under `0^0 = 0` (bases 15
  and 16) and true under `0^0 = 1` up to base 45 (section 8.6).

Model:

- A large base has about one nontrivial solution per convention, with `b-1`
  digits in 55% of cases. Odd bases have twice as many under `0^0 = 0`.
  Perturbed weights show that the residues of `x^x` cause this (section 9.6).
- About 17% of even and 8% of odd bases near base 40 have no solution
  (section 9.7). The large-base limits are 20% and 9% (section 4.5).
- The number of solutions in a base is a Poisson draw with the mean of its
  near-solution counts `n - F(n) = D` (section 11.1).
- The random-polynomial view, with local factors, explains the short
  solutions, and says the short lists are complete (section 11.4).
- A search that misses a few percent of solutions grows about 1.71x per
  base instead of 1.89x (section 9.3). The `--zscore` rule keeps its miss rate
  near 2% from base 30 to 300 (section 10.3). With `--zlaw cond` its threshold
  maps to a fixed miss rate (3.4 for about 2%, 3.8 for about 1%) and it visits
  1.1 to 1.3x fewer nodes at equal miss rate; stacked with `--hybrid` it ran
  3.1x faster than CPU `--zscore 3` at base 38 (chapter 28).
- The exact tree grows like `2^b` in the limit (section 10.1).
- Under `0^0 = 1`, long solutions lie within `ln k + ln ln k` of their length
  `k`, apart from algebraic families (Conjecture 10.3).
- Narcissistic numbers (weights `x^d`) fit the refined model where residues
  are forced: 207 found against 208.5 predicted (section 19.4).
- In every number system with a residue identity, the count factor follows
  its modulus: doubling exactly when it is even, a factor `q` per prime factor
  in `F_q[T]`. The coincidence model fails in the factorial number system,
  where large digits are tied to top positions (chapter 21).
- In base `-1+i` positive integers have exactly the lengths `== 1, 4 (mod 8)`,
  so its census is complete (section 23.4).
- In `F_q[T]` the model fails because Frobenius makes the digits of `F` far
  from uniform. The integer analog is only the forced top digits, a correction
  of a few percent (chapter 24).
- Near-solutions at different offsets are not independent: rearranging digits
  keeps `F` and moves the offset by a multiple of `b - 1` (Lemma 26.1). With
  the corrected calibration no verdict about the solutions changes, but the
  excess per-base scatter of the model is about half an artefact (chapter 26).
- A model of `F_q[T]` that keeps the Frobenius blocks and randomizes only the
  generating digits predicts the census within 3% to 9% in total, against
  18% to 33% for the refined model (Heuristic 29.20). The types with a
  repeated factor of `B - 1` are what it still misses.
- In the factorial system, a model that keeps the true top digits of `F`
  closes about half the lengths, among them all 8 lengths from 10 to 26
  without near-solutions. Open below `34!`: lengths 8, 10, 13, 14, 15, 18,
  19, 20, 24, 26, 28, 29, 30, 32. The empty census has probability 0.22 to
  0.39 after a cluster calibration (section 29.5).
- At length 2 the coincidence model is short by a factor of order `ln b`
  for narcissistic numbers: it misses the local factors at the primes of
  `b^2 + 1` (section 30.3.4). The shifted collisions should be
  `(2 + o(1)) (p - 1)` (Conjecture 30.9).
- Base 100 is expected to have about one solution, most likely with 99 digits.

## Scripts and data

Everything is reproducible with the scripts in `analysis/`:

| script | produces |
|---|---|
| `catalog.py` | one catalog of all known solutions |
| `structure.py` | the balance classification of every solution |
| `kdigit.py` | every `k`-digit solution in every base up to a bound |
| `model.py`, `refined.py` | the probabilistic model and its comparison with the data |
| `counts.py` | the per-base table and the Poisson comparison |
| `correlation.py`, `distance.py` | the tests for hidden correlations |
| `selfpaying.py` | bases with self-paying digits |
| `verify_constructions.py` | exact checks of the constructions in chapter 2 |
| `tree.py`, `typical.py` | measurements of the search tree |
| `tree_model.py` | the formula for the size of the search tree |
| `walk.py`, `miss_rates.py`, `min_deficit.py`, `scaled_thresholds.py` | miss rates of the inexact rules, by replaying real and planted solutions |
| `inexact_sweep.py` | speed and misses of the inexact search |
| `perturb_experiment.py`, `emptiness_experiment.py` | tests of the model with perturbed weights |
| `empty_bases.py`, `record_bases.py`, `lengths_vs_base.py` | empty bases, bases with many solutions, length against base |
| `exponents.py` | growth rates of the exact tree and of its likely part |
| `zscore_sweep.py`, `min_zscore.py` | speed and misses of the `--zscore` rule |
| `dynamics.py` | orbits of `n -> F(n)` |
| `length_window.py`, `length_window2.py`, `length_law.py` | the length window against the model |

`analysis/data/` holds the lists of short solutions and the search of bases
39 to 127 for numbers with at most 30 digits.
