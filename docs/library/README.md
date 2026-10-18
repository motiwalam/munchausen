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
| [Open questions](questions.md) | 30 research questions, with priorities |

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
- Short solutions under `0^0 = 1` with one large digit are finite in the
  square class, with an explicit bound (Theorem 8.3).
- Base `n^(n-1)` has at least `2^(n-1) - 2` solutions under `0^0 = 0`, and
  at most `X^(1/(c+1))` bases up to `X` have `c` self-paying digits
  (section 9.8).
- In the model, every search that walks the digit tree from the top needs
  about `1.638^b` nodes, exact or not (Theorem 10.1). The only residue that
  the digit multiset determines is `n mod (b-1)` (Proposition 10.2).
- Up to `B`, at most a power of `ln B` bases have a solution with a fixed
  number of digits (Proposition 10.4).
- Almost all bases have no solution with fewer than `(1/2 - eps) ln b / ln ln b`
  digits (Theorem 11.2).
- A digit string whose polynomial `Q_s` has no root modulo some prime is not a
  solution in any base (Proposition 11.1). If `Q_s` is irreducible, this
  happens for a positive density of primes (Proposition 12.1).
- Munchausen numbers in negative bases have an odd number of digits
  (Proposition 12.2); 3-digit solutions with `s_1 | s_2` have a partner in a
  negative base (Proposition 12.3).
- Under `0^0 = 1`, base 3 is the only base with two 2-digit solutions
  (Theorem 15.7).
- The Aurifeuillian factors `L < M` of `x^x + 1` satisfy `M / L -> e^2`
  (Theorem 16.1). This explains `(1,7,1)` in base 904 and why no larger `x`
  works the same way; `b(b+x) = x^x + 1` has no further solution for `x` up to
  `4 * 10^9`, and the abc conjecture would rule them out entirely.
- With arbitrary weights in place of `x^x`, deciding whether a solution exists
  is NP-complete and counting them is #P-complete (chapter 13). Any fast
  algorithm for real Munchausen numbers must use the arithmetic of `x^x`.
- Infinitely many digit strings are excluded in every base by covering
  congruences with moduli `3^e` and `2^e`; `(2,1,x)` is never a solution
  (chapter 15).
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
- The conjecture "no `b`-digit solution" is false under `0^0 = 0` (bases 15
  and 16) and true under `0^0 = 1` up to base 41.

Model:

- A large base has about one nontrivial solution per convention, with `b-1`
  digits in 55% of cases. Odd bases have twice as many under `0^0 = 0`.
  Perturbed weights show that the residues of `x^x` cause this (section 9.6).
- About 17% of even and 8% of odd bases have no solution (section 9.7).
- The number of solutions in a base is a Poisson draw with the mean of its
  near-solution counts `n - F(n) = D` (section 11.1).
- The random-polynomial view, with local factors, explains the short
  solutions, and says the short lists are complete (section 11.4).
- A search that misses a few percent of solutions grows about 1.71x per
  base instead of 1.89x (section 9.3). The `--zscore` rule keeps its miss rate
  near 2% from base 30 to 300 (section 10.3).
- The exact tree grows like `2^b` in the limit (section 10.1).
- Under `0^0 = 1`, long solutions lie within `ln k + ln ln k` of their length
  `k` (Conjecture 10.3).
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
