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
- Under `0^0 = 1` no base up to 100,000 has a 9-digit solution, and no base up
  to 10,000 has one with 18, 21, 22, 24, 26 or 28 digits.
- The conjecture "no `b`-digit solution" is false under `0^0 = 0` (bases 15
  and 16) and true under `0^0 = 1` up to base 41.

Model:

- A large base has about one nontrivial solution per convention, with `b-1`
  digits in 55% of cases. Odd bases have twice as many under `0^0 = 0`.
  Perturbed weights show that the residues of `x^x` cause this (section 9.6).
- About 17% of even and 8% of odd bases have no solution (section 9.7).
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
