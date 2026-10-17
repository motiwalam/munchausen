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
- Under `0^0 = 1` no base up to 127 has a solution with 9, 18, 21, 22, 24, 26
  or 28 digits.
- The conjecture "no `b`-digit solution" is false under `0^0 = 0` (bases 15
  and 16) and true under `0^0 = 1` up to base 41.

Model:

- A large base has about one nontrivial solution per convention, with `b-1`
  digits in 55% of cases. Odd bases have twice as many under `0^0 = 0`.
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

`analysis/data/` holds the lists of short solutions and the search of bases
39 to 127 for numbers with at most 30 digits.
