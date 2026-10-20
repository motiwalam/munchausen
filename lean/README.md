# Munchausen: a Lean 4 formalization

This project formalizes the library of facts about Munchausen numbers in
`docs/library/`. It uses Lean 4.35.0 and Mathlib v4.35.0.

`STATUS.md` maps every proven or cited result of the library to its Lean name
and status. Extend that table when you add a result.

## Build

```
export PATH="$HOME/.elan/bin:$PATH"
cd lean
lake exe cache get   # only once, downloads the Mathlib build
lake build
```

A full build of the project takes about 5 minutes after Mathlib is cached. The
build has no `sorry`, no new `axiom` and no `native_decide`. Concrete examples
use `decide`, which the kernel checks.

## Conventions

- `w m x` is the weight of a digit: `x ^ x` for `x ≥ 1` and `m` for `x = 0`.
  The parameter `m` is the convention `0^0 = m`.
- `F b m n` is the sum of the weights of the base-`b` digits of `n`
  (`Nat.digits`), and `IsMunchausen b m n` says `F b m n = n`.
- Digit strings are lists written most significant digit first, as in the
  library: `(3,4,3,5)` is `[3, 4, 3, 5]`.
- `P b s` is the value of a string in any commutative semiring, so the same
  definition serves positive bases, negative bases (`b : ℤ`) and the
  polynomial `P_s(r)` (`b = X`).
- `IsSolution b m s` says that `s` has digits below `b`, a nonzero leading
  digit and `P b s = Fs m s`. `IsNegSolution b m s` is the same in base `-b`.
- `Q m s : ℤ[X]` is the Munchausen polynomial `P_s(r) - F(s)`.
- Mathlib writes 0 with no digits, so `IsMunchausen b m 0` holds for every
  `m`. The library calls 0 and 1 trivial; results about nontrivial solutions
  assume `2 ≤ n` or strings of length at least 2.

## Layout

| file | contents |
|---|---|
| `Munchausen/Defs.lean` | weights, `F`, `IsMunchausen`, strings, `P`, `IsSolution`, `Q`, self-paying digits |
| `Munchausen/Basic.lean` | chapter 1: length bound, finitely many solutions per base, digit bound, one base per string, the two conventions, the top digit (1.7) |
| `Munchausen/Congruences.lean` | section 1.6, Proposition 10.2, Theorem 15.2, Corollary 15.3 |
| `Munchausen/Constructions.lean` | chapter 2 (twins, self-paying digits and the converse of 2.2, swaps, 2-digit solutions, Corollary 2.4, Proposition 2.7), Propositions 4.2, 8.5 and 15.15, Theorems 9.2 and 15.9, chapter 22 (splits, blocks, binomial families) and Theorem 25.5 |
| `Munchausen/SelfPayingDigits.lean` | Proposition 2.3 (moves and cores), Propositions 8.6, 15.4, 15.5 and 15.8, Theorem 15.14 (chains and cycles), the counts of Propositions 8.5 and 9.3 |
| `Munchausen/Counting.lean` | Propositions 4.1 and 10.4, the finite form of Theorem 11.2 |
| `Munchausen/AlmostAll.lean` | Theorems 11.2 and 20.3: almost all bases have no short solution, by the string count and by the multiset count |
| `Munchausen/BaseWindow.lean` | Lemma 20.1 and Proposition 15.17 (the window of the base), Proposition 20.2, Lemma 20.4 |
| `Munchausen/Polynomial.lean` | `Q_s`, local obstructions (11.1, 19.1), the test modulo 2 (15.11), negative bases (12.2, 12.3), rational roots (16.15) |
| `Munchausen/Residues.lean` | residues of `x^x - x` modulo 27 and 81, Lemmas 20.6, 20.7, Theorem 20.8, the coverings 15.13 and 20.13 |
| `Munchausen/AdicLaws.lean` | Theorem 20.11 (the 3-adic law), Theorem 20.12 (the 5-adic law) and Lemma 15.12 (1) |
| `Munchausen/ShortEquations.lean` | Propositions 18.1, 16.5, 20.20, Lemma 18.14, Theorem 15.7 |
| `Munchausen/LocalTests.lean` | Proposition 16.8, section 19.1.1, Lemma 20.21, the families of 11.3 and 12.3 |
| `Munchausen/ThreeDigits.lean` | Theorem 8.3, Theorem 25.2, Corollary 25.3, Theorem 25.7 (ii) and (iii), Lemma 25.13, Corollary 25.14 |
| `Munchausen/ThreeDigitBases.lean` | Theorem 25.7 (i), Propositions 25.9, 25.16, 25.17, Theorems 25.10 and 25.15 |
| `Munchausen/OtherSystems.lean` | negative bases (14.4, 14.5, 14.6), the factorial system (21.14, 21.15), `F_p[T]` (21.1, 21.3, 21.5), base `-1+i` (23.1), section 17.2 |
| `Munchausen/FunctionField.lean` | base-`B` expansions in `F_p[T]`: Corollary 21.2, Propositions 21.3, 21.4, Theorem 21.7, chapter 24 (Lemmas 24.1, 24.5, 24.7, 24.8, Propositions 24.2, 24.6, 24.11, Corollaries 24.3, 24.4, 24.12 (1)) |
| `Munchausen/Search.lean` | chapters 26 and 27: the swap lemma, the fibre (26.3), the image of `F`, bottom digits, Lemma 27.3 and Theorem 27.5 in the interval oracle |
| `Munchausen/Applications.lean` | chapter 30: Lemmas 30.1, 30.2, 30.4, Propositions 30.6, 30.7, 30.10, Corollaries 30.11, 30.13, Theorem 30.12 (the completed square), Proposition 30.14 (the divisor pairing) |
| `Munchausen/TwoSquares.lean` | the count of Theorem 30.12 (`tau(b^2 + 1) - 2` two-digit narcissistic numbers) with Gaussian integers, and both directions of Corollary 30.13 (2) |
| `Munchausen/ModelTheorems.lean` | chapter 29: Lemma 29.2, `k(B)` and Berlekamp's count, Theorems 21.6 and 29.11 (1), (3), Corollary 29.10 (the factor), Lemma 29.14 |
| `Munchausen/SearchRules.lean` | chapters 31 and 32: the residue rule (31.1), the interval (31.4, 31.5), the Pell form of `(p, q, x)` and `(p, x, q)`, the sieve |
| `Munchausen/Factorials.lean` | chapter 33: factorions and other weights (33.9, 33.12, 33.13), the completed square, Lemmas 33.1, 33.2, Theorem 33.4 (b), (d), Proposition 33.21, Theorem 33.16 for `x^x` and for factorials, and Theorem 15.10, with abc as a hypothesis |
| `Munchausen/ModelComplete.lean` | chapter 34: the two conventions (34.2, 34.3), `N_1(b)` (34.5), the residues of the `d`-digit numbers (34.10), the parity character (34.11, 34.12) |
| `Munchausen/Existence.lean` | chapter 35: the root factor as a sum over residues (35.3), the invariant ideal of a positional system (35.5, 35.6), the share of multisets without small digits (35.9), the last step of Theorem 35.13 |
| `Munchausen/Examples.lean` | concrete solutions checked by `decide`, and `(1,6,46666)` in base `46666^23333 - 3` |
| `Munchausen/Conjectures.lean` | open problems as named `Prop`s, and proofs that refuted conjectures are false |

## Adding a result

1. Put the statement in the file for its theme, with a docstring that states
   it in words and cites the library, for example
   "**Proposition 1.3** (section 1.4)".
2. Run `lake build`. It must pass with no `sorry`.
3. Add or update the row in `STATUS.md`.
