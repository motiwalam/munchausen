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

A full build of the project takes about 3 minutes after Mathlib is cached. The
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
| `Munchausen/Basic.lean` | chapter 1: length bound, finitely many solutions per base, digit bound, one base per string, the two conventions |
| `Munchausen/Congruences.lean` | section 1.6, Proposition 10.2, Theorem 15.2, Corollary 15.3 |
| `Munchausen/Constructions.lean` | chapter 2 (twins, self-paying digits, swaps, 2-digit solutions, Proposition 2.7) and chapter 22 (splits, blocks, binomial families) |
| `Munchausen/Polynomial.lean` | `Q_s`, local obstructions (11.1, 19.1), the test modulo 2 (15.11), negative bases (12.2, 12.3) |
| `Munchausen/Residues.lean` | residues of `x^x - x` modulo 27 and 81, Lemma 20.6, the coverings 15.13 and 20.13 |
| `Munchausen/ShortEquations.lean` | Propositions 18.1, 16.5, 20.20, Lemma 18.14, Theorem 15.7 |
| `Munchausen/OtherSystems.lean` | negative bases (14.4, 14.5), the factorial system (21.14, 21.15), `F_p[T]` (21.1, 21.3, 21.5, 24.1), base `-1+i` (23.1) |
| `Munchausen/Examples.lean` | concrete solutions checked by `decide`, and `(1,6,46666)` in base `46666^23333 - 3` |
| `Munchausen/Conjectures.lean` | open problems as named `Prop`s, and proofs that refuted conjectures are false |

## Adding a result

1. Put the statement in the file for its theme, with a docstring that states
   it in words and cites the library, for example
   "**Proposition 1.3** (section 1.4)".
2. Run `lake build`. It must pass with no `sorry`.
3. Add or update the row in `STATUS.md`.
