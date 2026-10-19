# Formalization status

This table maps the proven and cited results of `docs/library/` to Lean. All
Lean names live in the namespace `Munchausen`. The file is given in brackets.

Status values:

- **formalized**: the statement is proven in Lean, with no `sorry`.
- **partial**: a named part is proven; the row says which part is missing.
- **conjecture**: stated as a `Prop` in `Conjectures.lean`, not proven.
- **refuted**: stated as a `Prop`, and its negation is proven.
- **not formalized**: the reason is given. The usual reasons are model
  statements (heuristics about random digits), large computations, and deep
  cited theorems (Chebotarev, Laurent, Matveev, Faltings, Szalay, Bertrand is
  in Mathlib and was used).

Abbreviations of the files: Defs, Basic, Cong (Congruences), Cons
(Constructions), Poly (Polynomial), Res (Residues), Short (ShortEquations),
Other (OtherSystems), Ex (Examples), Conj (Conjectures).

Counts of table rows at the time of writing: 64 formalized (one of them a
list of computed solutions checked by `decide`), 8 partial, 10 rows of open
problems (13 `Prop`s), 4 refuted conjectures, 87 not formalized and 2 not
stated.

## Chapter 1. Basics

| result | Lean name | status |
|---|---|---|
| definitions (1.1): `w`, `F`, solutions | `w`, `Fs`, `F`, `IsMunchausen`, `P`, `IsSolution` [Defs] | formalized |
| strings against numbers | `isMunchausen_iff_isSolution`, `IsSolution.isMunchausen`, `digits_P` [Basic] | formalized |
| Proposition 1.1 (at most `b` digits) | `length_digits_le`, `lt_pow_self` [Basic] | formalized |
| finitely many solutions per base (1.2) | `finite_setOf_isMunchausen` [Basic], `finite_setOf_isSolution` [Conj] | formalized |
| Proposition 1.2 (`x^x < b^k`) | `pow_self_lt_of_mem_digits` [Basic] | formalized |
| Proposition 1.3 (one base per string) | `IsSolution.base_unique`, `P_strictMono` [Basic] | formalized |
| Proposition 1.4 (`F_1 = F_0 + z`) | `Fs_one_eq`, `F_one_eq`, `isMunchausen_one_iff_zero`, `not_both_of_mem` [Basic] | formalized |
| `n ≡ digit sum (mod b-1)` (1.6) | `P_modEq_sum`, `sub_one_dvd_P_sub_sum` [Cong] | formalized |
| Proposition 1.5 | `Fs_modEq_sum`, `IsSolution.Fs_modEq_sum` [Cong] | formalized |
| 1.6: odd base, `m = 1`, even number of zeros | `IsSolution.even_count_zero` [Cong] | formalized |
| 1.6: odd base, `m = 0`, condition mod 2 free | `Fs_zero_modEq_two` [Cong] | formalized |
| 1.6: `b ≡ 1 (mod 4)`, `m = 0` | `IsSolution.even_countP_mod_four`, `pow_self_modEq_four` [Cong] | formalized |
| 1.6: `b ≡ 1 (mod 3)`, `m = 0` | `IsSolution.three_dvd_countP_mod_six`, `pow_self_modEq_three` [Cong] | formalized |
| 1.6: even base, last digit | `IsMunchausen.last_digit_parity` [Cong] | formalized |
| 1.7: digit `b-1` at most twice in a `(b-1)`-digit solution | `count_top_digit_le_two`, `pow_lt_three_mul` [Basic] | formalized |
| Proposition 1.6 (`b ≥ 7`, three copies of `b-1`) | none | not formalized (needs `2(1-1/b)^(b-1) + (1-2/b)^(b-2) < 1` for all `b ≥ 7`; a truncated binomial bound works, see "Next") |

## Chapter 2. Constructions

| result | Lean name | status |
|---|---|---|
| Proposition 2.1 (twins) | `isSolution_twin`, `isMunchausen_twin` [Cons] | formalized |
| Proposition 2.2 (which bases have self-paying digits) | `selfPaying_of_dvd`, `SelfPaying.exists_pow`, `exists_primitive_root` [Cons] | formalized: the construction, and the converse (a self-paying digit and its base are powers `c^s`, `c^t` of one integer with `t k = s (c^s - 1)`, and every such `c` is a power of one primitive root of `b`) |
| Proposition 2.3 (structure under `0^0 = 0`) | `isSolution_selfPaying_iff`, `SelfPaying.balance` [Cons] | partial: placing or removing one self-paying digit on a 0 below the leading digit; the unique decomposition into core, digits and final 1 is not formalized |
| Corollary 2.4 (`N_0(b) ≥ 2^(C+1) - 2`) | `corollary_2_4`, `isMunchausen_spNum`, `spNum` [Cons] | formalized |
| Proposition 2.5 | `isSolution_selfPaying_cons_iff` [Cons] | formalized |
| swaps (2.3) | `isSolution_swap` [Cons]; `(2,4)` in base 128 [Ex] | formalized |
| Proposition 2.6 (2-digit criterion) | `isSolution_two_iff`, `exists_isSolution_two_iff` [Cons] | formalized |
| 2-digit families (2.4) | `isSolution_one_c`, `isSolution_c_c`, `isSolution_a_one`, `isSolution_a_zero`, `isSolution_one_zero`, `isSolution_two_c` [Cons] | formalized |
| Proposition 2.7 | `isSolution_prop27`, `infinite_bases_of_length` [Cons] | formalized |

## Chapters 3 to 7

| result | Lean name | status |
|---|---|---|
| short solutions of 3.2, 3.3 (computed lists) | examples in [Ex] | each listed solution is checked by `decide`; completeness of the lists is not formalized (large computation) |
| 3.5 table: infinitely many for every length | `infinite_solutions_of_length` [Cons], `infinite_bases_of_length` [Cons] | formalized |
| finiteness conjecture (3.5, 7.2) | `FinitenessConjecture`, `not_finitenessConjecture` [Conj] | refuted |
| missing lengths (3.4, 7.3) | `MissingLengthsConjecture`, `not_missingLengthsConjecture` [Conj] | refuted |
| Proposition 4.1 (`N_{m,k}(b) ≤ 2 (X+1)^(k-1)`) | none | not formalized (counting argument; convexity of `a^a - a b^(k-1)`) |
| Proposition 4.2 (`N_0(b)` unbounded) | `prop4_2`, `count_zero_unbounded` [Cons] | formalized |
| original conjecture 7.1 under `0^0 = 0` | `NoFullLengthConjecture`, `not_noFullLengthConjecture_zero` [Conj] | refuted (base 15) |
| conjecture 7.1 under `0^0 = 1` | `NoFullLengthConjecture_one` [Conj] | conjecture |
| is `N_1(b)` bounded (7.4) | `BoundedCountOne` [Conj] | conjecture |
| infinitely many empty bases (7.4, 8.5) | `InfinitelyManyEmptyBases` [Conj] | conjecture |
| every count occurs (4.4) | `EveryCountOccurs` [Conj] | conjecture |
| chapter 5 (model), chapter 6 (search costs) | none | not formalized (model and computation) |

## Chapter 8. Barriers

| result | Lean name | status |
|---|---|---|
| Proposition 8.1 (`L_m` in NP), Corollary 8.2 | none | not formalized (complexity classes are not in Mathlib) |
| Theorem 8.3 (large leading digit in the square class) | none | not formalized (elementary, but needs care with the explicit bound) |
| Corollary 8.4 and its correction | none | not formalized (depends on a computation; the correction is Proposition 22.8) |
| Proposition 8.5 (self-paying digits not adjacent) | `SelfPaying.position_gt`, `prop8_5_ineq` [Cons] | partial: positions satisfy `k' ≥ 2k + 1` (the proof shows `k' > r k`); the count "fewer than `log2 b` self-paying digits" is not formalized |
| 8.3: under `0^0 = 1` only `(a,1)` from zero-balance placements | `zero_balance_solution`, `selfPaying_of_balance` [Cons] | formalized |
| Proposition 8.6 | none | not formalized (bookkeeping of near-solutions; elementary) |

## Chapters 9 and 10

| result | Lean name | status |
|---|---|---|
| Conjecture 9.1 | none | not formalized (statement about the probabilistic model) |
| Theorem 9.2 (base `n^(n-1)`) | `theorem9_2` [Cons] | formalized |
| Proposition 9.3 (corrected bound `X^(1/(c+1)) + X^(1/(c+2)) log2 X`) | none | not formalized |
| Conjecture 9.4 | `Conjecture_9_4`, `not_conjecture_9_4` [Conj] | refuted (as stated, by Corollary 22.7) |
| Theorem 10.1 | none | not formalized (theorem inside the probabilistic model) |
| Proposition 10.2 (only `b-1` is invariant) | `residue_invariant_iff` [Cong] | formalized |
| Conjecture 10.3 | `Conjecture_10_3_lower` [Conj] | conjecture (second part only; the first part excludes "algebraic families", which the library does not define) |
| Proposition 10.4 | none | not formalized (follows from 1.2 and 1.3 by counting strings; good next step) |

## Chapters 11 and 12. Local obstructions and the polynomial

| result | Lean name | status |
|---|---|---|
| `Q_s` and its values | `Q`, `eval_Q`, `eval_Q_int`, `isSolution_iff_eval_Q` [Defs, Poly] | formalized |
| Proposition 11.1 | `not_isSolution_of_no_root_mod`, `no_int_root_of_no_root_mod` [Poly] | formalized (for every modulus) |
| Theorem 11.2 | none | not formalized (asymptotic counting) |
| covering families `(2,0,x)`, `(4,0,x)`, `(6,0,x)` (11.3) | none | not formalized (parity; follows from Proposition 15.11) |
| Proposition 12.1 | none | not formalized (cites Jordan, Cameron-Cohen and Chebotarev) |
| Proposition 12.2 (odd length in negative bases) | `IsNegSolution`, `IsNegSolution.odd_length` [Poly] | formalized |
| Proposition 12.3 (partners) | `IsSolution.negPartner` [Poly] | formalized |
| negative-base solutions of 12.3 (404201091 and others) | examples in [Ex] | formalized (checked by `decide`) |
| 12.3 family `(x,0,0)` in base `-x^((x-1)/2)` (needs `x` odd or a square) | none | not formalized |

## Chapter 13. Complexity

| result | Lean name | status |
|---|---|---|
| Lemma 13.1, Proposition 13.2, Theorem 13.3, Corollaries 13.4, 13.5, Proposition 13.6 | none | not formalized (complexity theory) |
| Lemma 13.7 to Corollary 13.11 | none | not formalized (probability in the coupled model) |

## Chapter 14. Other number systems

| result | Lean name | status |
|---|---|---|
| Proposition 14.1, Corollary 14.2, Proposition 14.3 | none | not formalized (need the existence of negative-base representations) |
| Proposition 14.4 | `neg_residue_invariant_iff` [Other] | formalized |
| Proposition 14.5 | `IsNegSolution.dvd` [Other] | formalized |
| 14.1.1: odd `b`, `0^0 = 1`, even zeros | `IsNegSolution.even_count_zero` [Other] | formalized |
| Proposition 14.6 (length at most `b+1`) | none | not formalized (odd length is Proposition 12.2; the bound is an inequality like 1.1) |
| Propositions 14.8, 14.9, 14.10 (imaginary and Gaussian bases) | none | not formalized |
| Propositions 14.7, 14.11 | none | not formalized (model) |

## Chapter 15. Dynamics, coverings, constructions

| result | Lean name | status |
|---|---|---|
| Proposition 15.1 | `F_lt_pow_self` [Cong] | partial: `F` maps numbers below `b^b` into themselves; the bijection with multiset cycles is not formalized |
| Theorem 15.2 | `F_modEq_self_iff` [Cong] | formalized |
| Corollary 15.3 | `exists_even_cycle` [Cong] | formalized |
| Propositions 15.4, 15.5 | none | not formalized (follow from 1.4, 2.1 and 2.3) |
| Proposition 15.6 | none | not formalized (model) |
| Theorem 15.7 | `theorem15_7`, `two_two_digit` [Short] | partial: the statement under `0^0 = 1`, proven in full; the `0^0 = 0` variant (twin bases `a^(a-1)`) is not formalized |
| Proposition 15.8 | none | not formalized (the converse of Proposition 2.2 is now available; next step) |
| Theorem 15.9 | `theorem15_9` [Cons] | formalized (for every `a ≥ 2`, as the library now states it) |
| Theorem 15.10 (assuming abc) | none | not formalized (abc is a conjecture; it could be stated as a hypothesis) |
| Proposition 15.11 | `exists_root_mod_two_iff` [Poly] | formalized |
| Lemma 15.12 (1) | `pow_self_modEq_two` [Cong], `multiple_mem_T` [Res] | partial: `x^x - x` is even, and every multiple of 2 occurs modulo `2^e` |
| Lemma 15.12 (2) (`T(p)` is everything for `p ≥ 5`) | none | not formalized (primitive roots and CRT) |
| Lemma 15.12 (3) | `pow_self_modEq_27`, `pow_self_modEq_three_of_ne` [Res] | formalized |
| Theorem 15.13 | `covering_27` [Res] | formalized |
| example `(2,1,x)` | `not_isSolution_two_one` [Res] | formalized |
| Theorem 15.14 (chains and cycles) | none | not formalized |
| Proposition 15.15 | none | not formalized |
| Proposition 15.16 (needs `c ≥ 3` for the pair `(c,1)`) | none | not formalized |
| Proposition 15.17 | none | not formalized (same as Lemma 20.1) |

## Chapter 16. Algebra of the polynomial

| result | Lean name | status |
|---|---|---|
| Proposition 16.1 | none | not formalized (cyclotomic factorization) |
| Theorem 16.2 (`M/L → e^2`) | none | not formalized (analysis of cyclotomic values) |
| Proposition 16.3, Theorem 16.4 | none | not formalized |
| Proposition 16.5 (`x` even or an odd square) | `prop16_5` [Short] | formalized |
| Propositions 16.6, 16.7 | none | not formalized (`x`-adic and unit forms; need `Z_x` and quadratic fields) |
| Proposition 16.8 (3 and 5 never exclude; no finite set of primes suffices) | none | not formalized (elementary, good next step) |
| Proposition 16.9 (abc triple) | none | not formalized |
| Propositions 16.10, 16.11, Theorem 16.12, Corollary 16.13, Theorem 16.14 | none | not formalized (Chebotarev, Galois groups) |
| Proposition 16.15 (rational roots for `k = 3`) | none | not formalized (Gauss's lemma; possible) |
| Proposition 16.16 (no twins for `q > 1`) | none | not formalized (needs the AFS number system) |
| Theorem 16.17 | none | not formalized |

## Chapter 17. Other weights

| result | Lean name | status |
|---|---|---|
| 17.2 identity with forced residues | none | not formalized (same proof as Proposition 1.5) |
| everything else | none | not formalized (computed or model) |

## Chapter 18. The equation `b(b+x) = x^n + 1`

| result | Lean name | status |
|---|---|---|
| Proposition 18.1 (a), (b), (c), (d) | `prop18_1_a`, `prop18_1_b`, `prop18_1_c`, `prop18_1_d` [Short] | formalized |
| Lemmas 18.2, 18.3, Proposition 18.4, Corollary 18.5, Proposition 18.6 | none | not formalized (ideals in real quadratic fields) |
| Theorems 18.7, 18.8, 18.10, Corollaries 18.9, 18.11 | none | not formalized (cite Laurent and Szalay; also computations) |
| Theorem 18.12 | none | not formalized (computation) |
| Proposition 18.13 | none | not formalized (cites abc and Faltings) |
| Lemma 18.14 | `lemma18_14` [Short] | formalized |
| Proposition 18.15 | none | not formalized (computation) |
| Lemma 18.16, Corollary 18.17 | none | not formalized (elementary; the proof gap reported under "Problems found" is fixed in the library) |
| Proposition 18.18, Lemma 18.19 | none | not formalized (heuristic weights; Lemma 18.19 is elementary) |
| Theorem 18.20, Corollary 18.21 | none | not formalized (Gauss sums) |
| Proposition 18.22, Corollary 18.23 | none | not formalized (cite Laurent) |
| Question 12, Question 32 | `Question12`, `Question32` [Conj] | conjecture |

## Chapter 19. Sieve and spectra

| result | Lean name | status |
|---|---|---|
| 19.1.1: any modulus works | `not_isSolution_of_no_root_mod` [Poly] | formalized |
| 19.1.1: CRT and prime powers make other moduli redundant | none | not formalized (easy) |
| 19.3.1: local factors | none | not formalized (Hensel) |
| everything else | none | not formalized (computed or heuristic) |

## Chapter 20. Multisets and residues

| result | Lean name | status |
|---|---|---|
| Lemma 20.1, Propositions 20.2, 20.5, Lemma 20.4, Theorem 20.3 | none | not formalized (counting; Lemma 20.1 and 20.4 are elementary) |
| Lemma 20.6 | `multiple_mem_T` [Res] | formalized |
| Lemma 20.7, Theorem 20.8, Lemma 20.9 | none | not formalized (lifting modulo `p^e`) |
| Lemma 20.10 | none | not formalized (`p`-adic exponential) |
| Theorem 20.11 (3-adic law) | `pow_self_modEq_81` [Res] | partial: the inclusion `T(81) ⊆ 3Z ∪ {2, 29}`, by a finite check over one period of 162; the equality for every `e` is not formalized |
| Theorem 20.12 (5-adic law) | none | not formalized |
| Corollary 20.13 | `covering_81`, `not_isSolution_eight_seven` [Res] | formalized |
| Proposition 20.14 | none | not formalized |
| Lemmas 20.15, 20.16, Proposition 20.17, Theorem 20.18 | none | not formalized (orders in quadratic fields; cites Matveev) |
| Proposition 20.20 | `prop20_20` [Short] | formalized |
| Lemma 20.21 | none | not formalized (parts (a), (c), (d) are elementary like 18.1) |
| Lemma 20.22, Propositions 20.23, 20.24, 20.25, 20.29, Theorems 20.26, 20.27, Corollary 20.28 | none | not formalized (quadratic orders and Laurent) |
| Theorems 20.19, 20.30 | none | not formalized (computation) |
| Question 51 | `Question51_two`, `Question51_three` [Conj] | conjecture |

## Chapter 21. Five more number systems

| result | Lean name | status |
|---|---|---|
| Proposition 21.1 | `ffWeight`, `ffWeight_eq_expand`, `ffWeight_sum_of_degree` [Other] | formalized (for `F_p`, `p` prime) |
| Corollary 21.2 | none | not formalized (needs base-`B` expansions in `F_p[T]`) |
| Proposition 21.3 | `ffWeight_add_C` [Other] | formalized (the weight identity; the family statement needs expansions) |
| Proposition 21.4 | none | not formalized |
| Proposition 21.5 | `sub_one_dvd_ringVal_sub_sum` [Other] | formalized (in any commutative ring) |
| Theorem 21.6, Theorem 21.7 | none | not formalized (traces, expansions) |
| Proposition 21.8 | none | not formalized (cites the AFS representation theorem) |
| Proposition 21.9 | none | not formalized |
| Propositions 21.10 to 21.13 | none | not formalized |
| Proposition 21.14 | `factorial_no_invariant_residue`, `factVal`, `FactValid` [Other] | formalized |
| Proposition 21.15 | `factorial_selfPaying` [Other] | formalized (the library now chooses `p >= 3`, as the Lean proof does) |
| Question 62 (finiteness in the factorial system) | none | not stated |

## Chapter 22. Blocks and binomial families

| result | Lean name | status |
|---|---|---|
| Lemma 22.1 | `split_iff` [Cons] | formalized |
| Definition 22.2, Lemma 22.3 | `P_Fs_append_zeros` [Cons] | formalized |
| Lemma 22.4 | `block_append` [Cons] | formalized |
| Theorem 22.6 | `isSolution_binomial`, `binomDigits`, `mul_P_binomDigits` [Cons] | formalized |
| Corollary 22.7 | `isSolution_corollary_22_7`, `infinite_solutions_of_length` [Cons] | formalized |
| `(1,2,6)` in base 215, `(1,6,46666)` in base `46666^23333 - 3` | examples, `isSolution_1_6_46666` [Ex] | formalized |
| Proposition 22.8 | none | not formalized (elementary; good next step) |
| Lemma 22.9 | `P_sub_Fs_append_one`, `P_sub_Fs_append_zero` [Cons] | formalized |
| Heuristic 22.5, refined heuristic | none | not formalized (heuristic) |
| Question 65 | `Question65` [Conj] | conjecture |

## Chapter 23. Factorions, negative bases, base `-1+i`

| result | Lean name | status |
|---|---|---|
| Theorem 23.1 (lengths in base `-1+i`) | `gaussian_blocks`, `beta_pow_four`, `blockC` [Other] | partial: the block form (a `{0,1}` string with a real value has blocks `(a, 0, c, c)` and is the base `-4` number with digits `a + 2c`); existence and uniqueness of representations in base `-1+i` and `-4` are cited, not formalized |
| Corollary 23.2 | none | not formalized (needs the uniqueness above) |
| everything else | none | not formalized (computed or heuristic) |

## Chapter 24. The model gap in `F_q[T]`

| result | Lean name | status |
|---|---|---|
| Lemma 24.1 (Frobenius blocks) | `expand_ringVal` [Other] | partial: the identity `n(T^p) = sum d_i(T^p) (B^p)^i`; the digit statement needs uniqueness of expansions |
| Proposition 24.2, Corollaries 24.3, 24.4, Lemma 24.5, Proposition 24.6 | none | not formalized (need base-`B` expansions in `F_p[T]`) |
| Lemmas 24.7, 24.8, 24.9, 24.10 | none | not formalized |
| Proposition 24.11, Corollary 24.12 | none | not formalized (traces) |
| Proposition 24.13, Theorem 24.15, Corollary 24.16 | none | not formalized |

## Chapter 25. Identity families and 3-digit solutions

| result | Lean name | status |
|---|---|---|
| Definition 25.1, Theorem 25.2 (the last digit is large) | none | not formalized (needs a real root of `A` and a derivative argument, or Descartes' rule; next step) |
| Corollary 25.3 | none | not formalized (depends on 25.2) |
| Theorem 25.4 | none | not formalized ((a) is Theorem 22.6 and 25.5 after rescaling; (b), (c) need valuations) |
| Theorem 25.5 | `theorem25_5`, `theorem25_5_conditions` [Cons] | formalized (the prime condition is stated as `c ∣ (j-1)^c`, which is equivalent; the conditions hold for `c = (j-1)^a`) |
| Proposition 25.6 | none | not formalized |
| Theorem 25.7 | none | not formalized (completing the square; same work as Theorem 8.3 and Proposition 22.8) |
| Conjecture 25.8 | none | not stated (it refers to "the two linear families"; could be stated with Theorems 22.6 and 25.5) |
| Proposition 25.9, Theorem 25.10 | none | not formalized (elementary, needs Theorem 25.7) |
| Theorem 25.11, Heuristic 25.12 | none | not formalized (computation, heuristic) |
| Lemma 25.13, Corollary 25.14 | none | not formalized (elementary; good next step) |
| Theorem 25.15 | none | not formalized |
| Propositions 25.16, 25.17 | none | not formalized (elementary given the family shape) |
| Question 50 (at most two 3-digit solutions per base) | `Question50` [Conj] | conjecture |
| Question 65 (the next 3-digit solution) | `Question65` [Conj] | conjecture (the family part is Theorem 25.10, not formalized) |

## Open questions stated as `Prop`s

`FinitenessConjecture` (refuted), `MissingLengthsConjecture` (refuted),
`Conjecture_9_4` (refuted), `NoFullLengthConjecture 0` (refuted),
`NoFullLengthConjecture_one`, `BoundedCountOne`, `InfinitelyManyEmptyBases`,
`EveryCountOccurs`, `Conjecture_10_3_lower`, `Question65`, `Question50`,
`Question36`, `Question39`, `Question12`, `Question32`, `Question51_two`,
`Question51_three`. All are in `Conjectures.lean`. The round 5 questions (72
to 89) are research directions and are not stated.

## Problems found

Items 1 and 2 and the hypothesis of Theorem 15.9 were fixed in the library
(commit ba0b75f).

1. **Proposition 21.15** (section 21.5.1). The proof takes a prime `p` with
   `i/2 < p <= i` from Bertrand's postulate and then uses
   `a - 1 >= p - 1 >= 2`. For `i = 3` the interval `(1.5, 3]` contains
   `p = 2`, and then `p - 1 = 1`, so the step fails for that choice. The
   statement is true: for `i = 3` take `p = 3`, and for `i >= 4` every
   Bertrand prime in `(i/2, i]` is at least 3. The Lean proof
   (`factorial_selfPaying`) chooses `p >= 3` this way.
2. **Lemma 18.16** (section 18.3), found while reading, not formalized. The
   proof says "the largest digit `d'` of `R` is at most `c`". For `c = 0`,
   `R` can be the single digit 1, since `w(1) = w(0) = 1` under `0^0 = 1`;
   then `d' = 1 > c`. The right claim is `w(d') <= w(c)`. The conclusions of
   the lemma still hold, because for `c <= 1` the proof only uses
   `w(c) = 1`.
3. **Convention for 0.** Mathlib gives 0 no digits, so `F(0) = 0` and 0 is a
   solution under `0^0 = 1` in the Lean definitions. The library treats 0 as
   a solution only under `0^0 = 0` (section 1.1). This is a difference in
   definitions, not an error. Every Lean theorem about nontrivial solutions
   assumes `n >= 2` or a nonempty string.

The library corrections that landed during this work (Proposition 9.3, the
pair `(c, 1)` in Proposition 15.16 needs `c >= 3`, the negative-base family
`(x, 0, 0)` needs `x` odd or a square, the renumbering of chapters 16, 23 and
24) touch only rows that are not formalized yet, or citations, which now use
the new numbers.

## Next

In order of value and effort:

1. Proposition 10.4 and Theorem 11.2 type counts: strings with digits up to
   `X` and one base each.
2. Propositions 15.8, 9.3 (corrected), Theorem 15.9, and the count in
   Proposition 8.5, now that the converse of Proposition 2.2 is formalized.
3. The unique decomposition of Proposition 2.3 (core, self-paying digits,
   final 1).
4. Proposition 22.8, Theorem 8.3 and Theorem 25.7 (completing the square for
   3 digits), then Theorem 25.2 and Lemma 25.13 / Corollary 25.14.
5. Proposition 1.6 (a truncated binomial bound for `(1 + 1/n)^n`).
6. Lemma 15.12 (2) and Theorem 20.8 (primitive roots, lifting).
7. Theorem 15.7 under `0^0 = 0`, Propositions 15.16 and 18.16/18.17.
8. Base-`B` expansions in `F_p[T]`, for Corollary 21.2, Theorem 21.7 and
   chapter 24.
