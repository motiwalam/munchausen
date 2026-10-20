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
(Constructions), SPD (SelfPayingDigits), Count (Counting), Almost (AlmostAll),
Window (BaseWindow), Poly (Polynomial), Res (Residues), Adic (AdicLaws), Short
(ShortEquations), Local (LocalTests), Three (ThreeDigits), TDB
(ThreeDigitBases), Other (OtherSystems), FF (FunctionField), Search, Ex
(Examples), Conj (Conjectures), MT (ModelTheorems), App (Applications), SR
(SearchRules), Fact (Factorials), MC (ModelComplete), Exist (Existence), TS (TwoSquares).

Counts of table rows at the time of writing: 155 formalized (one of them a
list of computed solutions checked by `decide`), 24 partial, 12 rows of open
problems (15 `Prop`s), 4 refuted conjectures, 79 not formalized and 5 not
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
| Proposition 1.6 (`b ≥ 7`, three copies of `b-1`) | `prop1_6`, `prop1_6_ineq`, `large_case` [Basic] | formalized (`b ≤ 60` by `decide`, `b ≥ 61` with `log` and `exp` bounds) |

## Chapter 2. Constructions

| result | Lean name | status |
|---|---|---|
| Proposition 2.1 (twins) | `isSolution_twin`, `isMunchausen_twin` [Cons] | formalized |
| Proposition 2.2 (which bases have self-paying digits) | `selfPaying_of_dvd`, `SelfPaying.exists_pow`, `exists_primitive_root` [Cons] | formalized: the construction, and the converse (a self-paying digit and its base are powers `c^s`, `c^t` of one integer with `t k = s (c^s - 1)`, and every such `c` is a power of one primitive root of `b`) |
| Proposition 2.3 (structure under `0^0 = 0`) | `isSolution_selfPaying_iff` [Cons], `isMunchausen_add_selfPaying`, `isMunchausen_iff_core`, `digitAt` [SPD] | formalized (one move at any zero position, also above the leading digit, and removal of any set of self-paying digits; with Proposition 2.1 for the final 1 this is the decomposition) |
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
| Proposition 4.1 (`N_{m,k}(b) ≤ 2 (X+1)^(k-1)`) | `prop4_1`, `solStrings`, `card_le_two_of_convex` [Count] | formalized |
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
| Theorem 8.3 (large leading digit in the square class) | `theorem8_3`, `theorem8_3_one` [Three] | formalized (the explicit bound is stated as three inequalities in `x`, `Z`, `B`, `k`, which hold for large `x`) |
| Corollary 8.4 and its correction | none | not formalized (depends on a computation; the correction is Proposition 22.8) |
| Proposition 8.5 (self-paying digits not adjacent, fewer than `log2 b`) | `SelfPaying.position_gt`, `prop8_5_ineq` [Cons], `card_selfPaying_lt_log` [SPD] | formalized (positions `k' ≥ 2k + 1`; the proof shows `k' > r k`) |
| 8.3: under `0^0 = 1` only `(a,1)` from zero-balance placements | `zero_balance_solution`, `selfPaying_of_balance` [Cons] | formalized |
| Proposition 8.6 | `prop8_6`, `prop8_6_iff`, `SPFill` [SPD] | formalized (each self-paying digit placed on a 0 lowers the defect by 1; a filled string satisfies the equation exactly when the zeroed string has defect `j`) |

## Chapters 9 and 10

| result | Lean name | status |
|---|---|---|
| Conjecture 9.1 | none | not formalized (statement about the probabilistic model) |
| Theorem 9.2 (base `n^(n-1)`) | `theorem9_2` [Cons] | formalized |
| Proposition 9.3 (corrected bound `X^(1/(c+1)) + X^(1/(c+2)) log2 X`) | `prop9_3`, `selfPaying_base_pow`, `card_pow_le` [SPD] | formalized |
| Conjecture 9.4 | `Conjecture_9_4`, `not_conjecture_9_4` [Conj] | refuted (as stated, by Corollary 22.7) |
| Theorem 10.1 | none | not formalized (theorem inside the probabilistic model) |
| Proposition 10.2 (only `b-1` is invariant) | `residue_invariant_iff` [Cong] | formalized |
| Conjecture 10.3 | `Conjecture_10_3_lower` [Conj] | conjecture (second part only; the first part excludes "algebraic families", which the library does not define) |
| Proposition 10.4 | `prop10_4`, `basesWith`, `stringsLE` [Count] | formalized |

## Chapters 11 and 12. Local obstructions and the polynomial

| result | Lean name | status |
|---|---|---|
| `Q_s` and its values | `Q`, `eval_Q`, `eval_Q_int`, `isSolution_iff_eval_Q` [Defs, Poly] | formalized |
| Proposition 11.1 | `not_isSolution_of_no_root_mod`, `no_int_root_of_no_root_mod` [Poly] | formalized (for every modulus) |
| Theorem 11.2 | `theorem11_2`, `shortBases`, `shortBases_card_le` [Almost], `theorem11_2_finite` [Count] | formalized (for `α, δ > 0` and all large `B`, at most `B^(2α + δ)` bases; `α = 1/2 - ε` is the library's form) |
| covering families `(2,0,x)`, `(4,0,x)`, `(6,0,x)` (11.3) | `not_isSolution_even_zero` [Local] | formalized (every even first digit, `x ≥ 1`) |
| Proposition 12.1 | none | not formalized (cites Jordan, Cameron-Cohen and Chebotarev) |
| Proposition 12.2 (odd length in negative bases) | `IsNegSolution`, `IsNegSolution.odd_length` [Poly] | formalized |
| Proposition 12.3 (partners) | `IsSolution.negPartner` [Poly] | formalized |
| negative-base solutions of 12.3 (404201091 and others) | examples in [Ex] | formalized (checked by `decide`) |
| 12.3 family `(x,0,0)` in base `-x^((x-1)/2)` (needs `x` odd or a square) | `isNegSolution_x_0_0`, `isNegSolution_x_0_0_odd`, `isNegSolution_x_0_0_sq` [Local] | formalized (needs `x ≥ 4`; see problem 4) |

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
| Proposition 14.6 (length at most `b+1`) | `prop14_6`, `prop14_6_ineq`, `neg_base_odd_lower`, `IsNegSolution.odd_length` [Other, Poly] | formalized (with odd length this gives `d ≤ b` for odd `b`) |
| Propositions 14.8, 14.9, 14.10 (imaginary and Gaussian bases) | none | not formalized |
| Propositions 14.7, 14.11 | none | not formalized (model) |

## Chapter 15. Dynamics, coverings, constructions

| result | Lean name | status |
|---|---|---|
| Proposition 15.1 | `F_lt_pow_self` [Cong] | partial: `F` maps numbers below `b^b` into themselves; the bijection with multiset cycles is not formalized |
| Theorem 15.2 | `F_modEq_self_iff` [Cong] | formalized |
| Corollary 15.3 | `exists_even_cycle` [Cong] | formalized |
| Propositions 15.4, 15.5 | `prop15_4`, `prop15_5`, `F_add_selfPaying`, `F_succ_of_mod_eq_zero` [SPD] | formalized |
| Proposition 15.6 | none | not formalized (model) |
| Theorem 15.7 | `theorem15_7`, `two_two_digit`, `theorem15_7_zero` [Short] | formalized (both conventions; under `0^0 = 0` the other bases are the twin bases `a^(a-1)`) |
| Proposition 15.8 | `prop15_8`, `NotPerfectPower` [SPD] | formalized |
| Theorem 15.9 | `theorem15_9` [Cons] | formalized (for every `a ≥ 2`, as the library now states it) |
| Theorem 15.10 (assuming abc) | `theorem15_10`, `ABC`, `abc_le_gcd_mul`, `abc_case_nat`, `bounded_of_rpow_le` [Fact] | formalized (with abc as the hypothesis `ABC`; the set of pairs `(a, c)` is finite, and each pair has one base) |
| Proposition 15.11 | `exists_root_mod_two_iff` [Poly] | formalized |
| Lemma 15.12 (1) | `lemma15_12_one` [Adic], `pow_self_modEq_two` [Cong], `multiple_mem_T` [Res] | formalized (`x^x - x` is even, and every even residue occurs modulo `2^e`) |
| Lemma 15.12 (2) (`T(p)` is everything for `p ≥ 5`, `T(3) = {0, 2}`) | `T_prime_eq_univ`, `T_three` [Res] | formalized |
| Lemma 15.12 (3) | `pow_self_modEq_27`, `pow_self_modEq_three_of_ne` [Res] | formalized |
| Theorem 15.13 | `covering_27` [Res] | formalized |
| example `(2,1,x)` | `not_isSolution_two_one` [Res] | formalized |
| Theorem 15.14 (chains and cycles) | `theorem15_14`, `chainDigit`, `P_map_range` [SPD] | formalized (the chain `u_0 -> ... -> 0` and the cycles are given as a set `X` in `[1, t)` with `φ` injective on `X` and `φ(X) = (X minus u_0) ∪ {0}`, which is the same data; the 11-digit solution of base 64 is an example) |
| Proposition 15.15 | `prop15_15` [Cons] | partial: `c^c + 1` is a solution in every base `r^t` with `u < t`, `t ∣ u (c - 1)`, and in base `c^c - c + 1`; that the number of such `t` is unbounded is not formalized |
| Proposition 15.16 (needs `c ≥ 3` for the pair `(c,1)`) | `prop15_16`, `pow_self_pair`, `pow_self_injective` [Short] | formalized |
| Proposition 15.17 | `prop15_17` [Window] | formalized |

## Chapter 16. Algebra of the polynomial

| result | Lean name | status |
|---|---|---|
| Proposition 16.1 | none | not formalized (cyclotomic factorization) |
| Theorem 16.2 (`M/L → e^2`) | none | not formalized (analysis of cyclotomic values) |
| Proposition 16.3, Theorem 16.4 | none | not formalized |
| Proposition 16.5 (`x` even or an odd square) | `prop16_5` [Short] | formalized |
| Propositions 16.6, 16.7 | none | not formalized (`x`-adic and unit forms; need `Z_x` and quadratic fields) |
| Proposition 16.8 (3 and 5 never exclude; no finite set of primes suffices) | `prop16_8_a`, `prop16_8_b`, `prop16_8_finite` [Local] | formalized |
| Proposition 16.9 (abc triple) | none | not formalized |
| Propositions 16.10, 16.11, Theorem 16.12, Corollary 16.13, Theorem 16.14 | none | not formalized (Chebotarev, Galois groups) |
| Proposition 16.15 (rational roots for `k = 3`) | `prop16_15`, `prop16_15_quadratic` [Poly] | formalized (`Q_s = (q r - p)(q' r - p')` over `ℤ` with `q q' = s_1`, roots of opposite signs; the proof divides out the root instead of citing Gauss's lemma) |
| Proposition 16.16 (no twins for `q > 1`) | none | not formalized (needs the AFS number system) |
| Theorem 16.17 | none | not formalized |

## Chapter 17. Other weights

| result | Lean name | status |
|---|---|---|
| 17.2 identity with forced residues | `forced_residue` [Other] | formalized |
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
| Lemma 18.16 | `lemma18_16`, `lemma18_16_length`, `max_digit_eq` [Short] | formalized |
| Corollary 18.17 | `corollary18_17` [Short] | formalized (the length range of a third representation; the divisibility conditions are Proposition 2.6) |
| Proposition 18.18, Lemma 18.19 | none | not formalized (heuristic weights; Lemma 18.19 is elementary) |
| Theorem 18.20, Corollary 18.21 | none | not formalized (Gauss sums) |
| Proposition 18.22, Corollary 18.23 | none | not formalized (cite Laurent) |
| Question 12, Question 32 | `Question12`, `Question32` [Conj] | conjecture |

## Chapter 19. Sieve and spectra

| result | Lean name | status |
|---|---|---|
| 19.1.1: any modulus works | `not_isSolution_of_no_root_mod` [Poly] | formalized |
| 19.1.1: CRT and prime powers make other moduli redundant | `exists_root_mod_mul_iff`, `exists_root_mod_of_dvd`, `exists_root_zmod_iff` [Local] | formalized |
| 19.3.1: local factors | none | not formalized (Hensel) |
| everything else | none | not formalized (computed or heuristic) |

## Chapter 20. Multisets and residues

| result | Lean name | status |
|---|---|---|
| Lemma 20.1 | `lemma20_1`, `lemma20_1_root` [Window] | formalized |
| Proposition 20.2 | `prop20_2`, `card_multisets_le`, `sum_inv_le_harmonic`, `card_le_of_window` [Window] | formalized |
| Lemma 20.4 | `lemma20_4`, `prod_le_lcm_mul_pow` [Window] | formalized (for `r ≥ 1`; see problem 7) |
| Theorem 20.3, Proposition 20.5 | none | not formalized (asymptotics of the counts of Proposition 20.2 and Lemma 20.4) |
| Lemma 20.6 | `multiple_mem_T` [Res] | formalized |
| Lemma 20.7 | `lemma20_7`, `step_lemma20_7` [Res] | formalized (for every prime `p`; the library's "odd" is not needed) |
| Theorem 20.8 | `theorem20_8`, `exists_start`, `exists_generator_avoiding` [Res] | formalized (`p = 7` by a finite check, `p ≥ 11` with three generators) |
| Lemma 20.9 | `lemma20_9_five` [Res], `pow_self_modEq_three` [Cong] | formalized (the residue 3 mod 5 needs `x ≡ 8 (mod 20)`; mod 3, the residue 2 needs `x ≡ 2 (mod 6)` and 1 never occurs) |
| Lemma 20.10 | none | not formalized (`p`-adic exponential) |
| Theorem 20.11 (3-adic law) | `theorem20_11`, `step_three_adic`, `three_adic_unit`, `lift_three_adic` [Adic], `pow_self_modEq_81` [Res] | formalized (for every `e ≥ 4`; the lifting uses the congruence `f(x + 2·3^k t) ≡ f(x) + 3^k t B(x) (mod 3^(k+3))` in place of the 3-adic series, and a finite check over one period of 162) |
| Theorem 20.12 (5-adic law) | `theorem20_12`, `theorem20_12_three_mod_five`, `theorem20_12_good`, `theorem20_12_card`, `theorem20_12_card_T`, `card_sqMod`, `two_mul_pow_self_sub_eq`, `step_five_adic`, `five_adic_unit`, `exists_sqrt_neg_one_five_pow`; `theorem20_12_two`, `theorem20_12_three`, `theorem20_12_four` [Adic] | formalized (for every `e >= 1`, with `i` a square root of -1 modulo `5^e`, `i = 3 (mod 5)`: the class `3 (mod 5)` is `2 v = (1 - i)(2 - 25 y^2)`, it has `sq(e - 2)` elements, `12 sq(k) = 5^(k+1) + 7` or `+ 11`, and `T(5^e)` has `4 * 5^(e-1) + sq(e - 2)` elements, which gives the density `49/60` in the limit; the 5-adic series of Lemma 20.10 is replaced by the binomial expansion of `(i + D)^x` and a step congruence whose coefficient has valuation `v_5(x - i)`) |
| Corollary 20.13 | `covering_81`, `not_isSolution_eight_seven` [Res] | formalized |
| Proposition 20.14 | none | not formalized |
| Lemmas 20.15, 20.16, Proposition 20.17, Theorem 20.18 | none | not formalized (orders in quadratic fields; cites Matveev) |
| Proposition 20.20 | `prop20_20` [Short] | formalized |
| Lemma 20.21 | `lemma20_21_a`, `lemma20_21_a_even`, `lemma20_21_a_25`, `lemma20_21_b_three`, `lemma20_21_b_even`, `lemma20_21_b_prime`, `lemma20_21_c_even`, `lemma20_21_c_five`, `lemma20_21_d` [Local] | formalized (all four parts; for `c = 25` the direct check of `x ≤ 5` leaves only `(3, 6, 26)`) |
| Lemma 20.22, Propositions 20.23, 20.24, 20.25, 20.29, Theorems 20.26, 20.27, Corollary 20.28 | none | not formalized (quadratic orders and Laurent) |
| Theorems 20.19, 20.30 | none | not formalized (computation) |
| Question 51 | `Question51_two`, `Question51_three` [Conj] | conjecture |

## Chapter 21. Five more number systems

| result | Lean name | status |
|---|---|---|
| base-`B` expansions exist and are unique (21.1.1) | `IsExpansion`, `polyDigits`, `polyDigits_spec`, `IsExpansion.eq_of_ringVal_eq`, `IsFFSolution` [FF] | formalized (over any field, `deg B ≥ 1`) |
| Proposition 21.1 | `ffWeight`, `ffWeight_eq_expand`, `ffWeight_sum_of_degree` [Other], `sum_ffw_eq` [FF] | formalized (for `F_p`, `p` prime) |
| Corollary 21.2 | `IsFFSolution.natDegree_le`, `IsFFSolution.length_le`, `corollary21_2_card` [FF] | formalized (degree, length, and at most `p^(e(e+1)/2) · p` solutions under either convention; the sharper `p^(e(e+1)/2)` for `0^0 = 0` is not stated) |
| Proposition 21.3 | `ffWeight_add_C` [Other], `IsFFSolution.add_C` [FF] | formalized |
| Proposition 21.4 | `ffWeight_eq_mul_pow_iff`, `ffWeight_C_mul_X_pow_iff`, `IsFFSolution.add_selfPaying` [FF] | formalized |
| Proposition 21.5 | `sub_one_dvd_ringVal_sub_sum` [Other] | formalized (in any commutative ring) |
| Theorem 21.6 (`k(B) ≥ ω(B - 1)`) | `theorem21_6`, `kDim`, `Jsum`, `finrank_ker_frobR`, `finrank_ker_le_kDim` [MT] | formalized (via Lemma 29.8 (4) and Berlekamp's count `dim R^φ = ω`, in place of traces) |
| Theorem 21.7 | `theorem21_7`, `theorem21_7_card`, `theorem21_7_necessary` [FF] | formalized (the proof is shorter than the library's: once `B - 1 ∣ T^p - T`, the digit sum is `c + βT` and every `c` works) |
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
| Proposition 22.8 | `prop22_8`, `R_pos_middle`, `R_pos_leading` [Three] | formalized (`R = 0` needs the large digit last; for even `x` the members are those of Theorem 22.6 with `j = 2`) |
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
| Lemma 24.1 (Frobenius blocks) | `lemma24_1`, `lemma24_1_zero`, `frobBlock` [FF], `expand_ringVal` [Other] | formalized |
| Proposition 24.2 (Horner form) | `prop24_2` [FF] | formalized |
| Corollary 24.3 | `corollary24_3`, `corollary24_3_ffF`, `hornerDigit`, `ffF_eq_sum_expand` [FF] | formalized (for any digits `D_0, ..., D_(n-1)`, and for `F(n)` with `D_0` including `m z`) |
| Corollary 24.4 (forced zeros) | `corollary24_4`, `corollary24_4_ffF` [FF] | formalized (for every Horner sum of digits, and for `F(n)`) |
| Lemma 24.5 | `lemma24_5`, `lemma24_5_zero_block` [FF] | formalized |
| Proposition 24.6 | `prop24_6_one`, `prop24_6_two`, `ffDigit_add`, `ffDigit_C_mul` [FF] | formalized ((1) from the `F_p`-linearity of the digits; (2) for any digits `D_j`, with `c` the coefficient of `T^(e-1)` in `sum (D_j(T^(p^(j-1))) mod (B - 1))`, which is `sum sigma'^(j-1)(D_j)`) |
| Lemma 24.7 | `IsFFSolution.comp` [FF] | formalized |
| Lemma 24.8 | `IsFFSolution.C_mul_add_C`, `C_mul_add_C_injective` [FF] | formalized |
| Lemmas 24.9, 24.10 | none | not formalized |
| Proposition 24.11 | `prop24_11`, `ffF_one_eq`, `sub_pow_eq_sub_frob` [FF] | formalized for `q = p` prime (as all of [FF]); the proof iterates `y ↦ y^p` in `F_p[T]/(P)` in place of the trace |
| Corollary 24.12 | `corollary24_12_one`, `theorem21_7_card` [FF] | partial: (1), with one root of `B - 1` in place of two (the digits of `c' + β T^p` are `c' + β c`, `(p-3)/2` zeros and `β lam^(-(p-1)/2) (T - c)`); (2) is computed |
| Proposition 24.13, Theorem 24.15, Corollary 24.16 | none | not formalized |

## Chapter 25. Identity families and 3-digit solutions

| result | Lean name | status |
|---|---|---|
| Definition 25.1, Theorem 25.2 (the last digit is large) | `theorem25_2` [Three] | formalized (core form: `P_s(r) - E` is not `lam A(r)^j` when `E ≥` the last digit, with the next digit nonzero if equal; this is exactly the situation when the last digit is not large; the proof uses the intermediate value theorem and a derivative instead of Descartes' rule) |
| Corollary 25.3 | `corollary25_3` [Three] | formalized (the form `r P_t(r) + C = lam A^j` and the solution criterion `x^x = lam A(b)^j`; that `x` is last is Theorem 25.2; the normalization of `A` by Gauss's lemma is not stated) |
| Theorem 25.4 | none | not formalized ((a) is Theorem 22.6 and 25.5 after rescaling; (b), (c) need valuations) |
| Theorem 25.5 | `theorem25_5`, `theorem25_5_conditions` [Cons] | formalized (the prime condition is stated as `c ∣ (j-1)^c`, which is equivalent; the conditions hold for `c = (j-1)^a`) |
| Proposition 25.6 | none | not formalized |
| Theorem 25.7 | `theorem25_7_i`, `theorem25_7_i_parity` [TDB], `theorem25_7_ii_last`, `theorem25_7_ii_middle`, `theorem25_7_ii_leading`, `theorem25_7_iii_last`, `theorem25_7_iii_middle`, `theorem25_7_iii_leading`, `complete_square`, `prop22_8`, `R_pos_middle`, `R_pos_leading` [Three]; `pell_last`, `pell_middle` [SR] | formalized: case (i) for every `x` (with `lam = 1` for even `x` and `x / lam` a square for odd `x`), case (ii) in all three positions, and case (iii): a square identity forces `R = 0` (large digit last), and there is none with the large digit in the middle or leading (via Theorem 25.2); the Pell form is `complete_square` |
| Conjecture 25.8 | none | not stated (it refers to "the two linear families"; could be stated with Theorems 22.6 and 25.5) |
| Proposition 25.9, Theorem 25.10 | `prop25_9`, `theorem25_10` [TDB] | formalized |
| Theorem 25.11, Heuristic 25.12 | none | not formalized (computation, heuristic) |
| Lemma 25.13, Corollary 25.14 | `lemma25_13`, `corollary25_14` [Three] | formalized |
| Theorem 25.15 | `theorem25_15`, `card_solsTop`, `card_shape_Muv`, `card_le_thirteen` [TDB] | formalized |
| Proposition 25.16 | `prop25_16` [TDB] | formalized |
| Proposition 25.17 | `prop25_17`, `prop25_17_card` [TDB] | formalized (see problem 5 for a missing step) |
| Question 50 (at most two 3-digit solutions per base) | `Question50` [Conj] | conjecture |
| Question 65 (the next 3-digit solution) | `Question65` [Conj] | conjecture (the family part is Theorem 25.10) |

## Chapter 26. Near-solutions as evidence

| result | Lean name | status |
|---|---|---|
| Lemma 26.1 (the swap lemma) | `swap_lemma_perm`, `swap_lemma`, `swap_last_two` [Search] | formalized |
| Corollary 26.2 (the class of the moved offset) | `corollary26_2`, `corollary26_2_odd`, `repunit_identity` [Search] | formalized (general and odd bases; the even-base case is the same identity) |
| Lemma 26.3 (the fibre) | `lemma26_3`, `lemma26_3_unique` [Search] | formalized |
| Lemma 26.4 (other systems) | `swap_lemma`, `swap_last_two` [Search] | partial: base `-b` (the ring identity at `r = -b`); factorial, Pisot and `F_q[T]` not formalized |
| Proposition 26.5, Heuristic 26.6, Proposition 26.9 | none | not formalized (statements about the probabilistic model, computed) |
| Proposition 26.10 | `prop26_10_one`, `prop26_10_two`, `ImageSet` [Search] | formalized |

## Chapter 27. Limits of search

| result | Lean name | status |
|---|---|---|
| Lemma 27.1, Theorem 27.2 | none | not formalized (entropy statements in the model) |
| Theorem 27.5 | `theorem27_5_oracle`, `theorem27_5_claim`, `theorem27_5`, `card_image_le_of_fooling`, `Cylinder.Fails`, `topDigit`, `prefixCount` [Search] | formalized (in the interval oracle of section 27.3.1, with the claim of the proof proven; `lam(c)` and `theta(c)` may be any values with the defining properties, so the largest `lam` and least `theta` of the library are covered) |
| Lemma 27.3 | `lemma27_3`, `not_fails_of_prefix` [Search] | formalized |
| Proposition 27.4, Remark 27.6, Corollary 27.7 | none | not formalized (27.4 is a statement about algorithms; 27.6 and 27.7 concern the engine's forcing test and the top-down tree) |
| Proposition 27.8 | `prop27_8`, `not_dvd_w_of_coprime` [Search] | formalized |
| Corollary 27.9 | `corollary27_9` [Search] | formalized (as: if every unrevealed value below `k` has `b^L ∣ w(v)`, then `k ≤ 1`, and `k = 0` under `0^0 = 1`) |

## Chapter 29. Theorems about the model

| result | Lean name | status |
|---|---|---|
| Theorem 29.1, Lemmas 29.3, 29.4, Theorem 29.5, Corollary 29.6, Proposition 29.7 | none | not formalized (theorems about the probabilistic model; Lemma 29.3 cites the Barbour-Hall bound) |
| Lemma 29.2 (weights) | `lemma29_2` [MT] | formalized |
| Lemma 29.8 | `finrank_ker_frobR`, `natCard_fixed_local`, `exists_C_of_dvd_pow_card_sub` (1); `lemma29_8_two_nil`, `mem_range_pow_sub_one_of_pow_eq_zero` (2); `lemma29_8_three`, `iSup_range_pow_sub_one_eq`, `pow_card_pow_add_local`, `range_pow_gcd_sub_one_le`, `frobA` (3); `range_pow_sub_one_le`, `Jsum_le_range` (4) [MT] | partial: (1) for `j = 1` (Berlekamp's count `dim R^φ = ω(B - 1)`, by the Chinese remainder theorem); of (2), that the image of `φ^j - 1` (`j ≥ 1`) contains every nilpotent element, in `R` and in each `R_i`; (3) in full, without traces (`φ^(a+f) = φ^a` on `F_q[T]/(P^a)`, and Euclid's algorithm on the exponents); and (4). (1) for `j ≥ 2` and the trace description in (2) are not formalized |
| Theorem 29.9 | `theorem29_9`, `sub_one_mem_range_pow`, `pow_card_pow_mul_add_one`, `dvd_pow_card_pow_sub`, `sub_one_apply_eq` [MT] | formalized (the part reached by the term `j = e - 1` is the ideal `Q R`, `Q = (B - 1)/P`, on which `φ^(k f + 1) = φ`; this replaces Lemma 29.8 (3) with `S = {e - 1}`, and the terms `j = e - 2, e - 1` cover `R` modulo `Q R`) |
| Corollary 29.10 | `corollary29_10`, `corollary29_10_two`, `exists_good_factor`, `exists_coprime_of_sum` [MT] | formalized (`k(B) = ω(B - 1)` when `e - 1 = r^s`, `s ≥ 1`, and for `e = 2` separately; see problem 6) |
| Theorem 29.11 | `theorem29_11_one`, `kDim_le`, `codim_le_finrank_ker_add_one`, `theorem29_11_two`, `codim_gt_iff`, `mem_dualAnnihilator_Jsum`, `topCoeff_span`, `comp_pow_eq_of_codim_gt`, `theorem29_11_three`, `topCoeff`, `exists_topCoeff_mul_ne_zero` [MT] | partial: (1), (2) (both directions, with (a), (b), (c)) and (3) in full; (4) (Euler's formula over the roots of `B - 1` and the element `D = M'^(1-q)`) is not formalized |
| Remark 29.12 | none | not formalized (it uses the roots and the `u_m` of the proof of Theorem 29.11 (4)) |
| Conjecture 29.13 (`k(B) = ω(B - 1)`) | `Conjecture29_13` [MT] | conjecture (proved for non-squarefree `B - 1` by `theorem29_11_three`, and when `B - 1` has a good factor by `theorem29_9`) |
| Lemma 29.14 (Assumption R fails at `b = 10`, `d = 2`) | `lemma29_14` [MT] | formalized (the digit 3 is the only 1-digit string with a 2-digit weight) |
| Theorem 29.15, Corollary 29.16, Propositions 29.17, 29.19 | none | not formalized (model, computation, exponential sums) |
| Conjecture 29.18 | none | not stated (exponential sums) |
| Heuristic 29.20, Lemma 29.21 | none | not formalized (model) |

## Chapter 30. Connections to other fields

| result | Lean name | status |
|---|---|---|
| Lemma 30.1 (`g(z) ≥ 2 z g(z-1)`) | `lemma30_1`, `g`, `g_mono` [App] | formalized |
| Lemma 30.2 (dissociation) | `lemma30_2`, `lemma30_2_mod` [App] | formalized |
| Theorem 30.3 | none | not formalized (probability with Chernoff bounds; its counting core is Lemma 30.2) |
| Lemma 30.4 | `lemma30_4`, `lemma30_4_allowed` [App] | formalized (`x^x < b^d` with `b ≤ 2d`, `b ≥ 12` forces `x ≤ 2d - 5`; every `x < b`, `x ≤ d` is allowed) |
| Theorem 30.5, Corollary 30.8 | none | not formalized (model) |
| Proposition 30.6 | `prop30_6_forced`, `prop30_6_step` [App] | partial: `x^d ≡ x (mod p)` for all `x` iff `p - 1 ∣ d - 1`, and `p^d - p ≡ -p (mod p^2)`; the limit law not formalized |
| Proposition 30.7 | `prop30_7` [App] | partial: the two-step count (pairs with `f x + f y = r` are at most the collisions); the `k`-step form and the probability language not formalized |
| Conjecture 30.9 | none | not stated |
| Proposition 30.10 | `prop30_10`, `pow_self_modEq_self_iff`, `card_pow_modEq_self`, `sum_div_orderOf` [App] | formalized (the count `(p-1) + ∑_(d ∣ p-1) φ(d) (p-1)/d` over one period `1 ≤ c ≤ p(p-1)`) |
| Corollary 30.11 | `corollary30_11_two`, `corollary30_11_two_solution`, `dvd_g_iff_modEq` [App] | partial: (2); (1) and (3) cite Kurlberg, Luca and Shparlinski |
| correction: 7 has a fixed point (`4^4 ≡ 4 (mod 7)`) | example [App] | formalized |
| Theorem 30.12 | `theorem30_12`, `narcSet`, `IsNarc2`, `isNarc2_iff`, `IsNarc2.swap` [App, TS]; `card_oddPos_sq_add_one`, `card_repG_mul`, `card_repG_prime_pow`, `card_repG_odd` [TS] | formalized (the count `tau(b^2 + 1) - 2` for every `b >= 2`; in place of `r_2(N) = 4 sum chi(d)` the proof counts Gaussian integers of norm `n`: `r(m) r(n) = 4 r(m n)` for coprime `m, n` via `gcd(z, m)`, and `r(p^k) = 4 (k + 1)` for `p = 1 (mod 4)`) |
| Corollary 30.13 | `corollary30_13_one`, `corollary30_13_two`, `corollary30_13_two_iff`, `not_dvd_of_prime_sq_add_sq` [App, TS] | partial: (1) with the two explicit numbers, and (2) in both directions (an even base `b >= 2` has a 2-digit narcissistic number exactly when `b^2 + 1` is composite); (3) and (4) (Iwaniec, Hooley) are cited |
| Proposition 30.14 | `card_divisors_sq_add_one` [App] | partial: the divisor pairing `τ(n^2 + 1) = 2 #{d ≤ n : d ∣ n^2 + 1}`; the asymptotics not formalized |

## Chapter 31. Pruning by the residue

| result | Lean name | status |
|---|---|---|
| Theorem 31.1 (the residue rule) | `theorem31_1`, `IsSolution.sum_g_modEq_zero`, `Fs_eq_sum_g_add_sum` [SR] | formalized |
| Corollary 31.2 | none | not formalized (a statement about the engine; the rule it applies is Theorem 31.1) |
| Lemma 31.4 (the interval is the hull) | `lemma31_4`, `lemma31_4_attained` [SR] | formalized |
| Proposition 31.5 | `prop31_5_hi`, `prop31_5_lo` [SR] | formalized (the two interval inequalities; the claim about the nodes of the engine is about code) |
| Heuristics 31.3, 31.6 | none | not formalized (heuristic) |

## Chapter 32. The basic questions revisited

| result | Lean name | status |
|---|---|---|
| Theorem 32.1 (Bugeaud and Laurent) | none | not formalized (cited) |
| Theorem 32.2 | `pell_last`, `pell_middle`, `pell_last_R_ne_zero`, `pell_middle_R_ne_zero`, `two_pow_dvd_V` [SR] | partial: the reduction to `U^2 - n V^2 = R` with `V = 2 f x^(x/2)`, `R ≠ 0` for non-square `n`, and `2^(x/2+2) ∣ 2V`; the Baker step (heights, 2-adic logarithms, Theorem 32.1) is not formalized |
| Theorem 32.3 | `isSolution_last_iff_disc`, `isSolution_mid_iff_disc`, `sieve_last`, `sieve_mid` [SR] | partial: the test `D = U^2` and the soundness of the sieve (`D` is a square modulo every `l`); the bound `X0` and the run are computations |
| Corollary 32.4, Proposition 32.7 | none | not formalized (computation) |
| Theorem 32.5, Proposition 32.6 | none | not formalized (Baker and Matveev bounds, class number formula) |

## Chapter 33. Factorials against `x^x`

| result | Lean name | status |
|---|---|---|
| factorions, weights in general | `IsWSolution`, `fw`, `isSolution_iff_isWSolution` [Fact] | formalized (definitions) |
| the completed square `U^2 = M + K` (table of chapter 33) | `three_digit_iff_sq`, `factorion_last_iff` [Fact] | formalized |
| Lemma 33.1 | `lemma33_1`, `lemma33_1_two`, `sq_eq_pow_mul` [Fact] | formalized (in finite form: `v` even and the unit part a square modulo `l`, or `≡ 1 (mod 8)` for `l = 2`; that is "`K` is a square in `Q_l`" without citing Hensel) |
| Lemma 33.2 | `lemma33_2`, `pow_div_dvd_factorial` [Fact] | partial: the obstruction behind (a) and (c) (`K = l^v k` not an `l`-adic square and `l^(v+1) ∣ x!`, with `l^(x/l) ∣ x!`); the discriminant bound of (b) and the explicit forms with `log abs(K)` are not stated |
| Lemma 33.3 | none | not formalized (cites Trevino, Pomerance, Bach; computed) |
| Theorem 33.4 | `theorem33_4_b`, `theorem33_4_d_A`, `theorem33_4_d`, `factorion_last_iff` [Fact] | partial: (b) (`x < 2 p A`) and (d) in full, and the equivalence with `U^2 = M + K`; the bounds `X0` of (a) to (c) need Lemma 33.3 |
| Theorems 33.5, 33.6, Table 33.1.1 | none | not formalized (computation) |
| Corollary 33.7 | `ABC`, `theorem33_16_abc` [Fact] | not formalized (the abc step is `theorem33_16_abc`; the bound on `rad(x!)` is cited and the rest is computed) |
| Proposition 33.8, Theorem 33.10 | none | not formalized (GRH, Chebotarev) |
| Proposition 33.9 | `prop33_9`, `infinite_two_digit_factorions` [Fact] | formalized |
| Conjecture 33.11 | `Conjecture33_11` [Fact] | conjecture |
| Theorem 33.12 | `theorem33_12`, `theorem33_12_member` [Fact] | formalized (every `u ≥ j` gives a member, since then `t_i ≤ (M u)^j ≤ x`; (S3) is stated as `y > M (x + v)` whenever `v^j ≤ x`) |
| Proposition 33.13 | `prop33_13`, `prop33_13_lt`, `prop33_13_identity` [Fact] | formalized (the consequence for identities with `lam` an integer dividing `t_0`, as the normalization of Corollary 25.3 gives) |
| Theorem 33.14, Corollary 33.15, Theorem 33.19 | none | not formalized (conditional on abc; the Tschirnhaus reduction is not stated) |
| Theorem 33.16 | `rad`, `ABC`, `theorem33_16_abc`, `theorem33_16`, `abc_div_gcd` [Fact] | partial: under abc, `N ≤ K (rad(N) U abs(R))^(1+ε)` and `N^((1-ε)/2) ≤ 2 K (rad(N) abs(R))^(1+ε)` for `0 < abs(R) ≤ N`; the bounds on `rad(N)` and `abs(R)` and the final bound on `x` are not formalized |
| Corollaries 33.17, 33.18, Proposition 33.20, Table 33.4.1 | none | not formalized (conditional on abc; computation) |
| Proposition 33.21 | `prop33_21`, `prop33_21_card` [Fact] | formalized (the arithmetic; Theorem 15.14 itself is not formalized) |
| Proposition 33.22 | none | not formalized (inequalities closed by a computation) |
| Heuristic 33.23, the census of 33.3.4 | none | not formalized (heuristic, computed) |

## Chapter 34. Is the refined model complete?

| result | Lean name | status |
|---|---|---|
| Proposition 34.1 (the exact refined model) | none | not formalized (a statement about the model) |
| Lemma 34.2 | `lemma34_2`, `lemma34_2_F` [MC], `isMunchausen_one_iff_zero` [Basic] | formalized |
| Lemma 34.3 | `lemma34_3` [MC], `F_one_eq` [Basic] | formalized |
| Proposition 34.5 | `N1`, `N1_eq`, `prop34_5`, `prop34_5_one_digit` [MC] | partial: (2), the values of `N_1(b)` and the 1-digit strings whose `F` has one digit; (1) is about the model, and `N_1(b) ~ ln b / ln ln b` is not formalized |
| Theorem 34.6, Corollary 34.7, Proposition 34.8 | none | not formalized (theorems about the model; they use Theorem 29.1) |
| Proposition 34.10 | `prop34_10_uniform` [MC] | partial: every residue modulo `b - 1` occurs `b^(d-1)` times among the `d`-digit numbers; the trace and the characters are about the model |
| Corollary 34.11 | `corollary34_11` [MC], `F_modEq_self_iff` [Cong] | partial: `F_0(n) ≡ n (mod 2)` for odd `b`, and no other modulus or convention has such an identity (Theorem 15.2); the multiplicity of the eigenvalue is about the model |
| Theorem 34.12 | `theorem34_12_parity` [MC] | partial: `F_1(n) - n ≡ c_0(n) (mod 2)` for odd `b`; the limit `e^-2` uses Lemmas 29.3 and 29.4 (model) |
| Conjecture 34.13 | none | not stated (about the model) |
| Heuristics 34.4, 34.9, 34.14, 34.15 and the tables | none | not formalized (heuristic, computed) |

## Chapter 35. One heuristic and existence

| result | Lean name | status |
|---|---|---|
| Theorem 35.1, Corollary 35.2 | none | not formalized (character sums over random arrangements) |
| Proposition 35.3 | `prop35_3`, `P_one` [Exist] | formalized (the exchange of the two sums, and `P_s(1)` is the digit sum; the other residues are estimated by Theorem 35.1) |
| Heuristics 35.4, 35.11, sections 35.1.3, 35.1.4, 35.2, Table 35.3.2.1 | none | not formalized (heuristic, computed) |
| Proposition 35.5 | `invIdeal`, `exchIdeal`, `Exch`, `ringVal_exch`, `prop35_5_one`, `prop35_5_two`, `prop35_5_three_le`, `prop35_5_three` [Exist] | partial: (1), (2) and (3) for place values `u β^i` with `i ≥ 0`; the negative positions of a unit `β` are not covered |
| Proposition 35.6 | `prop35_6`, `prop35_6_rat` [Exist] | formalized (for `Z[t]/(f)` with any `f`, which is `Z[β]` when `f` is the minimal polynomial of the algebraic integer `β`; and for `p/q` in `Z[1/q]`, which covers `-p/q`) |
| Proposition 35.7 | none | not formalized (convergence of a random walk on a finite group) |
| Proposition 35.8 | none | not formalized (the window of Lemma 20.1 with the mean value theorem) |
| Proposition 35.9 | `prop35_9_share`, `prop35_9_bounds` [Exist] | partial: the exact share as a product and its two exponential bounds; the limit `-2A` is not formalized |
| Corollary 35.10, Theorem 35.12 | none | not formalized (asymptotic counts) |
| Theorem 35.13 | `theorem35_13_step3`, `theorem35_13_strict`, `div_add_eq_of_digit_le`, `P_inj_of_length_eq` [Exist] | partial: Step 3 (no carry from `E < P_(T+1)`, so `n` and `F(n)` agree in the top digits, and an exchange below the top makes `n ≠ F(n)`); Steps 1 and 2 (the steering, with real bounds) are not formalized |
| Corollary 35.14 | none | not formalized (asymptotics of the conditions; computed thresholds) |

## Open questions stated as `Prop`s

`FinitenessConjecture` (refuted), `MissingLengthsConjecture` (refuted),
`Conjecture_9_4` (refuted), `NoFullLengthConjecture 0` (refuted),
`NoFullLengthConjecture_one`, `BoundedCountOne`, `InfinitelyManyEmptyBases`,
`EveryCountOccurs`, `Conjecture_10_3_lower`, `Question65`, `Question50`,
`Question36`, `Question39`, `Question12`, `Question32`, `Question51_two`,
`Question51_three`, `Conjecture29_13`, `Conjecture33_11`. All are in
`Conjectures.lean`, except `Conjecture29_13`, which is in `ModelTheorems.lean`,
and `Conjecture33_11`, which is in `Factorials.lean`. The abc conjecture is
stated as `ABC` in `Factorials.lean` and used only as a hypothesis. The round
5 questions (72 to 89) are research directions and are not stated.

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

4. **Section 12.3, the family `(x, 0, 0)` in base `-x^((x-1)/2)`.** The
   text says it works when `x` is odd or a square. For `x = 3` the base is
   `-3`, and the digit 3 is not below 3, so the string is not valid. The
   family needs `x ≥ 4`: odd `x ≥ 5`, or `x = y^2` with `y ≥ 2` (base
   `-y^(x-1)`, for `x = 4` base -8). The Lean statements
   (`isNegSolution_x_0_0_odd`, `isNegSolution_x_0_0_sq`) carry these bounds.
5. **Proposition 25.17** (section 25.3.3), a missing step. The proof uses
   `x >= w(p) + w(q) >= p^p + 4`, that is `q >= 2`, which needs `e >= 1`.
   The text does not justify `e >= 1` there. It holds by the argument in the
   proof of Theorem 25.10: with `e = 0` the last digit is `x = p^p + 1`,
   prime to `p`, so `x^x = p b^2` forces `p = 1`, `x = 2` and `b = 2`, which
   is not a valid base. The Lean proof adds this step (`member_e_pos`).
6. **Corollary 29.10** (section 29.2.2), a small gap. The list of covered
   degrees starts at `e = 2`, where `e - 1 = 1` is not a prime power `r^s`
   with `s >= 1`, and the proof ("`r` divides every `f_i`, hence `e`, but `r`
   divides `e - 1`") needs a prime `r`. The case `e = 2` holds for the
   trivial reason that every degree is prime to 1. The Lean statements
   (`exists_good_factor`, `corollary29_10`) assume `s >= 1`, and
   `corollary29_10_two` covers `e = 2`.
7. **Lemma 20.4** (section 20.1.4), an edge case. For `r = 0` the claim reads
   `m > 1`, false for `m = 1`. The lemma needs `r >= 1`, which holds wherever
   it is used. The Lean statement (`lemma20_4`) assumes a nonempty set.
8. **Proposition 33.13** (section 33.3.2), a small gap in the consequence.
   The proposition allows `lam` rational, and the bound is `x < 2 P(lam)`
   with `P(lam)` the largest prime of the numerator or the denominator.
   The consequence for identities says `lam c^j = t_0`, "so `lam <= t_0`",
   and concludes `x < 2 t_0`. That needs `P(lam) <= t_0`, which `lam <= t_0`
   gives only when `lam` is an integer; a prime of the denominator of `lam`
   is not bounded by `lam`. With the normalization of Corollary 25.3 (`A`
   primitive, Gauss's lemma) `lam` is an integer dividing `t_0`, and the
   conclusion holds. The Lean statement (`prop33_13_identity`) assumes
   `lam` an integer dividing `t_0`.

The library corrections that landed during this work (Proposition 9.3, the
pair `(c, 1)` in Proposition 15.16 needs `c >= 3`, the negative-base family
`(x, 0, 0)` needs `x` odd or a square, the renumbering of chapters 16, 23 and
24) touch only rows that are not formalized yet, or citations, which now use
the new numbers.

## Next

In order of value and effort:

1. Chapter 29 with traces: Lemma 29.8 (1) for `j >= 2`, (2) and (3) (the
   subfields and trace kernels of `F_(q^f)`, Hensel lifting), then
   Theorem 29.9, the conclusion of Corollary 29.10, Theorem 29.11 (2)
   (sufficiency, (b), (c)) and (4), and Remark 29.12. The Chinese remainder
   setup of `finrank_ker_frobR` and the dual argument of
   `comp_pow_eq_of_codim_gt` are in place.
2. Theorem 33.16 under abc to the end: the bounds `rad(N) <= 2 l x` and
   `abs(R) <= 9 x^2 B^B` of Theorem 25.7 and the bound on `x`, then
   Corollary 33.17. `ABC`, `abc_le_gcd_mul` and `bounded_of_rpow_le` (used for
   Theorem 15.10) are the tools.
3. Theorem 35.13, Steps 1 and 2 (the steering of the top digits by
   monotonicity, with the real bounds on `theta_i`), and Corollary 35.14.
4. Chapter 35, smaller items: Proposition 35.5 (3) for negative positions of
   a unit `beta`, Proposition 35.8 (the window with the small part), and the
   count of Theorem 35.12.
5. Smaller items: the `k`-step form of Proposition 30.7, the unbounded
   number of bases in Proposition 15.15, Corollary 34.7 and Theorem 34.6
   (they need Theorem 29.1).
