// Results that are formalized in Lean (lean/ in the repository).
//
// Map the id of a statement in the exposition to the name of its Lean
// declaration. The statement then shows a "Lean" badge, and the index of
// results lists the name. Keep this in sync with lean/STATUS.md, which is the
// record of what is formalized. All names live in the namespace Munchausen.
// A partial formalization says what it covers.

#let lean-names = (
  // Chapter 1
  "thm-length": "length_digits_le",
  "thm-digit-bound": "pow_self_lt_of_mem_digits",
  "thm-one-base": "IsSolution.base_unique",
  "thm-conventions": "F_one_eq",
  "thm-digit-sum": "IsSolution.Fs_modEq_sum",
  "basics-parity-rules": "IsSolution.even_count_zero, IsSolution.even_countP_mod_four, IsSolution.three_dvd_countP_mod_six, IsMunchausen.last_digit_parity",
  "thm-only-residue": "residue_invariant_iff",
  "thm-parity-invariant": "F_modEq_self_iff",
  // Chapter 2
  "thm-twins": "isSolution_twin",
  "thm-self-paying": "selfPaying_of_dvd, SelfPaying.exists_pow",
  "cons-sp-char": "prop15_8",
  "cons-sp-spacing": "SelfPaying.position_gt, card_selfPaying_lt_log",
  "thm-structure-m0": "isSolution_selfPaying_iff, isMunchausen_iff_core",
  "cons-sp-count": "corollary_2_4",
  "cons-sp-top": "isSolution_selfPaying_cons_iff",
  "cons-swap-cores": "theorem15_9",
  "thm-two-digit": "isSolution_two_iff",
  "thm-two-two-digit": "theorem15_7 (partial: the case 0^0 = 1)",
  "thm-every-length-m0": "isSolution_prop27",
  "thm-binomial": "isSolution_binomial",
  "thm-every-length-m1": "isSolution_corollary_22_7, infinite_solutions_of_length",
  "cons-r-zero": "prop22_8",
  "cons-last-large": "theorem25_2",
  "cons-zero-family": "theorem25_5",
  "cons-split": "split_iff",
  "thm-many-m0": "theorem9_2, prop4_2",
  "cons-rare": "selfPaying_base_pow, card_selfPaying_le (partial: the shape r^t with t >= c + 1)",
  "cons-two-reps": "prop15_16",
  // Chapter 3
  "model-lem-swap": "swap_lemma, swap_lemma_perm, swap_last_two",
  "model-prop-image": "prop26_10_one, prop26_10_two",
  "model-prop-cycles": "F_lt_pow_self (partial: F maps numbers below b^b to themselves)",
  // Chapter 4
  "search-prop-fixed-length": "prop4_1, prop10_4",
  // Chapter 5
  "thm-local": "not_isSolution_of_no_root_mod",
  "short-mod2": "exists_root_mod_two_iff",
  "short-tq-small": "T_prime_eq_univ, T_three, pow_self_modEq_27, multiple_mem_T (partial: part 1 modulo 2^e only for multiples of 2)",
  "thm-covering": "covering_27",
  "short-lift": "lemma20_7",
  "short-tq-large": "theorem20_8",
  "short-3adic": "pow_self_modEq_81 (partial: the inclusion modulo 81)",
  "short-81": "covering_81",
  "short-per-base": "prop4_1",
  "short-bases-k": "prop10_4",
  "thm-square-class": "theorem8_3, theorem8_3_one",
  "short-three-digit-class": "theorem25_7_ii_last, theorem25_7_ii_middle, theorem25_7_ii_leading, prop22_8 (partial: case (ii), and case (i) for even x)",
  "short-largest-digit": "lemma25_13",
  "short-two-values": "corollary25_14",
  "short-one-member": "prop25_16_even (partial: members with even x)",
  "short-odd-length": "IsNegSolution.odd_length",
  "short-partners": "IsSolution.negPartner",
  "short-block-route": "P_sub_Fs_append_one, P_sub_Fs_append_zero",
  "short-two-digit-size": "lemma18_14",
  // Chapter 6
  "dio-elementary": "prop18_1_a, prop18_1_b, prop18_1_c, prop18_1_d, prop16_5",
  "dio-12x": "prop20_20",
  // Chapter 7
  "worlds-odd-length": "IsNegSolution.odd_length",
  "worlds-nega-residue": "neg_residue_invariant_iff, IsNegSolution.dvd",
  "worlds-minus1i": "gaussian_blocks (partial: the block form; existence and uniqueness cited)",
  "worlds-ff-linear": "ffWeight_eq_expand, ffWeight_sum_of_degree",
  "worlds-ff-families": "ffWeight_add_C (partial: the weight identity)",
  "worlds-ff-blocks": "expand_ringVal (partial: the identity before uniqueness of expansions)",
  "worlds-fact-noresidue": "factorial_no_invariant_residue",
  "worlds-fact-selfpaying": "factorial_selfPaying",
)
