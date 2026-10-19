import Munchausen.ShortEquations

/-!
# Other number systems (chapters 14, 21, 23 and 24)

* negative bases: the digit-sum identity modulo `b + 1` (Propositions 14.4 and 14.5) and the
  even number of zeros in odd negative bases;
* the factorial number system: no invariant residue (Proposition 21.14) and the self-paying
  digits (Proposition 21.15);
* function fields `F_p[T]`: the linearity of the weight (Proposition 21.1), translates
  (Proposition 21.3), the identity modulo `B - 1` (Proposition 21.5) and the Frobenius
  identity behind Lemma 24.1;
* base `-1 + i`: the block form of Theorem R2.1 (section 23.4).
-/

namespace Munchausen

/-! ### Negative bases -/

/-- **Proposition 14.5** (section 14.1.1). Every solution in base `-b` satisfies
`sum (w(x) - x) ≡ 0 (mod b + 1)`. -/
theorem IsNegSolution.dvd {b m : ℕ} {s : List ℕ} (h : IsNegSolution b m s) :
    ((b : ℤ) + 1) ∣ (Fs m s : ℤ) - s.sum := by
  have := sub_one_dvd_P_sub_sum (-(b : ℤ)) s
  rw [h.eq] at this
  have e : -(b : ℤ) - 1 = -((b : ℤ) + 1) := by ring
  rwa [e, neg_dvd] at this

/-- Section 14.1.1: in a base `-b` with `b` odd, a solution under `0^0 = 1` has an even number
of zeros. -/
theorem IsNegSolution.even_count_zero {b : ℕ} {s : List ℕ} (hb : Odd b)
    (h : IsNegSolution b 1 s) : Even (s.count 0) := by
  have h1 := h.dvd
  have h2 : (2 : ℤ) ∣ (b : ℤ) + 1 := by
    obtain ⟨k, rfl⟩ := hb; exact ⟨k + 1, by push_cast; ring⟩
  have h3 := h2.trans h1
  rw [Fs_one_eq] at h3
  have h5 : (2 : ℤ) ∣ (Fs 0 s : ℤ) - s.sum := Nat.modEq_iff_dvd.1 (Fs_zero_modEq_two s).symm
  have h6 := dvd_sub h3 h5
  rw [Nat.cast_add] at h6
  have h7 : (2 : ℤ) ∣ (s.count 0 : ℤ) := by
    have e : (Fs 0 s : ℤ) + s.count 0 - s.sum - ((Fs 0 s : ℤ) - s.sum) = s.count 0 := by ring
    rwa [e] at h6
  exact even_iff_two_dvd.2 (Int.natCast_dvd_natCast.1 h7)

/-- **Proposition 14.4** (section 14.1.1). The residue of `n` modulo `M` depends only on the
digit multiset, for all numbers with at least 3 digits in base `-b`, exactly when
`M ∣ b + 1`. -/
theorem neg_residue_invariant_iff {b : ℕ} (hb : 2 ≤ b) (M : ℤ) :
    (∀ s t : List ℕ, Valid b s → Valid b t → 3 ≤ s.length → s.Perm t →
        M ∣ P (-(b : ℤ)) s - P (-(b : ℤ)) t) ↔ M ∣ (b : ℤ) + 1 := by
  constructor
  · intro h
    have hv1 : Valid b [1, 1, 0] := ⟨by simp; omega, by simp⟩
    have hv2 : Valid b [1, 0, 1] := ⟨by simp; omega, by simp⟩
    have := h [1, 0, 1] [1, 1, 0] hv2 hv1 (by simp) (by decide)
    have e : P (-(b : ℤ)) [1, 0, 1] - P (-(b : ℤ)) [1, 1, 0] = (b : ℤ) + 1 := by
      simp [P_cons]; ring
    rwa [e] at this
  · intro hM s t _ _ _ hst
    have h1 := sub_one_dvd_P_sub_sum (-(b : ℤ)) s
    have h2 := sub_one_dvd_P_sub_sum (-(b : ℤ)) t
    have e : -(b : ℤ) - 1 = -((b : ℤ) + 1) := by ring
    rw [e, neg_dvd] at h1 h2
    have := dvd_sub h1 h2
    rw [hst.sum_eq] at this
    have e2 : P (-(b : ℤ)) s - (t.sum : ℤ) - (P (-(b : ℤ)) t - t.sum) =
      P (-(b : ℤ)) s - P (-(b : ℤ)) t := by ring
    rw [e2] at this
    exact hM.trans this

/-! ### The factorial number system (section 21.5) -/

/-- The value of a digit string in the factorial number system (section 21.5.1), most
significant digit first: the last digit sits at position 1 and counts `1!`. -/
def factVal : List ℕ → ℕ
  | [] => 0
  | d :: t => d * (t.length + 1).factorial + factVal t

/-- A string is a valid factorial representation: the digit at position `i` is at most `i`,
and the leading digit is not 0. -/
def FactValid : List ℕ → Prop
  | [] => True
  | d :: t => 1 ≤ d ∧ d ≤ t.length + 1 ∧ ∀ i (h : i < t.length), t[i] ≤ t.length - i

/-- **Proposition 21.14** (section 21.5.1). No modulus `M ≥ 2` makes `n mod M` a function of
the digit multiset on numbers with 3 or more digits: `(1,0,1) = 7` and `(1,1,0) = 8`. -/
theorem factorial_no_invariant_residue :
    ¬ ∃ M, 2 ≤ M ∧ ∀ s t : List ℕ, FactValid s → FactValid t → 3 ≤ s.length → s.Perm t →
      factVal s ≡ factVal t [MOD M] := by
  rintro ⟨M, hM, h⟩
  have v : ∀ s ∈ [[1, 1, 0], [1, 0, 1]], FactValid s := by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;>
      refine ⟨by norm_num, by norm_num, fun i hi => ?_⟩ <;> simp at hi <;> interval_cases i <;> simp
  have := h [1, 1, 0] [1, 0, 1] (v _ (by simp)) (v _ (by simp)) (by simp) (by decide)
  have e1 : factVal [1, 1, 0] = 7 + 1 := by decide
  have e2 : factVal [1, 0, 1] = 7 + 0 := by decide
  rw [e1, e2] at this
  have := Nat.ModEq.add_left_cancel' 7 this
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
  omega

/-- For a prime `p` with `p ≤ i < 2 p`, `p^2` does not divide `i!`. -/
lemma not_sq_dvd_factorial {p i : ℕ} (hp : p.Prime) (h1 : p ≤ i) (h2 : i < 2 * p) :
    ¬ p ^ 2 ∣ i.factorial := by
  have hp2 := hp.two_le
  have hlog : Nat.log p i < 2 := Nat.log_lt_of_lt_pow (by omega) (by nlinarith)
  rw [hp.pow_dvd_factorial_iff hlog]
  simp only [show Finset.Ico 1 2 = {1} by rfl, Finset.sum_singleton, pow_one]
  have : i / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **Proposition 21.15** (section 21.5.1). A digit `a ≥ 1` at position `i ≥ 1` of the
factorial system pays for itself, `a * i! = a^a`, only for `(a, i) = (1, 1)` and `(2, 2)`. -/
theorem factorial_selfPaying {a i : ℕ} (ha : 1 ≤ a) (hi : 1 ≤ i)
    (h : a ^ (a - 1) = i.factorial) : (a = 1 ∧ i = 1) ∨ (a = 2 ∧ i = 2) := by
  -- a prime `p ≥ 3` with `p ≤ i < 2 p`
  have hprime : 3 ≤ i → ∃ p, p.Prime ∧ 3 ≤ p ∧ p ≤ i ∧ i < 2 * p := by
    intro hi3
    rcases Nat.eq_or_lt_of_le hi3 with rfl | hi4
    · exact ⟨3, Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
    · obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (i / 2) (by omega)
      exact ⟨p, hp, by omega, by omega, by omega⟩
  rcases Nat.lt_or_ge i 3 with hi3 | hi3
  · -- `i = 1` or `i = 2`
    have hge : 2 ≤ a → 2 ≤ a ^ (a - 1) := fun h2 =>
      le_trans h2 (by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ (a - 1) := by
            rcases Nat.eq_or_lt_of_le h2 with rfl | h3
            · norm_num
            · exact Nat.pow_le_pow_right (by omega) (by omega))
    interval_cases i
    · left; refine ⟨?_, rfl⟩
      by_contra hne
      have := hge (by omega); simp at h; omega
    · right; refine ⟨?_, rfl⟩
      rcases Nat.lt_or_ge a 3 with ha3 | ha3
      · interval_cases a <;> simp_all
      · have : 3 ^ 2 ≤ a ^ (a - 1) :=
          (Nat.pow_le_pow_left ha3 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
        simp at h; omega
  · exfalso
    obtain ⟨p, hp, hp3, hpi, hip⟩ := hprime hi3
    have hpa : p ∣ a := hp.dvd_of_dvd_pow (h ▸ Nat.dvd_factorial (by omega) hpi)
    have hap : p ≤ a := Nat.le_of_dvd (by omega) hpa
    have : p ^ 2 ∣ i.factorial := h ▸ (pow_dvd_pow_of_dvd hpa 2).trans (pow_dvd_pow a (by omega))
    exact not_sq_dvd_factorial hp hpi hip this

/-! ### Function fields `F_p[T]` (sections 21.1 and 24.2) -/

section FunctionField

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- The weight of a digit `d` in `F_p[T]` (section 21.1.1): `w(d) = d ^ (p ^ deg d)`. A nonzero
constant weighs itself, and `w(0) = 0`, the convention `0^0 = 0`. -/
noncomputable def ffWeight (d : (ZMod p)[X]) : (ZMod p)[X] := d ^ (p ^ d.natDegree)

/-- `f ^ (p ^ k) = f(T^(p^k))` in `F_p[T]`. -/
lemma pow_pow_eq_expand (f : (ZMod p)[X]) (k : ℕ) : f ^ (p ^ k) = expand (ZMod p) (p ^ k) f := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih, expand_mul, ZMod.expand_card, map_pow]

/-- **Proposition 21.1** (section 21.1.2). For a digit of degree `j`, `w(d) = d(T^(p^j))`. -/
theorem ffWeight_eq_expand (d : (ZMod p)[X]) :
    ffWeight d = expand (ZMod p) (p ^ d.natDegree) d :=
  pow_pow_eq_expand d _

/-- **Proposition 21.1**, linearity (section 21.1.2): within one degree class the weight is
additive, so the weight sum of a list of digits of degree `j` is the expansion of their sum. -/
theorem ffWeight_sum_of_degree (L : List (ZMod p)[X]) (j : ℕ)
    (hL : ∀ d ∈ L, d.natDegree = j) :
    (L.map ffWeight).sum = expand (ZMod p) (p ^ j) L.sum := by
  induction L with
  | nil => simp
  | cons d L ih =>
    simp only [List.map_cons, List.sum_cons, map_add]
    rw [ih (fun e he => hL e (by simp [he])), ffWeight_eq_expand, hL d (by simp)]

/-- **Proposition 21.3** (section 21.1.3). Adding a constant `c` to a digit adds `c` to its
weight: `w(d + c) = w(d) + c`. So under `0^0 = 0` the translates `n + c` of a solution are
solutions. -/
theorem ffWeight_add_C (d : (ZMod p)[X]) (c : ZMod p) : ffWeight (d + C c) = ffWeight d + C c := by
  rw [ffWeight, ffWeight, natDegree_add_C, add_pow_char_pow, ← C_pow, ZMod.pow_card_pow]

/-- The value `sum d_i B^i` of a list of digits, least significant first, in any commutative
ring. -/
def ringVal {R : Type*} [CommRing R] (B : R) : List R → R
  | [] => 0
  | d :: t => d + B * ringVal B t

/-- **Proposition 21.5** (section 21.1.4), and the identity behind section 1.6 in any
commutative ring: `B - 1` divides `sum d_i B^i - sum d_i`. -/
theorem sub_one_dvd_ringVal_sub_sum {R : Type*} [CommRing R] (B : R) (L : List R) :
    B - 1 ∣ ringVal B L - L.sum := by
  induction L with
  | nil => simp [ringVal]
  | cons d t ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨ringVal B t + k, ?_⟩
    simp only [ringVal, List.sum_cons]
    linear_combination hk

/-- **The Frobenius identity behind Lemma 24.1** (section 24.2.1). In `F_p[T]`,
`n(T^p) = n^p = sum d_i(T^p) (B^p)^i`: Frobenius maps each digit and the base separately. -/
theorem expand_ringVal (B : (ZMod p)[X]) (L : List (ZMod p)[X]) :
    expand (ZMod p) p (ringVal B L) = ringVal (B ^ p) (L.map fun d => expand (ZMod p) p d) := by
  induction L with
  | nil => simp [ringVal]
  | cons d t ih =>
    simp only [ringVal, List.map_cons, map_add, map_mul, ih, ZMod.expand_card]

end FunctionField

/-! ### Base `-1 + i` (section 23.4) -/

section GaussianBase

/-- The base `β = -1 + i` of section 23.4. -/
def beta : GaussianInt := ⟨-1, 1⟩

/-- `β^4 = -4` (proof of Theorem R2.1). -/
lemma beta_pow_four : beta ^ 4 = -4 := by decide

/-- The value `a₀ + a₁ β + a₂ β^2 + a₃ β^3` of a block of four digits. -/
def blockC (a : ℕ × ℕ × ℕ × ℕ) : GaussianInt :=
  a.1 + a.2.1 * beta + a.2.2.1 * beta ^ 2 + a.2.2.2 * beta ^ 3

lemma blockC_re (a : ℕ × ℕ × ℕ × ℕ) : (blockC a).re = a.1 - a.2.1 + 2 * a.2.2.2 := by
  simp [blockC, beta, pow_succ]; ring

lemma blockC_im (a : ℕ × ℕ × ℕ × ℕ) : (blockC a).im = a.2.1 - 2 * a.2.2.1 + 2 * a.2.2.2 := by
  simp [blockC, beta, pow_succ]; ring

/-- Cut a digit string, least significant first, into blocks of four digits. -/
def flatten4 : List (ℕ × ℕ × ℕ × ℕ) → List ℕ
  | [] => []
  | a :: t => a.1 :: a.2.1 :: a.2.2.1 :: a.2.2.2 :: flatten4 t

/-- `sum_j C_j (-4)^j` for a list of blocks, least significant first. -/
def gVal : List (ℕ × ℕ × ℕ × ℕ) → GaussianInt
  | [] => 0
  | a :: t => blockC a + (-4) * gVal t

/-- `sum_j y_j (-4)^j` for a list of integers, least significant first. -/
def zVal : List ℤ → ℤ
  | [] => 0
  | y :: t => y + (-4) * zVal t

/-- The value in base `β` of a string cut into blocks is `sum C_j (-4)^j`. -/
lemma ofDigits_beta_flatten4 (bl : List (ℕ × ℕ × ℕ × ℕ)) :
    Nat.ofDigits beta (flatten4 bl) = gVal bl := by
  induction bl with
  | nil => simp [flatten4, gVal, Nat.ofDigits]
  | cons a t ih =>
    rw [flatten4, ofDigits_cons', ofDigits_cons', ofDigits_cons', ofDigits_cons', ih, gVal,
      blockC]
    linear_combination gVal t * beta_pow_four

/-- An integer combination `sum y_j (-4)^j` with `-2 ≤ y_j ≤ 3` vanishes only when every
`y_j` is 0. -/
lemma eq_zero_of_zVal (L : List ℤ) (hL : ∀ y ∈ L, -2 ≤ y ∧ y ≤ 3) (h : zVal L = 0) :
    ∀ y ∈ L, y = 0 := by
  induction L with
  | nil => simp
  | cons y L ih =>
    rw [zVal] at h
    have hy := hL y (by simp)
    have h4 : y = 4 * zVal L := by linarith
    have hy0 : y = 0 := by
      have : zVal L = 0 := by
        rcases lt_trichotomy (zVal L) 0 with h | h | h <;> [nlinarith; exact h; nlinarith]
      rw [h4, this]; ring
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hy0
    · apply ih (fun w hw => hL w (by simp [hw])) _ z hz
      rw [hy0] at h; linarith

lemma im_gVal (bl : List (ℕ × ℕ × ℕ × ℕ)) :
    (gVal bl).im = zVal (bl.map fun a => (blockC a).im) := by
  induction bl with
  | nil => rfl
  | cons a t ih =>
    simp only [gVal, List.map_cons, zVal]
    rw [← ih]
    simp

lemma re_gVal (bl : List (ℕ × ℕ × ℕ × ℕ)) :
    (gVal bl).re = zVal (bl.map fun a => (blockC a).re) := by
  induction bl with
  | nil => rfl
  | cons a t ih =>
    simp only [gVal, List.map_cons, zVal]
    rw [← ih]
    simp

lemma zVal_eq_ofDigits (L : List ℕ) :
    zVal (L.map fun d : ℕ => (d : ℤ)) = Nat.ofDigits (-4 : ℤ) L := by
  induction L with
  | nil => rfl
  | cons d t ih => rw [List.map_cons, zVal, ih, ofDigits_cons']

/-- **Theorem R2.1** (section 23.4), block form. Let a string of digits 0 and 1 in base
`β = -1 + i` be cut into blocks `(a₀, a₁, a₂, a₃)` of four digits. If its value is a rational
integer, then every block has `a₁ = 0` and `a₂ = a₃`, and the value is the base `-4` number
with digits `a₀ + 2 a₂`. With the uniqueness of representations in base `-1 + i` and base
`-4` (cited), this gives the lengths `≡ 1, 4 (mod 8)` of positive integers. -/
theorem gaussian_blocks (bl : List (ℕ × ℕ × ℕ × ℕ))
    (hdig : ∀ a ∈ bl, a.1 ≤ 1 ∧ a.2.1 ≤ 1 ∧ a.2.2.1 ≤ 1 ∧ a.2.2.2 ≤ 1)
    (hreal : (Nat.ofDigits beta (flatten4 bl)).im = 0) :
    (∀ a ∈ bl, a.2.1 = 0 ∧ a.2.2.1 = a.2.2.2) ∧
      (Nat.ofDigits beta (flatten4 bl)).re =
        Nat.ofDigits (-4 : ℤ) (bl.map fun a => a.1 + 2 * a.2.2.1) := by
  rw [ofDigits_beta_flatten4, im_gVal] at hreal
  have hzero := eq_zero_of_zVal _ (by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    have := hdig a ha
    rw [blockC_im]; omega) hreal
  have hblock : ∀ a ∈ bl, a.2.1 = 0 ∧ a.2.2.1 = a.2.2.2 := by
    intro a ha
    have h1 := hzero _ (List.mem_map.2 ⟨a, ha, rfl⟩)
    have := hdig a ha
    rw [blockC_im] at h1
    omega
  refine ⟨hblock, ?_⟩
  rw [ofDigits_beta_flatten4, re_gVal, ← zVal_eq_ofDigits, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a ha
  rw [Function.comp_apply, blockC_re, (hblock a ha).1, ← (hblock a ha).2]
  push_cast
  ring

end GaussianBase

end Munchausen
