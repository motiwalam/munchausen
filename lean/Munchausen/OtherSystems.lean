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
* base `-1 + i`: the block form of Theorem 23.1 (section 23.4);
* other weights: the identity with forced residues (section 17.2).
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

/-- `β^4 = -4` (proof of Theorem 23.1). -/
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

/-- **Theorem 23.1** (section 23.4), block form. Let a string of digits 0 and 1 in base
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

/-! ### Section 17.2: other weights with forced residues -/

/-- **Section 17.2**, the identity with forced residues. Let a weight `W` satisfy
`W(x) ≡ x + r (mod b - 1)` for every digit `x ≥ 1`, and `W(0) = z`. A string with `P_s(b)`
equal to its weight sum, `d` digits and `c₀` zeros, has `r (d - c₀) + z c₀ ≡ 0 (mod b - 1)`. -/
theorem forced_residue {b r z : ℕ} (hb : 1 ≤ b) (W : ℕ → ℕ)
    (hW : ∀ x, 1 ≤ x → W x ≡ x + r [MOD b - 1]) (hW0 : W 0 = z) {s : List ℕ}
    (hs : P b s = (s.map W).sum) :
    r * (s.length - s.count 0) + z * s.count 0 ≡ 0 [MOD b - 1] := by
  -- the weight sum is the digit sum plus `r (d - c₀) + z c₀`
  have key : ∀ t : List ℕ, (t.map W).sum ≡ t.sum + (r * (t.length - t.count 0) +
      z * t.count 0) [MOD b - 1] := by
    intro t
    induction t with
    | nil => simp [Nat.ModEq.refl]
    | cons d t ih =>
      have hc : t.count 0 ≤ t.length := List.count_le_length
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp only [List.map_cons, List.sum_cons, hW0, List.count_cons_self, List.length_cons]
        have e : r * (t.length + 1 - (t.count 0 + 1)) + z * (t.count 0 + 1) =
            z + (r * (t.length - t.count 0) + z * t.count 0) := by
          rw [show t.length + 1 - (t.count 0 + 1) = t.length - t.count 0 by omega]; ring
        rw [e]
        calc z + (t.map W).sum ≡ z + (t.sum + (r * (t.length - t.count 0) + z * t.count 0))
            [MOD b - 1] := ih.add_left z
          _ = 0 + t.sum + (z + (r * (t.length - t.count 0) + z * t.count 0)) := by ring
      · simp only [List.map_cons, List.sum_cons, List.count_cons_of_ne hd.ne',
          List.length_cons]
        have e : r * (t.length + 1 - t.count 0) + z * t.count 0 =
            r + (r * (t.length - t.count 0) + z * t.count 0) := by
          rw [show t.length + 1 - t.count 0 = (t.length - t.count 0) + 1 by omega]; ring
        rw [e]
        have := (hW d hd).add ih
        calc W d + (t.map W).sum ≡ d + r + (t.sum + (r * (t.length - t.count 0) +
              z * t.count 0)) [MOD b - 1] := this
          _ = d + t.sum + (r + (r * (t.length - t.count 0) + z * t.count 0)) := by ring
  have h1 := P_modEq_sum hb s
  rw [hs] at h1
  have h2 := h1.symm.trans (key s)
  -- cancel the digit sum
  exact Nat.ModEq.add_left_cancel' s.sum (h2.symm.trans (Nat.ModEq.refl _))

/-! ### Proposition 14.6: the length in a negative base -/

/-- An even-length string with digits below `b` has `(b + 1) P_t(-b) ≥ -b (b^|t| - 1)`: the
odd powers of `-b` are negative and the digits are at most `b - 1`. -/
lemma neg_base_even_lower {b : ℕ} (hb : 1 ≤ b) :
    ∀ (k : ℕ) (t : List ℕ), t.length = 2 * k → (∀ d ∈ t, d < b) →
      -((b : ℤ) * (b ^ t.length - 1)) ≤ (b + 1) * P (-(b : ℤ)) t := by
  intro k
  induction k with
  | zero =>
    intro t ht _
    obtain rfl : t = [] := List.length_eq_zero_iff.1 (by omega)
    simp
  | succ k ih =>
    intro t ht hdig
    obtain ⟨x, y, t', rfl⟩ : ∃ x y t', t = x :: y :: t' := by
      match t, ht with
      | x :: y :: t', _ => exact ⟨x, y, t', rfl⟩
    simp only [List.length_cons] at ht
    have ht' : t'.length = 2 * k := by omega
    have ih' := ih t' ht' (fun d hd => hdig d (by simp [hd]))
    have hx : (x : ℤ) ≤ b - 1 := by have := hdig x (by simp); omega
    have hy : (0 : ℤ) ≤ y := by positivity
    have he : Even t'.length := ⟨k, by omega⟩
    set B : ℤ := (b : ℤ) ^ t'.length
    have hB : 0 ≤ B := by positivity
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have h1 : (-(b : ℤ)) ^ (t'.length + 1) = -(b * B) := by rw [pow_succ, he.neg_pow]; ring
    have h2 : (-(b : ℤ)) ^ t'.length = B := he.neg_pow _
    simp only [P_cons, List.length_cons, h1, h2]
    have h3 : (b : ℤ) ^ (t'.length + 1 + 1) = b * b * B := by rw [pow_succ, pow_succ]; ring
    rw [h3]
    have h4 : 0 ≤ ((b : ℤ) - 1 - x) * ((b + 1) * (b * B)) :=
      mul_nonneg (by linarith) (by positivity)
    have h5 : 0 ≤ ((b : ℤ) + 1) * (y * B) := by positivity
    linear_combination ih' + h4 + h5

/-- An odd-length string `d :: t` with `1 ≤ d` and digits below `b` has
`(b + 1) P(-b) ≥ b^|t| + b`, the smallest value of that length. -/
lemma neg_base_odd_lower {b d : ℕ} (hb : 1 ≤ b) (hd : 1 ≤ d) {t : List ℕ} (ht : Even t.length)
    (hdig : ∀ e ∈ t, e < b) : (b : ℤ) ^ t.length + b ≤ (b + 1) * P (-(b : ℤ)) (d :: t) := by
  obtain ⟨k, hk⟩ := ht
  have h := neg_base_even_lower hb k t (by omega) hdig
  have he : Even t.length := ⟨k, hk⟩
  rw [P_cons, he.neg_pow]
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hB : (0 : ℤ) ≤ (b : ℤ) ^ t.length := by positivity
  have h6 : 0 ≤ ((d : ℤ) - 1) * ((b + 1) * (b : ℤ) ^ t.length) :=
    mul_nonneg (by linarith) (by positivity)
  linear_combination h + h6

/-- Three terms of the binomial expansion: `2 Y^2 (Y+1)^k ≥ 2 Y^(k+2) + 2 k Y^(k+1) + k (k-1) Y^k`. -/
lemma three_terms_le (Y k : ℕ) :
    2 * Y ^ (k + 2) + 2 * k * Y ^ (k + 1) + k * (k - 1) * Y ^ k ≤ 2 * Y ^ 2 * (Y + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e1 : 2 * Y ^ 2 * (Y + 1) ^ (k + 1) = 2 * Y ^ 2 * (Y + 1) ^ k * (Y + 1) := by ring
    rw [e1]
    have h := Nat.mul_le_mul_right (Y + 1) ih
    have e2 : (2 * Y ^ (k + 2) + 2 * k * Y ^ (k + 1) + k * (k - 1) * Y ^ k) * (Y + 1) =
        2 * Y ^ (k + 3) + (2 * k + 2) * Y ^ (k + 2) + (k * (k - 1) + 2 * k) * Y ^ (k + 1) +
          k * (k - 1) * Y ^ k := by ring
    rw [e2] at h
    have e3 : (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k := by
      rw [Nat.add_sub_cancel]
      rcases k with _ | k
      · rfl
      · rw [Nat.add_sub_cancel]; ring
    rw [e3]
    have e4 : 2 * Y ^ (k + 1 + 2) = 2 * Y ^ (k + 3) := by ring
    have e5 : 2 * (k + 1) * Y ^ (k + 1 + 1) = (2 * k + 2) * Y ^ (k + 2) := by ring
    rw [e4, e5]
    omega

/-- `7 (b-1)^(b-1) ≤ 3 b^(b-1)` for `b ≥ 4`, since `(1 + 1/n)^n ≥ 2 + (n-1)/(2n) ≥ 7/3`. -/
lemma seven_mul_pow_le {b : ℕ} (hb : 4 ≤ b) : 7 * (b - 1) ^ (b - 1) ≤ 3 * b ^ (b - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h := three_terms_le n n
  have hn : 3 ≤ n := by omega
  have e : 2 * n ^ (n + 2) + 2 * n * n ^ (n + 1) + n * (n - 1) * n ^ n =
      (5 * n ^ 2 - n) * n ^ n := by
    have : n ≤ 5 * n ^ 2 := by nlinarith
    zify [this, (by omega : 1 ≤ n)]
    ring
  rw [e] at h
  have hpos : 0 < n ^ 2 := by positivity
  have h2 : 14 * n ^ 2 * n ^ n ≤ 3 * ((5 * n ^ 2 - n) * n ^ n) := by
    have : 14 * n ^ 2 ≤ 3 * (5 * n ^ 2 - n) := by
      have : n ≤ 5 * n ^ 2 := by nlinarith
      zify [this]; nlinarith
    calc 14 * n ^ 2 * n ^ n ≤ 3 * (5 * n ^ 2 - n) * n ^ n := Nat.mul_le_mul_right _ this
      _ = 3 * ((5 * n ^ 2 - n) * n ^ n) := by ring
  have h3 : 14 * n ^ 2 * n ^ n ≤ 6 * n ^ 2 * (n + 1) ^ n := by nlinarith
  have h4 : 7 * n ^ n * (2 * n ^ 2) ≤ 3 * (n + 1) ^ n * (2 * n ^ 2) := by nlinarith
  exact Nat.le_of_mul_le_mul_right h4 (by positivity)

/-- The inequality of Proposition 14.6: for odd `d ≥ b + 2` (and `d ≥ 5`),
`d (b+1) (b-1)^(b-1) + 1 ≤ b^(d-1)`. -/
lemma prop14_6_ineq {b d : ℕ} (hb : 2 ≤ b) (hd : b + 2 ≤ d) (hd5 : 5 ≤ d) :
    d * (b + 1) * (b - 1) ^ (b - 1) + 1 ≤ b ^ (d - 1) := by
  rcases (by omega : b = 2 ∨ b = 3 ∨ 4 ≤ b) with rfl | rfl | hb4
  · induction d, hd5 using Nat.le_induction with
    | base => norm_num
    | succ d hd ih =>
      have := ih (by omega)
      rw [show d + 1 - 1 = d - 1 + 1 by omega, pow_succ]
      norm_num at this ⊢; omega
  · induction d, hd5 using Nat.le_induction with
    | base => norm_num
    | succ d hd ih =>
      have := ih (by omega)
      rw [show d + 1 - 1 = d - 1 + 1 by omega, pow_succ]
      norm_num at this ⊢; omega
  · induction d, hd using Nat.le_induction with
    | base =>
      have h7 := seven_mul_pow_le hb4
      have e : b ^ (b + 2 - 1) = b ^ 2 * b ^ (b - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      have hq : 3 * ((b + 2) * (b + 1)) < 7 * b ^ 2 := by nlinarith
      have hpos : 0 < b ^ (b - 1) := by positivity
      have : 7 * ((b + 2) * (b + 1) * (b - 1) ^ (b - 1)) <
          7 * (b ^ 2 * b ^ (b - 1)) := by
        calc 7 * ((b + 2) * (b + 1) * (b - 1) ^ (b - 1))
            = (b + 2) * (b + 1) * (7 * (b - 1) ^ (b - 1)) := by ring
          _ ≤ (b + 2) * (b + 1) * (3 * b ^ (b - 1)) := Nat.mul_le_mul_left _ h7
          _ = 3 * ((b + 2) * (b + 1)) * b ^ (b - 1) := by ring
          _ < 7 * b ^ 2 * b ^ (b - 1) := Nat.mul_lt_mul_of_pos_right hq hpos
          _ = 7 * (b ^ 2 * b ^ (b - 1)) := by ring
      omega
    | succ d hd ih =>
      rw [show d + 1 - 1 = d - 1 + 1 by omega, pow_succ]
      have := ih (by omega)
      set C := (b - 1) ^ (b - 1)
      have h1 : (d + 1) * (b + 1) * C ≤ 2 * (d * (b + 1) * C) := by
        have : d + 1 ≤ 2 * d := by omega
        calc (d + 1) * (b + 1) * C ≤ (2 * d) * (b + 1) * C :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
          _ = 2 * (d * (b + 1) * C) := by ring
      have h2 : 4 * b ^ (d - 1) ≤ b ^ (d - 1) * b := by
        rw [mul_comm 4]; exact Nat.mul_le_mul_left _ hb4
      omega

/-- **Proposition 14.6** (section 14.1). A solution in base `-b`, `b ≥ 2`, under `0^0 = m ≤ 1`
has at most `b + 1` digits (and an odd number of them, Proposition 12.2). -/
theorem prop14_6 {b m : ℕ} {s : List ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) (h : IsNegSolution b m s) :
    s.length ≤ b + 1 := by
  by_contra hlen
  have hodd := h.odd_length
  obtain ⟨d, t, rfl⟩ : ∃ d t, s = d :: t := by
    cases s with
    | nil => exact absurd rfl h.ne_nil
    | cons d t => exact ⟨d, t, rfl⟩
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 h.head_ne_zero
  have ht : Even t.length := by
    rw [List.length_cons, Nat.odd_add_one, Nat.not_odd_iff_even] at hodd; exact hodd
  have hdig : ∀ e ∈ t, e < b := fun e he => h.lt_base e (by simp [he])
  have hlow := neg_base_odd_lower (by omega) hd ht hdig
  have hF := Fs_le hm hb h.lt_base
  have heq := h.eq
  have hL5 : 5 ≤ t.length + 1 := by
    obtain ⟨k, hk⟩ := ht
    simp only [List.length_cons] at hlen
    omega
  have hineq := prop14_6_ineq hb (by simp only [List.length_cons] at hlen; omega) hL5
  simp only [List.length_cons, Nat.add_sub_cancel] at hF hineq
  rw [heq] at hlow
  have hF' : ((Fs m (d :: t) : ℕ) : ℤ) ≤ ((t.length + 1) * (b - 1) ^ (b - 1) : ℕ) := by
    exact_mod_cast hF
  have hineq' : (((t.length + 1) * (b + 1) * (b - 1) ^ (b - 1) + 1 : ℕ) : ℤ) ≤
      ((b ^ t.length : ℕ) : ℤ) := by exact_mod_cast hineq
  push_cast at hF' hineq' hlow
  nlinarith

end Munchausen
