import Munchausen.Applications

/-!
# Theorems about the model: the algebraic parts of chapter 29

Section 29.2 studies the free residue dimension `k(B)` of a base `B ∈ F_q[T]` of degree
`e ≥ 2`. Let `R = F_q[T]/(B - 1)`, `φ(x) = x^q` its Frobenius, `W_j` the classes of the
polynomials of degree at most `j`, and

    J = ∑_{j = 1}^{e-1} (φ^j - 1) W_j,     k(B) = e - dim J.

Both bounds below are linear algebra over `F_q`. The lower bound is the inclusion
`J ⊆ (φ - 1) R` of Lemma 29.8 (4). The upper bound, Theorem 29.11 (1), uses only the terms
`j = e - 2` and `j = e - 1` of `J`. We prove both in abstract form
(`finrank_ker_le_codim`, `codim_le_finrank_ker_add_one`) and then for `R` itself:

    dim R^φ ≤ k(B) ≤ dim R^φ + 1.

With Berlekamp's count `dim R^φ = ω(B - 1)` (Lemma 29.8 (1) for `j = 1`, proved with the
Chinese remainder theorem and the fixed points of `x ↦ x^q` modulo a prime power), these are
Theorem 21.6 and Theorem 29.11 (1): `ω(B - 1) ≤ k(B) ≤ ω(B - 1) + 1`. The dual argument also
gives condition (a) of Theorem 29.11 (2) (`comp_pow_eq_of_codim_gt`), and with the
nondegenerate pairing `(x, y) ↦ ℓ(x y)` this proves Theorem 29.11 (3): `k(B) = ω(B - 1)` when
`B - 1` is not squarefree.

Corollary 29.10 rests on a counting fact about the degrees of the factors of `B - 1`, proved
here as `exists_good_factor`. The example of Lemma 29.14 is checked by `decide`.
-/

open Polynomial Module

namespace Munchausen

/-! ### Lemma 29.2: the weights near the top -/

/-- **Lemma 29.2** (section 29.1.2). For `0 ≤ y < b`,
`e^(-y) b^(b-y) ≤ w(b - y) ≤ e^(-y) b^(b-y) exp(y^2 / (2 (b - y)))`. -/
theorem lemma29_2 {b y : ℕ} (hy : y < b) :
    Real.exp (-(y : ℝ)) * (b : ℝ) ^ (b - y) ≤ ((b - y : ℕ) : ℝ) ^ (b - y) ∧
      ((b - y : ℕ) : ℝ) ^ (b - y) ≤
        Real.exp (-(y : ℝ)) * (b : ℝ) ^ (b - y) * Real.exp ((y : ℝ) ^ 2 / (2 * (b - y : ℕ))) := by
  set n := b - y with hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : (b : ℝ) = n + y := by rw [hn]; push_cast [Nat.cast_sub hy.le]; ring
  have hb0 : (0 : ℝ) < b := by rw [hb]; positivity
  have hpow : ∀ x : ℝ, 0 < x → x ^ n = Real.exp (n * Real.log x) := by
    intro x hx; rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [hpow b hb0, hpow n hn0, ← Real.exp_add, ← Real.exp_add]
  have hlog : Real.log b - Real.log n = Real.log (1 + y / n) := by
    rw [← Real.log_div hb0.ne' hn0.ne', hb, add_div, div_self hn0.ne']
  have hs : (0 : ℝ) ≤ y / n := by positivity
  constructor
  · apply Real.exp_le_exp.2
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + y / n by positivity)
    have : (n : ℝ) * (Real.log b - Real.log n) ≤ y := by
      rw [hlog]
      calc (n : ℝ) * Real.log (1 + y / n) ≤ n * (1 + y / n - 1) :=
            mul_le_mul_of_nonneg_left h1 hn0.le
        _ = y := by field_simp; ring
    linarith
  · apply Real.exp_le_exp.2
    have h1 := Real.le_log_one_add_of_nonneg hs
    have h2 : (y : ℝ) / n - (y / n) ^ 2 / 2 ≤ 2 * (y / n) / (y / n + 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [pow_nonneg hs 3]
    have : (y : ℝ) - y ^ 2 / (2 * n) ≤ n * (Real.log b - Real.log n) := by
      rw [hlog]
      calc (y : ℝ) - y ^ 2 / (2 * n) = n * (y / n - (y / n) ^ 2 / 2) := by
            field_simp
        _ ≤ n * Real.log (1 + y / n) := mul_le_mul_of_nonneg_left (h2.trans h1) hn0.le
    linarith

/-! ### The abstract statement -/

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- **Lemma 29.8 (4)**, abstract form: `φ^j - 1 = (φ - 1)(1 + φ + ... + φ^(j-1))`, so the image
of `φ^j - 1` lies in the image of `φ - 1`. -/
lemma range_pow_sub_one_le (φ : V →ₗ[K] V) (j : ℕ) :
    LinearMap.range (φ ^ j - 1) ≤ LinearMap.range (φ - 1) := by
  rw [← mul_geom_sum φ j]
  exact LinearMap.range_comp_le_range _ _

/-- The codimension of a subspace is the dimension of its annihilator. -/
lemma finrank_dualAnnihilator (J : Submodule K V) :
    finrank K J.dualAnnihilator = finrank K V - finrank K J := by
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq J
  omega

/-- **Theorem 29.11 (1)**, abstract form (section 29.2.3). Let `φ` be a linear endomorphism of a
finite-dimensional space `V`, let `W` be a subspace of codimension at most 1, and let `J`
contain `(φ^(n+1) - 1) V` and `(φ^n - 1) W`. Then the codimension of `J` is at most
`dim ker(φ - 1) + 1`. -/
theorem codim_le_finrank_ker_add_one (φ : V →ₗ[K] V) (W J : Submodule K V) (n : ℕ)
    (hW : finrank K V ≤ finrank K W + 1)
    (htop : LinearMap.range (φ ^ (n + 1) - 1) ≤ J) (hWJ : W.map (φ ^ n - 1) ≤ J) :
    finrank K V - finrank K J ≤ finrank K (LinearMap.ker (φ - 1)) + 1 := by
  rw [← finrank_dualAnnihilator]
  set S := J.dualAnnihilator
  set T := ((φ - 1).dualMap).domRestrict S
  have hrk := LinearMap.finrank_range_add_finrank_ker (K := K) (V := ↥S) T
  -- the image: `λ ∘ (φ - 1) = -(λ ∘ (φ^n - 1)) ∘ φ` with `λ ∘ (φ^n - 1)` vanishing on `W`
  have hrange : LinearMap.range T ≤ W.dualAnnihilator.map (-φ.dualMap) := by
    rintro _ ⟨⟨l, hl⟩, rfl⟩
    have hl' : ∀ v ∈ J, l v = 0 := (Submodule.mem_dualAnnihilator l).1 hl
    refine ⟨(φ ^ n - 1).dualMap l, ?_, ?_⟩
    · rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      intro w hw
      exact hl' _ (hWJ ⟨w, hw, rfl⟩)
    · ext v
      have h0 : l ((φ ^ (n + 1) - 1) v) = 0 := hl' _ (htop ⟨v, rfl⟩)
      have hsplit : (φ ^ (n + 1) - 1) v = (φ ^ n - 1) (φ v) + (φ - 1) v := by
        simp only [LinearMap.sub_apply, Module.End.one_apply, pow_succ, Module.End.mul_apply]
        abel
      rw [hsplit, map_add] at h0
      simp only [T, LinearMap.domRestrict_apply, LinearMap.neg_apply, LinearMap.dualMap_apply]
      linear_combination (-1 : K) * h0
  have hW' : finrank K W.dualAnnihilator ≤ 1 := by rw [finrank_dualAnnihilator]; omega
  have h1 : finrank K (LinearMap.range T) ≤ 1 :=
    (Submodule.finrank_mono hrange).trans ((Submodule.finrank_map_le _ _).trans hW')
  -- the kernel: functionals vanishing on `(φ - 1) V`
  have h2 : finrank K (LinearMap.ker T) ≤ finrank K (LinearMap.ker (φ - 1)) := by
    have hinj : Function.Injective (S.subtype ∘ₗ (LinearMap.ker T).subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hle : LinearMap.range (S.subtype ∘ₗ (LinearMap.ker T).subtype) ≤
        (LinearMap.range (φ - 1)).dualAnnihilator := by
      rintro _ ⟨⟨⟨l, hl⟩, hk⟩, rfl⟩
      rw [Submodule.mem_dualAnnihilator]
      rintro _ ⟨v, rfl⟩
      have : T ⟨l, hl⟩ = 0 := hk
      simpa [T] using congrArg (fun f => f v) this
    have := (LinearMap.finrank_range_of_inj hinj).symm.le.trans (Submodule.finrank_mono hle)
    rw [finrank_dualAnnihilator] at this
    have hrn := LinearMap.finrank_range_add_finrank_ker (φ - 1)
    omega
  omega

/-- **Theorem 21.6**, abstract form (with Lemma 29.8 (4)): if `J ⊆ (φ - 1) V`, the codimension
of `J` is at least `dim ker(φ - 1)`. -/
theorem finrank_ker_le_codim (φ : V →ₗ[K] V) (J : Submodule K V)
    (hJ : J ≤ LinearMap.range (φ - 1)) :
    finrank K (LinearMap.ker (φ - 1)) ≤ finrank K V - finrank K J := by
  have h1 := Submodule.finrank_mono hJ
  have h2 := LinearMap.finrank_range_add_finrank_ker (φ - 1)
  omega

/-- **Theorem 29.11 (2)**, condition (a) and its consequence, abstract form (section 29.2.3).
Let `ℓ` be a functional such that every functional vanishing on `W` is a multiple of `ℓ`, and
let `J` contain `(φ^(n+1) - 1) V` and `(φ^n - 1) W`. If the codimension of `J` exceeds
`dim ker(φ - 1)`, then `Λ_n = ∑_{i ≤ n} ℓ ∘ φ^i = 0`, and so `ℓ ∘ φ^(n+1) = ℓ`. -/
theorem comp_pow_eq_of_codim_gt (φ : V →ₗ[K] V) (W J : Submodule K V) (ℓ : Dual K V) (n : ℕ)
    (hℓ : ∀ μ ∈ W.dualAnnihilator, ∃ c : K, μ = c • ℓ)
    (htop : LinearMap.range (φ ^ (n + 1) - 1) ≤ J) (hWJ : W.map (φ ^ n - 1) ≤ J)
    (hgt : finrank K (LinearMap.ker (φ - 1)) < finrank K V - finrank K J) :
    ∀ v, ℓ ((φ ^ (n + 1)) v) = ℓ v := by
  -- a functional on `J` that is not `φ`-invariant
  obtain ⟨l, hl, hne⟩ : ∃ l ∈ J.dualAnnihilator, ∃ v, l (φ v - v) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : J.dualAnnihilator ≤ (LinearMap.range (φ - 1)).dualAnnihilator := by
      intro l hl
      rw [Submodule.mem_dualAnnihilator]
      rintro _ ⟨v, rfl⟩
      simpa using hcon l hl v
    have h1 := Submodule.finrank_mono hle
    rw [finrank_dualAnnihilator, finrank_dualAnnihilator] at h1
    have h2 := LinearMap.finrank_range_add_finrank_ker (φ - 1)
    have h3 := Submodule.finrank_le J
    omega
  have hl' : ∀ v ∈ J, l v = 0 := (Submodule.mem_dualAnnihilator l).1 hl
  -- `δ_n = c ℓ`
  obtain ⟨c, hc⟩ := hℓ ((φ ^ n - 1).dualMap l) (by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact hl' _ (hWJ ⟨w, hw, rfl⟩))
  have hδ : ∀ v, l ((φ ^ n) v) - l v = c * ℓ v := by
    intro v
    have := congrArg (fun f => f v) hc
    simpa [LinearMap.dualMap_apply, map_sub] using this
  -- `δ_1 = -c ℓ ∘ φ`
  have hkey : ∀ v, l (φ v) - l v = -(c * ℓ (φ v)) := by
    intro v
    have h0 : l ((φ ^ (n + 1) - 1) v) = 0 := hl' _ (htop ⟨v, rfl⟩)
    have h1 := hδ (φ v)
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, pow_succ,
      Module.End.mul_apply] at h0
    linear_combination h0 - h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hne
    apply hv
    rw [map_sub, hkey v]; ring
  -- telescoping: `δ_n = ∑_{i<n} δ_1 ∘ φ^i`
  have htel : ∀ v, l ((φ ^ n) v) - l v = ∑ i ∈ Finset.range n, -(c * ℓ ((φ ^ (i + 1)) v)) := by
    intro v
    have := Finset.sum_range_sub (fun i => l ((φ ^ i) v)) n
    simp only [pow_zero, Module.End.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', Module.End.mul_apply]
    exact hkey _
  have hΛ : ∀ v, ∑ i ∈ Finset.range (n + 1), ℓ ((φ ^ i) v) = 0 := by
    intro v
    have h := (hδ v).symm.trans (htel v)
    rw [Finset.sum_range_succ', pow_zero, Module.End.one_apply]
    have : c * (∑ i ∈ Finset.range n, ℓ ((φ ^ (i + 1)) v) + ℓ v) = 0 := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h
      linear_combination h
    exact (mul_eq_zero.1 this).resolve_left hc0
  intro v
  have h1 := hΛ v
  have h2 := hΛ (φ v)
  rw [Finset.sum_range_succ'] at h1
  rw [Finset.sum_range_succ] at h2
  simp only [← Module.End.mul_apply, ← pow_succ] at h2
  simp only [pow_zero, Module.End.one_apply] at h1
  linear_combination h2 - h1

end Abstract

/-! ### The residue ring `F_q[T]/(B - 1)` -/

lemma natDegree_sub_one {K : Type*} [Field K] (B : K[X]) : (B - 1).natDegree = B.natDegree := by
  rw [← C_1, natDegree_sub_C]

lemma sub_one_ne_zero {K : Type*} [Field K] {B : K[X]} (hB : 1 ≤ B.natDegree) : B - 1 ≠ 0 := by
  intro h
  have := natDegree_sub_one B
  rw [h, natDegree_zero] at this
  omega

section Residue

variable {K : Type*} [Field K] [Fintype K]

/-- The Frobenius `x ↦ x^q` of `R = F_q[T]/(B - 1)`, as an `F_q`-linear map (section 29.2.1). -/
noncomputable def frobR (B : K[X]) : AdjoinRoot (B - 1) →ₗ[K] AdjoinRoot (B - 1) :=
  (FiniteField.frobeniusAlgHom K (AdjoinRoot (B - 1))).toLinearMap

/-- `W_j`, the classes of the polynomials of degree at most `j` (section 29.2.1). -/
noncomputable def Wj (B : K[X]) (j : ℕ) : Submodule K (AdjoinRoot (B - 1)) :=
  LinearMap.range ((AdjoinRoot.mkₐ (B - 1)).toLinearMap ∘ₗ (degreeLT K (j + 1)).subtype)

/-- The image `J = ∑_{j=1}^{e-1} (φ^j - 1) W_j` of the digit sums (section 29.2.1). -/
noncomputable def Jsum (B : K[X]) : Submodule K (AdjoinRoot (B - 1)) :=
  ⨆ j ∈ Finset.Icc 1 (B.natDegree - 1), (Wj B j).map (frobR B ^ j - 1)

/-- The free residue dimension `k(B) = e - dim J` (sections 21.1.4 and 29.2.1). -/
noncomputable def kDim (B : K[X]) : ℕ := B.natDegree - finrank K (Jsum B)

variable {B : K[X]}

omit [Fintype K] in
lemma finrank_residue (hB : 1 ≤ B.natDegree) : finrank K (AdjoinRoot (B - 1)) = B.natDegree := by
  rw [(AdjoinRoot.powerBasis (sub_one_ne_zero hB)).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_sub_one B]

omit [Fintype K] in
/-- `dim W_j = j + 1` for `j < e`: no nonzero polynomial of degree below `e` is a multiple of
`B - 1`. -/
lemma finrank_Wj (hB : 1 ≤ B.natDegree) {j : ℕ} (hj : j < B.natDegree) :
    finrank K (Wj B j) = j + 1 := by
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero (B := B) (by omega))).finite
  rw [Wj, LinearMap.finrank_range_of_inj, (degreeLTEquiv K (j + 1)).finrank_eq,
    Module.finrank_fin_fun]
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  change AdjoinRoot.mk (B - 1) p = AdjoinRoot.mk (B - 1) p' at h
  have hdvd : B - 1 ∣ p - p' := AdjoinRoot.mk_eq_mk.1 h
  have hdeg : (p - p').degree < (B - 1).degree := by
    rw [mem_degreeLT] at hp hp'
    rw [degree_eq_natDegree (sub_one_ne_zero hB), natDegree_sub_one B]
    refine (degree_sub_le _ _).trans_lt (max_lt (hp.trans_le ?_) (hp'.trans_le ?_)) <;>
      exact_mod_cast (show j + 1 ≤ B.natDegree by omega)
  have := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  exact Subtype.ext (sub_eq_zero.1 this)

omit [Fintype K] in
lemma Wj_top (hB : 1 ≤ B.natDegree) : Wj B (B.natDegree - 1) = ⊤ := by
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero (B := B) (by omega))).finite
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_Wj hB (by omega), finrank_residue hB]
  omega

lemma Jsum_le_range : Jsum B ≤ LinearMap.range (frobR B - 1) :=
  iSup₂_le fun j _ => (LinearMap.map_le_range).trans (range_pow_sub_one_le _ j)

/-- **Theorem 21.6** and **Lemma 29.8 (4)** for `R = F_q[T]/(B - 1)`, with `dim R^φ` in place of
`ω(B - 1)`: `k(B) ≥ dim ker(φ - 1)`. -/
theorem finrank_ker_le_kDim (hB : 1 ≤ B.natDegree) :
    finrank K (LinearMap.ker (frobR B - 1)) ≤ kDim B := by
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero (B := B) (by omega))).finite
  have := finrank_ker_le_codim (frobR B) (Jsum B) Jsum_le_range
  rwa [finrank_residue hB] at this

lemma Jsum_top_le (hB : 2 ≤ B.natDegree) :
    LinearMap.range (frobR B ^ (B.natDegree - 2 + 1) - 1) ≤ Jsum B := by
  have h1 : 1 ≤ B.natDegree := by omega
  have := le_iSup₂ (f := fun j (_ : j ∈ Finset.Icc 1 (B.natDegree - 1)) =>
    (Wj B j).map (frobR B ^ j - 1)) (B.natDegree - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  rw [show B.natDegree - 2 + 1 = B.natDegree - 1 by omega]
  rwa [Wj_top h1, Submodule.map_top] at this

lemma Jsum_W_le (hB : 2 ≤ B.natDegree) :
    (Wj B (B.natDegree - 2)).map (frobR B ^ (B.natDegree - 2) - 1) ≤ Jsum B := by
  rcases Nat.eq_zero_or_pos (B.natDegree - 2) with h0 | hpos
  · rw [h0, pow_zero, sub_self, Submodule.map_zero]
    exact bot_le
  · exact le_iSup₂ (f := fun j (_ : j ∈ Finset.Icc 1 (B.natDegree - 1)) =>
      (Wj B j).map (frobR B ^ j - 1)) (B.natDegree - 2) (Finset.mem_Icc.2 ⟨hpos, by omega⟩)

/-- **Theorem 29.11 (1)** (section 29.2.3), with `dim R^φ` in place of `ω(B - 1)`: for `B` of
degree `e ≥ 2`, `k(B) ≤ dim ker(φ - 1) + 1`. -/
theorem kDim_le (hB : 2 ≤ B.natDegree) :
    kDim B ≤ finrank K (LinearMap.ker (frobR B - 1)) + 1 := by
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero (B := B) (by omega))).finite
  have h1 : 1 ≤ B.natDegree := by omega
  have := codim_le_finrank_ker_add_one (frobR B) (Wj B (B.natDegree - 2)) (Jsum B)
    (B.natDegree - 2) (by rw [finrank_Wj h1 (by omega), finrank_residue h1]; omega)
    (Jsum_top_le hB) (Jsum_W_le hB)
  rwa [finrank_residue h1] at this

end Residue

/-! ### Berlekamp's count: `dim R^φ = ω(B - 1)` -/

section Berlekamp

variable {K : Type*} [Field K] [Fintype K]

/-- `X^q - X = ∏_{c ∈ F_q} (X - c)`. -/
lemma X_pow_card_sub_X_eq_prod :
    (X ^ Fintype.card K - X : K[X]) = ∏ c : K, (X - C c) := by
  have hm : (X ^ Fintype.card K - X : K[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast Fintype.one_lt_card)
  have hc : Multiset.card (X ^ Fintype.card K - X : K[X]).roots =
      (X ^ Fintype.card K - X : K[X]).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
    simp
  rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc,
    FiniteField.roots_X_pow_card_sub_X]
  rfl

/-- The fixed points of the Frobenius modulo a prime power are the constants: if
`P^e ∣ f^q - f` with `P` prime and `e ≥ 1`, then `f ≡ c (mod P^e)` for some `c ∈ F_q`
(proof of Lemma 29.8 (1), for `j = 1`). -/
lemma exists_C_of_dvd_pow_card_sub {P f : K[X]} (hP : Prime P) {e : ℕ}
    (hdvd : P ^ e ∣ f ^ Fintype.card K - f) : ∃ c : K, P ^ e ∣ f - C c := by
  set q := Fintype.card K
  have hprod : f ^ q - f = ∏ c : K, (f - C c) := by
    have := congrArg (aeval f) (X_pow_card_sub_X_eq_prod (K := K))
    simpa [map_prod] using this
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact ⟨0, by simp⟩
  have hP1 : P ∣ ∏ c : K, (f - C c) := hprod ▸ (dvd_pow_self P he.ne').trans hdvd
  obtain ⟨c, -, hc⟩ := (Prime.dvd_finsetProd_iff hP _).1 hP1
  refine ⟨c, ?_⟩
  -- `y = f - c` has `P^e ∣ y^e` and `P^e ∣ y^q - y`, hence `P^e ∣ y`
  set y := f - C c
  have hy : P ^ e ∣ y * (y ^ (q - 1) - 1) := by
    have hfr : y ^ q = f ^ q - C c := by
      have h1 := map_sub (FiniteField.frobeniusAlgHom K K[X]) f (C c)
      have h2 := (FiniteField.frobeniusAlgHom K K[X]).commutes c
      simp only [FiniteField.coe_frobeniusAlgHom, algebraMap_eq] at h1 h2
      rw [h1, h2]
    have hq : 1 ≤ q := Fintype.card_pos
    have : y * (y ^ (q - 1) - 1) = f ^ q - f := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq, hfr]; ring
    rw [this]; exact hdvd
  refine hP.pow_dvd_of_dvd_mul_right e ?_ hy
  intro h
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have : P ∣ y ^ (q - 1) := (hc.trans (dvd_pow_self y (by omega)))
  have h1 : P ∣ 1 := by
    have := dvd_sub this h
    rwa [sub_sub_cancel] at this
  exact hP.not_isUnit (isUnit_of_dvd_one h1)

/-- In `F_q[T]/(P^e)` with `P` prime and `e ≥ 1`, the fixed points of `x ↦ x^q` are the
`q` constants. -/
lemma natCard_fixed_local {P : K[X]} (hP : Prime P) {e : ℕ} (he : 1 ≤ e) :
    Nat.card {a : K[X] ⧸ Ideal.span {P} ^ e // a ^ Fintype.card K = a} = Fintype.card K := by
  set I := Ideal.span {P} ^ e
  have hI : I = Ideal.span {P ^ e} := Ideal.span_singleton_pow P e
  have hmk : ∀ f g : K[X], Ideal.Quotient.mk I f = Ideal.Quotient.mk I g ↔ P ^ e ∣ f - g := by
    intro f g
    rw [Ideal.Quotient.eq, hI, Ideal.mem_span_singleton]
  let toFix : K → {a : K[X] ⧸ I // a ^ Fintype.card K = a} := fun c =>
    ⟨Ideal.Quotient.mk I (C c), by rw [← map_pow, ← C_pow, FiniteField.pow_card]⟩
  have hbij : Function.Bijective toFix := by
    constructor
    · intro c c' h
      have h' := (hmk _ _).1 (congrArg Subtype.val h)
      rw [← C_sub] at h'
      by_contra hne
      have hu : IsUnit (C (c - c')) := isUnit_C.2 (sub_ne_zero.2 hne).isUnit
      exact hP.not_isUnit (isUnit_of_dvd_unit ((dvd_pow_self P (by omega)).trans h') hu)
    · rintro ⟨a, ha⟩
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hdvd : P ^ e ∣ f ^ Fintype.card K - f := by
        rw [← map_pow] at ha
        exact (hmk _ _).1 ha
      obtain ⟨c, hc⟩ := exists_C_of_dvd_pow_card_sub hP hdvd
      exact ⟨c, Subtype.ext ((hmk _ _).2 (by rw [← neg_sub, dvd_neg]; exact hc))⟩
  rw [← Nat.card_eq_of_bijective toFix hbij, Nat.card_eq_fintype_card]

variable [DecidableEq K]

/-- `ω(M)`, the number of distinct monic irreducible factors of `M` (section 29.2.1). -/
noncomputable def omegaF (M : K[X]) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors M).toFinset.card

/-- **Berlekamp's count**, Lemma 29.8 (1) for `j = 1` (section 29.2.1): the fixed ring of the
Frobenius of `R = F_q[T]/(B - 1)` has dimension `ω(B - 1)`. -/
theorem finrank_ker_frobR {B : K[X]} (hB : 1 ≤ B.natDegree) :
    finrank K (LinearMap.ker (frobR B - 1)) = omegaF (B - 1) := by
  have hne := sub_one_ne_zero hB
  have : Module.Finite K (AdjoinRoot (B - 1)) := (AdjoinRoot.powerBasis hne).finite
  set q := Fintype.card K
  set S := (UniqueFactorizationMonoid.normalizedFactors (B - 1)).toFinset
  set nf := UniqueFactorizationMonoid.normalizedFactors (B - 1)
  -- the Chinese remainder theorem
  have hprime : ∀ i ∈ S, Prime (Ideal.span {i}) := by
    intro i hi
    have hpi := UniqueFactorizationMonoid.prime_of_normalized_factor i
      (Multiset.mem_toFinset.1 hi)
    exact Ideal.prime_of_isPrime (by simpa using hpi.ne_zero)
      ((Ideal.span_singleton_prime hpi.ne_zero).2 hpi)
  have hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Ideal.span {i} ≠ Ideal.span {j} := by
    intro i hi j hj hij h
    apply hij
    exact (Ideal.span_singleton_eq_span_singleton.1 h).eq_of_normalized
      (UniqueFactorizationMonoid.normalize_normalized_factor i (Multiset.mem_toFinset.1 hi))
      (UniqueFactorizationMonoid.normalize_normalized_factor j (Multiset.mem_toFinset.1 hj))
  have hprod : ∏ i ∈ S, Ideal.span {i} ^ nf.count i = Ideal.span {B - 1} := by
    simp only [Ideal.span_singleton_pow, Ideal.prod_span_singleton]
    rw [← Finset.prod_multiset_count]
    exact Ideal.span_singleton_eq_span_singleton.2
      (UniqueFactorizationMonoid.prod_normalizedFactors hne)
  let Φ := IsDedekindDomain.quotientEquivPiOfFinsetProdEq (Ideal.span {B - 1})
    (fun i => Ideal.span {i}) (fun i => nf.count i) hprime hcop hprod
  -- count the fixed points
  have hker : Nat.card (LinearMap.ker (frobR B - 1)) =
      Nat.card {x : K[X] ⧸ Ideal.span {B - 1} // x ^ q = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rfl
  have hpi : Nat.card {x : K[X] ⧸ Ideal.span {B - 1} // x ^ q = x} = q ^ S.card := by
    let A := fun i : S => K[X] ⧸ Ideal.span {(i : K[X])} ^ nf.count (i : K[X])
    have e1 : {x : K[X] ⧸ Ideal.span {B - 1} // x ^ q = x} ≃ {y : (i : S) → A i // y ^ q = y} :=
      Φ.toEquiv.subtypeEquiv fun x =>
        (show x ^ q = x ↔ (Φ x) ^ q = Φ x by rw [← map_pow, Φ.injective.eq_iff])
    have e2 : {y : (i : S) → A i // y ^ q = y} ≃ ((i : S) → {a : A i // a ^ q = a}) :=
      (Equiv.subtypeEquivRight fun y => by simp only [funext_iff, Pi.pow_apply]).trans
        Equiv.subtypePiEquivPi
    rw [Nat.card_congr (e1.trans e2), Nat.card_pi]
    have hloc : ∀ i : S, Nat.card {a : A i // a ^ q = a} = q := by
      intro i
      have hmem := Multiset.mem_toFinset.1 i.2
      exact natCard_fixed_local (UniqueFactorizationMonoid.prime_of_normalized_factor _ hmem)
        (Multiset.one_le_count_iff_mem.2 hmem)
    simp only [hloc, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  rw [hpi, Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card] at hker
  exact Nat.pow_right_injective Fintype.one_lt_card hker

/-- **Theorem 21.6** (section 21.1.4) and **Lemma 29.8 (4)**: `k(B) ≥ ω(B - 1)` for every `B`
of degree at least 1. -/
theorem theorem21_6 {B : K[X]} (hB : 1 ≤ B.natDegree) : omegaF (B - 1) ≤ kDim B :=
  finrank_ker_frobR hB ▸ finrank_ker_le_kDim hB

/-- **Theorem 29.11 (1)** (section 29.2.3): `k(B) ≤ ω(B - 1) + 1` for every `B` of degree
`e ≥ 2`. -/
theorem theorem29_11_one {B : K[X]} (hB : 2 ≤ B.natDegree) : kDim B ≤ omegaF (B - 1) + 1 :=
  finrank_ker_frobR (B := B) (by omega) ▸ kDim_le hB

end Berlekamp

/-! ### Theorem 29.11 (3): no extra dimension when `B - 1` is not squarefree -/

section NotSquarefree

variable {K : Type*} [Field K] {B : K[X]}

/-- In the basis `1, t, ..., t^(e-1)`, the coordinates of the class of a polynomial of degree
below `e` are its coefficients. -/
lemma repr_mk (hB : 1 ≤ B.natDegree) {f : K[X]}
    (hf : f.natDegree < (AdjoinRoot.powerBasis (sub_one_ne_zero hB)).dim)
    (i : Fin (AdjoinRoot.powerBasis (sub_one_ne_zero hB)).dim) :
    (AdjoinRoot.powerBasis (sub_one_ne_zero hB)).basis.repr (AdjoinRoot.mk (B - 1) f) i =
      f.coeff i := by
  set pb := AdjoinRoot.powerBasis (sub_one_ne_zero hB)
  have : AdjoinRoot.mk (B - 1) f = pb.basis.equivFun.symm (fun j => f.coeff j) := by
    rw [Basis.equivFun_symm_apply, ← AdjoinRoot.aeval_eq, aeval_eq_sum_range' hf,
      ← Fin.sum_univ_eq_sum_range (fun j => f.coeff j • AdjoinRoot.root (B - 1) ^ j)]
    simp [pb, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
  rw [this, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

lemma dim_powerBasis (hB : 1 ≤ B.natDegree) :
    (AdjoinRoot.powerBasis (sub_one_ne_zero hB)).dim = B.natDegree := by
  rw [AdjoinRoot.powerBasis_dim, natDegree_sub_one]

/-- The functional `ℓ`, the coefficient of `t^(e-1)` (section 29.2.3). -/
noncomputable def topCoeff (hB : 1 ≤ B.natDegree) : Dual K (AdjoinRoot (B - 1)) :=
  (AdjoinRoot.powerBasis (sub_one_ne_zero hB)).basis.coord
    ⟨B.natDegree - 1, by rw [dim_powerBasis hB]; omega⟩

lemma topCoeff_mk (hB : 1 ≤ B.natDegree) {f : K[X]} (hf : f.natDegree < B.natDegree) :
    topCoeff hB (AdjoinRoot.mk (B - 1) f) = f.coeff (B.natDegree - 1) := by
  rw [topCoeff, Basis.coord_apply, repr_mk hB (by rwa [dim_powerBasis hB])]

/-- The pairing `(x, y) ↦ ℓ(x y)` is nondegenerate (section 29.2.3). -/
lemma exists_topCoeff_mul_ne_zero (hB : 1 ≤ B.natDegree) {x : AdjoinRoot (B - 1)}
    (hx : x ≠ 0) : ∃ y, topCoeff hB (x * y) ≠ 0 := by
  have hne := sub_one_ne_zero hB
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  set f := g % (B - 1)
  have hfg : AdjoinRoot.mk (B - 1) g = AdjoinRoot.mk (B - 1) f := by
    rw [AdjoinRoot.mk_eq_mk]
    have := EuclideanDomain.div_add_mod g (B - 1)
    exact ⟨g / (B - 1), by simp only [f]; linear_combination (-1 : K[X]) * this⟩
  rw [hfg] at hx ⊢
  have hf0 : f ≠ 0 := fun h => hx (by rw [h, map_zero])
  have hfd : f.natDegree < B.natDegree := by
    have := degree_mod_lt g hne
    rw [degree_eq_natDegree hf0, degree_eq_natDegree hne, natDegree_sub_one] at this
    exact_mod_cast this
  refine ⟨AdjoinRoot.mk (B - 1) (X ^ (B.natDegree - 1 - f.natDegree)), ?_⟩
  rw [← map_mul, topCoeff_mk hB]
  · have key := coeff_mul_X_pow f (B.natDegree - 1 - f.natDegree) f.natDegree
    rw [show f.natDegree + (B.natDegree - 1 - f.natDegree) = B.natDegree - 1 by omega] at key
    rw [key]
    exact leadingCoeff_ne_zero.2 hf0
  · exact natDegree_mul_le.trans_lt (by rw [natDegree_X_pow]; omega)

/-- The iterates of the Frobenius: `φ^k(x) = x^(q^k)`. -/
lemma frobR_pow_apply [Fintype K] (k : ℕ) (x : AdjoinRoot (B - 1)) :
    (frobR B ^ k) x = x ^ (Fintype.card K ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, frobR, AlgHom.toLinearMap_apply,
      FiniteField.coe_frobeniusAlgHom]
    beta_reduce
    rw [← pow_mul, pow_succ]

/-- If `B - 1` is not squarefree, `R` has a nonzero element of square zero. -/
lemma exists_sq_eq_zero (hB : 1 ≤ B.natDegree) (hsq : ¬ Squarefree (B - 1)) :
    ∃ x : AdjoinRoot (B - 1), x ≠ 0 ∧ x * x = 0 := by
  have hne := sub_one_ne_zero hB
  unfold Squarefree at hsq
  push Not at hsq
  obtain ⟨P, ⟨Q, hQ⟩, hP⟩ := hsq
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hne (by rw [hQ, mul_zero])
  have hP0 : P ≠ 0 := by rintro rfl; exact hne (by rw [hQ, zero_mul, zero_mul])
  refine ⟨AdjoinRoot.mk (B - 1) (P * Q), ?_, ?_⟩
  · rw [Ne, AdjoinRoot.mk_eq_zero, hQ]
    intro h
    apply hP
    have h' : P * (P * Q) ∣ 1 * (P * Q) := by rw [one_mul]; convert h using 1; ring
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right (mul_ne_zero hP0 hQ0)).1 h')
  · rw [← map_mul, AdjoinRoot.mk_eq_zero, hQ]
    exact ⟨Q, by ring⟩

variable [Fintype K] [DecidableEq K]

/-- **Theorem 29.11 (3)** (section 29.2.3). If `B - 1` is not squarefree, then
`k(B) = ω(B - 1)`. -/
theorem theorem29_11_three (hB : 2 ≤ B.natDegree) (hsq : ¬ Squarefree (B - 1)) :
    kDim B = omegaF (B - 1) := by
  have h1 : 1 ≤ B.natDegree := by omega
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero h1)).finite
  have hlo := theorem21_6 h1
  have hhi := theorem29_11_one hB
  by_contra hne
  have hgt : finrank K (LinearMap.ker (frobR B - 1)) <
      finrank K (AdjoinRoot (B - 1)) - finrank K (Jsum B) := by
    rw [finrank_ker_frobR h1, finrank_residue h1]
    rw [kDim] at hlo hhi hne
    omega
  -- `ℓ` spans the annihilator of `W_(e-2)`
  set W := Wj B (B.natDegree - 2)
  have hℓW : topCoeff h1 ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro _ ⟨⟨f, hf⟩, rfl⟩
    rw [mem_degreeLT] at hf
    have hfd : f.natDegree < B.natDegree - 1 := by
      rcases eq_or_ne f 0 with rfl | hf0
      · simp; omega
      · have := (natDegree_lt_iff_degree_lt hf0).2 hf
        omega
    change topCoeff h1 (AdjoinRoot.mk (B - 1) f) = 0
    rw [topCoeff_mk h1 (by omega)]
    exact coeff_eq_zero_of_natDegree_lt hfd
  have hℓ0 : topCoeff h1 ≠ 0 := by
    intro h
    have := congrArg (fun l => l (AdjoinRoot.mk (B - 1) (X ^ (B.natDegree - 1)))) h
    simp only [LinearMap.zero_apply] at this
    rw [topCoeff_mk h1 (by rw [natDegree_X_pow]; omega), coeff_X_pow_self] at this
    exact one_ne_zero this
  have hdimW : finrank K W.dualAnnihilator = 1 := by
    rw [finrank_dualAnnihilator, finrank_Wj h1 (by omega), finrank_residue h1]; omega
  have hspan : ∀ μ ∈ W.dualAnnihilator, ∃ c : K, μ = c • topCoeff h1 := by
    intro μ hμ
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨topCoeff h1, hℓW⟩ : W.dualAnnihilator)
      (by simpa using hℓ0)).1 hdimW ⟨μ, hμ⟩
    exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
  have hinv := comp_pow_eq_of_codim_gt (frobR B) W (Jsum B) (topCoeff h1) (B.natDegree - 2)
    hspan (Jsum_top_le hB) (Jsum_W_le hB) hgt
  -- a nonzero `x` with `x^2 = 0` is killed by `φ^(e-1)`, so `ℓ(x y) = 0` for all `y`
  obtain ⟨x, hx0, hxx⟩ := exists_sq_eq_zero h1 hsq
  obtain ⟨y, hy⟩ := exists_topCoeff_mul_ne_zero h1 hx0
  apply hy
  rw [← hinv, frobR_pow_apply, mul_pow]
  have h2 : 2 ≤ Fintype.card K ^ (B.natDegree - 2 + 1) :=
    (Fintype.one_lt_card (α := K)).trans_le (Nat.le_self_pow (by omega) _)
  rw [show Fintype.card K ^ (B.natDegree - 2 + 1) =
    2 + (Fintype.card K ^ (B.natDegree - 2 + 1) - 2) by omega, pow_add, sq, hxx]
  simp

end NotSquarefree

/-- **Conjecture 29.13** (section 29.2.5): `k(B) = ω(B - 1)` for every base `B` of degree at
least 2 over every finite field. Proved here for `B - 1` not squarefree
(`theorem29_11_three`); the library also proves it when `B - 1` has a factor of degree prime to
`e - 1` and for `e ≤ 10`. -/
def Conjecture29_13 : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (B : K[X]), 2 ≤ B.natDegree →
    kDim B = omegaF (B - 1)

/-! ### Corollary 29.10: a good factor exists when `e - 1` is a prime power -/

/-- The counting step of **Corollary 29.10** (section 29.2.2). If `e - 1 = r^s` with `r` prime
and `s ≥ 1`, and `e` is a sum `∑ a_i f_i`, then some `f_i` is prime to `e - 1`; otherwise `r`
divides every `f_i`, hence `e`, and also `e - 1`. -/
theorem exists_coprime_of_sum {ι : Type*} (S : Finset ι) (a f : ι → ℕ) {e r s : ℕ}
    (hr : r.Prime) (hs : 1 ≤ s) (he : e - 1 = r ^ s) (hsum : ∑ i ∈ S, a i * f i = e) :
    ∃ i ∈ S, Nat.Coprime (f i) (e - 1) := by
  by_contra hcon
  push Not at hcon
  have hdvd : ∀ i ∈ S, r ∣ f i := by
    intro i hi
    have h := hcon i hi
    rw [he] at h
    have h' : ¬ Nat.Coprime (f i) r := fun hc => h (Nat.Coprime.pow_right s hc)
    by_contra hnd
    exact h' ((hr.coprime_iff_not_dvd.2 hnd).symm)
  have hre : r ∣ e := hsum ▸ Finset.dvd_sum fun i hi => dvd_mul_of_dvd_right (hdvd i hi) _
  have hre1 : r ∣ e - 1 := he ▸ dvd_pow_self r (by omega)
  have : r ∣ 1 := by
    have h1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h] at he
        have := Nat.one_le_pow s r hr.pos
        omega
      · exact h
    have := (Nat.dvd_sub hre hre1)
    rwa [Nat.sub_sub_self h1] at this
  exact hr.one_lt.ne' (Nat.dvd_one.1 this)

/-- **Corollary 29.10**, the factor statement: if `e - 1` is a prime power, every `B - 1` of
degree `e ≥ 2` over a field has a monic irreducible factor (a member of its normalized
factorization) whose degree is prime to `e - 1`. -/
theorem exists_good_factor {K : Type*} [Field K] [DecidableEq K] {B : K[X]} {r s : ℕ}
    (hB : 2 ≤ B.natDegree) (hr : r.Prime) (hs : 1 ≤ s) (he : B.natDegree - 1 = r ^ s) :
    ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors (B - 1),
      Nat.Coprime P.natDegree (B.natDegree - 1) := by
  set M := UniqueFactorizationMonoid.normalizedFactors (B - 1)
  have hne := sub_one_ne_zero (B := B) (by omega)
  have hprod : M.prod.natDegree = B.natDegree := by
    rw [← natDegree_sub_one B]
    exact natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated (UniqueFactorizationMonoid.prod_normalizedFactors hne))
  have hsum : (M.map natDegree).sum = B.natDegree := by
    rw [← hprod, natDegree_multiset_prod]
    intro h0
    exact hne (UniqueFactorizationMonoid.zero_notMem_normalizedFactors _ (by
      simpa [M] using h0) |>.elim)
  obtain ⟨P, hP, hc⟩ := exists_coprime_of_sum M.toFinset (fun P => M.count P) natDegree hr hs he
    (by rw [← hsum, Finset.sum_multiset_map_count]; simp [smul_eq_mul])
  exact ⟨P, Multiset.mem_toFinset.1 hP, hc⟩

/-! ### Lemma 29.14 -/

/-- **Lemma 29.14** (section 29.3.1): Assumption R fails for `b = 10`, `d = 2`. A 1-digit string
`x` whose weight has 2 digits is the digit 3, so its residue `g(3) = 24 ≡ 6 (mod 9)` has
probability 1. -/
theorem lemma29_14 : ∀ x < 10, (10 ≤ x ^ x ∧ x ^ x < 100 ↔ x = 3) := by decide

end Munchausen
