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

Berlekamp's count `dim R^φ = ω(B - 1)` (Lemma 29.8 (1)) is not formalized, so these are
Theorem 21.6 and Theorem 29.11 (1) with `dim R^φ` in place of `ω(B - 1)`.

Corollary 29.10 rests on a counting fact about the degrees of the factors of `B - 1`, proved
here as `exists_good_factor`. The example of Lemma 29.14 is checked by `decide`.
-/

open Polynomial Module

namespace Munchausen

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

/-- **Theorem 29.11 (1)** (section 29.2.3), with `dim R^φ` in place of `ω(B - 1)`: for `B` of
degree `e ≥ 2`, `k(B) ≤ dim ker(φ - 1) + 1`. -/
theorem kDim_le (hB : 2 ≤ B.natDegree) :
    kDim B ≤ finrank K (LinearMap.ker (frobR B - 1)) + 1 := by
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero (B := B) (by omega))).finite
  have h1 : 1 ≤ B.natDegree := by omega
  set e := B.natDegree with he
  have hJ : ∀ j ∈ Finset.Icc 1 (e - 1), (Wj B j).map (frobR B ^ j - 1) ≤ Jsum B :=
    fun j hj => le_iSup₂ (f := fun j _ => (Wj B j).map (frobR B ^ j - 1)) j hj
  have := codim_le_finrank_ker_add_one (frobR B) (Wj B (e - 2)) (Jsum B) (e - 2) ?_ ?_ ?_
  · rwa [finrank_residue h1] at this
  · rw [finrank_Wj h1 (by omega), finrank_residue h1]; omega
  · have := hJ (e - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
    rwa [Wj_top h1, Submodule.map_top, ← show e - 2 + 1 = e - 1 by omega] at this
  · rcases Nat.eq_zero_or_pos (e - 2) with h0 | hpos
    · rw [h0, pow_zero, sub_self, Submodule.map_zero]
      exact bot_le
    · exact hJ (e - 2) (Finset.mem_Icc.2 ⟨hpos, by omega⟩)

end Residue

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
