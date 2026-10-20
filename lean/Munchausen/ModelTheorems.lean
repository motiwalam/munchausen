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

Theorem 29.9 (a good factor gives `k(B) = ω(B - 1)`) and Lemma 29.8 (3) are proved without
traces. The Frobenius of `F_q[T]/(P^a)` satisfies `φ^(a+f) = φ^a` (`f = deg P`), and for such an
eventually periodic map Euclid's algorithm on exponents gives `∑_(j ∈ S) (φ^j - 1) V = (φ - 1) V`
whenever `gcd(S, f) = 1` (`iSup_range_pow_sub_one_eq`). In Theorem 29.9 the part of `R` reached
by the term `j = e - 1` is the ideal `Q R` with `Q = (B - 1)/P`, where `φ^(k f + 1) = φ`.
Theorem 29.11 (2) is the dual argument of (1) carried to the end (`theorem29_11_two`).
Lemma 29.8 (1) for every `j` (`lemma29_8_one`) counts the fixed points of `x ↦ x^(q^g)` in
`F_q[T]/(P^a)`: they reduce bijectively onto the roots of `X^(q^g) - X` in the residue field.
Lemma 29.8 (2) (`lemma29_8_two`) writes the trace to `F_(q^g)` as the sum of the conjugates; the
image of `φ^j - 1` lies in its kernel, which has at most `q^(f-g)` elements, so they agree.
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

/-! ### Eventually periodic maps: the core of Lemma 29.8 (2), (3) -/

section Periodic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Two consecutive exponents suffice: `(φ - 1) v = (φ^(n+1) - 1) v - (φ^n - 1) (φ v)`. -/
lemma sub_one_apply_eq (φ : V →ₗ[K] V) (n : ℕ) (v : V) :
    (φ - 1) v = (φ ^ (n + 1) - 1) v - (φ ^ n - 1) (φ v) := by
  simp only [LinearMap.sub_apply, Module.End.one_apply, pow_succ, Module.End.mul_apply]
  abel

/-- If `n` is prime to `f`, some `k f + 1` is a multiple of `n`. -/
lemma exists_dvd_mul_add_one {n f : ℕ} (hn : 1 ≤ n) (h : Nat.Coprime f n) :
    ∃ k, n ∣ k * f + 1 := by
  have : NeZero n := ⟨by omega⟩
  set u := ZMod.unitOfCoprime f h
  refine ⟨(-(↑u⁻¹ : ZMod n)).val, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime f h, neg_mul, Units.inv_mul,
    neg_add_cancel]

/-- **Lemma 29.8 (3)**, the core (section 29.2.1). If `φ^(k f + 1) v = φ v` for every `k`
and `n` is prime to `f`, then `(φ - 1) v` lies in the image of `φ^n - 1`. -/
lemma sub_one_mem_range_pow (φ : V →ₗ[K] V) {f n : ℕ} (hn : 1 ≤ n) (hfn : Nat.Coprime f n)
    {v : V} (hv : ∀ k, (φ ^ (k * f + 1)) v = φ v) :
    (φ - 1) v ∈ LinearMap.range (φ ^ n - 1) := by
  obtain ⟨k, t, ht⟩ := exists_dvd_mul_add_one hn hfn
  have h1 : (φ - 1) v = ((φ ^ n) ^ t - 1) v := by
    rw [← pow_mul, ← ht, LinearMap.sub_apply, LinearMap.sub_apply, hv]
  rw [h1]
  exact range_pow_sub_one_le (φ ^ n) t ⟨v, rfl⟩

/-- If `φ` maps `U` into itself and `(φ - 1) U ⊆ J`, then `(φ^j - 1) U ⊆ J` for every `j`. -/
lemma pow_sub_one_mem_of_sub_one_mem (φ : V →ₗ[K] V) {U J : Submodule K V}
    (hU : ∀ u ∈ U, φ u ∈ U) (hJ : ∀ u ∈ U, (φ - 1) u ∈ J) (j : ℕ) :
    ∀ u ∈ U, (φ ^ j - 1) u ∈ J := by
  induction j with
  | zero => intro u _; simp
  | succ j ih =>
    intro u hu
    have : (φ ^ (j + 1) - 1) u = (φ ^ j - 1) (φ u) + (φ - 1) u := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, pow_succ, Module.End.mul_apply]
      abel
    rw [this]
    exact J.add_mem (ih _ (hU u hu)) (hJ u hu)


/-- `φ^n - 1` is invertible where `φ` is nilpotent: if `φ^m v = 0` and `n ≥ 1`, then `v` lies in
the image of `φ^n - 1` (proof of Lemma 29.8 (2)). -/
lemma mem_range_pow_sub_one_of_pow_eq_zero (φ : V →ₗ[K] V) {m n : ℕ} (hn : 1 ≤ n) {v : V}
    (hv : (φ ^ m) v = 0) : v ∈ LinearMap.range (φ ^ n - 1) := by
  have h0 : ((φ ^ n) ^ m) v = 0 := by
    rw [← pow_mul, ← Nat.sub_add_cancel (Nat.le_mul_of_pos_left m hn), pow_add,
      Module.End.mul_apply, hv, map_zero]
  refine ⟨-((∑ i ∈ Finset.range m, (φ ^ n) ^ i) v), ?_⟩
  rw [map_neg, ← Module.End.mul_apply, mul_geom_sum, LinearMap.sub_apply, h0]
  simp

/-- Euclid's algorithm on exponents: the images of `φ^a - 1` and `φ^b - 1` together contain the
image of `φ^gcd(a, b) - 1`. -/
lemma range_pow_gcd_sub_one_le (φ : V →ₗ[K] V) (a b : ℕ) :
    LinearMap.range (φ ^ Nat.gcd a b - 1) ≤
      LinearMap.range (φ ^ a - 1) ⊔ LinearMap.range (φ ^ b - 1) := by
  induction a, b using Nat.gcd.induction with
  | H0 n => rw [Nat.gcd_zero_left]; exact le_sup_right
  | H1 m n _ ih =>
    rw [Nat.gcd_rec]
    refine ih.trans (sup_le ?_ le_sup_left)
    rintro _ ⟨v, rfl⟩
    have hn : φ ^ n = (φ ^ m) ^ (n / m) * φ ^ (n % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have hsplit : (φ ^ (n % m) - 1) v =
        (φ ^ n - 1) v - ((φ ^ m) ^ (n / m) - 1) ((φ ^ (n % m)) v) := by
      rw [hn]
      simp only [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply]
      abel
    rw [hsplit]
    refine Submodule.sub_mem _ (Submodule.mem_sup_right ⟨v, rfl⟩) (Submodule.mem_sup_left ?_)
    exact range_pow_sub_one_le (φ ^ m) _ ⟨_, rfl⟩

/-- For a finite set `S` of exponents there is a common divisor `d` of `S` such that the images
of `φ^j - 1`, `j ∈ S`, contain the image of `φ^d - 1`. -/
lemma exists_range_pow_sub_one_le_iSup (φ : V →ₗ[K] V) (S : Finset ℕ) :
    ∃ d, (∀ j ∈ S, d ∣ j) ∧
      LinearMap.range (φ ^ d - 1) ≤ ⨆ j ∈ S, LinearMap.range (φ ^ j - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert a S _ ih =>
    obtain ⟨d, hd, hle⟩ := ih
    refine ⟨Nat.gcd a d, ?_, (range_pow_gcd_sub_one_le φ a d).trans (sup_le ?_ ?_)⟩
    · intro j hj
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (hd j hj)
    · exact le_iSup₂_of_le (f := fun j (_ : j ∈ insert a S) => LinearMap.range (φ ^ j - 1)) a
        (Finset.mem_insert_self a S) le_rfl
    · exact hle.trans (iSup₂_le fun j hj => le_iSup₂_of_le (f := fun j (_ : j ∈ insert a S) =>
        LinearMap.range (φ ^ j - 1)) j (Finset.mem_insert_of_mem hj) le_rfl)

/-- **Lemma 29.8 (3)**, abstract form (section 29.2.1). Let `φ` be eventually periodic with
period `f`: `φ^(m+f) = φ^m`. If the only common divisor of a set `S` of exponents and `f` is 1,
then the images of `φ^j - 1`, `j ∈ S`, add up to the image of `φ - 1`. -/
theorem iSup_range_pow_sub_one_eq (φ : V →ₗ[K] V) {m f : ℕ}
    (hper : ∀ v, (φ ^ (m + f)) v = (φ ^ m) v) (S : Finset ℕ)
    (hS0 : ∃ j ∈ S, j ≠ 0) (hS : ∀ d, (∀ j ∈ S, d ∣ j) → d ∣ f → d = 1) :
    ⨆ j ∈ S, LinearMap.range (φ ^ j - 1) = LinearMap.range (φ - 1) := by
  refine le_antisymm (iSup₂_le fun j _ => range_pow_sub_one_le φ j) ?_
  obtain ⟨d, hd, hle⟩ := exists_range_pow_sub_one_le_iSup φ S
  refine le_trans ?_ hle
  have hdf : Nat.Coprime f d := by
    have := hS (Nat.gcd d f) (fun j hj => (Nat.gcd_dvd_left d f).trans (hd j hj))
      (Nat.gcd_dvd_right d f)
    exact Nat.coprime_comm.1 this
  have hd1 : 1 ≤ d := by
    obtain ⟨j, hj, hj0⟩ := hS0
    exact Nat.pos_of_ne_zero fun h => hj0 (Nat.eq_zero_of_zero_dvd (h ▸ hd j hj))
  -- `φ^(m + k f) = φ^m`
  have hperk : ∀ k v, (φ ^ (m + k * f)) v = (φ ^ m) v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro v
      rw [show m + (k + 1) * f = k * f + (m + f) by ring, pow_add, Module.End.mul_apply, hper,
        ← Module.End.mul_apply, ← pow_add, show k * f + m = m + k * f by ring, ih]
  rintro _ ⟨u, rfl⟩
  obtain ⟨k, t, ht⟩ := exists_dvd_mul_add_one hd1 hdf
  set w := (φ ^ (k * f)) (φ u) - φ u
  have hsplit : (φ - 1) u = ((φ ^ d) ^ t - 1) u - w := by
    rw [← pow_mul, ← ht]
    simp only [w, LinearMap.sub_apply, Module.End.one_apply, pow_succ, Module.End.mul_apply]
    abel
  have hw : (φ ^ m) w = 0 := by
    simp only [w, map_sub]
    rw [← Module.End.mul_apply (φ ^ m), ← pow_add, hperk, sub_self]
  rw [hsplit]
  exact Submodule.sub_mem _ (range_pow_sub_one_le (φ ^ d) t ⟨u, rfl⟩)
    (mem_range_pow_sub_one_of_pow_eq_zero φ hd1 hw)

/-- The codimension of `J ⊆ (φ - 1) V` exceeds `dim ker(φ - 1)` exactly when some functional
vanishing on `J` is not `φ`-invariant (section 29.2.3). -/
lemma codim_gt_iff [FiniteDimensional K V] (φ : V →ₗ[K] V) (J : Submodule K V)
    (hJ : J ≤ LinearMap.range (φ - 1)) :
    finrank K (LinearMap.ker (φ - 1)) < finrank K V - finrank K J ↔
      ∃ l ∈ J.dualAnnihilator, ∃ v, l (φ v - v) ≠ 0 := by
  have h2 := LinearMap.finrank_range_add_finrank_ker (φ - 1)
  have h3 := Submodule.finrank_le J
  constructor
  · intro hgt
    by_contra hcon
    push Not at hcon
    have hle : J.dualAnnihilator ≤ (LinearMap.range (φ - 1)).dualAnnihilator := by
      intro l hl
      rw [Submodule.mem_dualAnnihilator]
      rintro _ ⟨v, rfl⟩
      simpa using hcon l hl v
    have h1 := Submodule.finrank_mono hle
    rw [finrank_dualAnnihilator, finrank_dualAnnihilator] at h1
    omega
  · rintro ⟨l, hl, v, hv⟩
    have hlt : (LinearMap.range (φ - 1)).dualAnnihilator < J.dualAnnihilator := by
      refine lt_of_le_of_ne (Submodule.dualAnnihilator_anti hJ) fun h => hv ?_
      rw [← h, Submodule.mem_dualAnnihilator] at hl
      simpa using hl _ ⟨v, rfl⟩
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_dualAnnihilator, finrank_dualAnnihilator] at h1
    omega

end Periodic

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

/-- `ℓ` vanishes on `W_j` for `j ≤ e - 2`. -/
lemma topCoeff_Wj (hB : 1 ≤ B.natDegree) {j : ℕ} (hj : j + 2 ≤ B.natDegree) {v}
    (hv : v ∈ Wj B j) : topCoeff hB v = 0 := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := hv
  rw [mem_degreeLT] at hf
  have hfd : f.natDegree < B.natDegree - 1 := by
    rcases eq_or_ne f 0 with rfl | hf0
    · simp; omega
    · have := (natDegree_lt_iff_degree_lt hf0).2 hf
      omega
  change topCoeff hB (AdjoinRoot.mk (B - 1) f) = 0
  rw [topCoeff_mk hB (by omega)]
  exact coeff_eq_zero_of_natDegree_lt hfd

lemma topCoeff_ne_zero (hB : 1 ≤ B.natDegree) : topCoeff hB ≠ 0 := by
  intro h
  have := congrArg (fun l => l (AdjoinRoot.mk (B - 1) (X ^ (B.natDegree - 1)))) h
  simp only [LinearMap.zero_apply] at this
  rw [topCoeff_mk hB (by rw [natDegree_X_pow]; omega), coeff_X_pow_self] at this
  exact one_ne_zero this

/-- `ℓ` spans the functionals vanishing on `W_(e-2)` (section 29.2.3). -/
lemma topCoeff_span (hB : 2 ≤ B.natDegree) :
    ∀ μ ∈ (Wj B (B.natDegree - 2)).dualAnnihilator,
      ∃ c : K, μ = c • topCoeff (one_le_two.trans hB) := by
  have h1 : 1 ≤ B.natDegree := one_le_two.trans hB
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero h1)).finite
  set W := Wj B (B.natDegree - 2)
  have hℓW : topCoeff h1 ∈ W.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    exact topCoeff_Wj h1 (by omega) hv
  have hdimW : finrank K W.dualAnnihilator = 1 := by
    rw [finrank_dualAnnihilator, finrank_Wj h1 (by omega), finrank_residue h1]; omega
  intro μ hμ
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨topCoeff h1, hℓW⟩ : W.dualAnnihilator)
    (by simpa using topCoeff_ne_zero h1)).1 hdimW ⟨μ, hμ⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

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
  set W := Wj B (B.natDegree - 2)
  have hspan := topCoeff_span hB
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
(`theorem29_11_three`), when `B - 1` has a factor of degree prime to `e - 1` (`theorem29_9`), and
so when `e - 1` is 1 or a prime power (`corollary29_10`, `corollary29_10_two`); the library also
proves it for `e ≤ 10`. -/
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

/-! ### Lemma 29.8 (2), (3), Theorem 29.9 and Corollary 29.10 -/

section Good

variable {K : Type*} [Field K] [Fintype K]

/-- Over `F_q`, an irreducible `P` of degree `f` divides `h^(q^(k f)) - h` for every `h`. -/
lemma dvd_pow_card_pow_sub {P : K[X]} (hP : Irreducible P) (k : ℕ) (h : K[X]) :
    P ∣ h ^ (Fintype.card K ^ (k * P.natDegree)) - h := by
  have : Fact (Irreducible P) := ⟨hP⟩
  have hfin : Module.Finite K (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  let _ := Fintype.ofFinite (AdjoinRoot P)
  have hcard : Fintype.card (AdjoinRoot P) = Fintype.card K ^ P.natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K),
      Nat.card_eq_fintype_card, (AdjoinRoot.powerBasis hP.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, sub_eq_zero, mul_comm, pow_mul, ← hcard]
  exact FiniteField.pow_card_pow k _


/-- With `B - 1 = P Q`, `P` irreducible of degree `f`, every multiple `x` of `Q` in
`R = F_q[T]/(B - 1)` has `x^(q^(k f + 1)) = x^q`: the Frobenius is periodic of period `f` on
`φ(Q R)`. -/
lemma pow_card_pow_mul_add_one {B P Q : K[X]} (hP : Irreducible P) (hPQ : B - 1 = P * Q)
    (k : ℕ) (g : K[X]) :
    (AdjoinRoot.mk (B - 1) (Q * g)) ^ (Fintype.card K ^ (k * P.natDegree + 1)) =
      (AdjoinRoot.mk (B - 1) (Q * g)) ^ Fintype.card K := by
  set q := Fintype.card K
  set h := Q * g
  set D := h ^ (q ^ (k * P.natDegree)) - h
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hPD : P ∣ D := dvd_pow_card_pow_sub hP k h
  have hQD : Q ∣ D := by
    refine dvd_sub ((dvd_mul_right Q g).trans (dvd_pow_self h ?_)) (dvd_mul_right Q g)
    exact (pow_pos (by omega) _).ne'
  have hDq : D ^ q = h ^ (q ^ (k * P.natDegree + 1)) - h ^ q := by
    have h1 := map_sub (FiniteField.frobeniusAlgHom K K[X]) (h ^ (q ^ (k * P.natDegree))) h
    simp only [FiniteField.coe_frobeniusAlgHom] at h1
    rw [h1, ← pow_mul, pow_succ]
  rw [← map_pow, ← map_pow, AdjoinRoot.mk_eq_mk, ← hDq, hPQ]
  calc P * Q ∣ D * D := mul_dvd_mul hPD hQD
    _ = D ^ 2 := (sq D).symm
    _ ∣ D ^ q := pow_dvd_pow D hq2

/-- `(x - y)^(q^n) = x^(q^n) - y^(q^n)` in every commutative `F_q`-algebra. -/
lemma sub_pow_card_pow {A : Type*} [CommRing A] [Algebra K A] (x y : A) (n : ℕ) :
    (x - y) ^ (Fintype.card K ^ n) = x ^ (Fintype.card K ^ n) - y ^ (Fintype.card K ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, ih]
    exact map_sub (FiniteField.frobeniusAlgHom K A) _ _

/-- The Frobenius `x ↦ x^q` of a commutative `F_q`-algebra, as an `F_q`-linear map. -/
noncomputable def frobA (K A : Type*) [Field K] [Fintype K] [CommRing A] [Algebra K A] :
    A →ₗ[K] A :=
  (FiniteField.frobeniusAlgHom K A).toLinearMap

lemma frobA_pow_apply {A : Type*} [CommRing A] [Algebra K A] (k : ℕ) (x : A) :
    (frobA K A ^ k) x = x ^ (Fintype.card K ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, frobA, AlgHom.toLinearMap_apply,
      FiniteField.coe_frobeniusAlgHom]
    beta_reduce
    rw [← pow_mul, pow_succ]

/-- **Lemma 29.8 (2)**, the nilradical (section 29.2.1): in every commutative `F_q`-algebra,
in particular in `R = F_q[T]/(B - 1)` and in each local factor `R_i`, the image of `φ^j - 1`
(`j ≥ 1`) contains every nilpotent element. -/
theorem lemma29_8_two_nil {A : Type*} [CommRing A] [Algebra K A] {x : A} (hx : IsNilpotent x)
    {j : ℕ} (hj : 1 ≤ j) : x ∈ LinearMap.range (frobA K A ^ j - 1) := by
  obtain ⟨n, hn⟩ := hx
  refine mem_range_pow_sub_one_of_pow_eq_zero _ hj (m := n) ?_
  rw [frobA_pow_apply]
  exact pow_eq_zero_of_le (Nat.lt_pow_self Fintype.one_lt_card).le hn

/-- The Frobenius of `F_q[T]/(P^a)`, `P` irreducible of degree `f`, is eventually periodic:
`φ^(a + f) = φ^a` (proof of Lemma 29.8 (2)). -/
lemma pow_card_pow_add_local {P : K[X]} (hP : Irreducible P) (a : ℕ) (x : AdjoinRoot (P ^ a)) :
    x ^ (Fintype.card K ^ (a + P.natDegree)) = x ^ (Fintype.card K ^ a) := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [← map_pow, ← map_pow, AdjoinRoot.mk_eq_mk]
  have h1 : g ^ (Fintype.card K ^ (a + P.natDegree)) - g ^ (Fintype.card K ^ a) =
      (g ^ (Fintype.card K ^ P.natDegree) - g) ^ (Fintype.card K ^ a) := by
    rw [sub_pow_card_pow, ← pow_mul, ← pow_add, add_comm]
  rw [h1]
  have hP1 : P ∣ g ^ (Fintype.card K ^ P.natDegree) - g := by
    simpa using dvd_pow_card_pow_sub hP 1 g
  exact (pow_dvd_pow P (Nat.lt_pow_self Fintype.one_lt_card).le).trans (pow_dvd_pow_of_dvd hP1 _)

/-- **Lemma 29.8 (3)** (section 29.2.1). Let `P` be irreducible of degree `f` and
`R_i = F_q[T]/(P^a)`. If the only common divisor of a set `S` of exponents (not all 0) and `f`
is 1, then the images of `φ^j - 1` on `R_i`, `j ∈ S`, add up to `I_i`, the image of `φ - 1`.
The library proves this with traces; here it follows from `φ^(a + f) = φ^a` alone. -/
theorem lemma29_8_three {P : K[X]} (hP : Irreducible P) (a : ℕ) (S : Finset ℕ)
    (hS0 : ∃ j ∈ S, j ≠ 0) (hS : ∀ d, (∀ j ∈ S, d ∣ j) → d ∣ P.natDegree → d = 1) :
    ⨆ j ∈ S, LinearMap.range (frobA K (AdjoinRoot (P ^ a)) ^ j - 1) =
      LinearMap.range (frobA K (AdjoinRoot (P ^ a)) - 1) :=
  iSup_range_pow_sub_one_eq _ (m := a) (f := P.natDegree)
    (fun v => by rw [frobA_pow_apply, frobA_pow_apply]; exact pow_card_pow_add_local hP a v)
    S hS0 hS

variable [DecidableEq K]

/-- **Theorem 29.9** (section 29.2.2). If `B - 1` has a good factor, an irreducible `P` whose
degree is prime to `e - 1`, then `k(B) = ω(B - 1)`.

The proof follows the library with one change: the part of `R = F_q[T]/(B - 1)` that the term
`j = e - 1` controls is the ideal `Q R`, `Q = (B - 1)/P`, where `φ^(k f + 1) = φ` (`f = deg P`),
so Lemma 29.8 (3) becomes `sub_one_mem_range_pow`. Since `deg Q ≤ e - 1`, the terms
`j = e - 2` and `j = e - 1` cover `R` modulo `Q R`, and two consecutive exponents give
`φ - 1`. -/
theorem theorem29_9 {B : K[X]} (hB : 2 ≤ B.natDegree) {P : K[X]} (hP : Irreducible P)
    (hPB : P ∣ B - 1) (hgood : Nat.Coprime P.natDegree (B.natDegree - 1)) :
    kDim B = omegaF (B - 1) := by
  have h1 : 1 ≤ B.natDegree := by omega
  have hne := sub_one_ne_zero h1
  have := (AdjoinRoot.powerBasis hne).finite
  obtain ⟨Q, hQ⟩ := hPB
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hne (by rw [hQ, mul_zero])
  have hQdeg : Q.natDegree + 1 ≤ B.natDegree := by
    have := natDegree_mul hP.ne_zero hQ0
    rw [← hQ, natDegree_sub_one] at this
    have := hP.natDegree_pos
    omega
  set q := Fintype.card K
  set φ := frobR B
  have hφ : ∀ x, φ x = x ^ q := fun x => by simpa using frobR_pow_apply (B := B) 1 x
  -- the ideal `Q R`
  set U := (Ideal.span {AdjoinRoot.mk (B - 1) Q}).restrictScalars K
  have hmemU : ∀ u ∈ U, ∃ g : K[X], u = AdjoinRoot.mk (B - 1) (Q * g) := by
    intro u hu
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
    exact ⟨g, by rw [map_mul, mul_comm]⟩
  have hUφ : ∀ u ∈ U, φ u ∈ U := fun u hu => by
    rw [hφ]
    exact Ideal.pow_mem_of_mem _ hu q Fintype.card_pos
  -- Step A: `(φ - 1) (Q R) ⊆ (φ^(e-1) - 1) R ⊆ J`
  have hA : ∀ u ∈ U, (φ - 1) u ∈ Jsum B := by
    intro u hu
    obtain ⟨g, rfl⟩ := hmemU u hu
    have hmem := sub_one_mem_range_pow φ (n := B.natDegree - 1) (by omega) hgood
      (v := AdjoinRoot.mk (B - 1) (Q * g)) (fun k => by
        rw [frobR_pow_apply, hφ]
        exact pow_card_pow_mul_add_one hP hQ k g)
    have htop := Jsum_top_le hB
    rw [show B.natDegree - 2 + 1 = B.natDegree - 1 by omega] at htop
    exact htop hmem
  -- Step B: `(φ^j - 1) (Q R) ⊆ J`
  have hB' := pow_sub_one_mem_of_sub_one_mem φ hUφ hA
  -- Step C: `(φ^j - 1) R ⊆ J` when `deg Q ≤ j + 1`
  have hC : ∀ j, 1 ≤ j → j ≤ B.natDegree - 1 → Q.natDegree ≤ j + 1 →
      ∀ v, (φ ^ j - 1) v ∈ Jsum B := by
    intro j hj1 hj2 hjQ v
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective v
    have hsplit : AdjoinRoot.mk (B - 1) g =
        AdjoinRoot.mk (B - 1) (g % Q) + AdjoinRoot.mk (B - 1) (Q * (g / Q)) := by
      rw [← map_add, add_comm, EuclideanDomain.div_add_mod]
    rw [hsplit, map_add]
    refine (Jsum B).add_mem ?_ (hB' j _ (Ideal.mem_span_singleton'.2 ⟨AdjoinRoot.mk (B - 1)
      (g / Q), by rw [← map_mul, mul_comm]⟩))
    have hW : AdjoinRoot.mk (B - 1) (g % Q) ∈ Wj B j := by
      refine ⟨⟨g % Q, ?_⟩, rfl⟩
      rw [mem_degreeLT]
      refine (degree_mod_lt g hQ0).trans_le ?_
      rw [degree_eq_natDegree hQ0]
      exact_mod_cast hjQ
    exact le_iSup₂ (f := fun j (_ : j ∈ Finset.Icc 1 (B.natDegree - 1)) =>
      (Wj B j).map (frobR B ^ j - 1)) j (Finset.mem_Icc.2 ⟨hj1, hj2⟩) ⟨_, hW, rfl⟩
  -- Step D: two consecutive exponents give `φ - 1`
  have hJ : LinearMap.range (φ - 1) ≤ Jsum B := by
    rintro _ ⟨v, rfl⟩
    rcases Nat.lt_or_ge B.natDegree 3 with he | he
    · have := hC 1 le_rfl (by omega) (by omega) v
      rwa [pow_one] at this
    · rw [sub_one_apply_eq φ (B.natDegree - 2) v]
      refine (Jsum B).sub_mem ?_ (hC _ (by omega) (by omega) (by omega) _)
      exact hC _ (by omega) (by omega) (by omega) v
  have hJeq : Jsum B = LinearMap.range (φ - 1) := le_antisymm Jsum_le_range hJ
  have hrk := LinearMap.finrank_range_add_finrank_ker (φ - 1)
  rw [finrank_residue h1] at hrk
  have hker : finrank K (LinearMap.ker (φ - 1)) = omegaF (B - 1) := finrank_ker_frobR h1
  rw [kDim, hJeq, ← hker]
  omega

/-- **Corollary 29.10** (section 29.2.2). If `e - 1` is a prime power `r^s` (`s ≥ 1`), then
`k(B) = ω(B - 1)` for every `B` of degree `e`. -/
theorem corollary29_10 {B : K[X]} (hB : 2 ≤ B.natDegree) {r s : ℕ} (hr : r.Prime) (hs : 1 ≤ s)
    (he : B.natDegree - 1 = r ^ s) : kDim B = omegaF (B - 1) := by
  obtain ⟨P, hP, hc⟩ := exists_good_factor hB hr hs he
  exact theorem29_9 hB (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP)
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) hc

/-- **Corollary 29.10** for `e = 2` (problem 6 of `STATUS.md`): every factor is good, since
every degree is prime to 1. -/
theorem corollary29_10_two {B : K[X]} (hB : B.natDegree = 2) : kDim B = omegaF (B - 1) := by
  have hne := sub_one_ne_zero (B := B) (by omega)
  have hnu : ¬ IsUnit (B - 1) := by
    intro hu
    have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_sub_one] at this
    omega
  obtain ⟨P, hP, hPB⟩ := WfDvdMonoid.exists_irreducible_factor hnu hne
  exact theorem29_9 (by omega) hP hPB (by rw [hB]; exact Nat.coprime_one_right _)

end Good

/-! ### Lemma 29.8 (1): the fixed points of `φ^j` -/

section KerPow

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- An eventually periodic map, `φ^(m+f) = φ^m`, has `φ^a = φ^b` from `m` on whenever
`a ≡ b (mod f)`. -/
lemma pow_apply_eq_of_modEq (φ : V →ₗ[K] V) {m f : ℕ}
    (hper : ∀ v, (φ ^ (m + f)) v = (φ ^ m) v) {a c : ℕ} (ha : m ≤ a) (hc : m ≤ c)
    (hac : a ≡ c [MOD f]) (v : V) : (φ ^ a) v = (φ ^ c) v := by
  have hperk : ∀ k v, (φ ^ (m + k * f)) v = (φ ^ m) v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro v
      rw [show m + (k + 1) * f = k * f + (m + f) by ring, pow_add, Module.End.mul_apply, hper,
        ← Module.End.mul_apply, ← pow_add, show k * f + m = m + k * f by ring, ih]
  have key : ∀ a k, m ≤ a → (φ ^ (a + k * f)) v = (φ ^ a) v := by
    intro a k ha
    rw [show a + k * f = (a - m) + (m + k * f) by omega, pow_add, Module.End.mul_apply, hperk,
      ← Module.End.mul_apply, ← pow_add, show a - m + m = a by omega]
  rcases le_total a c with h | h
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h).1 hac
    rw [show c = a + k * f by rw [mul_comm]; omega, key a k ha]
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h).1 hac.symm
    rw [show a = c + k * f by rw [mul_comm]; omega, key c k hc]

/-- **Lemma 29.8 (1)**, the reduction to `gcd(j, f)`: for an eventually periodic map,
`ker(φ^j - 1) = ker(φ^gcd(j, f) - 1)` for `j ≥ 1`. -/
lemma ker_pow_sub_one_eq_gcd (φ : V →ₗ[K] V) {m f j : ℕ} (hf : 1 ≤ f) (hj : 1 ≤ j)
    (hper : ∀ v, (φ ^ (m + f)) v = (φ ^ m) v) :
    LinearMap.ker (φ ^ j - 1) = LinearMap.ker (φ ^ Nat.gcd j f - 1) := by
  have hfix : ∀ n v, (φ ^ n) v = v → ∀ t, (φ ^ (n * t)) v = v := by
    intro n v hv t
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hv, ih]
  ext v
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · intro hv
    set g := Nat.gcd j f
    -- `j t ≡ g (mod f)` for some `t`
    obtain ⟨t0, ht0⟩ : ∃ t, j * t ≡ g [MOD f] := by
      rcases Nat.lt_or_ge g f with hlt | hge
      · obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_gcd (n := j) (k := f) hlt
        refine ⟨t, ?_⟩
        unfold Nat.ModEq
        rw [ht, Nat.mod_eq_of_lt hlt]
      · have hg : g = f := le_antisymm (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right j f)) hge
        refine ⟨0, ?_⟩
        rw [hg, mul_zero]
        unfold Nat.ModEq
        simp
    have h1 : (φ ^ (j * (t0 + f * m))) v = v := hfix j v hv _
    have h2 : (φ ^ (j * (f * m))) v = v := hfix j v hv _
    have hm1 : m ≤ j * (f * m) := by
      calc m ≤ f * m := Nat.le_mul_of_pos_left m hf
        _ ≤ j * (f * m) := Nat.le_mul_of_pos_left _ hj
    have hmod : g + j * (f * m) ≡ j * (t0 + f * m) [MOD f] := by
      have e1 : j * (f * m) ≡ 0 [MOD f] := by
        rw [Nat.modEq_zero_iff_dvd]; exact ⟨j * m, by ring⟩
      have e2 : j * (t0 + f * m) = j * t0 + j * (f * m) := by ring
      rw [e2]
      exact Nat.ModEq.add ht0.symm (e1.trans e1.symm)
    calc (φ ^ g) v = (φ ^ g) ((φ ^ (j * (f * m))) v) := by rw [h2]
      _ = (φ ^ (g + j * (f * m))) v := by rw [pow_add, Module.End.mul_apply]
      _ = (φ ^ (j * (t0 + f * m))) v :=
          pow_apply_eq_of_modEq φ hper (by omega) (by nlinarith) hmod v
      _ = v := h1
  · intro hv
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left j f
    rw [ht]
    exact hfix _ v hv t

end KerPow

section FixedCount

/-- In a finite field `L` with `q^f` elements, `x ↦ x^(q^g)` has exactly `q^g` fixed points when
`g ∣ f` and `q^g > 1`: they are the roots of `X^(q^g) - X`, a divisor of `X^(q^f) - X`, which
splits with distinct roots. -/
lemma natCard_fixed_field {L : Type*} [Field L] [Fintype L] {q f g : ℕ}
    (hL : Fintype.card L = q ^ f) (hgf : g ∣ f) (hq : 1 < q ^ g) :
    Nat.card {y : L // y ^ (q ^ g) = y} = q ^ g := by
  classical
  set Pg : L[X] := X ^ (q ^ g) - X
  set Pf : L[X] := X ^ Fintype.card L - X
  have hPf0 : Pf ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L Fintype.one_lt_card
  have hPg0 : Pg ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hq
  have hdvd : Pg ∣ Pf := by
    simp only [Pg, Pf, hL]
    exact dvd_pow_pow_sub_self_of_dvd hgf
  have hsplit : Splits Pf := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq L Fintype.one_lt_card]
    simp
  have hcard : Pg.roots.card = q ^ g := by
    rw [splits_iff_card_roots.1 (hsplit.of_dvd hPf0 hdvd)]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq L hq
  have hnodup : Pg.roots.Nodup := by
    refine Multiset.nodup_of_le (Polynomial.roots.le_of_dvd hPf0 hdvd) ?_
    rw [FiniteField.roots_X_pow_card_sub_X]
    exact Finset.univ.nodup
  have hmem : ∀ y : L, y ∈ Pg.roots.toFinset ↔ y ^ (q ^ g) = y := by
    intro y
    rw [Multiset.mem_toFinset, mem_roots hPg0]
    simp [Pg, sub_eq_zero]
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun y => (hmem y).symm), Nat.card_eq_fintype_card,
    Fintype.card_coe, Multiset.toFinset_card_of_nodup hnodup, hcard]

variable {K : Type*} [Field K] [Fintype K]

/-- In `F_q[T]/(P^a)`, `P` irreducible of degree `f` and `a ≥ 1`, the fixed points of
`x ↦ x^(q^g)` for `g ∣ f`, `g ≥ 1`, number `q^g`: reduction modulo `P` is a bijection onto the
fixed points of the residue field (the lifting of Lemma 29.8 (1), here by `x ↦ z^(q^(f a))`). -/
lemma natCard_fixed_pow_local {P : K[X]} (hP : Irreducible P) {a g : ℕ} (ha : 1 ≤ a)
    (hg : 1 ≤ g) (hgf : g ∣ P.natDegree) :
    Nat.card {x : AdjoinRoot (P ^ a) // x ^ (Fintype.card K ^ g) = x} =
      Fintype.card K ^ g := by
  classical
  set q := Fintype.card K
  set f := P.natDegree
  have hq : 2 ≤ q := Fintype.one_lt_card
  have : Fact (Irreducible P) := ⟨hP⟩
  have hfin : Module.Finite K (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  let _ := Fintype.ofFinite (AdjoinRoot P)
  have hcardL : Fintype.card (AdjoinRoot P) = q ^ f := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K),
      Nat.card_eq_fintype_card, (AdjoinRoot.powerBasis hP.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  -- reduction modulo `P`
  let ρ : AdjoinRoot (P ^ a) →ₐ[K] AdjoinRoot P :=
    AdjoinRoot.algHomOfDvd K (P ^ a) P (dvd_pow_self P (by omega))
  have hρ : ∀ h : K[X], ρ (AdjoinRoot.mk (P ^ a) h) = AdjoinRoot.mk P h := by
    intro h
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, AdjoinRoot.algHomOfDvd_root,
      AdjoinRoot.aeval_eq]
  -- elements with the same reduction have the same `q^a`-th power
  have hnil : ∀ w w' : AdjoinRoot (P ^ a), ρ w = ρ w' → w ^ (q ^ a) = w' ^ (q ^ a) := by
    intro w w' h
    obtain ⟨u, rfl⟩ := AdjoinRoot.mk_surjective w
    obtain ⟨u', rfl⟩ := AdjoinRoot.mk_surjective w'
    rw [hρ, hρ, AdjoinRoot.mk_eq_mk] at h
    rw [← map_pow, ← map_pow, AdjoinRoot.mk_eq_mk, ← sub_pow_card_pow]
    exact (pow_dvd_pow P (Nat.lt_pow_self (by omega)).le).trans (pow_dvd_pow_of_dvd h _)
  -- the bijection
  let toL : {x : AdjoinRoot (P ^ a) // x ^ (q ^ g) = x} →
      {y : AdjoinRoot P // y ^ (q ^ g) = y} :=
    fun x => ⟨ρ x.1, by rw [← map_pow, x.2]⟩
  have hiter : ∀ {R : Type _} [CommRing R] (x : R), x ^ (q ^ g) = x →
      ∀ n, x ^ (q ^ (g * n)) = x := by
    intro R _ x hx n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hx]
  have hbij : Function.Bijective toL := by
    constructor
    · rintro ⟨x, hx⟩ ⟨x', hx'⟩ h
      have h' : ρ x = ρ x' := congrArg Subtype.val h
      apply Subtype.ext
      have hd : (x - x') ^ (q ^ g) = x - x' := by rw [sub_pow_card_pow, hx, hx']
      have hd0 : ρ (x - x') = 0 := by rw [map_sub, h', sub_self]
      have h1 := hiter (x - x') hd a
      have h2 := hnil (x - x') 0 (by rw [hd0, map_zero])
      have h3 : (x - x') ^ (q ^ (g * a)) = 0 := by
        have hle : q ^ a ≤ q ^ (g * a) :=
          Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_left _ hg)
        rw [show q ^ (g * a) = q ^ a + (q ^ (g * a) - q ^ a) by omega, pow_add, h2,
          zero_pow (pow_ne_zero _ (by omega)), zero_mul]
      rw [h1] at h3
      exact sub_eq_zero.1 h3
    · rintro ⟨y, hy⟩
      obtain ⟨u, hu⟩ := AdjoinRoot.mk_surjective (y : AdjoinRoot P)
      set z := AdjoinRoot.mk (P ^ a) u
      have hz : ρ z = y := by rw [hρ, hu]
      have hfa : a ≤ f * a := Nat.le_mul_of_pos_left a hP.natDegree_pos
      have hyL : ∀ n, y ^ (q ^ (f * n)) = y := by
        intro n
        rw [pow_mul, ← hcardL]
        exact FiniteField.pow_card_pow n y
      have hyg : ∀ n, y ^ (q ^ (g + n)) = y ^ (q ^ n) := by
        intro n; rw [pow_add, pow_mul, hy]
      refine ⟨⟨z ^ (q ^ (f * a)), ?_⟩, ?_⟩
      · -- `z^(q^(f a + g)) = z^(q^(f a))`
        have e1 : (z ^ (q ^ (f * a))) ^ (q ^ g) =
            (z ^ (q ^ (f * a - a + g))) ^ (q ^ a) := by
          rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
          congr 2; omega
        have e2 : z ^ (q ^ (f * a)) = (z ^ (q ^ (f * a - a))) ^ (q ^ a) := by
          rw [← pow_mul, ← pow_add]; congr 2; omega
        rw [e1, e2]
        apply hnil
        rw [map_pow, map_pow, hz, show f * a - a + g = g + (f * a - a) by ring, hyg]
      · apply Subtype.ext
        simp only [toL, map_pow, hz]
        exact hyL a
  rw [Nat.card_congr (Equiv.ofBijective toL hbij)]
  exact natCard_fixed_field hcardL hgf (Nat.one_lt_pow (by omega) (by omega))

end FixedCount

/-- **Lemma 29.8 (1)** (section 29.2.1). In `R_i = F_q[T]/(P^a)`, `P` irreducible of degree `f`
and `a ≥ 1`, the kernel of `φ^j - 1` (`j ≥ 1`) has dimension `gcd(j, f)`. The kernel is that of
`φ^gcd(j, f) - 1`, since `φ^(a+f) = φ^a`, and its `q^gcd(j, f)` elements are the lifts of the
subfield `F_(q^gcd(j, f))` of the residue field. -/
theorem lemma29_8_one {K : Type*} [Field K] [Fintype K] {P : K[X]} (hP : Irreducible P)
    {a j : ℕ} (ha : 1 ≤ a) (hj : 1 ≤ j) :
    finrank K (LinearMap.ker (frobA K (AdjoinRoot (P ^ a)) ^ j - 1)) = Nat.gcd j P.natDegree := by
  have hf : 1 ≤ P.natDegree := hP.natDegree_pos
  have := (AdjoinRoot.powerBasis (pow_ne_zero a hP.ne_zero)).finite
  rw [ker_pow_sub_one_eq_gcd _ hf hj (m := a)
    (fun v => by rw [frobA_pow_apply, frobA_pow_apply]; exact pow_card_pow_add_local hP a v)]
  set g := Nat.gcd j P.natDegree
  have hg : 1 ≤ g := Nat.gcd_pos_of_pos_left _ hj
  have hcard : Nat.card (LinearMap.ker (frobA K (AdjoinRoot (P ^ a)) ^ g - 1)) =
      Fintype.card K ^ g := by
    rw [← natCard_fixed_pow_local hP ha hg (Nat.gcd_dvd_right j _)]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      frobA_pow_apply]
  rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card] at hcard
  exact Nat.pow_right_injective Fintype.one_lt_card hcard

/-! ### Lemma 29.8 (2): the image of `φ^j - 1` and the trace -/

section TraceKernel

variable {K : Type*} [Field K] [Fintype K]

/-- The trace from `F_(q^f)` down to `F_(q^g)`, `n = f/g`, written as the sum of the conjugates
`y^(q^(g i))`, `i < n`: an `F_q`-linear map. -/
noncomputable def trDown (K L : Type*) [Field K] [Fintype K] [CommRing L] [Algebra K L]
    (g n : ℕ) : L →ₗ[K] L :=
  ∑ i ∈ Finset.range n, frobA K L ^ (g * i)

lemma trDown_apply {L : Type*} [CommRing L] [Algebra K L] (g n : ℕ) (y : L) :
    trDown K L g n y = ∑ i ∈ Finset.range n, y ^ (Fintype.card K ^ (g * i)) := by
  simp [trDown, LinearMap.sum_apply, frobA_pow_apply]

/-- `Tr(y^(q^g)) = Tr(y)` when `y^(q^(g n)) = y` for every `y`. -/
lemma trDown_frob {L : Type*} [CommRing L] [Algebra K L] {g n : ℕ}
    (hper : ∀ y : L, y ^ (Fintype.card K ^ (g * n)) = y) (k : ℕ) (y : L) :
    trDown K L g n (((frobA K L ^ g) ^ k) y) = trDown K L g n y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    rw [trDown_apply, trDown_apply, frobA_pow_apply]
    have e : ∀ i, (y ^ (Fintype.card K ^ g)) ^ (Fintype.card K ^ (g * i)) =
        y ^ (Fintype.card K ^ (g * (i + 1))) := by
      intro i; rw [← pow_mul, ← pow_add]; congr 2; ring
    simp only [e]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have h1 := Finset.sum_range_succ (fun i => y ^ (Fintype.card K ^ (g * i))) n
    have h2 := Finset.sum_range_succ' (fun i => y ^ (Fintype.card K ^ (g * i))) n
    rw [hper y] at h1
    simp only [mul_zero, pow_zero, pow_one] at h2
    rw [h1] at h2
    linear_combination -h2

/-- The kernel of the trace has at most `q^(g (n - 1))` elements: they are roots of
`∑_(i < n) X^(q^(g i))`, a nonzero polynomial of that degree. -/
lemma natCard_ker_trDown_le {L : Type*} [Field L] [Finite L] [Algebra K L] {g n : ℕ}
    (hg : 1 ≤ g) (hn : 1 ≤ n) :
    Nat.card (LinearMap.ker (trDown K L g n)) ≤ Fintype.card K ^ (g * (n - 1)) := by
  classical
  set q := Fintype.card K
  have hq : 2 ≤ q := Fintype.one_lt_card
  set T : L[X] := ∑ i ∈ Finset.range n, X ^ (q ^ (g * i))
  have hinj : ∀ i i', q ^ (g * i) = q ^ (g * i') → i = i' := by
    intro i i' h
    have := Nat.pow_right_injective hq h
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hcoeff : T.coeff (q ^ (g * (n - 1))) = 1 := by
    rw [finsetSum_coeff, Finset.sum_eq_single (n - 1)]
    · simp
    · intro i _ hi
      rw [coeff_X_pow]
      split_ifs with h
      · exact absurd (hinj _ _ h.symm) hi
      · rfl
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hT0 : T ≠ 0 := fun h => by simp [h] at hcoeff
  have hdeg : T.natDegree ≤ q ^ (g * (n - 1)) := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    rw [natDegree_X_pow]
    exact Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left _ (by have := Finset.mem_range.1 hi; omega))
  have hsub : ∀ y ∈ LinearMap.ker (trDown K L g n), y ∈ T.roots.toFinset := by
    intro y hy
    rw [LinearMap.mem_ker, trDown_apply] at hy
    rw [Multiset.mem_toFinset, mem_roots hT0, IsRoot, eval_finsetSum]
    simpa using hy
  calc Nat.card (LinearMap.ker (trDown K L g n))
      ≤ Nat.card T.roots.toFinset := by
        refine Nat.card_mono (Set.toFinite _) fun y hy => hsub y hy
    _ = T.roots.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ T.roots.card := Multiset.toFinset_card_le _
    _ ≤ T.natDegree := card_roots' T
    _ ≤ q ^ (g * (n - 1)) := hdeg

/-- **Lemma 29.8 (2)** on the residue field (section 29.2.1): on `L = F_q[T]/(P)`, `P`
irreducible of degree `f`, the image of `φ^j - 1` (`j ≥ 1`) is the kernel of the trace from `L`
down to `F_(q^g)`, `g = gcd(j, f)`, written as `∑_(i < f/g) y^(q^(g i))` (additive
Hilbert 90). It lies in the kernel because the trace is invariant under `φ^g`, and both have
dimension `f - g`. -/
theorem lemma29_8_two_field {P : K[X]} (hP : Irreducible P) {j : ℕ} (hj : 1 ≤ j) :
    have : Fact (Irreducible P) := ⟨hP⟩
    LinearMap.range (frobA K (AdjoinRoot P) ^ j - 1) =
      LinearMap.ker (trDown K (AdjoinRoot P) (Nat.gcd j P.natDegree)
        (P.natDegree / Nat.gcd j P.natDegree)) := by
  intro inst
  set q := Fintype.card K
  set f := P.natDegree
  set g := Nat.gcd j f
  set n := f / g
  have hf : 1 ≤ f := hP.natDegree_pos
  have hg : 1 ≤ g := Nat.gcd_pos_of_pos_left _ hj
  have hgn : g * n = f := Nat.mul_div_cancel' (Nat.gcd_dvd_right j f)
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, mul_zero] at hgn; omega
    · exact h
  have hfin : Module.Finite K (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  let _ := Fintype.ofFinite (AdjoinRoot P)
  have hdim : finrank K (AdjoinRoot P) = f := by
    rw [(AdjoinRoot.powerBasis hP.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hcardL : Fintype.card (AdjoinRoot P) = q ^ f := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := K),
      Nat.card_eq_fintype_card, hdim]
  have hper : ∀ y : AdjoinRoot P, y ^ (q ^ (g * n)) = y := by
    intro y; rw [hgn, ← hcardL]; exact FiniteField.pow_card y
  set φ := frobA K (AdjoinRoot P)
  -- the image lies in the kernel of the trace
  have hle : LinearMap.range (φ ^ j - 1) ≤ LinearMap.ker (trDown K (AdjoinRoot P) g n) := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, Module.End.one_apply]
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_left j f
    rw [show j = g * t from ht, pow_mul, trDown_frob hper, sub_self]
  -- dimensions
  have hker : finrank K (LinearMap.ker (φ ^ j - 1)) = g := by
    have hperL : ∀ v, (φ ^ (0 + f)) v = (φ ^ 0) v := by
      intro v; rw [frobA_pow_apply, zero_add, ← hcardL, FiniteField.pow_card]; simp
    rw [ker_pow_sub_one_eq_gcd φ hf hj hperL]
    have hcard : Nat.card (LinearMap.ker (φ ^ g - 1)) = q ^ g := by
      rw [← natCard_fixed_field hcardL (Nat.gcd_dvd_right j f)
        (Nat.one_lt_pow (by omega) Fintype.one_lt_card)]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, φ,
        frobA_pow_apply]
      exact Iff.rfl
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card] at hcard
    exact Nat.pow_right_injective (Fintype.one_lt_card (α := K)) hcard
  have hrange : finrank K (LinearMap.range (φ ^ j - 1)) = f - g := by
    have := LinearMap.finrank_range_add_finrank_ker (φ ^ j - 1)
    omega
  have htr : finrank K (LinearMap.ker (trDown K (AdjoinRoot P) g n)) ≤ f - g := by
    have h1 := natCard_ker_trDown_le (K := K) (L := AdjoinRoot P) hg hn
    rw [Module.natCard_eq_pow_finrank (K := K), Nat.card_eq_fintype_card] at h1
    have h2 : g * (n - 1) = f - g := by rw [Nat.mul_sub, mul_one, hgn]
    rw [h2] at h1
    exact (Nat.pow_le_pow_iff_right (Fintype.one_lt_card (α := K))).1 h1
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

/-- **Lemma 29.8 (2)** (section 29.2.1). On `R_i = F_q[T]/(P^a)`, `a ≥ 1`, the image of
`φ^j - 1` (`j ≥ 1`) is the preimage, under reduction modulo `P`, of the kernel of the trace from
`F_(q^f)` down to `F_(q^gcd(j, f))`; it contains the nilradical (`lemma29_8_two_nil`). -/
theorem lemma29_8_two {P : K[X]} (hP : Irreducible P) {a j : ℕ} (ha : 1 ≤ a) (hj : 1 ≤ j) :
    have : Fact (Irreducible P) := ⟨hP⟩
    LinearMap.range (frobA K (AdjoinRoot (P ^ a)) ^ j - 1) =
      (LinearMap.ker (trDown K (AdjoinRoot P) (Nat.gcd j P.natDegree)
        (P.natDegree / Nat.gcd j P.natDegree))).comap
        (AdjoinRoot.algHomOfDvd K (P ^ a) P (dvd_pow_self P (by omega))).toLinearMap := by
  intro inst
  set ρ := AdjoinRoot.algHomOfDvd K (P ^ a) P (dvd_pow_self P (by omega))
  have hρ : ∀ h : K[X], ρ (AdjoinRoot.mk (P ^ a) h) = AdjoinRoot.mk P h := by
    intro h
    rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, AdjoinRoot.algHomOfDvd_root,
      AdjoinRoot.aeval_eq]
  have hcomm : ∀ x, ρ ((frobA K (AdjoinRoot (P ^ a)) ^ j - 1) x) =
      (frobA K (AdjoinRoot P) ^ j - 1) (ρ x) := by
    intro x
    simp only [LinearMap.sub_apply, Module.End.one_apply, frobA_pow_apply, map_sub, map_pow]
  have hfield := lemma29_8_two_field hP hj
  ext x
  rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, ← hfield]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨ρ z, (hcomm z).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨u, rfl⟩ := AdjoinRoot.mk_surjective y
    set z := AdjoinRoot.mk (P ^ a) u
    have hz : ρ z = AdjoinRoot.mk P u := hρ u
    -- `x - (φ^j - 1) z` reduces to 0, so it is nilpotent
    have hnil : IsNilpotent (x - (frobA K (AdjoinRoot (P ^ a)) ^ j - 1) z) := by
      obtain ⟨v, hv⟩ := AdjoinRoot.mk_surjective x
      have h0 : ρ (x - (frobA K (AdjoinRoot (P ^ a)) ^ j - 1) z) = 0 := by
        rw [map_sub, hcomm, hz, hy, sub_self]
      obtain ⟨w, hw⟩ := AdjoinRoot.mk_surjective (x - (frobA K (AdjoinRoot (P ^ a)) ^ j - 1) z)
      rw [← hw, hρ, AdjoinRoot.mk_eq_zero] at h0
      refine ⟨a, ?_⟩
      rw [← hw, ← map_pow, AdjoinRoot.mk_eq_zero]
      exact pow_dvd_pow_of_dvd h0 a
    have := Submodule.add_mem _ (LinearMap.mem_range_self _ z) (lemma29_8_two_nil (K := K) hnil hj)
    simpa using this

end TraceKernel

/-! ### Theorem 29.11 (2): the exact criterion -/

section Theorem29_11_two

variable {K : Type*} [Field K] [Fintype K] {B : K[X]}

/-- A functional vanishes on `J` exactly when `λ ∘ (φ^j - 1)` vanishes on `W_j` for
`j = 1, ..., e - 1` (section 29.2.3). -/
lemma mem_dualAnnihilator_Jsum {l : Dual K (AdjoinRoot (B - 1))} :
    l ∈ (Jsum B).dualAnnihilator ↔
      ∀ j ∈ Finset.Icc 1 (B.natDegree - 1), ∀ w ∈ Wj B j, l ((frobR B ^ j - 1) w) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h j hj w hw
    exact h _ (le_iSup₂ (f := fun j (_ : j ∈ Finset.Icc 1 (B.natDegree - 1)) =>
      (Wj B j).map (frobR B ^ j - 1)) j hj ⟨w, hw, rfl⟩)
  · intro h
    have : Jsum B ≤ LinearMap.ker l := iSup₂_le fun j hj => by
      rintro _ ⟨w, hw, rfl⟩
      exact h j hj w hw
    exact fun w hw => this hw

variable [DecidableEq K]

/-- **Theorem 29.11 (2)** (section 29.2.3). For `B` of degree `e ≥ 2`, `k(B) = ω(B - 1) + 1`
holds if and only if
(a) `Λ_(e-2) = 0`, where `Λ_j = ∑_(i ≤ j) ℓ ∘ φ^i`;
(b) `Λ_j` vanishes on `W_j` for `1 ≤ j ≤ e - 3`;
(c) `ℓ` vanishes on the fixed ring `R^φ`. -/
theorem theorem29_11_two (hB : 2 ≤ B.natDegree) :
    kDim B = omegaF (B - 1) + 1 ↔
      (∀ v, ∑ i ∈ Finset.range (B.natDegree - 1),
          topCoeff (one_le_two.trans hB) ((frobR B ^ i) v) = 0) ∧
      (∀ j, 1 ≤ j → j + 3 ≤ B.natDegree → ∀ v ∈ Wj B j,
          ∑ i ∈ Finset.range (j + 1), topCoeff (one_le_two.trans hB) ((frobR B ^ i) v) = 0) ∧
      (∀ v, frobR B v = v → topCoeff (one_le_two.trans hB) v = 0) := by
  have h1 : 1 ≤ B.natDegree := one_le_two.trans hB
  have := (AdjoinRoot.powerBasis (sub_one_ne_zero h1)).finite
  set e := B.natDegree with he
  set φ := frobR B
  set ℓ := topCoeff h1
  have hlo := theorem21_6 h1
  have hhi := theorem29_11_one hB
  have hker : finrank K (LinearMap.ker (φ - 1)) = omegaF (B - 1) := finrank_ker_frobR h1
  have hkey : kDim B = omegaF (B - 1) + 1 ↔
      ∃ l ∈ (Jsum B).dualAnnihilator, ∃ v, l (φ v - v) ≠ 0 := by
    rw [← codim_gt_iff φ (Jsum B) Jsum_le_range, hker, finrank_residue h1]
    rw [kDim] at hlo hhi ⊢
    omega
  rw [hkey]
  have hpow : ∀ i v, (φ ^ (i + 1)) v = (φ ^ i) (φ v) := fun i v => by
    rw [pow_succ, Module.End.mul_apply]
  constructor
  · rintro ⟨l, hl, v0, hv0⟩
    have hl' := mem_dualAnnihilator_Jsum.1 hl
    -- `δ_(e-2) = c ℓ`
    obtain ⟨c, hc⟩ := topCoeff_span hB ((φ ^ (e - 2) - 1).dualMap l) (by
      rw [Submodule.mem_dualAnnihilator]
      intro w hw
      rcases Nat.eq_zero_or_pos (e - 2) with h0 | hpos
      · simp [h0]
      · exact hl' _ (Finset.mem_Icc.2 ⟨hpos, by omega⟩) w hw)
    have hδ : ∀ v, l ((φ ^ (e - 2)) v) - l v = c * ℓ v := by
      intro v
      have := congrArg (fun f => f v) hc
      simpa [LinearMap.dualMap_apply, map_sub] using this
    -- `δ_1 = -c ℓ ∘ φ`
    have hδ1 : ∀ v, l (φ v) - l v = -(c * ℓ (φ v)) := by
      intro v
      have h0 := hl' (e - 1) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩) v
        (by rw [he, Wj_top h1]; trivial)
      have h2 := hδ (φ v)
      rw [show e - 1 = e - 2 + 1 by omega, pow_succ] at h0
      simp only [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, map_sub] at h0
      linear_combination h0 - h2
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hv0
      rw [map_sub, hδ1 v0]; ring
    have htel : ∀ j v, l ((φ ^ j) v) - l v =
        ∑ i ∈ Finset.range j, -(c * ℓ ((φ ^ (i + 1)) v)) := by
      intro j v
      have := Finset.sum_range_sub (fun i => l ((φ ^ i) v)) j
      simp only [pow_zero, Module.End.one_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', Module.End.mul_apply]
      exact hδ1 _
    refine ⟨fun v => ?_, fun j hj1 hj3 v hv => ?_, fun v hv => ?_⟩
    · have h := (hδ v).symm.trans (htel _ v)
      rw [show e - 1 = e - 2 + 1 by omega, Finset.sum_range_succ', pow_zero, Module.End.one_apply]
      have : c * (∑ i ∈ Finset.range (e - 2), ℓ ((φ ^ (i + 1)) v) + ℓ v) = 0 := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h
        linear_combination h
      exact (mul_eq_zero.1 this).resolve_left hc0
    · have h0 := hl' j (Finset.mem_Icc.2 ⟨hj1, by omega⟩) v hv
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub] at h0
      have h := htel j v
      rw [h0, Finset.sum_neg_distrib, ← Finset.mul_sum] at h
      have hs : ∑ i ∈ Finset.range j, ℓ ((φ ^ (i + 1)) v) = 0 :=
        (mul_eq_zero.1 (by linear_combination h)).resolve_left hc0
      rw [Finset.sum_range_succ', hs, pow_zero, Module.End.one_apply,
        topCoeff_Wj h1 (by omega) hv, add_zero]
    · have h := hδ1 v
      rw [hv, sub_self] at h
      have : c * ℓ v = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left hc0
  · rintro ⟨ha, hb, hc⟩
    -- `λ` with `λ ∘ (φ - 1) = ℓ ∘ φ`, by (c)
    have hμ : φ.dualMap ℓ ∈ (LinearMap.ker (φ - 1)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      have hv' : φ v = v := by simpa [sub_eq_zero] using hv
      rw [LinearMap.dualMap_apply, hv']
      exact hc v hv'
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hμ
    obtain ⟨l, hl⟩ := hμ
    have hl1 : ∀ v, l (φ v) - l v = ℓ (φ v) := by
      intro v
      have := congrArg (fun f => f v) hl
      simpa [LinearMap.dualMap_apply, map_sub] using this
    have htel : ∀ j v, l ((φ ^ j) v) - l v = ∑ i ∈ Finset.range j, ℓ ((φ ^ (i + 1)) v) := by
      intro j v
      have := Finset.sum_range_sub (fun i => l ((φ ^ i) v)) j
      simp only [pow_zero, Module.End.one_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', Module.End.mul_apply]
      exact hl1 _
    refine ⟨l, mem_dualAnnihilator_Jsum.2 fun j hj w hw => ?_, ?_⟩
    · obtain ⟨hj1, hje⟩ := Finset.mem_Icc.1 hj
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
      rw [htel]
      rcases Nat.lt_or_ge j (e - 1) with hlt | hge
      · have hΛ : ∑ i ∈ Finset.range (j + 1), ℓ ((φ ^ i) w) = 0 := by
          rcases Nat.lt_or_ge (j + 3) (e + 1) with h3 | h3
          · exact hb j hj1 (by omega) w hw
          · rw [show j + 1 = e - 1 by omega]; exact ha w
        rw [Finset.sum_range_succ', pow_zero, Module.End.one_apply,
          topCoeff_Wj h1 (by omega) hw, add_zero] at hΛ
        exact hΛ
      · rw [show j = e - 1 by omega]
        have := ha (φ w)
        simpa only [hpow] using this
    · by_contra hcon
      push Not at hcon
      apply topCoeff_ne_zero h1
      ext v
      have h0 : ∀ v, ℓ (φ v) = 0 := fun v => by
        have := hcon v
        rwa [map_sub, hl1] at this
      have := ha v
      rw [show e - 1 = e - 2 + 1 by omega, Finset.sum_range_succ', pow_zero,
        Module.End.one_apply] at this
      rw [Finset.sum_eq_zero fun i _ => by rw [pow_succ', Module.End.mul_apply]; exact h0 _,
        zero_add] at this
      simpa using this

end Theorem29_11_two

/-! ### Lemma 29.14 -/

/-- **Lemma 29.14** (section 29.3.1): Assumption R fails for `b = 10`, `d = 2`. A 1-digit string
`x` whose weight has 2 digits is the digit 3, so its residue `g(3) = 24 ≡ 6 (mod 9)` has
probability 1. -/
theorem lemma29_14 : ∀ x < 10, (10 ≤ x ^ x ∧ x ^ x < 100 ↔ x = 3) := by decide

end Munchausen
