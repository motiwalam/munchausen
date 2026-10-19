import Munchausen.Counting

/-!
# The window of the base (Lemma 20.1, Proposition 15.17)

A `k`-digit solution `n` with leading digit `p` and second digit at most `M` has
`p b^(k-1) ≤ n < p b^(k-1) + (M + 1) b^(k-2)`, so its base lies in a window of length
`(M + 1) / (p (k - 1))` above `(n / p)^(1/(k-1))`.
-/

open Real

namespace Munchausen

/-- **Lemma 20.1** (section 20.1.2). Let `(p, q, t)` be a solution in base `b` with
`k = |t| + 2` digits and `q ≤ M`. Then `p b^(k-1) ≤ n < p b^(k-1) + (M + 1) b^(k-2)`. -/
theorem lemma20_1 {b m p q M : ℕ} {t : List ℕ} (hs : IsSolution b m (p :: q :: t))
    (hq : q ≤ M) :
    p * b ^ (t.length + 1) ≤ P b (p :: q :: t) ∧
      P b (p :: q :: t) < p * b ^ (t.length + 1) + (M + 1) * b ^ t.length := by
  have hp := hs.lt_base p (by simp)
  have hb : 1 < b := by
    have := hs.head_ne_zero (by simp); simp at this; omega
  have ht : P b t < b ^ t.length := P_lt_pow hb fun d hd => hs.lt_base d (by simp [hd])
  simp only [P_cons, List.length_cons, Nat.cast_id]
  constructor
  · omega
  · have : q * b ^ t.length + b ^ t.length ≤ (M + 1) * b ^ t.length := by
      rw [← add_one_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- **Lemma 20.1**, the root form (section 20.1.2). With `j = k - 1 = |t| + 1`:
`b ≤ (n / p)^(1/j) < b + (M + 1) / (p j)`. -/
theorem lemma20_1_root {b m p q M : ℕ} {t : List ℕ} (hs : IsSolution b m (p :: q :: t))
    (hq : q ≤ M) :
    (b : ℝ) ≤ (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ ∧
      (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ <
        b + (M + 1) / (p * (t.length + 1 : ℕ)) := by
  obtain ⟨h1, h2⟩ := lemma20_1 hs hq
  have hp1 : 1 ≤ p := by
    have := hs.head_ne_zero (by simp); simp at this; omega
  have hb : 1 < b := by have := hs.lt_base p (by simp); omega
  set j := t.length + 1 with hj
  set n := P b (p :: q :: t)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  have hbR : (0 : ℝ) < b := by positivity
  have hjR : (0 : ℝ) < j := by positivity
  have hj0 : j ≠ 0 := by omega
  have h1R : (p : ℝ) * b ^ j ≤ n := by exact_mod_cast h1
  have h2R : (n : ℝ) < p * b ^ j + (M + 1) * b ^ t.length := by exact_mod_cast h2
  have hbj : (b : ℝ) ^ j = b * b ^ t.length := by rw [hj, pow_succ']
  have hN0 : (0 : ℝ) ≤ n / p := by positivity
  have hinv : (0 : ℝ) < (j : ℝ)⁻¹ := inv_pos.2 hjR
  constructor
  · have : (b : ℝ) ^ j ≤ n / p := by rw [le_div_iff₀ hpR]; linarith
    calc (b : ℝ) = ((b : ℝ) ^ j) ^ (j : ℝ)⁻¹ := (pow_rpow_inv_natCast hbR.le hj0).symm
      _ ≤ (n / p) ^ (j : ℝ)⁻¹ := rpow_le_rpow (by positivity) this hinv.le
  · set u : ℝ := (M + 1) / (p * b)
    have hu : 0 ≤ u := by positivity
    have hlt : (n : ℝ) / p < (b : ℝ) ^ j * (1 + u) := by
      rw [div_lt_iff₀ hpR]
      have : (b : ℝ) ^ j * (1 + u) * p = p * b ^ j + (M + 1) * b ^ t.length := by
        simp only [u]; rw [hbj]; field_simp
      linarith
    have hB : (1 + u) ^ (j : ℝ)⁻¹ ≤ 1 + (j : ℝ)⁻¹ * u :=
      rpow_one_add_le_one_add_mul_self (by linarith) hinv.le
        (inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ j by omega)))
    calc ((n : ℝ) / p) ^ (j : ℝ)⁻¹ < ((b : ℝ) ^ j * (1 + u)) ^ (j : ℝ)⁻¹ :=
          rpow_lt_rpow hN0 hlt hinv
      _ = b * (1 + u) ^ (j : ℝ)⁻¹ := by
          rw [mul_rpow (by positivity) (by positivity), pow_rpow_inv_natCast hbR.le hj0]
      _ ≤ b * (1 + (j : ℝ)⁻¹ * u) := mul_le_mul_of_nonneg_left hB hbR.le
      _ = b + (M + 1) / (p * j) := by simp only [u]; field_simp

/-- **Proposition 15.17** (section 15.6). Let `X` bound every digit `d` with `d^d ≤ N`. A
solution `N` with `k = |t| + 2` digits, leading digit `p`, has
`b ≤ (N / p)^(1/(k-1)) < b + (X + 1) / (p (k - 1))`. -/
theorem prop15_17 {b m p q X : ℕ} {t : List ℕ} (hs : IsSolution b m (p :: q :: t))
    (hX : ∀ d, d ^ d ≤ P b (p :: q :: t) → d ≤ X) :
    (b : ℝ) ≤ (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ ∧
      (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ <
        b + (X + 1) / (p * (t.length + 1 : ℕ)) := by
  refine lemma20_1_root hs (hX q ?_)
  rw [hs.eq]
  have hp1 : p ≠ 0 := by have := hs.head_ne_zero (by simp); simpa using this
  have := one_le_w (m := m) hp1
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero, Fs_cons]; omega
  · have : q ^ q = w m q := (w_of_ne_zero m hq.ne').symm
    rw [this, Fs_cons, Fs_cons]
    omega

end Munchausen
