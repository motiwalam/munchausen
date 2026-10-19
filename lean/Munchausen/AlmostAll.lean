import Munchausen.Counting

/-!
# Almost all bases have no short solution (Theorem 11.2)

The finite bound `theorem11_2_finite` and an estimate of the largest digit give the
asymptotic form: for `α > 0` and `δ > 0`, the bases `b ≤ B` with a solution of `k ≥ 2` digits,
`k ≤ α ln b / ln ln b`, number at most `B^(2 α + δ)` once `B` is large. With `α = 1/2 - ε` this
is the library's `B^(1 - 2 ε + o(1))`.
-/

open Real Filter

namespace Munchausen

/-- `t / log t` is monotone on `[e, ∞)`. -/
lemma div_log_le_div_log {s t : ℝ} (hs : exp 1 ≤ s) (hst : s ≤ t) :
    s / log s ≤ t / log t := by
  have h := log_div_self_antitoneOn (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hst)) hst
  have hs0 : 0 < s := (exp_pos 1).trans_le hs
  have hls : 1 ≤ log s := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hs
  have hlt : 1 ≤ log t := hls.trans (log_le_log hs0 hst)
  simp only at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

/-- `e ≤ ln b` for `b ≥ 16`. -/
lemma exp_one_le_log {b : ℕ} (hb : 16 ≤ b) : exp 1 ≤ log b := by
  have h16 : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  have h1 : log (16 : ℝ) ≤ log b := log_le_log (by norm_num) (by exact_mod_cast hb)
  have := exp_one_lt_d9
  have := log_two_gt_d9
  linarith

open Classical in
/-- The bases `2 ≤ b ≤ B` with a solution of `k ≥ 2` digits, `k ≤ α ln b / ln ln b`, under
`0^0 = m`. -/
noncomputable def shortBases (m : ℕ) (α : ℝ) (B : ℕ) : Finset ℕ :=
  (Finset.Icc 2 B).filter fun b => ∃ s : List ℕ, 2 ≤ s.length ∧
    (s.length : ℝ) ≤ α * log b / log (log b) ∧ IsSolution b m s

/-- Digits of short solutions are small (proof of Theorem 11.2): if `k ≤ α L / ln L` with
`L = ln B` and `ln L ≥ max 1 α`, then `x^x < B^k` forces `x ≤ L^2`. -/
lemma le_floor_sq_of_pow_self_lt {B k x : ℕ} {α : ℝ} (hB : 2 ≤ B)
    (hLL : max 1 α ≤ log (log (B : ℝ))) (hk : (k : ℝ) ≤ α * log B / log (log B))
    (hx : x ^ x < B ^ k) : x ≤ ⌊log (B : ℝ) ^ 2⌋₊ := by
  set L := log (B : ℝ)
  set LL := log L
  have hLL1 : 1 ≤ LL := (le_max_left _ _).trans hLL
  have hLLα : α ≤ LL := (le_max_right _ _).trans hLL
  have hL0 : 0 < L := log_pos (by exact_mod_cast hB)
  by_contra hlt
  have hxL : L ^ 2 < x := by
    have := Nat.lt_floor_add_one (L ^ 2)
    have h' : ⌊L ^ 2⌋₊ + 1 ≤ x := by omega
    have : ((⌊L ^ 2⌋₊ + 1 : ℕ) : ℝ) ≤ x := by exact_mod_cast h'
    push_cast at this
    linarith
  have hL2 : 0 < L ^ 2 := by positivity
  have hx0 : (0 : ℝ) < x := hL2.trans hxL
  -- `x ln x < k L ≤ α L^2 / LL`
  have h1 : (x : ℝ) * log x < k * L := by
    have : ((x ^ x : ℕ) : ℝ) < ((B ^ k : ℕ) : ℝ) := by exact_mod_cast hx
    push_cast at this
    have := log_lt_log (by positivity) this
    rwa [log_pow, log_pow] at this
  have h2 : (k : ℝ) * L ≤ α * L ^ 2 / LL := by
    have := mul_le_mul_of_nonneg_right hk hL0.le
    calc (k : ℝ) * L ≤ α * L / LL * L := this
      _ = α * L ^ 2 / LL := by ring
  -- `x ln x > L^2 ln (L^2) = 2 L^2 LL`
  have h3 : log (L ^ 2) < log x := log_lt_log hL2 hxL
  rw [log_pow] at h3
  have h4 : L ^ 2 * (2 * LL) < x * log x := by
    push_cast at h3
    exact mul_lt_mul'' hxL h3 hL2.le (by positivity)
  have h5 : L ^ 2 * (2 * LL) < α * L ^ 2 / LL := by linarith
  rw [lt_div_iff₀ (by linarith)] at h5
  have h6 : L ^ 2 * (2 * LL * LL) < L ^ 2 * α := by linarith
  have h7 := lt_of_mul_lt_mul_left h6 hL2.le
  nlinarith

/-- **Theorem 11.2**, for one large `B` (section 11.6). If `ln ln B ≥ max 1 α`,
`ln B ≥ 34 / δ^2` and `B ≥ 16`, then at most `B^(2 α + δ)` bases `b ≤ B` have a solution of
`k ≥ 2` digits with `k ≤ α ln b / ln ln b`. -/
lemma shortBases_card_le {m B : ℕ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hLL : max 1 α ≤ log (log (B : ℝ))) (hLδ : 34 / δ ^ 2 ≤ log (B : ℝ)) (hB : 16 ≤ B) :
    ((shortBases m α B).card : ℝ) ≤ (B : ℝ) ^ (2 * α + δ) := by
  classical
  set L := log (B : ℝ) with hLdef
  set LL := log L with hLLdef
  have hLL1 : 1 ≤ LL := (le_max_left _ _).trans hLL
  have hLLα : α ≤ LL := (le_max_right _ _).trans hLL
  have hL0 : 0 < L := log_pos (by exact_mod_cast (show 1 < B by omega))
  have hL1 : 1 ≤ L := by
    have := exp_one_le_log hB
    have := add_one_le_exp 1
    linarith
  set Kr := α * L / LL with hKr
  set K := ⌊Kr⌋₊
  set X := ⌊L ^ 2⌋₊
  -- the short bases are below 16 or have a solution of length `2 ≤ k ≤ K`
  have hsub : shortBases m α B ⊆
      Finset.Icc 2 15 ∪ (Finset.Icc 2 K).biUnion fun k => basesWith m B k := by
    intro b hb
    simp only [shortBases, Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb2, hbB⟩, s, hs2, hsk, hsol⟩ := hb
    by_cases hb15 : b ≤ 15
    · exact Finset.mem_union_left _ (Finset.mem_Icc.2 ⟨hb2, hb15⟩)
    apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨s.length, Finset.mem_Icc.2 ⟨hs2, Nat.le_floor ?_⟩, ?_⟩
    · have hmono : log b / log (log b) ≤ L / LL :=
        div_log_le_div_log (exp_one_le_log (by omega))
          (log_le_log (by positivity) (by exact_mod_cast hbB))
      calc (s.length : ℝ) ≤ α * log b / log (log b) := hsk
        _ = α * (log b / log (log b)) := by ring
        _ ≤ α * (L / LL) := mul_le_mul_of_nonneg_left hmono hα.le
        _ = Kr := by rw [hKr]; ring
    · simp only [basesWith, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hb2, hbB⟩, s, rfl, hsol⟩
  have hKKr : (K : ℝ) ≤ Kr := Nat.floor_le (by positivity)
  have hcard : (shortBases m α B).card ≤ 14 + K * (X + 1) ^ K := by
    have hterm : ∀ k ∈ Finset.Icc 2 K, (basesWith m B k).card ≤ (X + 1) ^ K := by
      intro k hk
      obtain ⟨hk2, hkK⟩ := Finset.mem_Icc.1 hk
      have hkr : (k : ℝ) ≤ α * log B / log (log B) :=
        (Nat.cast_le.2 hkK).trans hKKr
      have h := prop10_4 (m := m) (B := B) (X := X) hk2
        (fun x hx => le_floor_sq_of_pow_self_lt (by omega) hLL hkr hx)
      calc (basesWith m B k).card ≤ X * (X + 1) ^ (k - 1) := h
        _ ≤ (X + 1) * (X + 1) ^ (k - 1) := Nat.mul_le_mul_right _ (by omega)
        _ = (X + 1) ^ k := by rw [← pow_succ']; congr 1; omega
        _ ≤ (X + 1) ^ K := Nat.pow_le_pow_right (by omega) hkK
    calc (shortBases m α B).card
        ≤ (Finset.Icc 2 15).card + ((Finset.Icc 2 K).biUnion fun k => basesWith m B k).card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ 14 + ∑ k ∈ Finset.Icc 2 K, (basesWith m B k).card :=
          add_le_add (by simp) Finset.card_biUnion_le
      _ ≤ 14 + ∑ _k ∈ Finset.Icc 2 K, (X + 1) ^ K :=
          add_le_add_right (Finset.sum_le_sum hterm) _
      _ ≤ 14 + K * (X + 1) ^ K := by
          rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
          exact add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  -- the real estimate
  have hX : (X : ℝ) + 1 ≤ L ^ 2 + 1 := by
    have := Nat.floor_le (show 0 ≤ L ^ 2 by positivity); linarith
  have hlog : log (L ^ 2 + 1) ≤ 2 * LL + 1 / L ^ 2 := by
    have hL2 : 0 < L ^ 2 := by positivity
    have h1 := log_le_sub_one_of_pos (show 0 < (L ^ 2 + 1) / L ^ 2 by positivity)
    rw [log_div (by positivity) hL2.ne', log_pow] at h1
    have : (L ^ 2 + 1) / L ^ 2 - 1 = 1 / L ^ 2 := by field_simp; ring
    push_cast at h1
    linarith
  have hexp : log (L ^ 2 + 1) * Kr ≤ 2 * α * L + 1 := by
    have hKr0 : 0 ≤ Kr := by positivity
    calc log (L ^ 2 + 1) * Kr ≤ (2 * LL + 1 / L ^ 2) * Kr :=
          mul_le_mul_of_nonneg_right hlog hKr0
      _ = 2 * α * L + α / (L * LL) := by rw [hKr]; field_simp
      _ ≤ 2 * α * L + 1 := by
          have : α / (L * LL) ≤ 1 := by
            rw [div_le_one (by positivity)]; nlinarith
          linarith
  have hpow : ((X : ℝ) + 1) ^ K ≤ exp (2 * α * L) * exp 1 := by
    calc ((X : ℝ) + 1) ^ K ≤ (L ^ 2 + 1) ^ K := pow_le_pow_left₀ (by positivity) hX K
      _ = (L ^ 2 + 1) ^ (K : ℝ) := (rpow_natCast _ K).symm
      _ ≤ (L ^ 2 + 1) ^ Kr := rpow_le_rpow_of_exponent_le (by nlinarith) hKKr
      _ = exp (log (L ^ 2 + 1) * Kr) := rpow_def_of_pos (by positivity) _
      _ ≤ exp (2 * α * L + 1) := exp_le_exp.2 hexp
      _ = exp (2 * α * L) * exp 1 := exp_add _ _
  have hKL : (K : ℝ) ≤ L := by
    refine hKKr.trans ?_
    rw [hKr, div_le_iff₀ (by linarith)]
    nlinarith
  have hδL : 14 + 3 * L ≤ exp (δ * L) := by
    have h1 := quadratic_le_exp_of_nonneg (show 0 ≤ δ * L by positivity)
    have h2 : 34 ≤ δ ^ 2 * L := by
      rw [div_le_iff₀ (by positivity)] at hLδ; linarith
    nlinarith
  have he3 : exp 1 < 3 := lt_trans exp_one_lt_d9 (by norm_num)
  have hE1 : 1 ≤ exp (2 * α * L) := one_le_exp (by positivity)
  have hBpow : (B : ℝ) ^ (2 * α + δ) = exp (2 * α * L) * exp (δ * L) := by
    rw [rpow_def_of_pos (by positivity), ← exp_add, hLdef]; ring_nf
  have hcardR : ((shortBases m α B).card : ℝ) ≤ 14 + K * ((X : ℝ) + 1) ^ K := by
    exact_mod_cast hcard
  rw [hBpow]
  calc ((shortBases m α B).card : ℝ) ≤ 14 + K * ((X : ℝ) + 1) ^ K := hcardR
    _ ≤ 14 * exp (2 * α * L) + L * (exp (2 * α * L) * exp 1) := by
        have := mul_le_mul hKL hpow (by positivity) hL0.le
        linarith
    _ ≤ exp (2 * α * L) * (14 + 3 * L) := by
        have : L * (exp (2 * α * L) * exp 1) ≤ L * (exp (2 * α * L) * 3) := by gcongr
        linarith
    _ ≤ exp (2 * α * L) * exp (δ * L) := by gcongr

/-- **Theorem 11.2** (section 11.6). Let `α > 0` and `δ > 0`. For all large `B`, at most
`B^(2 α + δ)` bases `b ≤ B` have a solution with `k ≥ 2` digits and
`k ≤ α ln b / ln ln b`, under either convention. With `α = 1/2 - ε` this is the bound
`B^(1 - 2 ε + o(1))` of the library, so almost all bases have no such solution. -/
theorem theorem11_2 (m : ℕ) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ((shortBases m α B).card : ℝ) ≤ (B : ℝ) ^ (2 * α + δ) := by
  have hL : Tendsto (fun B : ℕ => log (B : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hT : Tendsto (fun B : ℕ => log (log (B : ℝ))) atTop atTop := tendsto_log_atTop.comp hL
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 ((hT.eventually_ge_atTop (max 1 α)).and
    ((hL.eventually_ge_atTop (34 / δ ^ 2)).and (eventually_ge_atTop 16)))
  exact ⟨B₀, fun B hB => shortBases_card_le hα hδ (hB₀ B hB).1 (hB₀ B hB).2.1 (hB₀ B hB).2.2⟩

end Munchausen
