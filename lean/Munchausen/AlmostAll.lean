import Munchausen.Counting
import Munchausen.BaseWindow

/-!
# Almost all bases have no short solution (Theorems 11.2 and 20.3)

The finite bound `theorem11_2_finite` and an estimate of the largest digit give the
asymptotic form: for `α > 0` and `δ > 0`, the bases `b ≤ B` with a solution of `k ≥ 2` digits,
`k ≤ α ln b / ln ln b`, number at most `B^(2 α + δ)` once `B` is large. With `α = 1/2 - ε` this
is the library's `B^(1 - 2 ε + o(1))`.

Theorem 20.3 (a), (c): the multiset count of Proposition 20.2, with
`C(X + K, K) ≤ (e (X + K)/K)^K` and `X = (ln B)^2`, improves this to `B^(α + δ)`, so for
`α < 1` the bases with a solution of `2 ≤ k ≤ α ln b / ln ln b` digits have density 0.
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

/-! ### Theorem 20.3: the range of the multiset count -/

/-- `C(n, k) ≤ (e n / k)^k`, in the form `C(n, k) ≤ exp(k (1 + log(n / k)))`, for `k ≥ 1`. -/
lemma choose_le_exp {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ exp (k * (1 + log ((n : ℝ) / k))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
  have h2 : (k : ℝ) ^ k / k.factorial ≤ exp k := pow_div_factorial_le_exp (k : ℝ) hk0.le k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h3 : (n : ℝ) ^ k / k.factorial ≤ ((n : ℝ) / k) ^ k * exp k := by
    rw [div_pow, div_le_iff₀ hf]
    rw [div_le_iff₀ hf] at h2
    have hkk : (0 : ℝ) < (k : ℝ) ^ k := by positivity
    calc (n : ℝ) ^ k = (n : ℝ) ^ k / (k : ℝ) ^ k * (k : ℝ) ^ k := by field_simp
      _ ≤ (n : ℝ) ^ k / (k : ℝ) ^ k * (exp k * k.factorial) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have h4 : ((n : ℝ) / k) ^ k * exp k = exp (k * (1 + log ((n : ℝ) / k))) := by
    rw [mul_add, mul_one, exp_add, ← log_rpow (by positivity), exp_log (by positivity),
      rpow_natCast, mul_comm]
  linarith

/-- **Theorem 20.3** (a), for one large `B` (section 20.1.3). Let `L = ln B`, `LL = ln L`,
`α, δ > 0`, and suppose `ln ln B ≥ max 1 α`, `α L / LL ≥ 2`,
`α (1 + log(1 + 2 LL/α)) ≤ (δ/2) LL` and `14 + L ((L^2 + 1)(1 + L) + L) ≤ e^(δ L / 2)`. Then at
most `B^(α + δ)` bases `b ≤ B` have a solution of `k ≥ 2` digits with
`k ≤ α ln b / ln ln b`. The proof is the multiset count of Proposition 20.2 with `X = L^2` and
`C(X + K, K) ≤ (e (X + K)/K)^K`. -/
lemma shortBases_card_le_multiset {m B : ℕ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hB : 16 ≤ B)
    (hLL : max 1 α ≤ log (log (B : ℝ))) (hKr2 : 2 ≤ α * log B / log (log B))
    (hc1 : α * (1 + log (1 + 2 * log (log (B : ℝ)) / α)) ≤ δ / 2 * log (log (B : ℝ)))
    (hc2 : 14 + log (B : ℝ) * ((log (B : ℝ) ^ 2 + 1) * (1 + log B) + log B) ≤
      exp (δ / 2 * log B)) :
    ((shortBases m α B).card : ℝ) ≤ (B : ℝ) ^ (α + δ) := by
  classical
  set L := log (B : ℝ) with hLdef
  set LL := log L with hLLdef
  have hLL1 : 1 ≤ LL := (le_max_left _ _).trans hLL
  have hL0 : 0 < L := log_pos (by exact_mod_cast (show 1 < B by omega))
  have hL1 : 1 ≤ L := by
    have := exp_one_le_log hB
    have := add_one_le_exp 1
    linarith
  set Kr := α * L / LL with hKr
  set K := ⌊Kr⌋₊
  set X := ⌊L ^ 2⌋₊
  have hKKr : (K : ℝ) ≤ Kr := Nat.floor_le (by positivity)
  have hK2 : 2 ≤ K := Nat.le_floor (by exact_mod_cast hKr2)
  have hKr_le : Kr ≤ 2 * K := by
    have := Nat.lt_floor_add_one Kr
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK2
    linarith
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
  -- sizes
  have hXL : (X : ℝ) ≤ L ^ 2 := Nat.floor_le (by positivity)
  have hKL : (K : ℝ) ≤ L := by
    refine hKKr.trans ?_
    rw [hKr, div_le_iff₀ (by linarith)]
    nlinarith [(le_max_right 1 α).trans hLL]
  have hK0 : (0 : ℝ) < K := by
    have : (2 : ℝ) ≤ K := by exact_mod_cast hK2
    linarith
  -- the window factor
  set W : ℝ := (L ^ 2 + 1) * (1 + L) + L with hW
  have hHK : (harmonic K : ℝ) ≤ 1 + L := by
    have h1 := harmonic_le_one_add_log K
    have h2 : log (K : ℝ) ≤ L := (log_le_sub_one_of_pos hK0).trans (by linarith)
    linarith
  -- the binomial
  set Cb := (X + K).choose K
  have hCb : (Cb : ℝ) ≤ exp ((α + δ / 2) * L) := by
    have h1 := choose_le_exp (n := X + K) (k := K) (by omega) (by omega)
    refine h1.trans (exp_le_exp.2 ?_)
    have hratio : ((X + K : ℕ) : ℝ) / K ≤ L * (1 + 2 * LL / α) := by
      rw [div_le_iff₀ hK0]
      push_cast
      have hLLα : 0 < α := hα
      -- `X ≤ L^2 = Kr L LL / α ≤ 2 K L LL / α`
      have e1 : L ^ 2 = Kr * (L * LL / α) := by rw [hKr]; field_simp
      have h3 : (X : ℝ) ≤ K * (2 * L * LL / α) := by
        calc (X : ℝ) ≤ L ^ 2 := hXL
          _ = Kr * (L * LL / α) := e1
          _ ≤ (2 * K) * (L * LL / α) := mul_le_mul_of_nonneg_right hKr_le (by positivity)
          _ = K * (2 * L * LL / α) := by ring
      have h4 : (K : ℝ) ≤ K * L := le_mul_of_one_le_right hK0.le hL1
      have : L * (1 + 2 * LL / α) * K = K * L + K * (2 * L * LL / α) := by ring
      linarith
    have hlog : log (((X + K : ℕ) : ℝ) / K) ≤ LL + log (1 + 2 * LL / α) := by
      have hpos : 0 < ((X + K : ℕ) : ℝ) / K := by
        apply div_pos _ hK0; exact_mod_cast (show 0 < X + K by omega)
      calc log (((X + K : ℕ) : ℝ) / K) ≤ log (L * (1 + 2 * LL / α)) := log_le_log hpos hratio
        _ = LL + log (1 + 2 * LL / α) := by rw [log_mul hL0.ne' (by positivity)]
    have hlog0 : 0 ≤ 1 + LL + log (1 + 2 * LL / α) := by
      have h2 : 0 ≤ 2 * LL / α := by positivity
      have : 0 ≤ log (1 + 2 * LL / α) := log_nonneg (by linarith)
      linarith
    calc (K : ℝ) * (1 + log (((X + K : ℕ) : ℝ) / K))
        ≤ K * (1 + LL + log (1 + 2 * LL / α)) := by
          apply mul_le_mul_of_nonneg_left _ hK0.le; linarith
      _ ≤ Kr * (1 + LL + log (1 + 2 * LL / α)) := mul_le_mul_of_nonneg_right hKKr hlog0
      _ = α * L + L / LL * (α * (1 + log (1 + 2 * LL / α))) := by
          rw [hKr]; field_simp; ring
      _ ≤ α * L + L / LL * (δ / 2 * LL) := by
          gcongr
      _ = (α + δ / 2) * L := by field_simp
  -- each length
  have hterm : ∀ k ∈ Finset.Icc 2 K, ((basesWith m B k).card : ℝ) ≤ Cb * W := by
    intro k hk
    obtain ⟨hk2, hkK⟩ := Finset.mem_Icc.1 hk
    have hkr : (k : ℝ) ≤ α * log B / log (log B) := (Nat.cast_le.2 hkK).trans hKKr
    have h := prop20_2 (m := m) (B := B) (X := X) hk2
      (fun x hx => le_floor_sq_of_pow_self_lt (by omega) hLL hkr hx)
    have hch : (X + k).choose k ≤ Cb := by
      show (X + k).choose k ≤ (X + K).choose K
      rw [← Nat.choose_symm_add, ← Nat.choose_symm_add]
      exact Nat.choose_le_choose X (by omega)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      linarith
    have hwin : ((X : ℝ) + 1) * (harmonic k : ℝ) / (k - 1) + k ≤ W := by
      have hHk : (harmonic k : ℝ) ≤ 1 + L := (harmonic_le_harmonic hkK).trans hHK
      have hH0 : (0 : ℝ) ≤ harmonic k := by exact_mod_cast (harmonic_pos (by omega)).le
      have h1 : ((X : ℝ) + 1) * (harmonic k : ℝ) / (k - 1) ≤ ((X : ℝ) + 1) * harmonic k :=
        div_le_self (by positivity) hk1
      have h2 : ((X : ℝ) + 1) * harmonic k ≤ (L ^ 2 + 1) * (1 + L) :=
        mul_le_mul (by linarith) hHk hH0 (by positivity)
      have h3 : (k : ℝ) ≤ L := (Nat.cast_le.2 hkK).trans hKL
      rw [hW]; linarith
    calc ((basesWith m B k).card : ℝ)
        ≤ (X + k).choose k * ((X + 1) * (harmonic k : ℝ) / (k - 1) + k) := h
      _ ≤ Cb * W := by
          have hH0 : (0 : ℝ) ≤ harmonic k := by exact_mod_cast (harmonic_pos (by omega)).le
          have : (0 : ℝ) ≤ ((X : ℝ) + 1) * (harmonic k : ℝ) / (k - 1) :=
            div_nonneg (by positivity) (by linarith)
          apply mul_le_mul (by exact_mod_cast hch) hwin (by positivity) (by positivity)
  have hcard : ((shortBases m α B).card : ℝ) ≤ 14 + L * (Cb * W) := by
    have h1 : (shortBases m α B).card ≤ 14 +
        ∑ k ∈ Finset.Icc 2 K, (basesWith m B k).card := by
      calc (shortBases m α B).card
          ≤ (Finset.Icc 2 15).card + ((Finset.Icc 2 K).biUnion fun k => basesWith m B k).card :=
            (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        _ ≤ 14 + ∑ k ∈ Finset.Icc 2 K, (basesWith m B k).card :=
            add_le_add (by simp) Finset.card_biUnion_le
    have h2 : (∑ k ∈ Finset.Icc 2 K, ((basesWith m B k).card : ℝ)) ≤ K * (Cb * W) := by
      calc (∑ k ∈ Finset.Icc 2 K, ((basesWith m B k).card : ℝ))
          ≤ ∑ _k ∈ Finset.Icc 2 K, (Cb * W : ℝ) := Finset.sum_le_sum hterm
        _ = ((Finset.Icc 2 K).card : ℝ) * (Cb * W) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ K * (Cb * W) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Nat.card_Icc]; exact_mod_cast (show K + 1 - 2 ≤ K by omega)
    have h1' : ((shortBases m α B).card : ℝ) ≤
        14 + ∑ k ∈ Finset.Icc 2 K, ((basesWith m B k).card : ℝ) := by exact_mod_cast h1
    have h3 : (K : ℝ) * (Cb * W) ≤ L * (Cb * W) :=
      mul_le_mul_of_nonneg_right hKL (by positivity)
    linarith
  have hE : 1 ≤ exp ((α + δ / 2) * L) := one_le_exp (by positivity)
  have hBpow : (B : ℝ) ^ (α + δ) = exp ((α + δ / 2) * L) * exp (δ / 2 * L) := by
    rw [rpow_def_of_pos (by positivity), ← exp_add, hLdef]; ring_nf
  rw [hBpow]
  calc ((shortBases m α B).card : ℝ) ≤ 14 + L * (Cb * W) := hcard
    _ ≤ 14 * exp ((α + δ / 2) * L) + L * (exp ((α + δ / 2) * L) * W) := by
        have : L * (Cb * W) ≤ L * (exp ((α + δ / 2) * L) * W) := by
          apply mul_le_mul_of_nonneg_left _ hL0.le
          exact mul_le_mul_of_nonneg_right hCb (by positivity)
        linarith
    _ = exp ((α + δ / 2) * L) * (14 + L * W) := by ring
    _ ≤ exp ((α + δ / 2) * L) * exp (δ / 2 * L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hW]; exact hc2

/-- `α (1 + log(1 + 2 t/α)) ≤ (δ/2) t` for all large `t`. -/
lemma eventually_log_cond {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, α * (1 + log (1 + 2 * t / α)) ≤ δ / 2 * t := by
  have hb := (isLittleO_log_id_atTop.bound (show 0 < δ / (4 * α) by positivity))
  filter_upwards [hb, eventually_ge_atTop 1,
    eventually_ge_atTop (4 * α * (1 + log (1 + 2 / α)) / δ)] with t h1 ht1 ht2
  have ht0 : 0 < t := by linarith
  have hlogt : log t ≤ δ / (4 * α) * t := by
    simp only [norm_eq_abs, id] at h1
    calc log t ≤ |log t| := le_abs_self _
      _ ≤ δ / (4 * α) * |t| := h1
      _ = δ / (4 * α) * t := by rw [abs_of_pos ht0]
  have hsplit : log (1 + 2 * t / α) ≤ log (1 + 2 / α) + log t := by
    rw [← log_mul (by positivity) ht0.ne']
    apply log_le_log (by positivity)
    have : 2 * t / α = 2 / α * t := by ring
    rw [this]; nlinarith [show 0 < 2 / α by positivity]
  have h3 : 4 * α * (1 + log (1 + 2 / α)) ≤ δ * t := by
    rw [div_le_iff₀ hδ] at ht2; linarith
  have h4 : α * log t ≤ δ / 4 * t := by
    have := mul_le_mul_of_nonneg_left hlogt hα.le
    calc α * log t ≤ α * (δ / (4 * α) * t) := this
      _ = δ / 4 * t := by field_simp
  nlinarith

/-- `14 + L ((L^2 + 1)(1 + L) + L) ≤ e^(δ L / 2)` for all large `L`. -/
lemma eventually_poly_le_exp {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, 14 + L * ((L ^ 2 + 1) * (1 + L) + L) ≤ exp (δ / 2 * L) := by
  have ht := tendsto_pow_mul_exp_neg_atTop_nhds_zero 4
  have hlin : Tendsto (fun L : ℝ => δ / 2 * L) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  have hc : 0 < (δ / 2) ^ 4 / 20 := by positivity
  have h1 := (ht.comp hlin).eventually (gt_mem_nhds hc)
  filter_upwards [h1, eventually_ge_atTop 1] with L hL hL1
  simp only [Function.comp_apply] at hL
  have hp : 14 + L * ((L ^ 2 + 1) * (1 + L) + L) ≤ 20 * L ^ 4 := by
    have a1 : 1 ≤ L ^ 2 := by nlinarith
    have a2 : L ≤ L ^ 2 := by nlinarith
    have a3 : L ^ 2 ≤ L ^ 3 := by nlinarith
    have a4 : L ^ 3 ≤ L ^ 4 := by nlinarith
    nlinarith
  have hE := exp_pos (δ / 2 * L)
  have : (δ / 2 * L) ^ 4 < (δ / 2) ^ 4 / 20 * exp (δ / 2 * L) := by
    have := (mul_lt_mul_iff_of_pos_right hE).2 hL
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one] at this
  have e : (δ / 2 * L) ^ 4 = (δ / 2) ^ 4 * L ^ 4 := by ring
  rw [e] at this
  have hd4 : 0 < (δ / 2) ^ 4 := by positivity
  have : L ^ 4 < exp (δ / 2 * L) / 20 := by
    have h' : (δ / 2) ^ 4 * L ^ 4 < (δ / 2) ^ 4 * (exp (δ / 2 * L) / 20) := by
      calc (δ / 2) ^ 4 * L ^ 4 < (δ / 2) ^ 4 / 20 * exp (δ / 2 * L) := this
        _ = (δ / 2) ^ 4 * (exp (δ / 2 * L) / 20) := by ring
    exact lt_of_mul_lt_mul_left h' hd4.le
  linarith

/-- **Theorem 20.3** (a) and (c) (section 20.1.3). Let `α > 0` and `δ > 0`. For all large `B`, at
most `B^(α + δ)` bases `b ≤ B` have a solution with `k ≥ 2` digits and
`k ≤ α ln b / ln ln b`, under either convention. So for `α < 1` almost all bases have no such
solution (`shortBases_density_zero`): the range `k ≤ (1 - ε) ln b / ln ln b`, twice the range
of Theorem 11.2. -/
theorem theorem20_3 (m : ℕ) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, ((shortBases m α B).card : ℝ) ≤ (B : ℝ) ^ (α + δ) := by
  have hL : Tendsto (fun B : ℕ => log (B : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hT : Tendsto (fun B : ℕ => log (log (B : ℝ))) atTop atTop := tendsto_log_atTop.comp hL
  -- `α L / ln L → ∞`
  have hKr : Tendsto (fun B : ℕ => α * log (B : ℝ) / log (log (B : ℝ))) atTop atTop := by
    have h1 : Tendsto (fun t : ℝ => t / log t) atTop atTop := by
      refine tendsto_atTop.2 fun M => ?_
      have hb := isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / (|M| + 1) by positivity)
      filter_upwards [hb, eventually_gt_atTop (exp 1)] with t h1 ht
      have ht0 : 0 < t := (exp_pos 1).trans ht
      have hlog : 1 < log t := by rw [lt_log_iff_exp_lt ht0]; exact ht
      simp only [norm_eq_abs, id, abs_of_pos ht0, abs_of_pos (by linarith : (0 : ℝ) < log t)]
        at h1
      rw [le_div_iff₀ (by linarith)]
      have : log t * (|M| + 1) ≤ t := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h1; linarith
      nlinarith [le_abs_self M]
    have h2 := (h1.comp hL).const_mul_atTop hα
    refine h2.congr fun B => ?_
    simp only [Function.comp_apply]; ring
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 ((hT.eventually_ge_atTop (max 1 α)).and
    ((hKr.eventually_ge_atTop 2).and ((hT.eventually (eventually_log_cond hα hδ)).and
      ((hL.eventually (eventually_poly_le_exp hδ)).and (eventually_ge_atTop 16)))))
  exact ⟨B₀, fun B hB => shortBases_card_le_multiset hα hδ (hB₀ B hB).2.2.2.2 (hB₀ B hB).1
    (hB₀ B hB).2.1 (hB₀ B hB).2.2.1 (hB₀ B hB).2.2.2.1⟩

/-- **Theorem 20.3** (c): for `α < 1`, the share of bases `b ≤ B` with a solution of
`2 ≤ k ≤ α ln b / ln ln b` digits tends to 0. -/
theorem shortBases_density_zero (m : ℕ) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun B : ℕ => ((shortBases m α B).card : ℝ) / B) atTop (nhds 0) := by
  set δ := (1 - α) / 2 with hδ
  have hδ0 : 0 < δ := by linarith
  obtain ⟨B₀, hB₀⟩ := theorem20_3 m hα hδ0
  have hlim : Tendsto (fun B : ℕ => (B : ℝ) ^ (α + δ - 1)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show 0 < 1 - (α + δ) by linarith)).comp
      tendsto_natCast_atTop_atTop |>.congr' (by
        filter_upwards with B
        simp only [Function.comp_apply, neg_sub])
  refine squeeze_zero' (Eventually.of_forall fun B => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop (max B₀ 1)] with B hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (le_max_right _ _).trans hB
  have hB0 : (0 : ℝ) < B := by linarith
  rw [div_le_iff₀ hB0]
  calc ((shortBases m α B).card : ℝ) ≤ (B : ℝ) ^ (α + δ) := hB₀ B ((le_max_left _ _).trans hB)
    _ = (B : ℝ) ^ (α + δ - 1) * B := by
        rw [rpow_sub hB0, rpow_one, div_mul_cancel₀ _ hB0.ne']

end Munchausen
