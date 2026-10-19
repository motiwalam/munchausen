import Munchausen.Residues

/-!
# Short equations (chapters 15, 16, 18 and 20)

* Proposition 18.1: elementary exclusions for `b (b + x) = x^n + 1`; Proposition 16.3;
* Proposition 20.20: `(1, 2, x)` is a solution only for `x = 6`;
* Lemma 18.14: the base of a 2-digit solution is at least `M^(M-1)`.
-/

namespace Munchausen

/-! ### Squares between consecutive squares -/

/-- If `x^2 + 4 < 4 Y + 1`, then `4 Y^2 + x^2 + 4` is not a square: it lies strictly between
`(2Y)^2` and `(2Y+1)^2` (proof of Proposition 18.1 (a), (b)). -/
lemma not_sq_between {U Y x : ℕ} (hx : x ^ 2 + 4 < 4 * Y + 1) :
    U ^ 2 ≠ 4 * Y ^ 2 + x ^ 2 + 4 := by
  intro h
  rcases Nat.lt_or_ge U (2 * Y + 1) with hU | hU
  · have : U ≤ 2 * Y := by omega
    nlinarith
  · nlinarith

/-- `U = 2b + x` turns `b (b + x) = N + 1` into `U^2 = 4 N + x^2 + 4`. -/
lemma sq_of_eq {b x N : ℕ} (h : b * (b + x) = N + 1) : (2 * b + x) ^ 2 = 4 * N + x ^ 2 + 4 := by
  nlinarith

/-- **Proposition 18.1 (a)** (section 18.1.1). `b (b + x) = x^n + 1` has no solution with
`x ≥ 2` and `n ≥ 4` even. -/
theorem prop18_1_a {b x n : ℕ} (hx : 2 ≤ x) (hn : 4 ≤ n) (heven : Even n) :
    b * (b + x) ≠ x ^ n + 1 := by
  intro h
  obtain ⟨k, rfl⟩ := heven
  have hY : x ^ 2 ≤ x ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  have hsq := sq_of_eq h
  rw [show x ^ (k + k) = (x ^ k) ^ 2 by ring] at hsq
  exact not_sq_between (by nlinarith) hsq

/-- **Proposition 18.1 (b)** (section 18.1.1). No solution with `n ≥ 4` and `x ≥ 2` a square. -/
theorem prop18_1_b {b z n : ℕ} (hz : 2 ≤ z) (hn : 4 ≤ n) :
    b * (b + z ^ 2) ≠ (z ^ 2) ^ n + 1 := by
  intro h
  have hY : (z ^ 2) ^ 2 ≤ z ^ n := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hsq := sq_of_eq h
  rw [show (z ^ 2) ^ n = (z ^ n) ^ 2 by ring] at hsq
  have : 2 ≤ z ^ 2 := by nlinarith
  exact not_sq_between (by nlinarith) hsq

/-- **Proposition 18.1 (c)** (section 18.1.1). No solution with `n ≥ 2` and `x ≡ 2 (mod 4)`. -/
theorem prop18_1_c {b x n : ℕ} (hx : x % 4 = 2) (hn : 2 ≤ n) : b * (b + x) ≠ x ^ n + 1 := by
  intro h
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
  have hV : (b + y) ^ 2 = (2 * y) ^ n + 1 + y ^ 2 := by nlinarith
  have h4 : 4 ∣ (2 * y) ^ n := (pow_dvd_pow_of_dvd (dvd_mul_right 2 y) 2).trans
    (pow_dvd_pow _ hn) |> fun h => by simpa [mul_pow] using h
  have hcast := congrArg (fun k : ℕ => (k : ZMod 4)) hV
  push_cast at hcast
  have hz : ((2 * y : ℕ) : ZMod 4) ^ n = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; simpa using h4
  push_cast at hz
  rw [hz] at hcast
  have hy : (y : ZMod 4) = 1 ∨ (y : ZMod 4) = 3 := by
    rw [← ZMod.natCast_mod]
    have : y % 4 = 1 ∨ y % 4 = 3 := by omega
    rcases this with h | h <;> simp [h]
  generalize (b : ZMod 4) = B at hcast
  generalize (y : ZMod 4) = Y at hcast hy
  revert B Y
  decide

/-- **Proposition 18.1 (d)** (section 18.1.1). No solution with `n ≥ 2` and `x ≡ 4 (mod 8)`. -/
theorem prop18_1_d {b x n : ℕ} (hx : x % 8 = 4) (hn : 2 ≤ n) : b * (b + x) ≠ x ^ n + 1 := by
  intro h
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
  have hV : (b + y) ^ 2 = (2 * y) ^ n + 1 + y ^ 2 := by nlinarith
  have h8 : 8 ∣ (2 * y) ^ n := by
    have h4 : 4 ∣ 2 * y := ⟨y / 2, by omega⟩
    have : 16 ∣ (2 * y) ^ 2 := by simpa using pow_dvd_pow_of_dvd h4 2
    exact (Dvd.dvd.trans (by norm_num : 8 ∣ 16) this).trans (pow_dvd_pow _ hn)
  have hcast := congrArg (fun k : ℕ => (k : ZMod 8)) hV
  push_cast at hcast
  have hz : ((2 * y : ℕ) : ZMod 8) ^ n = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact h8
  push_cast at hz
  rw [hz] at hcast
  have hy : (y : ZMod 8) = 2 ∨ (y : ZMod 8) = 6 := by
    rw [← ZMod.natCast_mod]
    have : y % 8 = 2 ∨ y % 8 = 6 := by omega
    rcases this with h | h <;> simp [h]
  generalize (b : ZMod 8) = B at hcast
  generalize (y : ZMod 8) = Y at hcast hy
  revert B Y
  decide

/-- **Proposition 16.3** (section 16.2.1). `b (b + x) = x^x + 1` has no solution with `x ≥ 2`
even or with `x` an odd square. -/
theorem prop16_3 {b x : ℕ} (hx : 2 ≤ x) (h : Even x ∨ IsSquare x) : b * (b + x) ≠ x ^ x + 1 := by
  intro heq
  have hsq := sq_of_eq heq
  rcases h with ⟨k, rfl⟩ | ⟨z, rfl⟩
  · rw [show (k + k) ^ (k + k) = ((k + k) ^ k) ^ 2 by ring] at hsq
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      exact not_sq_between (by norm_num) hsq
    · have : (k + k) ^ 2 ≤ (k + k) ^ k := Nat.pow_le_pow_right (by omega) hk
      exact not_sq_between (by nlinarith) hsq
  · have hz : 2 ≤ z := by nlinarith
    rw [show (z * z) ^ (z * z) = (z ^ (z * z)) ^ 2 by ring] at hsq
    have : (z * z) ^ 2 ≤ z ^ (z * z) := by
      calc (z * z) ^ 2 = z ^ 4 := by ring
        _ ≤ z ^ (z * z) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    exact not_sq_between (by nlinarith) hsq

/-! ### Proposition 20.20: the family `(1, 2, x)` -/

/-- For odd `x`, `x^x ≡ x (mod 8)`. -/
lemma pow_self_modEq_eight_of_odd {x : ℕ} (hx : x % 2 = 1) : x ^ x ≡ x [MOD 8] := by
  obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  have h1 : (2 * k + 1) ^ 2 ≡ 1 [MOD 8] := by
    unfold Nat.ModEq
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [this]
    have : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
    omega
  have : (2 * k + 1) ^ (2 * k + 1) = (2 * k + 1) * ((2 * k + 1) ^ 2) ^ k := by
    rw [pow_succ', ← pow_mul]
  rw [this]
  simpa using (Nat.ModEq.refl (2 * k + 1)).mul (h1.pow k)

/-- **Proposition 20.20** (section 20.4.1). `(1, 2, x)` is a solution in some base exactly for
`x = 6`, in base 215, under either convention (`m ≤ 1`). -/
theorem prop20_20 {m x : ℕ} (hm : m ≤ 1) : (∃ b, IsSolution b m [1, 2, x]) ↔ x = 6 := by
  constructor
  · rintro ⟨b, hs⟩
    have heq := hs.eq
    simp only [P_cons, Fs_cons, Fs_nil, List.length_cons, List.length_nil, P_nil, Nat.cast_id,
      w_one] at heq
    have h2 : w m 2 = 4 := by simp [w]
    rw [h2] at heq
    -- `(b + 1)^2 + x = w(x) + 6`
    have key : (b + 1) ^ 2 + x = w m x + 6 := by norm_num at heq; nlinarith
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp at key
      rcases Nat.lt_or_ge b 2 with hb | hb
      · interval_cases b <;> omega
      · nlinarith
    rw [w_of_ne_zero m hx.ne'] at key
    rcases Nat.mod_two_eq_zero_or_one x with hpar | hpar
    · -- even `x`
      obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
      have hZ : (2 * k) ^ (2 * k) = ((2 * k) ^ k) ^ 2 := by ring
      rw [hZ] at key
      by_cases hk : 4 ≤ k
      · exfalso
        have hZx : 2 * k ≤ (2 * k) ^ k := by
          calc 2 * k = (2 * k) ^ 1 := (pow_one _).symm
            _ ≤ (2 * k) ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        set Z := (2 * k) ^ k
        rcases Nat.lt_or_ge (b + 1) Z with hc | hc
        · have : b + 1 + 1 ≤ Z := hc
          nlinarith
        · nlinarith
      · interval_cases k
        · omega
        · -- x = 2
          norm_num at key
          rcases Nat.lt_or_ge b 3 with hb | hb
          · interval_cases b <;> omega
          · nlinarith
        · -- x = 4
          norm_num at key
          rcases Nat.lt_or_ge b 16 with hb | hb
          · interval_cases b <;> omega
          · nlinarith
        · rfl
    · -- odd `x`: the right side is `6 (mod 8)`, not a square plus `x`
      exfalso
      have h8 := pow_self_modEq_eight_of_odd hpar
      unfold Nat.ModEq at h8
      have hsq : (b + 1) ^ 2 % 8 = 0 ∨ (b + 1) ^ 2 % 8 = 1 ∨ (b + 1) ^ 2 % 8 = 4 := by
        have : ∀ r < 8, r ^ 2 % 8 = 0 ∨ r ^ 2 % 8 = 1 ∨ r ^ 2 % 8 = 4 := by decide
        rw [Nat.pow_mod]; exact this _ (Nat.mod_lt _ (by norm_num))
      omega
  · rintro rfl
    refine ⟨215, ?_⟩
    have h : IsSolution 215 1 [1, 2, 6] := by decide
    exact ⟨h.1, h.2, by rw [h.3]; simp [w]⟩

/-! ### Lemma 18.14 -/

/-- **Lemma 18.14** (section 18.2). If base `b` has a 2-digit solution `(a, c)` under
`0^0 = 1` and `M = max(a, c)`, then `b ≥ M^(M-1)`. -/
theorem lemma18_14 {a b c : ℕ} (h : IsSolution b 1 [a, c]) :
    max a c ^ (max a c - 1) ≤ b := by
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (h.head_ne_zero (by simp))
  obtain ⟨hab, hcb, heq⟩ := (isSolution_two_iff ha).1 h
  have hwc := le_w' 1 c
  have haa : a ^ a = a * a ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
  rcases le_total c a with hca | hac
  · rw [max_eq_left hca]
    have : a * a ^ (a - 1) ≤ a * b := by rw [← haa, heq]; omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  · rw [max_eq_right hac]
    rcases Nat.eq_or_lt_of_le hac with rfl | hlt
    · have : a * a ^ (a - 1) ≤ a * b := by rw [← haa, heq]; omega
      exact Nat.le_of_mul_le_mul_left this (by omega)
    · -- `c > a`: `a b ≥ c^c - c` and `a ≤ c - 1`
      rw [w_one_eq_pow] at heq
      have hcc : c ^ c = c * c ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
      have h1 : c ≤ c ^ (c - 1) := by
        calc c = c ^ 1 := (pow_one c).symm
          _ ≤ c ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (c - 1) * c ^ (c - 1) ≤ c ^ c - c := by
        rw [hcc, Nat.sub_one_mul]; omega
      have h3 : c ^ c - c ≤ a * b := by omega
      have h4 : a * b ≤ (c - 1) * b := Nat.mul_le_mul_right _ (by omega)
      have h5 : (c - 1) * c ^ (c - 1) ≤ (c - 1) * b := by omega
      exact Nat.le_of_mul_le_mul_left h5 (by omega)

end Munchausen
