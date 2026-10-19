import Munchausen.Residues

/-!
# Short equations (chapters 15, 16, 18 and 20)

* Proposition 18.1: elementary exclusions for `b (b + x) = x^n + 1`; Proposition 16.5;
* Proposition 20.20: `(1, 2, x)` is a solution only for `x = 6`;
* Lemma 18.14: the base of a 2-digit solution is at least `M^(M-1)`;
* Theorem 15.7: under `0^0 = 1`, only base 3 has two 2-digit solutions.
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

/-- **Proposition 16.5** (section 16.2.1). `b (b + x) = x^x + 1` has no solution with `x ≥ 2`
even or with `x` an odd square. -/
theorem prop16_5 {b x : ℕ} (hx : 2 ≤ x) (h : Even x ∨ IsSquare x) :
    b * (b + x) ≠ x ^ x + 1 := by
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

/-! ### Theorem 15.7: bases with two 2-digit solutions -/

/-- `g(x) = w(x) - x` under `0^0 = 1`, as an integer (chapter 15). -/
def G (x : ℕ) : ℤ := (x : ℤ) ^ x - x

lemma G_zero : G 0 = 1 := by simp [G]
lemma G_one : G 1 = 0 := by simp [G]
lemma G_two : G 2 = 2 := by norm_num [G]

lemma w_one_sub (x : ℕ) : ((w 1 x : ℕ) : ℤ) - x = G x := by
  rw [w_one_eq_pow, G]; push_cast; ring

/-- `y * x^x ≤ y^y` for `1 ≤ x < y`. -/
lemma mul_pow_self_le {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) : y * x ^ x ≤ y ^ y := by
  have h1 : x ^ x ≤ y ^ x := Nat.pow_le_pow_left hxy.le x
  have h2 : y ^ x ≤ y ^ (y - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : y ^ y = y * y ^ (y - 1) := by rw [← pow_succ']; congr 1; omega
  rw [h3]
  exact Nat.mul_le_mul_left _ (h1.trans h2)

lemma G_lt {x y : ℕ} (hx : 1 ≤ x) (hxy : x < y) : G x < G y := by
  have h := mul_pow_self_le hx hxy
  have h1 : 1 ≤ x ^ x := Nat.one_le_pow _ _ hx
  unfold G
  have h' : (y : ℤ) * (x : ℤ) ^ x ≤ (y : ℤ) ^ y := by exact_mod_cast h
  have h1' : (1 : ℤ) ≤ (x : ℤ) ^ x := by exact_mod_cast h1
  rcases Nat.eq_or_lt_of_le hx with rfl | hx2
  · have : (y : ℤ) < (y : ℤ) ^ y := by
      have : y < y ^ y := by
        calc y < y ^ 2 := by nlinarith
          _ ≤ y ^ y := Nat.pow_le_pow_right (by omega) (by omega)
      exact_mod_cast this
    simp; linarith
  · have hx2' : (2 : ℤ) ≤ x := by exact_mod_cast hx2
    have hxy' : (x : ℤ) < y := by exact_mod_cast hxy
    nlinarith

lemma G_le {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) : G x ≤ G y := by
  rcases Nat.eq_or_lt_of_le hxy with rfl | h
  · rfl
  · exact (G_lt hx h).le

lemma G_nonneg (x : ℕ) : 0 ≤ G x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [G_zero]
  · have := G_le (le_refl 1) hx; rw [G_one] at this; exact this

lemma G_ge_two {x : ℕ} (hx : 2 ≤ x) : 2 ≤ G x := by
  have := G_le (by norm_num : 1 ≤ 2) hx; rwa [G_two] at this

lemma G_injective {x y : ℕ} (h : G x = G y) : x = y := by
  rcases Nat.lt_trichotomy x y with hlt | heq | hgt
  · exfalso
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [G_zero] at h
      rcases Nat.lt_or_ge y 2 with hy | hy
      · interval_cases y; simp [G_one] at h
      · have := G_ge_two hy; omega
    · have := G_lt hx hlt; omega
  · exact heq
  · exfalso
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · rw [G_zero] at h
      rcases Nat.lt_or_ge x 2 with hx | hx
      · interval_cases x; simp [G_one] at h
      · have := G_ge_two hx; omega
    · have := G_lt hy hgt; omega

/-- `(c+1)^c ≥ 2 c^c` for `c ≥ 1` (Bernoulli). -/
lemma two_mul_pow_le (c : ℕ) (hc : 1 ≤ c) : 2 * c ^ c ≤ (c + 1) ^ c := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hpos : (0 : ℝ) ≤ 1 / c := by positivity
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / c by linarith) c
  have e : (1 : ℝ) + c * (1 / c) = 2 := by field_simp; ring
  rw [e] at hb
  have h2 : ((c : ℝ) + 1) ^ c = (c : ℝ) ^ c * (1 + 1 / c) ^ c := by
    rw [← mul_pow]; congr 1; field_simp
  have : (2 : ℝ) * (c : ℝ) ^ c ≤ ((c : ℝ) + 1) ^ c := by
    rw [h2]; nlinarith [pow_pos hcR c]
  exact_mod_cast this

/-- Step 2 of Theorem 15.7: `g(c+1) ≥ 2 (c+1) g(c)` for `c ≥ 2`. -/
lemma G_succ_ge {c : ℕ} (hc : 2 ≤ c) : 2 * (c + 1) * G c ≤ G (c + 1) := by
  have h := two_mul_pow_le c (by omega)
  have h' : (2 : ℤ) * (c : ℤ) ^ c ≤ ((c : ℤ) + 1) ^ c := by exact_mod_cast h
  unfold G
  push_cast
  have e : ((c : ℤ) + 1) ^ (c + 1) = ((c : ℤ) + 1) * ((c : ℤ) + 1) ^ c := by ring
  rw [e]
  have hc' : (2 : ℤ) ≤ c := by exact_mod_cast hc
  nlinarith

/-- `A^(A-1)` written as `PA`, with `A^A = A * PA`. -/
lemma pow_self_eq (A : ℕ) (hA : 1 ≤ A) : ((A : ℤ)) ^ A = A * (A : ℤ) ^ (A - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- The two equations of a 2-digit solution under `0^0 = 1`, in `ℤ` (Proposition 2.6). -/
lemma two_digit_eq {a c b : ℕ} (h : IsSolution b 1 [a, c]) :
    1 ≤ a ∧ a < b ∧ c < b ∧ (a : ℤ) * b = (a : ℤ) ^ a + G c := by
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (h.head_ne_zero (by simp))
  obtain ⟨h1, h2, h3⟩ := (isSolution_two_iff ha).1 h
  refine ⟨ha, h1, h2, ?_⟩
  have hc := le_w' 1 c
  rw [← w_one_sub]
  have : ((a * b : ℕ) : ℤ) = ((a ^ a + (w 1 c - c) : ℕ) : ℤ) := by rw [h3]
  push_cast [Nat.cast_sub hc] at this
  linarith

/-- Step 3 of Theorem 15.7, the arithmetic part. -/
lemma step3_ineq {A a PA pa u Gc GC : ℤ} (ha : 1 ≤ a) (haA : a + 1 ≤ A) (hu : 0 ≤ u)
    (hpa : 1 ≤ pa) (hK : 0 ≤ a * PA - a * pa) (e3 : Gc = a * PA - a * pa + a * u)
    (e4 : GC = A * u) (hle : GC ≤ Gc) : Gc < (A - 1) * (A * PA) := by
  set K := a * PA - a * pa with hKdef
  have h1 : (A - a) * u ≤ K := by rw [sub_mul]; linarith
  have h2 : u ≤ (A - a) * u := le_mul_of_one_le_left hu (by linarith)
  have h3 : a * u ≤ (A - 1) * K := mul_le_mul (by linarith) (by linarith) hu (by linarith)
  have h4 : Gc ≤ A * K := by
    have : A * K = K + (A - 1) * K := by ring
    linarith
  have h5 : A * K < A * (a * PA) := by
    have : 0 < A * (a * pa) := mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
    have : A * K = A * (a * PA) - A * (a * pa) := by rw [hKdef]; ring
    linarith
  have h6 : A * (a * PA) ≤ (A - 1) * (A * PA) := by
    have hPA : 0 ≤ PA := by nlinarith
    have : A * (a * PA) = a * (A * PA) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (by linarith) hPA)
  linarith

lemma step4_one {c PA GC : ℤ} (hc : 2 ≤ c) (hPA : 2 ≤ PA)
    (key : GC = c * PA * (c - 1) + c - c * c) (hle : GC ≤ c * PA - c) : c = 2 := by
  have h1 : c * ((c - 2) * (PA - 1)) ≤ 0 := by nlinarith
  have h2 : (c - 2) * (PA - 1) ≤ 0 := by
    by_contra h; replace h := not_le.1 h; nlinarith
  nlinarith

lemma step4_big {a c PA ap GC : ℤ} (ha : 2 ≤ a) (hca : 2 * a ≤ c) (hcPA : c ≤ PA)
    (hap : 2 * a ≤ ap) (key : a * GC = c * PA * (c - a) + c * ap - c * c)
    (hle : GC ≤ c * PA - c) : False := by
  have h1 : a * GC ≤ a * (c * PA - c) := mul_le_mul_of_nonneg_left hle (by linarith)
  have h2 : 0 < c * (c * PA - c) := by nlinarith
  nlinarith

lemma step4_gt {a c PA ap GC : ℤ} (ha : 2 ≤ a) (hac : a + 1 ≤ c) (hc2a : c + 1 ≤ 2 * a)
    (hPA : 0 ≤ PA) (hap : 2 * a ≤ ap) (key : a * GC = c * PA * (c - a) + c * ap - c * c) :
    PA < GC := by
  have h1 : (a + 1) * PA ≤ c * PA * (c - a) := by
    have : c * PA ≤ c * PA * (c - a) := le_mul_of_one_le_right (by nlinarith) (by linarith)
    nlinarith
  have h2 : 0 < c * ap - c * c := by nlinarith
  nlinarith

lemma step4_mid {a c PA ap : ℤ} (hac : a + 1 ≤ c) (hc2a : c + 1 ≤ 2 * a) (hc : 0 < c)
    (hPA : ap ≤ PA) (hap0 : 0 ≤ ap)
    (key : a * (c * PA - c) = c * PA * (c - a) + c * ap - c * c) : False := by
  have h1 : c * (PA * (2 * a - c)) = c * (ap + a - c) := by linarith
  have h2 : PA * (2 * a - c) = ap + a - c := mul_left_cancel₀ hc.ne' h1
  have h3 : PA ≤ PA * (2 * a - c) := le_mul_of_one_le_right (by linarith) (by linarith)
  linarith

/-- The core of **Theorem 15.7**: two 2-digit solutions `(a, c)` and `(A, C)` with `a < A` in
one base, under `0^0 = 1`, are `(1, 2)` and `(2, 2)` in base 3. -/
theorem two_two_digit {a c A C b : ℕ} (h1 : IsSolution b 1 [a, c]) (h2 : IsSolution b 1 [A, C])
    (haA : a < A) : a = 1 ∧ c = 2 ∧ A = 2 ∧ C = 2 ∧ b = 3 := by
  obtain ⟨ha, hab, hcb, e1⟩ := two_digit_eq h1
  obtain ⟨hA, hAb, hCb, e2⟩ := two_digit_eq h2
  have hGc := G_nonneg c
  have hGC := G_nonneg C
  -- powers
  set PA : ℤ := (A : ℤ) ^ (A - 1) with hPA
  set pa : ℤ := (a : ℤ) ^ (a - 1) with hpa
  have hAA := pow_self_eq A hA
  have haa := pow_self_eq a ha
  rw [← hPA] at hAA
  rw [← hpa] at haa
  have hpaPA : pa < PA := by
    have h1 : a ^ (a - 1) ≤ a ^ (A - 1) := Nat.pow_le_pow_right ha (by omega)
    have h2 : a ^ (A - 1) < A ^ (A - 1) := Nat.pow_lt_pow_left haA (by omega)
    rw [hpa, hPA]; exact_mod_cast h1.trans_lt h2
  have hpa1 : 1 ≤ pa := by rw [hpa]; exact_mod_cast Nat.one_le_pow _ _ ha
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have haA' : (a : ℤ) + 1 ≤ A := by exact_mod_cast haA
  -- `b ≥ PA`, `u = b - PA`
  have hbPA : PA ≤ b := by
    rw [hAA] at e2
    have : (A : ℤ) * PA ≤ A * b := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  set u : ℤ := (b : ℤ) - PA with hu
  have hu0 : 0 ≤ u := by linarith
  have e3 : G c = a * PA - a * pa + a * u := by rw [hu]; rw [haa] at e1; linarith
  have e4 : G C = A * u := by rw [hu]; rw [hAA] at e2; linarith
  -- Step 1: `c ≥ A`
  have step1 : A ≤ c := by
    by_contra hcA
    replace hcA := not_le.1 hcA
    rcases Nat.lt_or_ge A 3 with hA3 | hA3
    · -- `A = 2`, `a = 1`
      have hA2 : A = 2 := by omega
      have ha1 : a = 1 := by omega
      subst hA2 ha1
      have hb3 : (3 : ℤ) ≤ b := by exact_mod_cast hAb
      have hP : PA = 2 := by rw [hPA]; norm_num
      have hp : pa = 1 := by rw [hpa]; norm_num
      have : 2 ≤ G c := by rw [e3, hP, hp, hu, hP]; push_cast; linarith
      interval_cases c <;> simp [G_zero, G_one] at this
    · -- `A ≥ 3`: `g(c) ≥ A^(A-1) - (A-1)^(A-2) > g(A-1)`
      obtain ⟨q, rfl⟩ : ∃ q, A = q + 1 := ⟨A - 1, by omega⟩
      have hq : 2 ≤ q := by omega
      have hP1 : pa ≤ (q : ℤ) ^ (q - 1) := by
        have h1 : a ^ (a - 1) ≤ q ^ (a - 1) := Nat.pow_le_pow_left (by omega) _
        have h2 : q ^ (a - 1) ≤ q ^ (q - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [hpa]; exact_mod_cast h1.trans h2
      have hP2 : (q : ℤ) ^ q + (q : ℤ) ^ (q - 1) ≤ PA := by
        have h1 : q ^ (q - 1) ≤ (q + 1) ^ (q - 1) := Nat.pow_le_pow_left (by omega) _
        have e : (q : ℤ) ^ q = q * (q : ℤ) ^ (q - 1) := pow_self_eq q (by omega)
        have e' : PA = ((q : ℤ) + 1) * ((q : ℤ) + 1) ^ (q - 1) := by
          rw [hPA]; push_cast
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q)]
        have h1' : (q : ℤ) ^ (q - 1) ≤ ((q : ℤ) + 1) ^ (q - 1) := by exact_mod_cast h1
        rw [e, e']; nlinarith
      have hGq : G q = (q : ℤ) ^ q - q := rfl
      have hlow : (q : ℤ) ^ q ≤ G c := by nlinarith
      have hGle : G c ≤ G q := by
        rcases Nat.eq_zero_or_pos c with rfl | hc
        · rw [G_zero]; have := G_ge_two hq; linarith
        · exact G_le hc (by omega)
      have : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
      linarith
  have hc2 : 2 ≤ c := by omega
  have hGc2 := G_ge_two hc2
  have hAZ : (2 : ℤ) ≤ A := by exact_mod_cast (show 2 ≤ A by omega)
  have hcZ : (A : ℤ) ≤ c := by exact_mod_cast step1
  have hK : 0 < (a : ℤ) * PA - a * pa := by nlinarith
  -- Step 2: `C ≤ c`
  have step2 : C ≤ c := by
    by_contra hCc
    replace hCc := not_le.1 hCc
    have h1 : G (c + 1) ≤ G C := G_le (by omega) hCc
    have h2 := G_succ_ge hc2
    rcases eq_or_lt_of_le hu0 with hu0' | hupos
    · -- `u = 0` gives `g(C) = 0`, so `C = 1`
      rw [← hu0', mul_zero] at e4
      have : C = 1 := G_injective (by rw [e4, G_one])
      omega
    · have h3 : (a : ℤ) * u < G c := by linarith
      have h4 : (2 : ℤ) * (c + 1) * (a * u) < A * u := by
        calc (2 : ℤ) * (c + 1) * (a * u) < 2 * (c + 1) * G c := by
              have : (0 : ℤ) < 2 * (c + 1) := by positivity
              exact mul_lt_mul_of_pos_left h3 this
          _ ≤ G (c + 1) := by exact_mod_cast h2
          _ ≤ G C := h1
          _ = A * u := e4
      have h5 : (2 : ℤ) * (c + 1) * a < A := lt_of_mul_lt_mul_right (by nlinarith) hupos.le
      nlinarith
  -- Step 3: `c ≤ A`
  have step3 : c ≤ A := by
    by_contra hcA
    replace hcA := not_le.1 hcA
    have hGCc : G C ≤ G c := by
      rcases Nat.eq_zero_or_pos C with hC0 | hC
      · rw [hC0, G_zero]; linarith
      · exact G_le hC step2
    have hlt : G c < (A - 1) * (A * PA) :=
      step3_ineq ha' haA' hu0 hpa1 hK.le e3 e4 hGCc
    have hmono : G (A + 1) ≤ G c := G_le (by omega) hcA
    have hpow : (A + 1) * A ^ A ≤ (A + 1) ^ (A + 1) := mul_pow_self_le hA (by omega)
    have hpow' : ((A : ℤ) + 1) * (A * PA) ≤ ((A : ℤ) + 1) ^ (A + 1) := by
      rw [← hAA]; exact_mod_cast hpow
    have hGA1 : G (A + 1) = ((A : ℤ) + 1) ^ (A + 1) - (A + 1) := by simp [G]
    have hPA2 : (2 : ℤ) ≤ PA := by
      rw [hPA]
      have : 2 ≤ A ^ (A - 1) :=
        (show 2 ≤ A by omega).trans (by
          calc A = A ^ 1 := (pow_one A).symm
            _ ≤ A ^ (A - 1) := Nat.pow_le_pow_right (by omega) (by omega))
      exact_mod_cast this
    have hX : (2 : ℤ) * A ≤ A * PA := by
      have := mul_le_mul_of_nonneg_left hPA2 (show (0 : ℤ) ≤ A by linarith)
      linarith
    have e : ((A : ℤ) + 1) * (A * PA) = (A - 1) * (A * PA) + 2 * (A * PA) := by ring
    linarith
  have hcA : c = A := le_antisymm step3 step1
  subst hcA
  have step1' : a + 1 ≤ c := haA
  -- Step 4
  have hGA : G c = c * PA - c := by simp only [G, hAA]
  have hGCle : G C ≤ G c := by
    rcases Nat.eq_zero_or_pos C with hC0 | hC
    · rw [hC0, G_zero]; linarith
    · exact G_le hC step2
  -- `a g(C) = c^c (c - a) + c a^a - c^2`
  have key : (a : ℤ) * G C = c * PA * (c - a) + c * (a * pa) - c * c := by
    have : (a : ℤ) * (c * b) = c * (a * b) := by ring
    rw [e2, e1, hAA, haa, hGA] at this
    linarith
  have hPA2 : (2 : ℤ) ≤ PA := by
    rw [hPA]
    have : 2 ≤ c ^ (c - 1) := (show 2 ≤ c by omega).trans (by
      calc c = c ^ 1 := (pow_one c).symm
        _ ≤ c ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega))
    exact_mod_cast this
  have hcPA : (c : ℤ) ≤ PA := by
    rw [hPA]
    have : c ≤ c ^ (c - 1) := by
      calc c = c ^ 1 := (pow_one c).symm
        _ ≤ c ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast this
  have hcZ2 : (2 : ℤ) ≤ c := by exact_mod_cast hc2
  rw [hGA] at hGCle
  rcases Nat.eq_or_lt_of_le ha with ha1 | ha2
  · -- `a = 1`: then `c = 2`
    subst ha1
    have hp1 : pa = 1 := by rw [hpa]; norm_num
    rw [hp1] at key
    have key' : G C = c * PA * (c - 1) + c - c * c := by push_cast at key; linarith
    have hc2' : (c : ℤ) = 2 := step4_one hcZ2 hPA2 key' hGCle
    have hc2'' : c = 2 := by exact_mod_cast hc2'
    subst hc2''
    have hP : PA = 2 := by rw [hPA]; norm_num
    rw [hP] at key'
    have hGC2 : G C = 2 := by push_cast at key'; linarith
    have hC2 : C = 2 := G_injective (by rw [hGC2, G_two])
    refine ⟨rfl, rfl, rfl, hC2, ?_⟩
    rw [hP, hp1, hu, G_two] at e3
    push_cast at e3
    have : (b : ℤ) = 3 := by linarith
    exact_mod_cast this
  · exfalso
    have ha2Z : (2 : ℤ) ≤ a := by exact_mod_cast ha2
    have haa2 : (2 : ℤ) * a ≤ a * pa := by
      have : 2 ≤ a ^ (a - 1) := (show 2 ≤ a by omega).trans (by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ (a - 1) := Nat.pow_le_pow_right (by omega) (by omega))
      have hp2 : (2 : ℤ) ≤ pa := by rw [hpa]; exact_mod_cast this
      have := mul_le_mul_of_nonneg_left hp2 (show (0 : ℤ) ≤ a by linarith)
      linarith
    rcases le_or_gt (2 * a) c with h2a | h2a
    · exact step4_big ha2Z (by exact_mod_cast h2a) hcPA haa2 key hGCle
    · have h2a' : (c : ℤ) + 1 ≤ 2 * a := by exact_mod_cast h2a
      have hPAa : (a : ℤ) * pa ≤ PA := by
        have h1 : a ^ a ≤ (a + 1) ^ a := Nat.pow_le_pow_left (by omega) _
        have h2 : (a + 1) ^ a ≤ c ^ a := Nat.pow_le_pow_left (by omega) _
        have h3 : c ^ a ≤ c ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [← haa, hPA]; exact_mod_cast h1.trans (h2.trans h3)
      have hGCgt : PA < G C := step4_gt ha2Z (by exact_mod_cast step1') h2a' (by linarith)
        haa2 key
      have hCc : c ≤ C := by
        by_contra hlt
        replace hlt := not_le.1 hlt
        obtain ⟨q, rfl⟩ : ∃ q, c = q + 1 := ⟨c - 1, by omega⟩
        have hle : G C ≤ G q := by
          rcases Nat.eq_zero_or_pos C with hC0 | hC
          · rw [hC0, G_zero]; exact (show (1 : ℤ) ≤ 2 by norm_num).trans (G_ge_two (by omega))
          · exact G_le hC (by omega)
        have hq : G q < PA := by
          have h1 : q ^ q ≤ (q + 1) ^ q := Nat.pow_le_pow_left (by omega) _
          have : PA = ((q : ℤ) + 1) ^ q := by rw [hPA]; push_cast; rfl
          rw [this]
          have h1' : ((q : ℤ)) ^ q ≤ ((q : ℤ) + 1) ^ q := by exact_mod_cast h1
          have : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
          show (q : ℤ) ^ q - q < _
          linarith
        exact lt_irrefl _ (hGCgt.trans_le (hle.trans hq.le))
      have hCeq : C = c := le_antisymm step2 hCc
      rw [hCeq, hGA] at key
      exact step4_mid (by exact_mod_cast step1') h2a' (lt_of_lt_of_le (by norm_num) hcZ2) hPAa
        (mul_nonneg (le_trans zero_le_one ha') (le_trans zero_le_one hpa1)) key

/-- **Theorem 15.7** (section 15.2). Under `0^0 = 1`, two different 2-digit solutions in the
same base occur only in base 3. -/
theorem theorem15_7 {b : ℕ} {s t : List ℕ} (hs : s.length = 2) (ht : t.length = 2)
    (h1 : IsSolution b 1 s) (h2 : IsSolution b 1 t) (hne : s ≠ t) : b = 3 := by
  obtain ⟨a, c, rfl⟩ : ∃ a c, s = [a, c] := by
    match s, hs with
    | [a, c], _ => exact ⟨a, c, rfl⟩
  obtain ⟨A, C, rfl⟩ : ∃ A C, t = [A, C] := by
    match t, ht with
    | [A, C], _ => exact ⟨A, C, rfl⟩
  rcases lt_trichotomy a A with h | rfl | h
  · exact (two_two_digit h1 h2 h).2.2.2.2
  · obtain ⟨-, -, -, e1⟩ := two_digit_eq h1
    obtain ⟨-, -, -, e2⟩ := two_digit_eq h2
    have : c = C := G_injective (by linarith)
    exact absurd (by rw [this]) hne
  · exact (two_two_digit h2 h1 h).2.2.2.2

/-- Base 3 has the two 2-digit solutions `(1, 2)` and `(2, 2)` under `0^0 = 1`
(Theorem 15.7). -/
example : IsSolution 3 1 [1, 2] ∧ IsSolution 3 1 [2, 2] := by decide

end Munchausen
