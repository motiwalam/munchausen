import Munchausen.Residues

/-!
# The 3-adic law (Theorem 20.11)

For `e ≥ 4` the residues of `f(x) = x^x - x` modulo `3^e` are the multiples of 3 and the
`v ≡ 2 (mod 27)` with `v ≢ 56 (mod 81)`. The inclusion is the check modulo 81 of
`pow_self_modEq_81`. For the equality, the library expands `f` as a 3-adic power series. This
file replaces the series by a direct congruence: on `x ≡ 2 (mod 6)`, for `k ≥ 3`,

    f(x + 2·3^k t) ≡ f(x) + 3^k t B(x)   (mod 3^(k+3)),

where `B(x) = x^x (2 + a) - 2` and `x^54 = 1 + 27 a`. A finite check over one period shows
`B(x) = 9 c` with `3 ∤ c` unless `x ≡ 8 (mod 9)`. So `t ↦ f(x + 2·3^k t)` runs through the three
lifts of `f(x) mod 3^(k+2)`, which is Hensel's lemma for the series `G` of the library.
-/

namespace Munchausen

/-- If `3^m ∣ a - b` with `m ≥ 1`, then `3^(m+j) ∣ a^(3^j) - b^(3^j)`. -/
lemma three_pow_dvd_pow_sub_pow {a b : ℤ} {m : ℕ} (hm : 1 ≤ m) (h : (3 : ℤ) ^ m ∣ a - b)
    (j : ℕ) : (3 : ℤ) ^ (m + j) ∣ a ^ 3 ^ j - b ^ 3 ^ j := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have e : a ^ 3 ^ (j + 1) - b ^ 3 ^ (j + 1) =
        (a ^ 3 ^ j - b ^ 3 ^ j) * ((a ^ 3 ^ j - b ^ 3 ^ j) ^ 2 + 3 * (a ^ 3 ^ j * b ^ 3 ^ j)) := by
      rw [pow_succ, pow_mul, pow_mul]; ring
    rw [e, show m + (j + 1) = (m + j) + 1 by ring, pow_succ]
    apply mul_dvd_mul ih
    have h3 : (3 : ℤ) ∣ a ^ 3 ^ j - b ^ 3 ^ j := (dvd_pow_self 3 (by omega)).trans ih
    exact dvd_add (dvd_pow h3 two_ne_zero) (dvd_mul_right _ _)

/-- If `y^27 = 1 + 27 a`, then `y^(3^k) ≡ 1 + 3^k a (mod 3^(k+3))` for `k ≥ 3`. -/
lemma pow_three_pow_modEq {y a : ℤ} (ha : y ^ 27 = 1 + 27 * a) {k : ℕ} (hk : 3 ≤ k) :
    (3 : ℤ) ^ (k + 3) ∣ y ^ 3 ^ k - 1 - 3 ^ k * a := by
  induction k, hk using Nat.le_induction with
  | base => exact ⟨0, by rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ha]; ring⟩
  | succ k hk ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
    have hy : y ^ 3 ^ (n + 3) = 1 + 3 ^ (n + 3) * a + 3 ^ (n + 3 + 3) * m := by linarith
    have e : y ^ 3 ^ (n + 3 + 1) = (y ^ 3 ^ (n + 3)) ^ 3 := by rw [pow_succ, pow_mul]
    rw [e, hy]
    exact ⟨m + 3 ^ n * (a + 27 * m) ^ 2 + 3 ^ (2 * n + 2) * (a + 27 * m) ^ 3, by ring⟩

/-- The step of the 3-adic law (proof of Theorem 20.11). For `k ≥ 3`, `x₀ ≥ 1` and
`x₀^54 = 1 + 27 a`:
`f(x₀ + 2·3^k t) ≡ f(x₀) + 3^k t (x₀^x₀ (2 + a) - 2) (mod 3^(k+3))`, where `f(x) = x^x - x`. -/
lemma step_three_adic {x0 k t : ℕ} {a : ℤ} (hx0 : 1 ≤ x0) (hk : 3 ≤ k)
    (ha : (x0 : ℤ) ^ 54 = 1 + 27 * a) :
    (3 : ℤ) ^ (k + 3) ∣ (((x0 + 2 * 3 ^ k * t : ℕ) : ℤ) ^ (x0 + 2 * 3 ^ k * t) -
      (x0 + 2 * 3 ^ k * t : ℕ)) - ((x0 : ℤ) ^ x0 - x0) -
      3 ^ k * t * ((x0 : ℤ) ^ x0 * (2 + a) - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  set D : ℤ := 2 * 3 ^ (n + 3) * t with hD
  have hX : ((x0 + 2 * 3 ^ (n + 3) * t : ℕ) : ℤ) = (x0 : ℤ) + D := by rw [hD]; push_cast; ring
  rw [hX, pow_add ((x0 : ℤ) + D) x0]
  -- `(x₀ + D)^x₀ ≡ x₀^x₀ (1 + D)`
  obtain ⟨c, hc⟩ := add_pow_modEq_sq (x0 : ℤ) D x0
  have hxx : (x0 : ℤ) * (x0 : ℤ) ^ (x0 - 1) = (x0 : ℤ) ^ x0 := by
    rw [← pow_succ']; congr 1; omega
  have hA : ((x0 : ℤ) + D) ^ x0 =
      (x0 : ℤ) ^ x0 * (1 + D) + 3 ^ (n + 3 + 3) * (4 * 3 ^ n * t ^ 2 * c) := by
    rw [hD] at hc ⊢
    linear_combination hc + 2 * 3 ^ (n + 3) * (t : ℤ) * hxx
  -- `((x₀ + D)^2)^(3^k) ≡ (x₀^2)^(3^k) ≡ 1 + 3^k a`
  have h1 : (3 : ℤ) ^ (n + 3) ∣ ((x0 : ℤ) + D) ^ 2 - (x0 ^ 2 : ℤ) :=
    ⟨2 * t * (2 * x0 + D), by rw [hD]; ring⟩
  obtain ⟨m1, hm1⟩ := three_pow_dvd_pow_sub_pow (by omega) h1 (n + 3)
  obtain ⟨m2, hm2⟩ := pow_three_pow_modEq (y := (x0 : ℤ) ^ 2) (a := a)
    (by rw [← pow_mul]; exact ha) (k := n + 3) (by omega)
  set Y := (((x0 : ℤ) + D) ^ 2) ^ 3 ^ (n + 3) with hYdef
  have hY : Y = 1 + 3 ^ (n + 3) * (a + 27 * (m2 + 3 ^ n * m1)) := by
    have e1 : (3 : ℤ) ^ (n + 3 + (n + 3)) = 3 ^ (n + 3 + 3) * 3 ^ n := by ring
    rw [e1] at hm1
    linear_combination hm1 + hm2
  -- `Y^t ≡ 1 + t (Y - 1)`
  obtain ⟨c2, hc2⟩ := add_pow_modEq_sq 1 (3 ^ (n + 3) * (a + 27 * (m2 + 3 ^ n * m1))) t
  have hXd : ((x0 : ℤ) + D) ^ (2 * 3 ^ (n + 3) * t) = Y ^ t := by
    rw [hYdef, ← pow_mul, ← pow_mul, mul_assoc]
  rw [hXd, hY]
  set z : ℤ := a + 27 * (m2 + 3 ^ n * m1)
  have hYt : (1 + 3 ^ (n + 3) * z) ^ t =
      1 + 3 ^ (n + 3) * t * a + 3 ^ (n + 3 + 3) * (t * (m2 + 3 ^ n * m1) + 3 ^ n * z ^ 2 * c2) := by
    simp only [one_pow, mul_one] at hc2
    linear_combination hc2
  rw [hYt, hA]
  exact ⟨4 * 3 ^ n * t ^ 2 * c * (1 + 3 ^ (n + 3) * t * a + 3 ^ (n + 3 + 3) *
      (t * (m2 + 3 ^ n * m1) + 3 ^ n * z ^ 2 * c2)) + (x0 : ℤ) ^ x0 * (1 + D) *
      (t * (m2 + 3 ^ n * m1) + 3 ^ n * z ^ 2 * c2) + 2 * 3 ^ n * t ^ 2 * a * (x0 : ℤ) ^ x0,
    by rw [hD]; ring⟩

set_option maxRecDepth 100000 in
/-- The leading coefficient of the step (proof of Theorem 20.11): for `x ≡ 2 (mod 6)` with
`x ≢ 8 (mod 9)`, write `x^54 = 1 + 27 a`; then `x^x (2 + a) - 2 = 9 c` with `3 ∤ c`. A finite
check over one period of 162. -/
lemma three_adic_unit {x : ℕ} (h6 : x % 6 = 2) (h9 : x % 9 ≠ 8) :
    ∃ a : ℤ, (x : ℤ) ^ 54 = 1 + 27 * a ∧
      ∃ c : ℤ, (x : ℤ) ^ x * (2 + a) - 2 = 9 * c ∧ ¬ (3 : ℤ) ∣ c := by
  -- the same facts for `r = x mod 162`, by a finite check
  have hcheck : ∀ r < 162, r % 6 = 2 → r % 9 ≠ 8 → r ^ 54 % 27 = 1 ∧
      (r ^ r * (2 + r ^ 54 / 27) % 27 = 11 ∨ r ^ r * (2 + r ^ 54 / 27) % 27 = 20) := by
    decide
  set r := x % 162 with hr
  obtain ⟨hr1, hr2⟩ := hcheck r (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
  set ar := r ^ 54 / 27
  have har : (r : ℤ) ^ 54 = 1 + 27 * ar := by
    have : r ^ 54 = 1 + 27 * ar := by omega
    exact_mod_cast this
  -- `x^54 ≡ r^54 (mod 3^7)`
  have h81 : (3 : ℤ) ^ 4 ∣ (x : ℤ) ^ 2 - (r : ℤ) ^ 2 := by
    have : (81 : ℤ) ∣ (x : ℤ) - r := by
      have : (x : ℤ) - r = 162 * (x / 162 : ℕ) := by
        have := Nat.mod_add_div x 162; rw [hr]; push_cast; omega
      rw [this]; exact Dvd.dvd.mul_right (by norm_num) _
    obtain ⟨q, hq⟩ := this
    exact ⟨q * (x + r), by rw [show (x : ℤ) ^ 2 - r ^ 2 = (x - r) * (x + r) by ring, hq]; ring⟩
  obtain ⟨q, hq⟩ := three_pow_dvd_pow_sub_pow (by norm_num) h81 3
  have hx54 : (x : ℤ) ^ 54 = 1 + 27 * (ar + 81 * q) := by
    have e : ((x : ℤ) ^ 2) ^ 3 ^ 3 - ((r : ℤ) ^ 2) ^ 3 ^ 3 = (x : ℤ) ^ 54 - (r : ℤ) ^ 54 := by ring
    rw [e] at hq
    linear_combination hq + har
  refine ⟨ar + 81 * q, hx54, ?_⟩
  -- `x^x ≡ r^r (mod 27)`
  have hcop : x.Coprime 27 := coprime_three_pow (by omega) 3
  have hper := pow_self_modEq_mod (L := 162) hcop (by norm_num) (by decide)
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_dvd.1 hper.symm)
  rw [← hr] at hu
  have hB : (r ^ r * (2 + ar) : ℕ) % 27 = 11 ∨ (r ^ r * (2 + ar) : ℕ) % 27 = 20 := hr2
  have hBz : ∃ s : ℤ, ((r : ℤ) ^ r * (2 + ar) = 27 * s + 11 ∨
      (r : ℤ) ^ r * (2 + ar) = 27 * s + 20) := by
    set B := r ^ r * (2 + ar) with hBdef
    refine ⟨(B / 27 : ℕ), ?_⟩
    have := Nat.mod_add_div B 27
    rcases hB with h | h
    · left; exact_mod_cast (by omega : B = 27 * (B / 27) + 11)
    · right; exact_mod_cast (by omega : B = 27 * (B / 27) + 20)
  obtain ⟨s, hs⟩ := hBz
  -- `x^x (2 + a) - 2 = r^r (2 + a_r) - 2 + 27 (...)`
  have hxr : (x : ℤ) ^ x = (r : ℤ) ^ r + 27 * u := by
    push_cast at hu; linarith
  rcases hs with hs | hs
  · refine ⟨3 * (s + u * (2 + (ar + 81 * q)) + 3 * (r : ℤ) ^ r * q) + 1, ?_, ?_⟩
    · rw [hxr]; linear_combination hs
    · omega
  · refine ⟨3 * (s + u * (2 + (ar + 81 * q)) + 3 * (r : ℤ) ^ r * q) + 2, ?_, ?_⟩
    · rw [hxr]; linear_combination hs
    · omega

/-- Lifting along `x ≡ 2 (mod 6)`, `x ≢ 8 (mod 9)` (proof of Theorem 20.11): a solution of
`f(x₀) ≡ v (mod 3^5)` lifts to `f(x) ≡ v (mod 3^e)` for every `e ≥ 5`, with `x ≡ x₀ (mod 18)`. -/
lemma lift_three_adic {x0 : ℕ} (h6 : x0 % 6 = 2) (h9 : x0 % 9 ≠ 8) {v : ℤ}
    (h5 : (3 : ℤ) ^ 5 ∣ ((x0 : ℤ) ^ x0 - x0) - v) :
    ∀ e, 5 ≤ e → ∃ t : ℕ, (3 : ℤ) ^ e ∣
      (((x0 + 18 * t : ℕ) : ℤ) ^ (x0 + 18 * t) - (x0 + 18 * t : ℕ)) - v := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => exact ⟨0, by simpa using h5⟩
  | succ e he ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
    set x := x0 + 18 * t with hx
    obtain ⟨a, ha, c, hc, hc3⟩ := three_adic_unit (x := x) (by omega) (by omega)
    obtain ⟨m, hm⟩ := ht
    -- choose `s` with `3 ∣ m + s c`
    obtain ⟨s, hs⟩ : ∃ s : ℕ, (3 : ℤ) ∣ m + s * c := by
      have : c % 3 = 1 ∨ c % 3 = 2 := by omega
      rcases this with h | h <;>
        rcases (show m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 by omega) with h' | h' | h'
      · exact ⟨0, by omega⟩
      · exact ⟨2, by omega⟩
      · exact ⟨1, by omega⟩
      · exact ⟨0, by omega⟩
      · exact ⟨1, by omega⟩
      · exact ⟨2, by omega⟩
    obtain ⟨M, hM⟩ := step_three_adic (x0 := x) (k := k) (t := s) (a := a) (by omega)
      (by omega) ha
    obtain ⟨q, hq⟩ := hs
    refine ⟨t + 3 ^ (k - 2) * s, ?_⟩
    have hk : 2 * 3 ^ k = 18 * 3 ^ (k - 2) := by
      rw [show (18 : ℕ) = 2 * 3 ^ 2 by norm_num, mul_assoc, ← pow_add]; congr 2; omega
    have e1 : x0 + 18 * (t + 3 ^ (k - 2) * s) = x + 2 * 3 ^ k * s := by rw [hx, hk]; ring
    rw [e1]
    refine ⟨M + q, ?_⟩
    have e2 : (3 : ℤ) ^ (k + 3) = 3 ^ (k + 2) * 3 := by ring
    rw [show k + 2 + 1 = k + 3 by ring]
    rw [e2] at hM
    rw [hc] at hM
    linear_combination hM + hm + 3 ^ (k + 2) * hq

/-- Every multiple of 3 is a value of `f` modulo `3^e` (Lemma 20.6, in `ℤ`). -/
lemma exists_of_three_dvd {e : ℕ} {v : ℤ} (hv : (3 : ℤ) ∣ v) :
    ∃ x : ℕ, 1 ≤ x ∧ (3 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v := by
  obtain ⟨w, hw⟩ := hv
  obtain ⟨x, hx, hxw⟩ := multiple_mem_T (p := 3) (e := e) (by norm_num) (w % (3 : ℤ) ^ e).toNat
  refine ⟨x, hx, ?_⟩
  rw [show ((3 : ℤ)) ^ e = ((3 ^ e : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hxw, hw]
  have hnn : 0 ≤ w % (3 : ℤ) ^ e := Int.emod_nonneg _ (by positivity)
  have h1 : (((w % (3 : ℤ) ^ e).toNat : ℕ) : ZMod (3 ^ e)) =
      ((w % (3 : ℤ) ^ e : ℤ) : ZMod (3 ^ e)) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  have h2 : ((w % (3 : ℤ) ^ e : ℤ) : ZMod (3 ^ e)) = (w : ZMod (3 ^ e)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨w / (3 : ℤ) ^ e, by rw [Int.emod_def]; push_cast; ring⟩
  push_cast
  rw [h1, h2]; ring

/-- **Theorem 20.11** (the 3-adic law, section 20.2.2). For `e ≥ 4`, `v` is a value of
`x^x - x` modulo `3^e` (with `x ≥ 1`) exactly when `v ≡ 0 (mod 3)`, or `v ≡ 2 (mod 27)` and
`v ≢ 56 (mod 81)`. -/
theorem theorem20_11 {e : ℕ} (he : 4 ≤ e) (v : ℤ) :
    (∃ x : ℕ, 1 ≤ x ∧ (3 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v) ↔
      ((3 : ℤ) ∣ v ∨ ((27 : ℤ) ∣ v - 2 ∧ ¬ (81 : ℤ) ∣ v - 56)) := by
  constructor
  · rintro ⟨x, hx, hdvd⟩
    have h81 : (3 : ℤ) ^ 4 ∣ ((x : ℤ) ^ x - x) - v := (pow_dvd_pow 3 he).trans hdvd
    norm_num at h81
    by_cases h3 : (3 : ℤ) ∣ v
    · exact Or.inl h3
    right
    by_cases h62 : x % 6 = 2
    · rcases pow_self_modEq_81 h62 with h | h
      · have := h.dvd; push_cast at this; omega
      · have := h.dvd; push_cast at this; omega
    · have := (pow_self_modEq_three_of_ne hx h62).dvd
      push_cast at this
      omega
  · rintro (h3 | ⟨h27, h56⟩)
    · exact exists_of_three_dvd h3
    -- `v mod 243` is one of six classes; a witness for each, then lift
    have key : ∃ x0 : ℕ, x0 % 6 = 2 ∧ x0 % 9 ≠ 8 ∧
        (3 : ℤ) ^ 5 ∣ ((x0 : ℤ) ^ x0 - x0) - v := by
      have : v % 243 = 2 ∨ v % 243 = 29 ∨ v % 243 = 83 ∨ v % 243 = 110 ∨ v % 243 = 164 ∨
          v % 243 = 191 := by omega
      rcases this with h | h | h | h | h | h
      · exact ⟨2, by norm_num, by norm_num, by norm_num; omega⟩
      · exact ⟨32, by norm_num, by norm_num, by norm_num; omega⟩
      · exact ⟨20, by norm_num, by norm_num, by norm_num; omega⟩
      · exact ⟨14, by norm_num, by norm_num, by norm_num; omega⟩
      · exact ⟨38, by norm_num, by norm_num, by norm_num; omega⟩
      · exact ⟨50, by norm_num, by norm_num, by norm_num; omega⟩
    obtain ⟨x0, h6, h9, h5⟩ := key
    obtain ⟨t, ht⟩ := lift_three_adic h6 h9 h5 (max e 5) (le_max_right _ _)
    exact ⟨x0 + 18 * t, by omega, (pow_dvd_pow 3 (le_max_left _ _)).trans ht⟩

end Munchausen
