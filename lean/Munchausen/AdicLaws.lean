import Munchausen.Residues

/-!
# The 3-adic law (Theorem 20.11) and the 5-adic law (Theorem 20.12)

For `e ≥ 4` the residues of `f(x) = x^x - x` modulo `3^e` are the multiples of 3 and the
`v ≡ 2 (mod 27)` with `v ≢ 56 (mod 81)`. The inclusion is the check modulo 81 of
`pow_self_modEq_81`. For the equality, the library expands `f` as a 3-adic power series. This
file replaces the series by a direct congruence: on `x ≡ 2 (mod 6)`, for `k ≥ 3`,

    f(x + 2·3^k t) ≡ f(x) + 3^k t B(x)   (mod 3^(k+3)),

where `B(x) = x^x (2 + a) - 2` and `x^54 = 1 + 27 a`. A finite check over one period shows
`B(x) = 9 c` with `3 ∤ c` unless `x ≡ 8 (mod 9)`. So `t ↦ f(x + 2·3^k t)` runs through the three
lifts of `f(x) mod 3^(k+2)`, which is Hensel's lemma for the series `G` of the library.

For the 5-adic law, the residues `v ≢ 3 (mod 5)` are values modulo every `5^e` by Lemmas 20.6
and 20.7. The class `3 (mod 5)` is checked modulo 25, 125 and 625 (1, 3 and 11 values, the
numbers `A (1 - 25 s / 2)`). For every `e` the series of Lemma 20.10 is replaced by two
elementary facts. Let `i ≡ 3 (mod 5)` be a square root of `-1` modulo `5^e`, `4 ∣ x` and
`D = x - i`, with `5 ∣ D`. The binomial expansion of `(i + D)^x` gives

    2 (x^x - x) ≡ (1 - i)(2 + D^2) + 5 D^2 S   (mod 5^e),

so every value is `A (1 - 25 s / 2)` with `s` a square (`two_mul_pow_self_sub_eq`). Conversely,
`f(x + 4·5^k t) ≡ f(x) + 5^k t B(x) (mod 5^(k+j+1))` with `v_5(B(x)) = v_5(D) = j`
(`step_five_adic`, `five_adic_unit`), which replaces Hensel's lemma.
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

/-- Every multiple of `p` is a value of `f` modulo `p^e` (Lemma 20.6, in `ℤ`). -/
lemma exists_of_dvd {p e : ℕ} (hp : 2 ≤ p) {v : ℤ} (hv : (p : ℤ) ∣ v) :
    ∃ x : ℕ, 1 ≤ x ∧ (p : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v := by
  obtain ⟨w, hw⟩ := hv
  obtain ⟨x, hx, hxw⟩ := multiple_mem_T (p := p) (e := e) hp (w % (p : ℤ) ^ e).toNat
  refine ⟨x, hx, ?_⟩
  rw [show ((p : ℤ)) ^ e = ((p ^ e : ℕ) : ℤ) by push_cast; rfl,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [hxw, hw]
  have hp0 : (0 : ℤ) < (p : ℤ) ^ e := by have : (0 : ℤ) < p := by omega
                                         positivity
  have hnn : 0 ≤ w % (p : ℤ) ^ e := Int.emod_nonneg _ hp0.ne'
  have h1 : (((w % (p : ℤ) ^ e).toNat : ℕ) : ZMod (p ^ e)) =
      ((w % (p : ℤ) ^ e : ℤ) : ZMod (p ^ e)) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  have h2 : ((w % (p : ℤ) ^ e : ℤ) : ZMod (p ^ e)) = (w : ZMod (p ^ e)) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨w / (p : ℤ) ^ e, by rw [Int.emod_def]; push_cast; ring⟩
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
    · exact exists_of_dvd (p := 3) (by norm_num) h3
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

/-- **Lemma 15.12 (1)** (section 15.4.2). For `e ≥ 1`, the values of `x^x - x` modulo `2^e`
are exactly the even residues. -/
theorem lemma15_12_one {e : ℕ} (he : 1 ≤ e) (v : ℤ) :
    (∃ x : ℕ, 1 ≤ x ∧ (2 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v) ↔ (2 : ℤ) ∣ v := by
  constructor
  · rintro ⟨x, hx, hdvd⟩
    have hx2 : (2 : ℤ) ∣ (x : ℤ) ^ x - x := by
      have := Nat.modEq_iff_dvd.1 (pow_self_modEq_two x hx).symm
      push_cast at this; exact this
    have := (dvd_pow_self (2 : ℤ) (by omega : e ≠ 0)).trans hdvd
    have h := dvd_sub hx2 this
    simpa using h
  · intro hv
    exact_mod_cast exists_of_dvd (p := 2) (e := e) le_rfl (by exact_mod_cast hv)

/-! ### Theorem 20.12: the 5-adic law, small `e` -/

/-- **Theorem 20.12**, the residues prime to the class 3 (section 20.2.2). For every `e`, each
`v ≢ 3 (mod 5)` is a value of `x^x - x` modulo `5^e`: the multiples of 5 by Lemma 20.6, and
1, 2, 4 by lifting from `x₀ = 18, 2, 3` with Lemma 20.7. -/
theorem theorem20_12_good {e : ℕ} (he : 1 ≤ e) {v : ℤ} (hv : ¬ (5 : ℤ) ∣ v - 3) :
    ∃ x : ℕ, 1 ≤ x ∧ (5 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v := by
  have hp : Nat.Prime 5 := by norm_num
  by_cases h5 : (5 : ℤ) ∣ v
  · exact_mod_cast exists_of_dvd (p := 5) (e := e) (by norm_num) (by exact_mod_cast h5)
  -- a starting point `x₀` with `x₀^x₀ ≢ 1 (mod 5)` and `f(x₀) ≡ v (mod 5)`
  obtain ⟨x0, hx0, hx0p, hg, hv0⟩ : ∃ x0 : ℕ, 1 ≤ x0 ∧ ¬ ((5 : ℕ) : ℤ) ∣ x0 ∧
      ¬ ((5 : ℕ) : ℤ) ∣ (x0 : ℤ) ^ x0 - 1 ∧ ((5 : ℕ) : ℤ) ∣ v - ((x0 : ℤ) ^ x0 - x0) := by
    have : v % 5 = 1 ∨ v % 5 = 2 ∨ v % 5 = 4 := by omega
    rcases this with h | h | h
    · exact ⟨18, by norm_num, by norm_num, by norm_num, by norm_num; omega⟩
    · exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num; omega⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, by norm_num; omega⟩
  obtain ⟨t, ht⟩ := lemma20_7 hp hx0 hx0p hg v hv0 e he
  exact ⟨x0 + 5 * (5 - 1) * t, by omega, by exact_mod_cast ht⟩

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 600 in
/-- **Theorem 20.12** for `e = 3` (section 20.2.2). The values of `x^x - x` modulo 125 in the
class `3 (mod 5)` are exactly 33, 58 and 83, the three numbers `A (1 - 25 s / 2)` with `s` a
square modulo 5 (`A = 1 - i ≡ 58`). -/
theorem theorem20_12_three {v : ℤ} (hv : v % 5 = 3) :
    (∃ x : ℕ, 1 ≤ x ∧ (125 : ℤ) ∣ ((x : ℤ) ^ x - x) - v) ↔
      v % 125 = 33 ∨ v % 125 = 58 ∨ v % 125 = 83 := by
  constructor
  · rintro ⟨x, hx, hdvd⟩
    have hle : x ≤ x ^ x := by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ x := Nat.pow_le_pow_right hx hx
    have hcast : ((x ^ x - x : ℕ) : ℤ) = (x : ℤ) ^ x - x := by push_cast [hle]; ring
    have h20 : x % 20 = 8 := lemma20_9_five hx (by omega)
    have hcop5 : x.Coprime 5 := Nat.coprime_comm.1
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 (by omega))
    have hcop : x.Coprime 125 := by simpa using Nat.Coprime.pow_right 3 hcop5
    have hper := pow_self_modEq_mod (L := 500) hcop (by norm_num) (by decide)
    have hcheck : ∀ r < 500, r % 20 = 8 → (r ^ r - r) % 125 = 33 ∨ (r ^ r - r) % 125 = 58 ∨
        (r ^ r - r) % 125 = 83 := by decide
    set r := x % 500 with hr
    have hrle : r ≤ r ^ r := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have hrc : ((r ^ r - r : ℕ) : ℤ) = (r : ℤ) ^ r - r := by push_cast [hrle]; ring
    have h1 := hcheck r (Nat.mod_lt _ (by norm_num)) (by omega)
    have h2 := hper.dvd
    push_cast at h2
    have h3 : (r : ℤ) ^ r - r = ((r ^ r - r : ℕ) : ℤ) := hrc.symm
    have h4 : (x : ℤ) - r = 500 * (x / 500 : ℕ) := by
      have := Nat.mod_add_div x 500; push_cast; omega
    omega
  · rintro (h | h | h)
    · exact ⟨48, by norm_num, by norm_num; omega⟩
    · exact ⟨68, by norm_num, by norm_num; omega⟩
    · exact ⟨8, by norm_num, by norm_num; omega⟩

/-- **Theorem 20.12** for `e = 2` (section 20.2.2). The only value of `x^x - x` modulo 25 in the
class `3 (mod 5)` is `8 ≡ A`. -/
theorem theorem20_12_two {v : ℤ} (hv : v % 5 = 3) :
    (∃ x : ℕ, 1 ≤ x ∧ (25 : ℤ) ∣ ((x : ℤ) ^ x - x) - v) ↔ v % 25 = 8 := by
  constructor
  · rintro ⟨x, hx, hdvd⟩
    have h := (theorem20_12_three (v := (x : ℤ) ^ x - x) (by omega)).1 ⟨x, hx, by simp⟩
    omega
  · intro h
    exact ⟨8, by norm_num, by norm_num; omega⟩

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 3000 in
/-- **Theorem 20.12** for `e = 4` (section 20.2.2). The values of `x^x - x` modulo 625 in the
class `3 (mod 5)` are the 11 numbers `A (1 - 25 s / 2)` with `s` a square modulo 25
(`A ≡ 183`). -/
theorem theorem20_12_four {v : ℤ} (hv : v % 5 = 3) :
    (∃ x : ℕ, 1 ≤ x ∧ (625 : ℤ) ∣ ((x : ℤ) ^ x - x) - v) ↔
      v % 625 ∈ ({33, 83, 158, 183, 208, 283, 333, 408, 458, 533, 583} : Finset ℤ) := by
  constructor
  · rintro ⟨x, hx, hdvd⟩
    have hle : x ≤ x ^ x := by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ x := Nat.pow_le_pow_right hx hx
    have hcast : ((x ^ x - x : ℕ) : ℤ) = (x : ℤ) ^ x - x := by push_cast [hle]; ring
    have h20 : x % 20 = 8 := lemma20_9_five hx (by omega)
    have hcop5 : x.Coprime 5 := Nat.coprime_comm.1
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).2 (by omega))
    have hcop : x.Coprime 625 := by simpa using Nat.Coprime.pow_right 4 hcop5
    have hper := pow_self_modEq_mod (L := 2500) hcop (by norm_num) (by decide)
    have hcheck : ∀ r < 2500, r % 20 = 8 → (r ^ r - r) % 625 = 33 ∨ (r ^ r - r) % 625 = 83 ∨
        (r ^ r - r) % 625 = 158 ∨ (r ^ r - r) % 625 = 183 ∨ (r ^ r - r) % 625 = 208 ∨
        (r ^ r - r) % 625 = 283 ∨ (r ^ r - r) % 625 = 333 ∨ (r ^ r - r) % 625 = 408 ∨
        (r ^ r - r) % 625 = 458 ∨ (r ^ r - r) % 625 = 533 ∨ (r ^ r - r) % 625 = 583 := by
      decide
    set r := x % 2500 with hr
    have hrle : r ≤ r ^ r := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have hrc : ((r ^ r - r : ℕ) : ℤ) = (r : ℤ) ^ r - r := by push_cast [hrle]; ring
    have h1 := hcheck r (Nat.mod_lt _ (by norm_num)) (by omega)
    have h2 := hper.dvd
    push_cast at h2
    have h3 : (r : ℤ) ^ r - r = ((r ^ r - r : ℕ) : ℤ) := hrc.symm
    have h4 : (x : ℤ) - r = 2500 * (x / 2500 : ℕ) := by
      have := Nat.mod_add_div x 2500; push_cast; omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨388, by norm_num, by norm_num; omega⟩
    · exact ⟨128, by norm_num, by norm_num; omega⟩
    · exact ⟨88, by norm_num, by norm_num; omega⟩
    · exact ⟨68, by norm_num, by norm_num; omega⟩
    · exact ⟨28, by norm_num, by norm_num; omega⟩
    · exact ⟨48, by norm_num, by norm_num; omega⟩
    · exact ⟨8, by norm_num, by norm_num; omega⟩
    · exact ⟨348, by norm_num, by norm_num; omega⟩
    · exact ⟨108, by norm_num, by norm_num; omega⟩
    · exact ⟨148, by norm_num, by norm_num; omega⟩
    · exact ⟨208, by norm_num, by norm_num; omega⟩


/-! ### Theorem 20.12 for every `e` -/

/-- A digit `t < 5` solves `5 ∣ v + u t` when `5 ∤ u`. -/
lemma exists_five_dvd_add_mul {u : ℤ} (hu : ¬ (5 : ℤ) ∣ u) (v : ℤ) :
    ∃ t : ℕ, (5 : ℤ) ∣ v + u * t := by
  have hu' : u % 5 = 1 ∨ u % 5 = 2 ∨ u % 5 = 3 ∨ u % 5 = 4 := by omega
  have hv' : v % 5 = 0 ∨ v % 5 = 1 ∨ v % 5 = 2 ∨ v % 5 = 3 ∨ v % 5 = 4 := by omega
  rcases hu' with h | h | h | h <;> rcases hv' with h' | h' | h' | h' | h' <;>
    first
    | exact ⟨0, by push_cast; omega⟩ | exact ⟨1, by push_cast; omega⟩
    | exact ⟨2, by push_cast; omega⟩ | exact ⟨3, by push_cast; omega⟩
    | exact ⟨4, by push_cast; omega⟩

/-- Hensel's lemma for `y^2 = c` modulo powers of 5: a square root of `c` modulo 5 that is
prime to 5 lifts modulo every `5^e`. -/
lemma exists_sq_five_pow {a c : ℤ} (ha : ¬ (5 : ℤ) ∣ a) (h : (5 : ℤ) ∣ a ^ 2 - c) (e : ℕ) :
    ∃ y : ℤ, (5 : ℤ) ∣ y - a ∧ (5 : ℤ) ^ e ∣ y ^ 2 - c := by
  induction e with
  | zero => exact ⟨a, by simp, by simp⟩
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with rfl | he
    · exact ⟨a, by simp, by simpa using h⟩
    obtain ⟨y, hya, m, hm⟩ := ih
    obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
    have hy : ¬ (5 : ℤ) ∣ 2 * y := by omega
    obtain ⟨t, q, hq⟩ := exists_five_dvd_add_mul hy m
    refine ⟨y + 5 ^ (n + 1) * t, ?_, q + 5 ^ n * t ^ 2, ?_⟩
    · have : (5 : ℤ) ∣ 5 ^ (n + 1) * t := Dvd.dvd.mul_right (dvd_pow_self 5 (by omega)) _
      omega
    · linear_combination hm + 5 ^ (n + 1) * hq

/-- The expansion of `x^x` at the 5-adic `i = sqrt(-1)` (proof of Theorem 20.12), in any
commutative ring with `ι^2 = -1`: for `4 ∣ x` and `x = ι + D` with `D = 5 d`,
`2 (x^x - x) = (1 - ι)(2 + D^2) + 5 D^2 S`. This replaces the 5-adic series of Lemma 20.10:
the coefficient of `D` vanishes. -/
lemma two_mul_pow_self_sub_eq {R : Type*} [CommRing R] {ι D d : R} (hι : ι ^ 2 = -1)
    (hD : D = 5 * d) {x : ℕ} (h4 : 4 ∣ x) (hx : 0 < x) (hxD : (x : R) = ι + D) :
    ∃ S : R, 2 * ((x : R) ^ x - x) = (1 - ι) * (2 + D ^ 2) + 5 * D ^ 2 * S := by
  obtain ⟨q, rfl⟩ := h4
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  set n := 4 * (r + 1) with hn
  have hpow : (ι + D) ^ n = ∑ m ∈ Finset.range (n + 1), D ^ m * ι ^ (n - m) * (n.choose m) := by
    rw [add_comm, add_pow]
  rw [show n + 1 = (4 * r + 2) + 1 + 1 + 1 by omega] at hpow
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ'] at hpow
  have e0 : ι ^ (n - 0) = 1 := by
    rw [Nat.sub_zero, hn, show 4 * (r + 1) = 2 * (2 * (r + 1)) by ring, pow_mul, hι]
    simp [pow_mul]
  have e1 : ι ^ (n - (0 + 1)) = -ι := by
    rw [show n - (0 + 1) = 2 * (2 * r + 1) + 1 by omega, pow_succ, pow_mul, hι]
    simp [pow_succ, pow_mul]
  have e2 : ι ^ (n - (0 + 1 + 1)) = -1 := by
    rw [show n - (0 + 1 + 1) = 2 * (2 * r + 1) by omega, pow_mul, hι]
    simp [pow_succ, pow_mul]
  have c1 : ((n.choose (0 + 1) : ℕ) : R) = ι + D := by simpa using hxD
  have c2 : 2 * ((n.choose (0 + 1 + 1) : ℕ) : R) = (ι + D) * (ι + D - 1) := by
    have h : n.choose 2 * 2 = n * (n - 1) := by
      rw [Nat.choose_two_right]; exact Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd
    have h' : ((n.choose 2 * 2 : ℕ) : R) = ((n * (n - 1) : ℕ) : R) := by rw [h]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega)] at h'
    rw [← hxD]; linear_combination h'
  set T := ∑ m ∈ Finset.range (4 * r + 2), D ^ m * ι ^ (n - (m + 1 + 1 + 1)) *
    (n.choose (m + 1 + 1 + 1) : R) with hT
  have htail : ∑ m ∈ Finset.range (4 * r + 2), D ^ (m + 1 + 1 + 1) * ι ^ (n - (m + 1 + 1 + 1)) *
      (n.choose (m + 1 + 1 + 1) : R) = D ^ 3 * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [htail, e0, e1, e2] at hpow
  refine ⟨2 * d * T - d * (2 * ι + D - 1), ?_⟩
  rw [hxD, hpow]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, ] at c1 c2 ⊢
  rw [c1]
  linear_combination (-(D ^ 2) - 2 * D) * hι - D ^ 2 * (2 * ι + D - 1) * hD + (-D ^ 2) * c2 +
    2 * D ^ 2 * T * hD

/-- If `5^m ∣ a - b` with `m ≥ 1`, then `5^(m+j) ∣ a^(5^j) - b^(5^j)`. -/
lemma five_pow_dvd_pow_sub_pow {a b : ℤ} {m : ℕ} (hm : 1 ≤ m) (h : (5 : ℤ) ^ m ∣ a - b)
    (j : ℕ) : (5 : ℤ) ^ (m + j) ∣ a ^ 5 ^ j - b ^ 5 ^ j := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    set δ := a ^ 5 ^ j - b ^ 5 ^ j
    set B := b ^ 5 ^ j
    have e : a ^ 5 ^ (j + 1) - b ^ 5 ^ (j + 1) =
        δ * (5 * B ^ 4 + 10 * B ^ 3 * δ + 10 * B ^ 2 * δ ^ 2 + 5 * B * δ ^ 3 + δ ^ 4) := by
      have ha : a ^ 5 ^ j = B + δ := by simp [δ, B]
      rw [pow_succ, pow_mul, pow_mul, ha]; ring
    rw [e, show m + (j + 1) = (m + j) + 1 by ring, pow_succ]
    apply mul_dvd_mul ih
    have h5 : (5 : ℤ) ∣ δ := (dvd_pow_self 5 (by omega)).trans ih
    exact dvd_add (dvd_add (dvd_add (dvd_add (dvd_mul_right (5 : ℤ) _)
      (dvd_mul_of_dvd_right h5 _)) (dvd_mul_of_dvd_right (dvd_pow h5 two_ne_zero) _))
      (dvd_mul_of_dvd_left (dvd_mul_right (5 : ℤ) B) _)) (dvd_pow h5 (by norm_num))

/-- If `5^s ∣ u` with `s ≥ 1`, then `(1 + u)^(5^M) ≡ 1 + 5^M u (mod 5^(2s+M))`. -/
lemma five_pow_dvd_one_add_pow {u : ℤ} {s : ℕ} (hs : 1 ≤ s) (hu : (5 : ℤ) ^ s ∣ u) (M : ℕ) :
    (5 : ℤ) ^ (2 * s + M) ∣ (1 + u) ^ 5 ^ M - 1 - 5 ^ M * u := by
  induction M with
  | zero => simp
  | succ M ih =>
    obtain ⟨w, hw⟩ := ih
    set z := 5 ^ M * u + 5 ^ (2 * s + M) * w with hzdef
    have hz : (1 + u) ^ 5 ^ M = 1 + z := by rw [hzdef]; linear_combination hw
    obtain ⟨u', hu'⟩ := hu
    have hz' : z = 5 ^ (s + M) * (u' + 5 ^ s * w) := by rw [hzdef, hu']; ring
    have h5 : (5 : ℤ) ∣ z := (dvd_pow_self 5 (by omega)).trans ⟨_, hz'⟩
    have ha : (5 : ℤ) ^ (2 * s + 2 * M) ∣ z ^ 2 := ⟨(u' + 5 ^ s * w) ^ 2, by rw [hz']; ring⟩
    have hb : (5 : ℤ) ∣ 10 + 10 * z + 5 * z ^ 2 + z ^ 3 :=
      dvd_add (dvd_add (dvd_add ⟨2, by norm_num⟩ (h5.mul_left 10)) (dvd_mul_right 5 _))
        (dvd_pow h5 (by norm_num))
    have h2 : (5 : ℤ) ^ (2 * s + (M + 1)) ∣ z ^ 2 * (10 + 10 * z + 5 * z ^ 2 + z ^ 3) :=
      (pow_dvd_pow 5 (by omega : 2 * s + (M + 1) ≤ 2 * s + 2 * M + 1)).trans
        (by rw [pow_succ]; exact mul_dvd_mul ha hb)
    have h1 : (5 : ℤ) ^ (2 * s + (M + 1)) ∣ 5 ^ (2 * s + M + 1) * w := ⟨w, by ring⟩
    have e : (1 + u) ^ 5 ^ (M + 1) - 1 - 5 ^ (M + 1) * u =
        5 ^ (2 * s + M + 1) * w + z ^ 2 * (10 + 10 * z + 5 * z ^ 2 + z ^ 3) := by
      rw [pow_succ, pow_mul, hz, hzdef]; ring
    rw [e]
    exact dvd_add h1 h2

/-- Euler's theorem with the exponent: for `x` prime to 5, `x^(4·5^N) = 1 + 5^(N+1) a`. -/
lemma exists_pow_four_mul_five_pow {x : ℤ} (hx : ¬ (5 : ℤ) ∣ x) (N : ℕ) :
    ∃ a : ℤ, x ^ (4 * 5 ^ N) = 1 + 5 ^ (N + 1) * a := by
  have h4 : (5 : ℤ) ∣ x ^ 4 - 1 := by
    have hx0 : (x : ZMod 5) ≠ 0 := by
      intro h
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 5).1 h
      exact hx (by exact_mod_cast this)
    have key : ∀ y : ZMod 5, y ≠ 0 → y ^ 4 - 1 = 0 := by decide
    have := key _ hx0
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd (x ^ 4 - 1) 5).1 (by push_cast; exact this)
    simpa using h'
  obtain ⟨w, hw⟩ := five_pow_dvd_one_add_pow (u := x ^ 4 - 1) (s := 1) le_rfl (by simpa using h4) N
  obtain ⟨k, hk⟩ := h4
  refine ⟨k + 5 * w, ?_⟩
  rw [pow_mul]
  have e : (1 + (x ^ 4 - 1)) = x ^ 4 := by ring
  rw [e] at hw
  linear_combination hw + 5 ^ N * hk

/-- The step of the 5-adic law (proof of Theorem 20.12). For `x` prime to 5, `N + 1 ≤ k` and
`x^(4·5^N) = 1 + 5^(N+1) a`:
`f(x + 4·5^k t) ≡ f(x) + 5^k t (x^x (4 + 5 a) - 4) (mod 5^(k+N+1))`, where `f(x) = x^x - x`. -/
lemma step_five_adic {x k N t : ℕ} {a : ℤ} (hx : 1 ≤ x) (hk : N + 1 ≤ k)
    (hx5 : ¬ (5 : ℤ) ∣ x) (ha : (x : ℤ) ^ (4 * 5 ^ N) = 1 + 5 ^ (N + 1) * a) :
    (5 : ℤ) ^ (k + N + 1) ∣ (((x + 4 * 5 ^ k * t : ℕ) : ℤ) ^ (x + 4 * 5 ^ k * t) -
      (x + 4 * 5 ^ k * t : ℕ)) - ((x : ℤ) ^ x - x) -
      5 ^ k * t * ((x : ℤ) ^ x * (4 + 5 * a) - 4) := by
  obtain ⟨r, rfl⟩ : ∃ r, k = N + 1 + r := ⟨k - (N + 1), by omega⟩
  set h : ℤ := 4 * 5 ^ (N + 1 + r) * t with hh
  have hX : ((x + 4 * 5 ^ (N + 1 + r) * t : ℕ) : ℤ) = (x : ℤ) + h := by rw [hh]; push_cast; ring
  rw [hX, pow_add ((x : ℤ) + h) x]
  -- `(x + h)^x ≡ x^x (1 + h)`
  obtain ⟨c, hc⟩ := add_pow_modEq_sq (x : ℤ) h x
  have hxx : (x : ℤ) * (x : ℤ) ^ (x - 1) = (x : ℤ) ^ x := by
    rw [← pow_succ']; congr 1; omega
  have hA : ((x : ℤ) + h) ^ x = (x : ℤ) ^ x * (1 + h) + h ^ 2 * c := by
    linear_combination hc + h * hxx
  -- `((x + h)^4)^(5^N) = 1 + 5^(N+1) a'` with `a' ≡ a (mod 5^(N+r))`
  have h5h : (5 : ℤ) ∣ h := ⟨4 * 5 ^ (N + r) * t, by rw [hh]; ring⟩
  have hxh5 : ¬ (5 : ℤ) ∣ (x : ℤ) + h := fun hd => hx5 (by
    have := dvd_sub hd h5h; simpa using this)
  obtain ⟨a', ha'⟩ := exists_pow_four_mul_five_pow hxh5 N
  have hdiff : (5 : ℤ) ^ (N + 1 + r) ∣ ((x : ℤ) + h) ^ 4 - (x : ℤ) ^ 4 :=
    ⟨4 * t * (((x : ℤ) + h) ^ 3 + ((x : ℤ) + h) ^ 2 * x + ((x : ℤ) + h) * x ^ 2 + (x : ℤ) ^ 3),
      by rw [hh]; ring⟩
  obtain ⟨g0, hg0⟩ := five_pow_dvd_pow_sub_pow (by omega) hdiff N
  have hg : a' = a + 5 ^ (N + r) * g0 := by
    have e1 : (((x : ℤ) + h) ^ 4) ^ 5 ^ N = 1 + 5 ^ (N + 1) * a' := by rw [← pow_mul]; exact ha'
    have e2 : ((x : ℤ) ^ 4) ^ 5 ^ N = 1 + 5 ^ (N + 1) * a := by rw [← pow_mul]; exact ha
    rw [e1, e2] at hg0
    have e3 : (5 : ℤ) ^ (N + 1) * (a' - a - 5 ^ (N + r) * g0) = 0 := by
      linear_combination hg0
    have : a' - a - 5 ^ (N + r) * g0 = 0 :=
      (mul_eq_zero.1 e3).resolve_left (pow_ne_zero _ (by norm_num))
    linear_combination this
  -- `((x + h)^4)^(5^k) = 1 + 5^(k+1) a + 5^(k+N+1) E1`
  obtain ⟨w1, hw1⟩ := five_pow_dvd_one_add_pow (u := 5 ^ (N + 1) * a') (s := N + 1) (by omega)
    (dvd_mul_right _ _) (r + 1)
  have hY : (((x : ℤ) + h) ^ 4) ^ 5 ^ (N + 1 + r) =
      1 + 5 ^ (N + 1 + r + 1) * a + 5 ^ (N + 1 + r + N + 1) * (5 ^ r * g0 + 5 * w1) := by
    have e1 : (((x : ℤ) + h) ^ 4) ^ 5 ^ (N + 1 + r) =
        ((((x : ℤ) + h) ^ 4) ^ 5 ^ N) ^ 5 ^ (r + 1) := by
      rw [show 5 ^ (N + 1 + r) = 5 ^ N * 5 ^ (r + 1) by ring, pow_mul]
    have e2 : (((x : ℤ) + h) ^ 4) ^ 5 ^ N = 1 + 5 ^ (N + 1) * a' := by rw [← pow_mul]; exact ha'
    rw [e1, e2, hg]
    rw [hg] at hw1
    linear_combination hw1
  -- raise to the power `t`
  set E1 : ℤ := 5 ^ r * g0 + 5 * w1
  set z : ℤ := 5 ^ (N + 1 + r + 1) * a + 5 ^ (N + 1 + r + N + 1) * E1 with hzdef
  obtain ⟨c2, hc2⟩ := add_pow_modEq_sq 1 z t
  simp only [one_pow, mul_one] at hc2
  have hpow : ((x : ℤ) + h) ^ (4 * 5 ^ (N + 1 + r) * t) = (1 + z) ^ t := by
    rw [pow_mul, pow_mul, hY, hzdef]; ring
  have hz2 : z ^ 2 = 5 ^ (N + 1 + r + N + 1) * (5 ^ (r + 2) * (a + 5 ^ N * E1) ^ 2) := by
    rw [hzdef]; ring
  have hZ : (1 + z) ^ t = 1 + 5 ^ (N + 1 + r + 1) * t * a +
      5 ^ (N + 1 + r + N + 1) * (t * E1 + 5 ^ (r + 2) * (a + 5 ^ N * E1) ^ 2 * c2) := by
    rw [hz2] at hc2
    linear_combination hc2
  rw [hpow, hZ, hA]
  refine ⟨(x : ℤ) ^ x * 4 * 5 ^ (r + 1) * t ^ 2 * a + (x : ℤ) ^ x * (1 + h) *
      (t * E1 + 5 ^ (r + 2) * (a + 5 ^ N * E1) ^ 2 * c2) + 16 * 5 ^ r * t ^ 2 * c *
      (1 + 5 ^ (N + 1 + r + 1) * t * a +
        5 ^ (N + 1 + r + N + 1) * (t * E1 + 5 ^ (r + 2) * (a + 5 ^ N * E1) ^ 2 * c2)), ?_⟩
  rw [hh]; ring

lemma intCast_five_pow_eq_zero {n : ℕ} {A : ℤ} : (A : ZMod (5 ^ n)) = 0 ↔ (5 : ℤ) ^ n ∣ A := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rfl

lemma prime_five_int : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.2 (by norm_num)

lemma isCoprime_five_pow {u : ℤ} (hu : ¬ (5 : ℤ) ∣ u) (n : ℕ) : IsCoprime u ((5 : ℤ) ^ n) :=
  (((prime_five_int.irreducible).coprime_iff_not_dvd).2 hu).symm.pow_right

lemma five_pow_dvd_of_dvd_two_mul {n : ℕ} {A : ℤ} (h : (5 : ℤ) ^ n ∣ 2 * A) :
    (5 : ℤ) ^ n ∣ A :=
  ((isCoprime_five_pow (u := 2) (by norm_num) n).symm).dvd_of_dvd_mul_left h

/-- An `x ≥ 1` with `4 ∣ x` in a given class modulo `5^M` (Chinese remainder theorem). -/
lemma exists_four_dvd_modEq (M : ℕ) (u : ℤ) :
    ∃ x : ℕ, 1 ≤ x ∧ 4 ∣ x ∧ (5 : ℤ) ^ M ∣ (x : ℤ) - u := by
  have h4 : (4 : ℤ) ∣ 5 ^ M - 1 := by simpa using sub_dvd_pow_sub_pow (5 : ℤ) 1 M
  have hM : (1 : ℤ) ≤ 5 ^ M := one_le_pow₀ (by norm_num)
  set X : ℤ := u * (1 - 5 ^ M) + 4 * 5 ^ M * (|u| + 1) with hX
  have hpos : 1 ≤ X := by
    have h1 : 0 ≤ (|u| - u) * (5 ^ M - 1) := mul_nonneg (by linarith [le_abs_self u]) (by linarith)
    have h2 : 0 ≤ |u| := abs_nonneg u
    nlinarith
  refine ⟨X.toNat, by omega, ?_, ?_⟩
  · have : (4 : ℤ) ∣ X := by
      obtain ⟨q, hq⟩ := h4
      exact ⟨-u * q + 5 ^ M * (|u| + 1), by rw [hX]; linear_combination (-u) * hq⟩
    omega
  · rw [Int.toNat_of_nonneg (by omega)]
    exact ⟨-u + 4 * (|u| + 1), by rw [hX]; ring⟩

/-- The 5-adic `sqrt(-1)` with `i ≡ 3 (mod 5)` exists modulo every `5^e`. -/
lemma exists_sqrt_neg_one_five_pow (e : ℕ) :
    ∃ i : ℤ, (5 : ℤ) ^ e ∣ i ^ 2 + 1 ∧ (5 : ℤ) ∣ i - 3 := by
  obtain ⟨y, hy, hy2⟩ := exists_sq_five_pow (a := 3) (c := -1) (by norm_num) (by norm_num) e
  exact ⟨y, by simpa using hy2, hy⟩

/-- The leading coefficient of the step of the 5-adic law (proof of Theorem 20.12). Let
`x ≡ i (mod 5)`, `4 ∣ x`, and let `D = x - i` have valuation exactly `j ≥ 1` (it agrees with `c`
modulo `5^(j+1)`, and `v_5(c) = j`), with `2 j ≤ e`. Then the coefficient
`x^x (4 + 5 a) - 4` of the step, `x^(4·5^j) = 1 + 5^(j+1) a`, has valuation exactly `j`: it is
`≡ 4 (1 - i) D (mod 5^(2j))`. -/
lemma five_adic_unit {x j e : ℕ} {i c a : ℤ} (hj : 1 ≤ j) (hje : 2 * j ≤ e)
    (hi : (5 : ℤ) ^ e ∣ i ^ 2 + 1) (hi3 : (5 : ℤ) ∣ i - 3) (h4 : 4 ∣ x) (hx : 0 < x)
    (hD : (5 : ℤ) ^ (j + 1) ∣ ((x : ℤ) - i) - c) (hc : (5 : ℤ) ^ j ∣ c)
    (hc' : ¬ (5 : ℤ) ^ (j + 1) ∣ c) (ha : (x : ℤ) ^ (4 * 5 ^ j) = 1 + 5 ^ (j + 1) * a) :
    ∃ β : ℤ, (x : ℤ) ^ x * (4 + 5 * a) - 4 = 5 ^ j * β ∧ ¬ (5 : ℤ) ∣ β := by
  set D : ℤ := (x : ℤ) - i with hDdef
  obtain ⟨c', rfl⟩ := hc
  obtain ⟨k, hk⟩ := hD
  have hc'5 : ¬ (5 : ℤ) ∣ c' := fun h => hc' (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  set δ : ℤ := c' + 5 * k with hδ
  have hDδ : D = 5 ^ j * δ := by rw [hδ]; linear_combination hk
  have hδ5 : ¬ (5 : ℤ) ∣ δ := by omega
  -- work modulo `5^(2j)`
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  set N : ℕ := 5 ^ (2 * (n + 1)) with hN
  have hcast : ∀ A : ℤ, (A : ZMod N) = 0 ↔ (5 : ℤ) ^ (2 * (n + 1)) ∣ A := fun A => by
    rw [hN]; exact intCast_five_pow_eq_zero
  have hι : ((i : ℤ) : ZMod N) ^ 2 = -1 := by
    have : ((i ^ 2 + 1 : ℤ) : ZMod N) = 0 := (hcast _).2 ((pow_dvd_pow 5 hje).trans hi)
    push_cast at this; linear_combination this
  have hD2 : ((D : ℤ) : ZMod N) ^ 2 = 0 := by
    have : ((D ^ 2 : ℤ) : ZMod N) = 0 := (hcast _).2 ⟨δ ^ 2, by rw [hDδ]; ring⟩
    push_cast at this; exact this
  have hxR : ((x : ℕ) : ZMod N) = ((i : ℤ) : ZMod N) + ((D : ℤ) : ZMod N) := by
    rw [hDdef]; push_cast; ring
  obtain ⟨S, hS⟩ := two_mul_pow_self_sub_eq (R := ZMod N) hι
    (d := ((5 ^ n * δ : ℤ) : ZMod N)) (by rw [hDδ]; push_cast; ring) h4 hx hxR
  -- `5 a ≡ x^4 - 1 (mod 5^(2j))`
  have hx4 : (5 : ℤ) ^ (n + 1) ∣ (x : ℤ) ^ 4 - 1 := by
    have e : (x : ℤ) ^ 4 - 1 = (i ^ 2 + 1) * (i ^ 2 - 1) +
        D * (4 * i ^ 3 + 6 * i ^ 2 * D + 4 * i * D ^ 2 + D ^ 3) := by rw [hDdef]; ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left ((pow_dvd_pow 5 (by omega)).trans hi) _)
      (dvd_mul_of_dvd_left ⟨δ, hDδ⟩ _)
  obtain ⟨w, hw⟩ := five_pow_dvd_one_add_pow (by omega) hx4 (n + 1)
  have h5a : 5 * a = (x : ℤ) ^ 4 - 1 + 5 ^ (2 * (n + 1)) * w := by
    have e : (1 + ((x : ℤ) ^ 4 - 1)) ^ 5 ^ (n + 1) = (x : ℤ) ^ (4 * 5 ^ (n + 1)) := by
      rw [pow_mul]; ring
    rw [e, ha] at hw
    have : (5 : ℤ) ^ (n + 1) * (5 * a - ((x : ℤ) ^ 4 - 1 + 5 ^ (2 * (n + 1)) * w)) = 0 := by
      linear_combination hw
    linear_combination (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ (by norm_num))
  -- `2 B ≡ 8 (1 - i) D (mod 5^(2j))`
  set B : ℤ := (x : ℤ) ^ x * (4 + 5 * a) - 4 with hB
  have hBR : ((2 * B - 8 * (1 - i) * D : ℤ) : ZMod N) = 0 := by
    have h5aR : ((5 * a : ℤ) : ZMod N) = ((x : ℕ) : ZMod N) ^ 4 - 1 := by
      rw [h5a]; push_cast
      have : (((5 : ℤ) ^ (2 * (n + 1)) : ℤ) : ZMod N) = 0 := (hcast _).2 dvd_rfl
      push_cast at this; rw [this]; ring
    rw [hB]; push_cast at h5aR ⊢
    set ι : ZMod N := ((i : ℤ) : ZMod N)
    set DR : ZMod N := ((D : ℤ) : ZMod N)
    have hx4R : ((x : ℕ) : ZMod N) ^ 4 - 1 = -4 * ι * DR := by
      rw [hxR]
      linear_combination (ι ^ 2 - 1 + 4 * ι * DR) * hι + (6 * ι ^ 2 + 4 * ι * DR + DR ^ 2) * hD2
    have h5aR' : 5 * (a : ZMod N) = -4 * ι * DR := h5aR.trans hx4R
    have h2X : 2 * ((x : ℕ) : ZMod N) ^ x = 2 + 2 * DR := by
      linear_combination hS + 2 * hxR + ((1 - ι) + 5 * S) * hD2
    linear_combination (4 + 5 * (a : ZMod N)) * h2X + (2 + 2 * DR) * h5aR' - 8 * ι * hD2
  have hBd := (hcast _).1 hBR
  -- read off the valuation
  obtain ⟨κ, hκ⟩ := hBd
  have h2B : (5 : ℤ) ^ (n + 1) ∣ 2 * B :=
    ⟨8 * (1 - i) * δ + 5 ^ (n + 1) * κ, by linear_combination hκ + 8 * (1 - i) * hDδ⟩
  obtain ⟨β, hβ⟩ := five_pow_dvd_of_dvd_two_mul h2B
  refine ⟨β, hβ, fun h5 => ?_⟩
  have e : (5 : ℤ) ^ (n + 1) * (2 * β - 8 * ((1 - i) * δ) - 5 ^ (n + 1) * κ) = 0 := by
    linear_combination hκ - 2 * hβ + 8 * (1 - i) * hDδ
  have e' := (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ (by norm_num))
  have h1 : (5 : ℤ) ∣ (1 - i) * δ := by
    have : (5 : ℤ) ∣ 5 ^ (n + 1) * κ := dvd_mul_of_dvd_left (dvd_pow_self 5 (by omega)) _
    omega
  rcases prime_five_int.dvd_mul.1 h1 with h | h
  · omega
  · exact hδ5 h

/-- `x^x - x ≡ 3 (mod 5)` forces `x ≡ 8 (mod 20)` (Lemma 20.9), stated in `ℤ`. -/
lemma mod_twenty_of_five_dvd {x : ℕ} (hx : 1 ≤ x) (h : (5 : ℤ) ∣ ((x : ℤ) ^ x - x) - 3) :
    x % 20 = 8 := by
  have hle : x ≤ x ^ x := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ x := Nat.pow_le_pow_right hx hx
  have hcast : ((x ^ x - x : ℕ) : ℤ) = (x : ℤ) ^ x - x := by push_cast [hle]; ring
  exact lemma20_9_five hx (by omega)

/-- **Theorem 20.12**, the class `3 (mod 5)` (the 5-adic law, section 20.2.2). Let `i` be a
square root of `-1` modulo `5^e` with `i ≡ 3 (mod 5)` (it exists by
`exists_sqrt_neg_one_five_pow`), and `A = 1 - i`. A residue `v ≡ 3 (mod 5)` is a value of
`x^x - x` modulo `5^e` exactly when `v ≡ A (1 - 25 s / 2)` with `s = y^2` a square, that is
`2 v ≡ A (2 - 25 y^2)`. The proof replaces the 5-adic series by the expansion
`two_mul_pow_self_sub_eq` and Hensel's lemma by the step `step_five_adic`. -/
theorem theorem20_12_three_mod_five {e : ℕ} {i : ℤ} (hi : (5 : ℤ) ^ e ∣ i ^ 2 + 1)
    (hi3 : (5 : ℤ) ∣ i - 3) {v : ℤ} (hv : (5 : ℤ) ∣ v - 3) :
    (∃ x : ℕ, 1 ≤ x ∧ (5 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v) ↔
      ∃ y : ℤ, (5 : ℤ) ^ e ∣ 2 * v - (1 - i) * (2 - 25 * y ^ 2) := by
  have hcast : ∀ A : ℤ, (A : ZMod (5 ^ e)) = 0 ↔ (5 : ℤ) ^ e ∣ A := fun A =>
    intCast_five_pow_eq_zero
  have hι : ((i : ℤ) : ZMod (5 ^ e)) ^ 2 = -1 := by
    have : ((i ^ 2 + 1 : ℤ) : ZMod (5 ^ e)) = 0 := (hcast _).2 hi
    push_cast at this; linear_combination this
  have hA5 : ¬ (5 : ℤ) ∣ 1 - i := by omega
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact ⟨fun _ => ⟨0, by simp⟩, fun _ => ⟨1, le_rfl, by simp⟩⟩
  constructor
  · rintro ⟨x, hx, hdvd⟩
    have h20 : x % 20 = 8 := mod_twenty_of_five_dvd hx (by
      have := (dvd_pow_self (5 : ℤ) he.ne').trans hdvd; omega)
    have h4 : 4 ∣ x := by omega
    obtain ⟨δ, hδ⟩ : (5 : ℤ) ∣ (x : ℤ) - i := by omega
    obtain ⟨S, hS⟩ := two_mul_pow_self_sub_eq (R := ZMod (5 ^ e)) hι
      (D := (((x : ℤ) - i : ℤ) : ZMod (5 ^ e))) (d := ((δ : ℤ) : ZMod (5 ^ e)))
      (by rw [hδ]; push_cast; ring) h4 (by omega) (by push_cast; ring)
    -- an inverse of `1 - i` and a square root of `1 + 5 α S`
    obtain ⟨α, β, hαβ⟩ := isCoprime_five_pow hA5 e
    set σ : ℤ := ((S.val : ℕ) : ℤ)
    have hσ : ((σ : ℤ) : ZMod (5 ^ e)) = S := by simp [σ]
    obtain ⟨z, -, hz⟩ := exists_sq_five_pow (a := 1) (c := 1 + 5 * α * σ) (by norm_num)
      ⟨-(α * σ), by ring⟩ e
    refine ⟨i * δ * z, (hcast _).1 ?_⟩
    have hvR : ((v : ℤ) : ZMod (5 ^ e)) = ((x : ℕ) : ZMod (5 ^ e)) ^ x - x := by
      have := (hcast _).2 hdvd; push_cast at this; linear_combination -this
    have hαR : (α : ZMod (5 ^ e)) * (1 - i) = 1 := by
      have := (hcast (α * (1 - i) - 1)).2 ⟨-β, by linear_combination hαβ⟩
      push_cast at this; linear_combination this
    have hzR : (z : ZMod (5 ^ e)) ^ 2 = 1 + 5 * α * S := by
      have := (hcast _).2 hz; push_cast at this; rw [← hσ]; linear_combination this
    rw [hδ] at hS
    push_cast at hS ⊢
    linear_combination 2 * hvR + hS + (1 - (i : ZMod (5 ^ e))) * 25 * (δ : ZMod (5 ^ e)) ^ 2 *
      (z : ZMod (5 ^ e)) ^ 2 * hι - 25 * (δ : ZMod (5 ^ e)) ^ 2 * (1 - (i : ZMod (5 ^ e))) * hzR
      - 125 * (δ : ZMod (5 ^ e)) ^ 2 * S * hαR
  · rintro ⟨y, hy⟩
    set c : ℤ := 5 * i * y with hc
    have htarget : ((2 * v : ℤ) : ZMod (5 ^ e)) =
        (1 - (i : ZMod (5 ^ e))) * (2 + (c : ZMod (5 ^ e)) ^ 2) := by
      have := (hcast _).2 hy
      rw [hc]; push_cast at this ⊢
      linear_combination this - (1 - (i : ZMod (5 ^ e))) * 25 * (y : ZMod (5 ^ e)) ^ 2 * hι
    have he1 : (5 : ℤ) ^ e = 5 * 5 ^ (e - 1) := by rw [← pow_succ']; congr 1; omega
    by_cases hA : (5 : ℤ) ^ e ∣ c ^ 2
    · -- `c^2 ≡ 0`: take `x ≡ i (mod 5^e)`
      obtain ⟨x, hx1, hx4, κ, hκ⟩ := exists_four_dvd_modEq e i
      have hD0 : (((x : ℤ) - i : ℤ) : ZMod (5 ^ e)) = 0 := (hcast _).2 ⟨κ, hκ⟩
      obtain ⟨S, hS⟩ := two_mul_pow_self_sub_eq (R := ZMod (5 ^ e)) hι
        (D := (((x : ℤ) - i : ℤ) : ZMod (5 ^ e))) (d := ((5 ^ (e - 1) * κ : ℤ) : ZMod (5 ^ e)))
        (by rw [hκ, he1]; push_cast; ring) hx4 (by omega) (by push_cast; ring)
      have hc0 : (c : ZMod (5 ^ e)) ^ 2 = 0 := by
        have := (hcast _).2 hA; push_cast at this; exact this
      rw [hD0] at hS
      refine ⟨x, hx1, five_pow_dvd_of_dvd_two_mul ((hcast _).1 ?_)⟩
      push_cast at htarget ⊢
      linear_combination hS - htarget - (1 - (i : ZMod (5 ^ e))) * hc0
    -- the valuation `j` of `c`
    have hc0 : c ≠ 0 := by rintro h; exact hA (by rw [h]; simp)
    obtain ⟨j, m₀, hm₀, hcm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hc0) 5
      (by norm_num)
    have hcj : (5 : ℤ) ^ j ∣ c := by
      rw [← Int.natAbs_dvd_natAbs]; simp [hcm]
    have hcj' : ¬ (5 : ℤ) ^ (j + 1) ∣ c := by
      intro h
      have h' : 5 ^ (j + 1) ∣ c.natAbs := by
        have := Int.natAbs_dvd_natAbs.2 h; simpa [Int.natAbs_pow] using this
      rw [hcm, pow_succ] at h'
      exact hm₀ (Nat.dvd_of_mul_dvd_mul_left (pow_pos (by norm_num) j) h')
    have hj1 : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      apply hcj'
      simpa [hc] using dvd_mul_of_dvd_left (dvd_mul_right (5 : ℤ) i) y
    have h2j : 2 * j + 1 ≤ e := by
      by_contra h
      obtain ⟨c₁, hc₁⟩ := hcj
      exact hA ((pow_dvd_pow 5 (by omega : e ≤ 2 * j)).trans ⟨c₁ ^ 2, by rw [hc₁]; ring⟩)
    have h5c : (5 : ℤ) ∣ c := (dvd_pow_self 5 (by omega)).trans hcj
    have claim : ∀ m, 2 * j + 1 ≤ m → m ≤ e → ∃ x : ℕ, 1 ≤ x ∧ 4 ∣ x ∧
        (5 : ℤ) ^ (j + 1) ∣ ((x : ℤ) - i) - c ∧ (5 : ℤ) ^ m ∣ ((x : ℤ) ^ x - x) - v := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        intro _
        obtain ⟨x, hx1, hx4, κ, hκ⟩ := exists_four_dvd_modEq e (i + c)
        have hDc : (((x : ℤ) - i : ℤ) : ZMod (5 ^ e)) = (c : ZMod (5 ^ e)) :=
          (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by push_cast; exact ⟨-κ, by
            linear_combination -hκ - hc⟩)
        obtain ⟨S, hS⟩ := two_mul_pow_self_sub_eq (R := ZMod (5 ^ e)) hι
          (D := (((x : ℤ) - i : ℤ) : ZMod (5 ^ e))) (d := ((i * y + 5 ^ (e - 1) * κ : ℤ) :
            ZMod (5 ^ e))) (by
              have : (x : ℤ) - i = 5 * (i * y + 5 ^ (e - 1) * κ) := by
                linear_combination hκ + hc + κ * he1
              rw [this]; push_cast; ring) hx4 (by omega) (by push_cast; ring)
        rw [hDc] at hS
        set σ : ℤ := ((S.val : ℕ) : ℤ)
        have hσ : ((σ : ℤ) : ZMod (5 ^ e)) = S := by simp [σ]
        have h1 : (5 : ℤ) ^ e ∣ 2 * (((x : ℤ) ^ x - x) - v) - 5 * c ^ 2 * σ := by
          rw [← hcast]; push_cast at htarget ⊢; rw [hσ]
          linear_combination hS - htarget
        have h2 : (5 : ℤ) ^ (2 * j + 1) ∣ 5 * c ^ 2 * σ := by
          obtain ⟨c₁, hc₁⟩ := hcj
          exact ⟨c₁ ^ 2 * σ, by rw [hc₁]; ring⟩
        refine ⟨x, hx1, hx4, (pow_dvd_pow 5 (by omega : j + 1 ≤ e)).trans
          ⟨κ, by linear_combination hκ⟩,
          five_pow_dvd_of_dvd_two_mul ?_⟩
        have := dvd_add ((pow_dvd_pow 5 h2j).trans h1) h2
        simpa using this
      | succ m hm ih =>
        intro hme
        obtain ⟨x, hx1, hx4, hxc, μ, hμ⟩ := ih (by omega)
        obtain ⟨k, rfl⟩ : ∃ k, m = k + j := ⟨m - j, by omega⟩
        have hx5 : ¬ (5 : ℤ) ∣ (x : ℤ) := by
          have : (5 : ℤ) ∣ ((x : ℤ) - i) - c := (dvd_pow_self 5 (by omega)).trans hxc
          omega
        obtain ⟨a, ha⟩ := exists_pow_four_mul_five_pow hx5 j
        obtain ⟨β, hβ, hβ5⟩ := five_adic_unit hj1 (by omega) hi hi3 hx4 (by omega) hxc hcj hcj' ha
        obtain ⟨t, q, hq⟩ := exists_five_dvd_add_mul hβ5 μ
        obtain ⟨W, hW⟩ := step_five_adic (x := x) (k := k) (N := j) (t := t) hx1 (by omega) hx5 ha
        refine ⟨x + 4 * 5 ^ k * t, by omega, dvd_add hx4 ⟨5 ^ k * t, by ring⟩, ?_, ?_⟩
        · obtain ⟨g, hg⟩ := pow_dvd_pow (5 : ℤ) (by omega : j + 1 ≤ k)
          obtain ⟨u, hu⟩ := hxc
          exact ⟨u + 4 * g * t, by push_cast; linear_combination hu + 4 * (t : ℤ) * hg⟩
        · refine ⟨W + q, ?_⟩
          rw [hβ] at hW
          linear_combination hW + hμ + 5 ^ (k + j) * hq
    obtain ⟨x, hx1, -, -, h⟩ := claim e h2j le_rfl
    exact ⟨x, hx1, h⟩

/-- **Theorem 20.12** (the 5-adic law, section 20.2.2). With `i` and `A = 1 - i` as in
`theorem20_12_three_mod_five`, for `e ≥ 1` the values of `x^x - x` modulo `5^e` are the residues
`v ≢ 3 (mod 5)` and the residues `A (1 - 25 s / 2)` with `s` a square. -/
theorem theorem20_12 {e : ℕ} (he : 1 ≤ e) {i : ℤ} (hi : (5 : ℤ) ^ e ∣ i ^ 2 + 1)
    (hi3 : (5 : ℤ) ∣ i - 3) (v : ℤ) :
    (∃ x : ℕ, 1 ≤ x ∧ (5 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v) ↔
      (¬ (5 : ℤ) ∣ v - 3 ∨ ∃ y : ℤ, (5 : ℤ) ^ e ∣ 2 * v - (1 - i) * (2 - 25 * y ^ 2)) := by
  by_cases h : (5 : ℤ) ∣ v - 3
  · rw [theorem20_12_three_mod_five hi hi3 h]; simp [h]
  · exact ⟨fun _ => Or.inl h, fun _ => theorem20_12_good he h⟩

/-! ### Theorem 20.12: the count -/

/-- The squares modulo `5^k`, as residues in `[0, 5^k)`. -/
def sqMod (k : ℕ) : Finset ℕ := (Finset.range (5 ^ k)).image fun y => y ^ 2 % 5 ^ k

lemma mem_sqMod {k s : ℕ} : s ∈ sqMod k ↔ ∃ y : ℕ, y ^ 2 % 5 ^ k = s := by
  constructor
  · intro h
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine Finset.mem_image.2 ⟨y % 5 ^ k, Finset.mem_range.2 (Nat.mod_lt _ (by positivity)), ?_⟩
    rw [← Nat.pow_mod]

lemma lt_of_mem_sqMod {k s : ℕ} (h : s ∈ sqMod k) : s < 5 ^ k := by
  obtain ⟨y, rfl⟩ := mem_sqMod.1 h
  exact Nat.mod_lt _ (by positivity)

/-- A natural number whose square is `u` modulo `5^n`, from an integer one. -/
lemma exists_nat_sq_mod {n u : ℕ} (hu : u < 5 ^ n) {y : ℤ} (hy : (5 : ℤ) ^ n ∣ y ^ 2 - u) :
    ∃ z : ℕ, z ^ 2 % 5 ^ n = u := by
  refine ⟨y.natAbs, ?_⟩
  have h : u ≡ y.natAbs ^ 2 [MOD 5 ^ n] := by
    rw [Nat.modEq_iff_dvd]; push_cast; rw [sq_abs]; exact hy
  rw [← Nat.mod_eq_of_lt hu]
  exact h.symm

lemma card_filter_mod_five (m r : ℕ) (hr : r < 5) :
    ((Finset.range (5 * m)).filter fun u => u % 5 = r).card = m := by
  have : ((Finset.range (5 * m)).filter fun u => u % 5 = r) =
      (Finset.range (5 * m)).filter fun u => u ≡ r [MOD 5] := by
    refine Finset.filter_congr fun u _ => ?_
    rw [Nat.ModEq, Nat.mod_eq_of_lt hr]
  rw [this, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (by norm_num)]
  simp [Nat.mul_mod_right]

/-- The squares modulo `5^(k+2)`: the units `≡ ±1 (mod 5)` and `25` times the squares modulo
`5^k`. -/
theorem card_sqMod_add_two (k : ℕ) :
    (sqMod (k + 2)).card = 2 * 5 ^ (k + 1) + (sqMod k).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := sqMod (k + 2)) (fun s => ¬ 5 ∣ s)]
  have h5 : (5 : ℕ) ∣ 5 ^ (k + 2) := dvd_pow_self 5 (by omega)
  have hA : (sqMod (k + 2)).filter (fun s => ¬ 5 ∣ s) =
      ((Finset.range (5 * 5 ^ (k + 1))).filter fun u => u % 5 = 1) ∪
        ((Finset.range (5 * 5 ^ (k + 1))).filter fun u => u % 5 = 4) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range]
    constructor
    · rintro ⟨hs, h5s⟩
      have hlt := lt_of_mem_sqMod hs
      obtain ⟨y, rfl⟩ := mem_sqMod.1 hs
      have hmod : y ^ 2 % 5 ^ (k + 2) % 5 = y ^ 2 % 5 := Nat.mod_mod_of_dvd _ h5
      have hy : y ^ 2 % 5 = (y % 5) ^ 2 % 5 := Nat.pow_mod _ _ _
      have hlt' : y ^ 2 % 5 ^ (k + 2) < 5 * 5 ^ (k + 1) := by rw [← pow_succ']; exact hlt
      have key : y ^ 2 % 5 ^ (k + 2) % 5 = (y % 5) ^ 2 % 5 := by rw [hmod, hy]
      have : y % 5 < 5 := Nat.mod_lt _ (by norm_num)
      set r := y % 5
      interval_cases r <;> norm_num at key <;> omega
    · rintro (⟨hs, h1⟩ | ⟨hs, h4⟩)
      · refine ⟨mem_sqMod.2 ?_, by omega⟩
        obtain ⟨z, -, hz⟩ := exists_sq_five_pow (a := 1) (c := (s : ℤ)) (by norm_num)
          (by push_cast; omega) (k + 2)
        exact exists_nat_sq_mod (by rw [pow_succ']; exact hs) hz
      · refine ⟨mem_sqMod.2 ?_, by omega⟩
        obtain ⟨z, -, hz⟩ := exists_sq_five_pow (a := 2) (c := (s : ℤ)) (by norm_num)
          (by push_cast; omega) (k + 2)
        exact exists_nat_sq_mod (by rw [pow_succ']; exact hs) hz
  have hB : (sqMod (k + 2)).filter (fun s => ¬ ¬ 5 ∣ s) = (sqMod k).image (25 * ·) := by
    ext s
    simp only [Finset.mem_filter, not_not, Finset.mem_image]
    constructor
    · rintro ⟨hs, h5s⟩
      obtain ⟨y, rfl⟩ := mem_sqMod.1 hs
      have hy5 : 5 ∣ y := by
        have : 5 ∣ y ^ 2 := by
          have := (Nat.dvd_mod_iff h5).1 h5s; exact this
        exact Nat.prime_five.dvd_of_dvd_pow this
      obtain ⟨z, rfl⟩ := hy5
      refine ⟨z ^ 2 % 5 ^ k, mem_sqMod.2 ⟨z, rfl⟩, ?_⟩
      rw [show (5 * z) ^ 2 = 25 * z ^ 2 by ring, show 5 ^ (k + 2) = 25 * 5 ^ k by ring,
        Nat.mul_mod_mul_left]
    · rintro ⟨s', hs', rfl⟩
      obtain ⟨z, rfl⟩ := mem_sqMod.1 hs'
      refine ⟨mem_sqMod.2 ⟨5 * z, ?_⟩, dvd_mul_of_dvd_left (by norm_num) _⟩
      rw [show (5 * z) ^ 2 = 25 * z ^ 2 by ring, show 5 ^ (k + 2) = 25 * 5 ^ k by ring,
        Nat.mul_mod_mul_left]
  rw [hA, hB, Finset.card_union_of_disjoint, card_filter_mod_five _ _ (by norm_num),
    card_filter_mod_five _ _ (by norm_num),
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  · ring
  · rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega

/-- The number of squares modulo `5^k` (section 20.2.2): `(5^(k+1) + 7)/12` for even `k` and
`(5^(k+1) + 11)/12` for odd `k`. -/
theorem card_sqMod (k : ℕ) :
    12 * (sqMod k).card = 5 ^ (k + 1) + if Even k then 7 else 11 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · decide
    · decide
    · rw [card_sqMod_add_two, mul_add, ih k (by omega)]
      have : Even (k + 2) ↔ Even k := by simp [Nat.even_add]
      simp only [this]
      split_ifs <;> ring

open Classical in
/-- **Theorem 20.12**, the count (section 20.2.2). For `e ≥ 2` the class `3 (mod 5)` holds
exactly `sq(e - 2)` elements of `T(5^e)`, `sq(k)` the number of squares modulo `5^k`. -/
theorem theorem20_12_card {e : ℕ} (he : 2 ≤ e) :
    ((Finset.range (5 ^ e)).filter fun v : ℕ => v % 5 = 3 ∧
        ∃ x : ℕ, 1 ≤ x ∧ (5 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - (v : ℤ)).card =
      (sqMod (e - 2)).card := by
  obtain ⟨i, hi, hi3⟩ := exists_sqrt_neg_one_five_pow e
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 2 := ⟨e - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  set A : ℤ := 1 - i with hA
  set H : ℤ := (((5 ^ (n + 2) + 1) / 2 : ℕ) : ℤ) with hH
  have hM : (0 : ℤ) < 5 ^ (n + 2) := by positivity
  have h2H : (5 : ℤ) ^ (n + 2) ∣ 2 * H - 1 := by
    have hodd : (5 ^ (n + 2) + 1) % 2 = 0 := by
      have : Odd (5 ^ (n + 2)) := Odd.pow (by decide)
      obtain ⟨t, ht⟩ := this; omega
    refine ⟨1, ?_⟩
    rw [hH]; push_cast
    have : ((5 ^ (n + 2) + 1) / 2 : ℕ) * 2 = 5 ^ (n + 2) + 1 := Nat.div_mul_cancel
      (Nat.dvd_of_mod_eq_zero hodd)
    have : (((5 ^ (n + 2) + 1) / 2 : ℕ) : ℤ) * 2 = 5 ^ (n + 2) + 1 := by exact_mod_cast this
    push_cast at this
    linarith
  have hA5 : ¬ (5 : ℤ) ∣ A := by omega
  -- the map `s ↦ A (1 - 25 s / 2) mod 5^e`
  set V : ℕ → ℕ := fun s => ((A * (2 - 25 * s) * H) % 5 ^ (n + 2)).toNat with hV
  have hVz : ∀ s, (V s : ℤ) = (A * (2 - 25 * s) * H) % 5 ^ (n + 2) := fun s =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hM.ne')
  have hV2 : ∀ s, (5 : ℤ) ^ (n + 2) ∣ 2 * V s - A * (2 - 25 * s) := by
    intro s
    rw [hVz]
    obtain ⟨m, hm⟩ := h2H
    refine ⟨-2 * ((A * (2 - 25 * s) * H) / 5 ^ (n + 2)) + A * (2 - 25 * s) * m, ?_⟩
    have := Int.emod_add_mul_ediv (A * (2 - 25 * s) * H) (5 ^ (n + 2))
    linear_combination 2 * this + A * (2 - 25 * (s : ℤ)) * hm
  have h25 : (5 : ℤ) ^ (n + 2) = 25 * 5 ^ n := by ring
  have hsq : ∀ y : ℕ, (5 : ℤ) ^ n ∣ ((y ^ 2 % 5 ^ n : ℕ) : ℤ) - (y : ℤ) ^ 2 := by
    intro y
    have := Nat.modEq_iff_dvd.1 (Nat.mod_modEq (y ^ 2) (5 ^ n)).symm
    push_cast at this ⊢
    exact this
  have hlt : ∀ s, (V s : ℤ) < 5 ^ (n + 2) := fun s => by rw [hVz]; exact Int.emod_lt_of_pos _ hM
  symm
  refine Finset.card_bij (fun s _ => V s) ?_ ?_ ?_
  · -- `V s` lies in the class `3 (mod 5)` and is a value
    intro s hs
    obtain ⟨y, rfl⟩ := mem_sqMod.1 hs
    have h5V : (5 : ℤ) ∣ 2 * V (y ^ 2 % 5 ^ n) - A * (2 - 25 * (y ^ 2 % 5 ^ n : ℕ)) :=
      (dvd_pow_self 5 (by omega)).trans (hV2 _)
    have hlin : (5 : ℤ) ∣ A * (2 - 25 * ((y ^ 2 % 5 ^ n : ℕ) : ℤ)) - 2 * A :=
      ⟨-5 * A * ((y ^ 2 % 5 ^ n : ℕ) : ℤ), by ring⟩
    have hV3 : V (y ^ 2 % 5 ^ n) % 5 = 3 := by
      have : (V (y ^ 2 % 5 ^ n) : ℤ) % 5 = 3 := by omega
      omega
    have hlt' := hlt (y ^ 2 % 5 ^ n)
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by exact_mod_cast hlt'), hV3, ?_⟩
    refine (theorem20_12_three_mod_five (v := (V (y ^ 2 % 5 ^ n) : ℤ)) hi hi3
      (by omega)).2 ⟨y, ?_⟩
    obtain ⟨m, hm⟩ := hsq y
    obtain ⟨m', hm'⟩ := hV2 (y ^ 2 % 5 ^ n)
    refine ⟨m' - A * m, ?_⟩
    rw [h25] at hm' ⊢
    linear_combination hm' - 25 * A * hm
  · -- injective
    intro s hs s' hs' hss
    have h1 := hV2 s
    have h2 := hV2 s'
    rw [hss] at h1
    have hd : (5 : ℤ) ^ (n + 2) ∣ 25 * (((s : ℤ) - s') * A) := by
      obtain ⟨a, ha⟩ := h1
      obtain ⟨c, hc⟩ := h2
      exact ⟨a - c, by linear_combination ha - hc⟩
    rw [h25] at hd
    have hd' : (5 : ℤ) ^ n ∣ ((s : ℤ) - s') * A :=
      (mul_dvd_mul_iff_left (by norm_num : (25 : ℤ) ≠ 0)).1 hd
    have hd'' : (5 : ℤ) ^ n ∣ (s : ℤ) - s' :=
      ((isCoprime_five_pow hA5 n).symm).dvd_of_dvd_mul_right hd'
    have hmod : s' ≡ s [MOD 5 ^ n] := Nat.modEq_iff_dvd.2 (by push_cast; exact hd'')
    exact (hmod.eq_of_lt_of_lt (lt_of_mem_sqMod hs') (lt_of_mem_sqMod hs)).symm
  · -- surjective
    intro v hv
    obtain ⟨hvlt, hv3, hx⟩ := Finset.mem_filter.1 hv
    rw [Finset.mem_range] at hvlt
    obtain ⟨y, hy⟩ := (theorem20_12_three_mod_five hi hi3 (by omega)).1 hx
    refine ⟨y.natAbs ^ 2 % 5 ^ n, mem_sqMod.2 ⟨_, rfl⟩, ?_⟩
    obtain ⟨m, hm⟩ := hsq y.natAbs
    rw [Int.natCast_natAbs, sq_abs] at hm
    obtain ⟨m', hm'⟩ := hV2 (y.natAbs ^ 2 % 5 ^ n)
    obtain ⟨m'', hm''⟩ := hy
    have hd : (5 : ℤ) ^ (n + 2) ∣ 2 * ((V (y.natAbs ^ 2 % 5 ^ n) : ℤ) - v) := by
      refine ⟨m' - m'' - A * m, ?_⟩
      rw [h25] at hm' hm'' ⊢
      linear_combination hm' - hm'' - 25 * A * hm
    have hd2 := five_pow_dvd_of_dvd_two_mul hd
    have hmod : v ≡ V (y.natAbs ^ 2 % 5 ^ n) [MOD 5 ^ (n + 2)] :=
      Nat.modEq_iff_dvd.2 (by push_cast; exact hd2)
    have hlt' := hlt (y.natAbs ^ 2 % 5 ^ n)
    exact (hmod.eq_of_lt_of_lt hvlt (by exact_mod_cast hlt')).symm

open Classical in
/-- **Theorem 20.12**, the size of `T(5^e)`: for `e ≥ 2` it has `4 · 5^(e-1) + sq(e - 2)`
elements, so its density tends to `4/5 + 1/60 = 49/60`. -/
theorem theorem20_12_card_T {e : ℕ} (he : 2 ≤ e) :
    ((Finset.range (5 ^ e)).filter fun v : ℕ =>
        ∃ x : ℕ, 1 ≤ x ∧ (5 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - (v : ℤ)).card =
      4 * 5 ^ (e - 1) + (sqMod (e - 2)).card := by
  set T := (Finset.range (5 ^ e)).filter fun v : ℕ =>
    ∃ x : ℕ, 1 ≤ x ∧ (5 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - (v : ℤ)
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (fun v => v % 5 = 3)
  have h3 : T.filter (fun v => v % 5 = 3) = (Finset.range (5 ^ e)).filter fun v : ℕ =>
      v % 5 = 3 ∧ ∃ x : ℕ, 1 ≤ x ∧ (5 : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - (v : ℤ) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun v _ => and_comm
  have hn3 : T.filter (fun v => ¬ v % 5 = 3) =
      (Finset.range (5 * 5 ^ (e - 1))).filter fun v => ¬ v % 5 = 3 := by
    rw [Finset.filter_filter, ← pow_succ', show e - 1 + 1 = e by omega]
    refine Finset.filter_congr fun v _ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    exact theorem20_12_good (by omega) (by omega)
  have hrest := Finset.card_filter_add_card_filter_not
    (s := Finset.range (5 * 5 ^ (e - 1))) (fun v => v % 5 = 3)
  rw [card_filter_mod_five _ _ (by norm_num), Finset.card_range] at hrest
  rw [h3, hn3, theorem20_12_card he] at hsplit
  omega

end Munchausen
