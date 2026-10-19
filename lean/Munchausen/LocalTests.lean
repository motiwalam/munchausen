import Munchausen.ShortEquations

/-!
# Local tests and small families (sections 11.3, 12.3, 16.2.2 and 19.1.1)

Section 11.3: the families `(a, 0, x)` with `a` even are covered by the prime 2 under `0^0 = 1`.
Section 12.3: `(x, 0, 0)` and `(x, 0, 1)` are solutions in base `-x^((x-1)/2)` under `0^0 = 0`.
Lemma 20.21: elementary exclusions for `b (b + x) = x^n + c` with `c = 3` and `c = 25`.

Section 19.1.1: a root of a polynomial modulo `q₁ q₂` with coprime factors is the same as a root
modulo `q₁` and a root modulo `q₂`, and a root modulo `p^e` reduces to a root modulo `p^f` for
`f ≤ e`. So the only useful moduli are powers of single primes.

Section 16.2: the equation `b (b + x) = x^x + 1` holds exactly when
`f(x) = 4 x^x + x^2 + 4` is the square `(2 b + x)^2`. A prime `p` excludes `x` when `f(x)` is
not a square modulo `p`. Proposition 16.8 shows that no finite set of primes excludes every
`x > 7`.
-/

namespace Munchausen

/-- **Proposition 16.8 (b)** (section 16.2.2). If `x ≡ 1 (mod p - 1)`, then
`f(x) = 4 x^x + x^2 + 4` is a square modulo the prime `p`: it is `(x + 2)^2` if `p ∤ x`, and
`2^2` if `p ∣ x`. -/
theorem prop16_8_b {p x : ℕ} [Fact p.Prime] (hx1 : 1 ≤ x) (hx : x ≡ 1 [MOD p - 1]) :
    IsSquare ((4 * x ^ x + x ^ 2 + 4 : ℕ) : ZMod p) := by
  obtain ⟨k, hk⟩ : (p - 1) ∣ x - 1 := (Nat.modEq_iff_dvd' hx1).1 hx.symm
  push_cast
  by_cases hu : (x : ZMod p) = 0
  · rw [hu, zero_pow (by omega), zero_pow two_ne_zero]
    exact ⟨2, by ring⟩
  · have hxx : (x : ZMod p) ^ x = x := by
      have e : x = 1 + (p - 1) * k := by omega
      calc (x : ZMod p) ^ x = (x : ZMod p) ^ (1 + (p - 1) * k) := by rw [← e]
        _ = x := by rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hu]; simp
    rw [hxx]
    exact ⟨(x : ZMod p) + 2, by ring⟩

/-- For odd `x` and a unit `u` with `u^2 = ±1`, `u^x = ±u`. -/
lemma pow_odd_eq {R : Type*} [CommRing R] {u : R} (hu : u ^ 2 = 1 ∨ u ^ 2 = -1) {x : ℕ}
    (hx : Odd x) : u ^ x = u ∨ u ^ x = -u := by
  obtain ⟨k, rfl⟩ := hx
  have e : u ^ (2 * k + 1) = u * (u ^ 2) ^ k := by ring
  rcases hu with h | h
  · left; rw [e, h, one_pow, mul_one]
  · rw [e, h]
    rcases neg_one_pow_eq_or R k with h' | h'
    · left; rw [h', mul_one]
    · right; rw [h', mul_neg_one]

/-- **Proposition 16.8 (a)** (section 16.2.2). The primes 3 and 5 never exclude an odd `x`:
`f(x)` is a square modulo 3 and modulo 5, namely `(x ± 2)^2` or `2^2`. -/
theorem prop16_8_a {p x : ℕ} (hp : p = 3 ∨ p = 5) (hx : Odd x) :
    IsSquare ((4 * x ^ x + x ^ 2 + 4 : ℕ) : ZMod p) := by
  have hcheck : ∀ u : ZMod p, u ≠ 0 → u ^ 2 = 1 ∨ u ^ 2 = -1 := by
    rcases hp with rfl | rfl <;> decide
  push_cast
  by_cases hu : (x : ZMod p) = 0
  · rw [hu, zero_pow (Nat.pos_of_ne_zero (by rintro rfl; simp at hx)).ne',
      zero_pow two_ne_zero]
    exact ⟨2, by ring⟩
  · rcases pow_odd_eq (hcheck _ hu) hx with h | h <;> rw [h]
    · exact ⟨(x : ZMod p) + 2, by ring⟩
    · exact ⟨(x : ZMod p) - 2, by ring⟩

/-- **Proposition 16.8 (b)**, for a finite set of primes (section 16.2.2). For every finite set
`S` of primes and every `N`, some `x > N` passes the test at every `p ∈ S`. So no finite set of
congruences proves that `b (b + x) = x^x + 1` has no solution with `x > 7`. -/
theorem prop16_8_finite (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    ∃ x, N < x ∧ ∀ p ∈ S, ∀ _ : Fact p.Prime,
      IsSquare ((4 * x ^ x + x ^ 2 + 4 : ℕ) : ZMod p) := by
  set L := ∏ p ∈ S, (p - 1)
  have hL : 0 < L := Finset.prod_pos fun p hp => by have := (hS p hp).two_le; omega
  have hNL : N + 1 ≤ L * (N + 1) := Nat.le_mul_of_pos_left _ hL
  refine ⟨1 + L * (N + 1), by omega, fun p hp _ => prop16_8_b (by omega) ?_⟩
  have hdvd : p - 1 ∣ L := Finset.dvd_prod_of_mem _ hp
  refine ((Nat.modEq_iff_dvd' (by omega)).2 ?_).symm
  rw [Nat.add_sub_cancel_left]
  exact dvd_mul_of_dvd_left hdvd (N + 1)

/-! ### Section 19.1.1: only prime powers add anything -/

open Polynomial

/-- A root modulo `q`, in the form of Proposition 11.1, is an integer `r` with `q ∣ Q(r)`. -/
lemma exists_root_zmod_iff (q : ℕ) (Q : ℤ[X]) :
    (∃ r : ZMod q, (Q.map (Int.castRingHom (ZMod q))).eval r = 0) ↔
      ∃ r : ℤ, (q : ℤ) ∣ Q.eval r := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(r.cast : ℤ), ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← eval_map_intCast, ZMod.intCast_zmod_cast, hr]
  · rintro ⟨r, hr⟩
    refine ⟨(r : ZMod q), ?_⟩
    rw [eval_map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hr

/-- **Section 19.1.1**, the Chinese remainder theorem. For coprime `q₁` and `q₂`, a polynomial
has a root modulo `q₁ q₂` exactly when it has a root modulo `q₁` and a root modulo `q₂`. -/
theorem exists_root_mod_mul_iff {q₁ q₂ : ℕ} (h : q₁.Coprime q₂) (Q : ℤ[X]) :
    (∃ r : ZMod (q₁ * q₂), (Q.map (Int.castRingHom _)).eval r = 0) ↔
      (∃ r : ZMod q₁, (Q.map (Int.castRingHom _)).eval r = 0) ∧
        ∃ r : ZMod q₂, (Q.map (Int.castRingHom _)).eval r = 0 := by
  simp only [exists_root_zmod_iff]
  push_cast
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨⟨r, (dvd_mul_right _ _).trans hr⟩, ⟨r, (dvd_mul_left _ _).trans hr⟩⟩
  · rintro ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩⟩
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
    set k := r₁ + q₁ * u * (r₂ - r₁)
    have hk₁ : (q₁ : ℤ) ∣ Q.eval k := by
      have := sub_dvd_eval_sub k r₁ Q
      have h' : (q₁ : ℤ) ∣ k - r₁ := ⟨u * (r₂ - r₁), by simp only [k]; ring⟩
      have := dvd_add (h'.trans this) h₁
      rwa [sub_add_cancel] at this
    have hk₂ : (q₂ : ℤ) ∣ Q.eval k := by
      have := sub_dvd_eval_sub k r₂ Q
      have h' : (q₂ : ℤ) ∣ k - r₂ :=
        ⟨v * (r₁ - r₂), by simp only [k]; linear_combination (r₂ - r₁) * huv⟩
      have := dvd_add (h'.trans this) h₂
      rwa [sub_add_cancel] at this
    exact ⟨k, (Nat.isCoprime_iff_coprime.2 h).mul_dvd hk₁ hk₂⟩

/-- **Section 19.1.1**, prime powers. A root modulo `q` is a root modulo every divisor of `q`;
in particular a root modulo `p^e` is a root modulo `p^f` for `f ≤ e`. -/
theorem exists_root_mod_of_dvd {q q' : ℕ} (hq : q' ∣ q) (Q : ℤ[X])
    (h : ∃ r : ZMod q, (Q.map (Int.castRingHom _)).eval r = 0) :
    ∃ r : ZMod q', (Q.map (Int.castRingHom _)).eval r = 0 := by
  rw [exists_root_zmod_iff] at h ⊢
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (Int.natCast_dvd_natCast.2 hq).trans hr⟩

/-! ### Section 11.3: the families `(a, 0, x)` with `a` even -/

/-- **Section 11.3**, the covered families `(2, 0, x)`, `(4, 0, x)`, `(6, 0, x)`. Under
`0^0 = 1`, a string `(a, 0, x)` with `a` even and `x ≥ 1` is never a solution: `Q_s` is
always odd. -/
theorem not_isSolution_even_zero {a b x : ℕ} (ha : Even a) (ha1 : 1 ≤ a) (hx : 1 ≤ x) :
    ¬ IsSolution b 1 [a, 0, x] := by
  intro hs
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one, w_zero, zero_mul, w_one_eq_pow] at heq
  obtain ⟨k, rfl⟩ := ha
  have h1 : (k + k) * b ^ (1 + 1) % 2 = 0 := by
    rw [show k + k = 2 * k by ring, mul_assoc, Nat.mul_mod_right]
  have h2 : 2 ∣ (k + k) ^ (k + k) := dvd_pow ⟨k, by ring⟩ (by omega)
  have h3 := pow_self_modEq_two x hx
  unfold Nat.ModEq at h3
  omega

/-! ### Section 12.3: the family `(x, 0, 0)` in a negative base -/

/-- **Section 12.3**, the family `(x, 0, 0)`. Under `0^0 = 0`, if `B^2 = x^(x-1)` and `x < B`,
then `(x, 0, 0)` and `(x, 0, 1)` are solutions in base `-B`. -/
theorem isNegSolution_x_0_0 {x B : ℕ} (hx : 1 ≤ x) (hB : B ^ 2 = x ^ (x - 1)) (hxB : x < B) :
    IsNegSolution B 0 [x, 0, 0] ∧ IsNegSolution B 0 [x, 0, 1] := by
  have hxx : (x : ℤ) * (B : ℤ) ^ 2 = (x : ℤ) ^ x := by
    have : x * B ^ 2 = x ^ x := by rw [hB, ← pow_succ']; congr 1; omega
    exact_mod_cast this
  have hw : w 0 x = x ^ x := w_of_ne_zero 0 (by omega)
  constructor
  · refine ⟨fun d hd => ?_, by simp, by simp; omega, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega
    · simp only [P_cons, P_nil, List.length_cons, List.length_nil, Fs_cons, Fs_nil, w_zero, hw]
      push_cast
      linear_combination hxx
  · refine ⟨fun d hd => ?_, by simp, by simp; omega, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega
    · simp only [P_cons, P_nil, List.length_cons, List.length_nil, Fs_cons, Fs_nil, w_zero, hw,
        w_one]
      push_cast
      linear_combination hxx

/-- **Section 12.3**, odd `x ≥ 5`: `(x, 0, 0)` and `(x, 0, 1)` are solutions in base
`-x^((x-1)/2)` under `0^0 = 0`. -/
theorem isNegSolution_x_0_0_odd {x : ℕ} (hx : Odd x) (hx5 : 5 ≤ x) :
    IsNegSolution (x ^ ((x - 1) / 2)) 0 [x, 0, 0] ∧
      IsNegSolution (x ^ ((x - 1) / 2)) 0 [x, 0, 1] := by
  obtain ⟨k, rfl⟩ := hx
  refine isNegSolution_x_0_0 (by omega) ?_ ?_
  · rw [← pow_mul]; congr 1; omega
  · calc 2 * k + 1 < (2 * k + 1) ^ 2 := by nlinarith
      _ ≤ (2 * k + 1) ^ ((2 * k + 1 - 1) / 2) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **Section 12.3**, square `x = y^2 ≥ 4`: `(x, 0, 0)` and `(x, 0, 1)` are solutions in base
`-y^(x-1)` under `0^0 = 0`; for `x = 4` this is base -8. -/
theorem isNegSolution_x_0_0_sq {y : ℕ} (hy : 2 ≤ y) :
    IsNegSolution (y ^ (y ^ 2 - 1)) 0 [y ^ 2, 0, 0] ∧
      IsNegSolution (y ^ (y ^ 2 - 1)) 0 [y ^ 2, 0, 1] := by
  refine isNegSolution_x_0_0 (Nat.one_le_pow _ _ (by omega)) ?_ ?_
  · rw [← pow_mul, ← pow_mul, mul_comm]
  · have h4 : 4 ≤ y ^ 2 := by nlinarith
    calc y ^ 2 < y ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      _ ≤ y ^ (y ^ 2 - 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-! ### Lemma 20.21: `b (b + x) = x^n + 3` and `x^n + 25` -/

/-- If `0 < D < 4 Y + 1`, then `4 Y^2 + D` is not a square. -/
lemma not_sq_between' {U Y D : ℕ} (hD : 0 < D) (hDY : D < 4 * Y + 1) :
    U ^ 2 ≠ 4 * Y ^ 2 + D := by
  intro h
  rcases Nat.lt_or_ge U (2 * Y + 1) with hU | hU
  · have : U ≤ 2 * Y := by omega
    nlinarith
  · nlinarith

/-- **Lemma 20.21 (a)** (section 20.4.1). If `x^n = Y^2` (`n` even, or `x` a square) and
`x^2 + 4 c < 4 Y + 1`, then `b (b + x) = x^n + c` has no solution with `c ≥ 1`. -/
theorem lemma20_21_a {b x n c Y : ℕ} (hc : 1 ≤ c) (hY : x ^ n = Y ^ 2)
    (h : x ^ 2 + 4 * c < 4 * Y + 1) : b * (b + x) ≠ x ^ n + c := by
  intro heq
  have hsq : (2 * b + x) ^ 2 = 4 * Y ^ 2 + (x ^ 2 + 4 * c) := by rw [← hY]; nlinarith
  exact not_sq_between' (by omega) h hsq

/-- **Lemma 20.21 (a)** for `c = 3` and `c = 25` with `n ≥ 4` even: no solution for `x ≥ 2`
(`c = 3`) and for `x ≥ 6` (`c = 25`). -/
theorem lemma20_21_a_even {b x n c : ℕ} (hc : c = 3 ∧ 2 ≤ x ∨ c = 25 ∧ 6 ≤ x) (hn : 4 ≤ n)
    (heven : Even n) : b * (b + x) ≠ x ^ n + c := by
  obtain ⟨k, rfl⟩ := heven
  have hx : 2 ≤ x := by omega
  have hY : x ^ 2 ≤ x ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  refine lemma20_21_a (Y := x ^ k) (by omega) (by ring) ?_
  rcases hc with ⟨rfl, -⟩ | ⟨rfl, h6⟩ <;> nlinarith

/-- The exception of Lemma 20.21 (a): `(x, n, b) = (3, 6, 26)` solves `b (b + x) = x^n + 25`. -/
example : 26 * (26 + 3) = 3 ^ 6 + 25 := by norm_num

/-- **Lemma 20.21 (b)** (section 20.4.1), the prime 3. `b (b + x) = x^n + 3` with `n ≥ 2` has no
solution with `3 ∣ x`. -/
theorem lemma20_21_b_three {b x n : ℕ} (hn : 2 ≤ n) (hx : 3 ∣ x) : b * (b + x) ≠ x ^ n + 3 := by
  intro h
  have h9 : 9 ∣ x ^ n := (pow_dvd_pow_of_dvd hx 2).trans (pow_dvd_pow _ hn) |>
    fun h => by simpa using h
  have hcast := congrArg (fun k : ℕ => (k : ZMod 9)) h
  push_cast at hcast
  have hz : (x : ZMod 9) ^ n = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact h9
  rw [hz] at hcast
  have hx3 : (x : ZMod 9) = 0 ∨ (x : ZMod 9) = 3 ∨ (x : ZMod 9) = 6 := by
    rw [← ZMod.natCast_mod]
    have : x % 9 = 0 ∨ x % 9 = 3 ∨ x % 9 = 6 := by omega
    rcases this with h | h | h <;> simp [h]
  generalize (b : ZMod 9) = B at hcast
  generalize (x : ZMod 9) = X at hcast hx3
  revert B X
  decide

/-- **Lemma 20.21 (b)** (section 20.4.1), even `x`. `b (b + x) = x^n + 3` with `n ≥ 2` and `x`
even needs `x ≡ 2 (mod 4)`. -/
theorem lemma20_21_b_even {b x n : ℕ} (hn : 2 ≤ n) (hx : x % 4 = 0) :
    b * (b + x) ≠ x ^ n + 3 := by
  intro h
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
  have hV : (b + y) ^ 2 = (2 * y) ^ n + y ^ 2 + 3 := by nlinarith
  have h16 : 16 ∣ (2 * y) ^ n := by
    have h4 : 4 ∣ 2 * y := ⟨y / 2, by omega⟩
    have : 16 ∣ (2 * y) ^ 2 := by simpa using pow_dvd_pow_of_dvd h4 2
    exact this.trans (pow_dvd_pow _ hn)
  have hcast := congrArg (fun k : ℕ => (k : ZMod 16)) hV
  push_cast at hcast
  have hz : ((2 * y : ℕ) : ZMod 16) ^ n = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact h16
  push_cast at hz
  rw [hz] at hcast
  have hy : (y : ZMod 16) ∈ ({0, 2, 4, 6, 8, 10, 12, 14} : Finset (ZMod 16)) := by
    rw [← ZMod.natCast_mod]
    have : y % 16 = 0 ∨ y % 16 = 2 ∨ y % 16 = 4 ∨ y % 16 = 6 ∨ y % 16 = 8 ∨ y % 16 = 10 ∨
      y % 16 = 12 ∨ y % 16 = 14 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> simp [h]
  generalize (b : ZMod 16) = B at hcast
  generalize (y : ZMod 16) = Y at hcast hy
  revert B Y
  decide

/-- **Lemma 20.21 (c)** (section 20.4.1), even `x`. `b (b + x) = x^n + 25` with `n ≥ 2` and `x`
even needs `x ≡ 0 (mod 8)`. -/
theorem lemma20_21_c_even {b x n : ℕ} (hn : 2 ≤ n) (hx : x % 2 = 0) (hx8 : x % 8 ≠ 0) :
    b * (b + x) ≠ x ^ n + 25 := by
  intro h
  obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
  have hV : (b + y) ^ 2 = (2 * y) ^ n + y ^ 2 + 25 := by nlinarith
  have h4 : 4 ∣ (2 * y) ^ n := (pow_dvd_pow_of_dvd (dvd_mul_right 2 y) 2).trans
    (pow_dvd_pow _ hn) |> fun h => by simpa [mul_pow] using h
  by_cases hy : y % 2 = 1
  · -- `x ≡ 2 (mod 4)`: `V^2 ≡ 2 (mod 4)`
    have hcast := congrArg (fun k : ℕ => (k : ZMod 4)) hV
    push_cast at hcast
    have hz : ((2 * y : ℕ) : ZMod 4) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact h4
    push_cast at hz
    rw [hz] at hcast
    have hy' : (y : ZMod 4) = 1 ∨ (y : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod]
      have : y % 4 = 1 ∨ y % 4 = 3 := by omega
      rcases this with h | h <;> simp [h]
    generalize (b : ZMod 4) = B at hcast
    generalize (y : ZMod 4) = Y at hcast hy'
    revert B Y
    decide
  · -- `x ≡ 4 (mod 8)`: `V^2 ≡ 5 (mod 8)`
    have h8 : 8 ∣ (2 * y) ^ n := by
      have h4' : 4 ∣ 2 * y := ⟨y / 2, by omega⟩
      have : 16 ∣ (2 * y) ^ 2 := by simpa using pow_dvd_pow_of_dvd h4' 2
      exact (Dvd.dvd.trans (by norm_num : 8 ∣ 16) this).trans (pow_dvd_pow _ hn)
    have hcast := congrArg (fun k : ℕ => (k : ZMod 8)) hV
    push_cast at hcast
    have hz : ((2 * y : ℕ) : ZMod 8) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]; exact h8
    push_cast at hz
    rw [hz] at hcast
    have hy' : (y : ZMod 8) = 2 ∨ (y : ZMod 8) = 6 := by
      rw [← ZMod.natCast_mod]
      have : y % 8 = 2 ∨ y % 8 = 6 := by omega
      rcases this with h | h <;> simp [h]
    generalize (b : ZMod 8) = B at hcast
    generalize (y : ZMod 8) = Y at hcast hy'
    revert B Y
    decide

/-- **Lemma 20.21 (c)** (section 20.4.1), the prime 5. If `b (b + x) = x^n + 25` with `n ≥ 1`
and `5 ∣ x`, then `5 ∣ b`. -/
theorem lemma20_21_c_five {b x n : ℕ} (hn : 1 ≤ n) (hx : 5 ∣ x) (h : b * (b + x) = x ^ n + 25) :
    5 ∣ b := by
  have h25 : (25 : ZMod 5) = 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcast := congrArg (fun k : ℕ => (k : ZMod 5)) h
  push_cast at hcast
  have hx0 : (x : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff x 5).2 hx
  rw [hx0, zero_pow (by omega), add_zero, zero_add,
    h25, mul_self_eq_zero] at hcast
  exact (ZMod.natCast_eq_zero_iff b 5).1 hcast

/-- **Lemma 20.21 (d)** (section 20.4.1), `n = 2`. `b (b + x) = x^2 + 3` has no solution, and
every solution of `b (b + x) = x^2 + 25` has `5 ∣ x`. -/
theorem lemma20_21_d {b x : ℕ} :
    b * (b + x) ≠ x ^ 2 + 3 ∧ (b * (b + x) = x ^ 2 + 25 → 5 ∣ x) := by
  constructor
  · intro h
    have hU : (2 * b + x) ^ 2 = 5 * x ^ 2 + 12 := by nlinarith
    have hcast := congrArg (fun k : ℕ => (k : ZMod 5)) hU
    push_cast at hcast
    generalize (b : ZMod 5) = B at hcast
    generalize (x : ZMod 5) = X at hcast
    revert B X
    decide
  · intro h
    have hU : (2 * b + x) ^ 2 = 5 * x ^ 2 + 100 := by nlinarith
    have hcast := congrArg (fun k : ℕ => (k : ZMod 25)) hU
    push_cast at hcast
    have key : ∀ B X : ZMod 25, (2 * B + X) ^ 2 = 5 * X ^ 2 + 100 → X.val % 5 = 0 := by
      decide
    have := key _ _ hcast
    rw [ZMod.val_natCast] at this
    omega

end Munchausen
