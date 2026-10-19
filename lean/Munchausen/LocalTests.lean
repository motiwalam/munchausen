import Munchausen.ShortEquations

/-!
# Local tests (sections 16.2.2 and 19.1.1)

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

end Munchausen
