import Munchausen.Constructions

/-!
# The Munchausen polynomial (chapters 11, 12 and 19)

* `Q_s(r) = P_s(r) - F(s)` and its values;
* local obstructions: Proposition 11.1, for every modulus as in section 19.1.1;
* the test modulo 2, Proposition 15.11;
* Munchausen numbers in negative bases: odd length (Proposition 12.2) and the partners of
  3-digit solutions (Proposition 12.3).
-/

namespace Munchausen

open Polynomial

/-- The value of `Q_s` at an element of any commutative ring. -/
lemma eval_Q {R : Type*} [CommRing R] (m : ℕ) (s : List ℕ) (r : R) :
    ((Q m s).map (Int.castRingHom R)).eval r = P r s - (Fs m s : R) := by
  have h : ∀ p : ℤ[X], (p.map (Int.castRingHom R)).eval r = eval₂ (Int.castRingHom R) r p :=
    fun p => eval_map _ _
  rw [h, Q, eval₂_sub, eval₂_C]
  have h2 : eval₂ (Int.castRingHom R) r (P (X : ℤ[X]) s) = P r s := by
    rw [← coe_eval₂RingHom, map_P, coe_eval₂RingHom, eval₂_X]
  rw [h2]
  simp

/-- The value of `Q_s` at an integer `r` is `P_s(r) - F(s)` (section 11.3). -/
lemma eval_Q_int (m : ℕ) (s : List ℕ) (r : ℤ) : (Q m s).eval r = P r s - (Fs m s : ℤ) := by
  have := eval_Q (R := ℤ) m s r
  rwa [show Int.castRingHom ℤ = RingHom.id ℤ from rfl, Polynomial.map_id] at this

/-- Reducing `Q_s` modulo a ring commutes with evaluation at integers. -/
lemma eval_map_intCast {R : Type*} [CommRing R] (p : ℤ[X]) (r : ℤ) :
    (p.map (Int.castRingHom R)).eval (r : R) = ((p.eval r : ℤ) : R) := by
  rw [eval_map, ← eq_intCast (Int.castRingHom R) r, eval₂_at_apply]
  simp

/-- A string is a solution in base `b` exactly when it is valid and `Q_s(b) = 0`
(section 11.3). -/
theorem isSolution_iff_eval_Q {b m : ℕ} {s : List ℕ} :
    IsSolution b m s ↔ Valid b s ∧ (Q m s).eval (b : ℤ) = 0 := by
  rw [eval_Q_int, sub_eq_zero, ← cast_P, Nat.cast_inj]
  exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.3⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- **Proposition 11.1** (section 11.3), for every modulus as in section 19.1.1. If `Q_s` has
no root modulo `q`, then `Q_s` has no integer root. -/
theorem no_int_root_of_no_root_mod (q : ℕ) {m : ℕ} {s : List ℕ}
    (h : ∀ r : ZMod q, ((Q m s).map (Int.castRingHom (ZMod q))).eval r ≠ 0) :
    ∀ r : ℤ, (Q m s).eval r ≠ 0 := by
  intro r hr
  apply h r
  rw [eval_map_intCast, hr, Int.cast_zero]

/-- **Proposition 11.1** (section 11.3). If `Q_s` has no root modulo some `q`, then `s` is not
a solution in any base. -/
theorem not_isSolution_of_no_root_mod (q : ℕ) {m : ℕ} {s : List ℕ}
    (h : ∀ r : ZMod q, ((Q m s).map (Int.castRingHom (ZMod q))).eval r ≠ 0) (b : ℕ) :
    ¬ IsSolution b m s := fun hs =>
  no_int_root_of_no_root_mod q h b (isSolution_iff_eval_Q.1 hs).2

/-- The value `Q_s(0) = (last digit) - F(s)`. -/
lemma eval_Q_zero (m : ℕ) (s : List ℕ) (x : ℕ) :
    (Q m (s ++ [x])).eval (0 : ℤ) = x - (Fs m (s ++ [x]) : ℤ) := by
  rw [eval_Q_int, P_append_singleton]; simp

/-- The value `Q_s(1) = (digit sum) - F(s)`. -/
lemma eval_Q_one (m : ℕ) (s : List ℕ) : (Q m s).eval (1 : ℤ) = s.sum - (Fs m s : ℤ) := by
  rw [eval_Q_int]
  congr 1
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s d ih => simp [ih]; ring

/-- **Proposition 15.11** (section 15.4.1). `Q_s` has a root modulo 2 exactly when `Q_s(0)` or
`Q_s(1)` is even: the parity rules of section 1.6 for even and odd bases. -/
theorem exists_root_mod_two_iff (m : ℕ) (s : List ℕ) :
    (∃ r : ZMod 2, ((Q m s).map (Int.castRingHom (ZMod 2))).eval r = 0) ↔
      Even ((Q m s).eval (0 : ℤ)) ∨ Even ((Q m s).eval (1 : ℤ)) := by
  have key : ∀ r : ℤ, (((Q m s).map (Int.castRingHom (ZMod 2))).eval (r : ZMod 2) = 0 ↔
      Even ((Q m s).eval r)) := by
    intro r
    rw [eval_map_intCast, even_iff_two_dvd]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ 2
  constructor
  · rintro ⟨r, hr⟩
    have k0 := key 0
    have k1 := key 1
    rw [Int.cast_zero] at k0
    rw [Int.cast_one] at k1
    fin_cases r
    · exact Or.inl (k0.1 hr)
    · exact Or.inr (k1.1 hr)
  · have k0 := key 0
    have k1 := key 1
    rw [Int.cast_zero] at k0
    rw [Int.cast_one] at k1
    rintro (h | h)
    · exact ⟨0, k0.2 h⟩
    · exact ⟨1, k1.2 h⟩

/-! ### Negative bases -/

/-- A digit string `s` is a Munchausen number in base `-b` (section 12.3): its digits lie
below `b`, it is nonempty with a nonzero leading digit, and `P_s(-b) = F(s)`. In base `-b`
every integer has exactly one such representation. -/
structure IsNegSolution (b m : ℕ) (s : List ℕ) : Prop where
  lt_base : ∀ d ∈ s, d < b
  ne_nil : s ≠ []
  head_ne_zero : s.head ne_nil ≠ 0
  eq : P (-(b : ℤ)) s = Fs m s

instance (b m : ℕ) (s : List ℕ) : Decidable (IsNegSolution b m s) :=
  decidable_of_iff ((∀ d ∈ s, d < b) ∧ ∃ h : s ≠ [], s.head h ≠ 0 ∧ P (-(b : ℤ)) s = Fs m s)
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- A string with digits below `|x|` has `|P_s(x)| < |x| ^ |s|`. -/
lemma abs_P_lt (x : ℤ) (s : List ℕ) (hs : ∀ d ∈ s, (d : ℤ) < |x|) :
    |P x s| ≤ |x| ^ s.length - 1 := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s d ih =>
    have hd := hs d (by simp)
    have ih' := ih (fun e he => hs e (by simp [he]))
    rw [P_append_singleton, List.length_append, List.length_singleton, pow_succ]
    have h0 : 0 ≤ |x| := abs_nonneg x
    calc |(d : ℤ) + x * P x s| ≤ |(d : ℤ)| + |x| * |P x s| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (|x| - 1) + |x| * (|x| ^ s.length - 1) := by
          gcongr
          rw [abs_of_nonneg (by positivity)]; omega
      _ = |x| ^ s.length * |x| - 1 := by ring

/-- **Proposition 12.2** (section 12.3). A Munchausen number in a negative base has an odd
number of digits. -/
theorem IsNegSolution.odd_length {b m : ℕ} {s : List ℕ} (h : IsNegSolution b m s) :
    Odd s.length := by
  obtain ⟨d, t, rfl⟩ : ∃ d t, s = d :: t := by
    cases s with
    | nil => exact absurd rfl h.ne_nil
    | cons d t => exact ⟨d, t, rfl⟩
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 h.head_ne_zero
  have hb : d < b := h.lt_base d (by simp)
  have hbound := abs_P_lt (-(b : ℤ)) t (fun e he => by
    rw [abs_neg, Nat.abs_cast]; exact_mod_cast h.lt_base e (by simp [he]))
  rw [abs_neg, Nat.abs_cast] at hbound
  have heq := h.eq
  rw [P_cons] at heq
  have hF : (0 : ℤ) ≤ Fs m (d :: t) := by positivity
  rw [List.length_cons, Nat.odd_add_one, Nat.not_odd_iff_even]
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_pow] at heq
  have h1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have h2 : (0 : ℤ) ≤ (b : ℤ) ^ t.length := by positivity
  have h3 := (abs_le.1 hbound).2
  nlinarith

/-- **Proposition 12.3** (section 12.3). Let `(s₁, s₂, s₃)` be a solution in base `b` with
`s₁ ∣ s₂`. Then it is also a Munchausen number in base `-(b + s₂/s₁)`. -/
theorem IsSolution.negPartner {b m s₁ s₂ s₃ : ℕ} (h : IsSolution b m [s₁, s₂, s₃])
    (hdvd : s₁ ∣ s₂) : IsNegSolution (b + s₂ / s₁) m [s₁, s₂, s₃] := by
  obtain ⟨t, rfl⟩ := hdvd
  have hs1 : s₁ ≠ 0 := h.head_ne_zero (by simp)
  have hdiv : s₁ * t / s₁ = t := Nat.mul_div_cancel_left t (Nat.pos_of_ne_zero hs1)
  rw [hdiv]
  refine ⟨fun d hd => by have := h.lt_base d hd; omega, by simp, by simpa using hs1, ?_⟩
  have heq := h.eq
  have heq' : ((P b [s₁, s₁ * t, s₃] : ℕ) : ℤ) = Fs m [s₁, s₁ * t, s₃] := by rw [heq]
  rw [cast_P] at heq'
  rw [← heq']
  simp [P_cons]
  ring

/-- **Proposition 16.15**, the algebra (section 16.4). Let `a r^2 + b r + c` have `a > 0`,
`c < 0` and a rational root `p/q` in lowest terms (`q > 0`). Then it factors over `ℤ` as
`(q r - p)(q' r - p')` with `q q' = a`, so the other root `p'/q'` is rational, and `p p' = c < 0`:
the roots have opposite signs. -/
theorem prop16_15_quadratic {a b c p q : ℤ} (ha : 0 < a) (hc : c < 0) (hq : 0 < q)
    (hcop : IsCoprime p q) (hroot : a * p ^ 2 + b * p * q + c * q ^ 2 = 0) :
    ∃ p' q' : ℤ, q * q' = a ∧ p * p' = c ∧ 0 < q' ∧
      ∀ r : ℤ, a * r ^ 2 + b * r + c = (q * r - p) * (q' * r - p') := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    have : c * q ^ 2 = 0 := by linear_combination hroot
    rcases mul_eq_zero.1 this with h | h
    · omega
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h) hq.ne'
  -- `q ∣ a p^2` and `p ∣ c q^2`
  have hqa : q ∣ a := by
    have h1 : q ∣ a * p ^ 2 := ⟨-(b * p + c * q), by linear_combination hroot⟩
    exact (hcop.symm.pow_right (n := 2)).dvd_of_dvd_mul_right h1
  have hpc : p ∣ c := by
    have h1 : p ∣ c * q ^ 2 := ⟨-(a * p + b * q), by linear_combination hroot⟩
    exact (hcop.pow_right (n := 2)).dvd_of_dvd_mul_right h1
  obtain ⟨q', hq'⟩ := hqa
  obtain ⟨p', hp'⟩ := hpc
  refine ⟨p', q', hq'.symm, hp'.symm, ?_, ?_⟩
  · by_contra h
    push Not at h
    have : q * q' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le h
    omega
  · -- `b = -(q p' + p q')`
    have hb : b = -(q * p' + p * q') := by
      have : p * q * (b + (q * p' + p * q')) = 0 := by
        rw [hq', hp'] at hroot; linear_combination hroot
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_ne_zero hp0 hq.ne')
      · linarith
    intro r
    rw [hb, hq', hp']; ring

/-- **Proposition 16.15** (section 16.4). If `Q_s` of a 3-digit string `(s₁, s₂, s₃)` with
`s₁ ≥ 1` has a rational root `p/q` in lowest terms, then `Q_s(r) = (q r - p)(q' r - p')` over
`ℤ` with `q q' = s₁`, and the two roots have opposite signs. -/
theorem prop16_15 {m s₁ s₂ s₃ : ℕ} (hs : 1 ≤ s₁) {p q : ℤ} (hq : 0 < q) (hcop : IsCoprime p q)
    (hroot : ((Q m [s₁, s₂, s₃]).map (Int.castRingHom ℚ)).eval ((p : ℚ) / q) = 0) :
    ∃ p' q' : ℤ, q * q' = s₁ ∧ p * p' < 0 ∧ 0 < q' ∧
      ∀ r : ℤ, (Q m [s₁, s₂, s₃]).eval r = (q * r - p) * (q' * r - p') := by
  have hQ : ∀ r : ℤ, (Q m [s₁, s₂, s₃]).eval r =
      s₁ * r ^ 2 + s₂ * r + ((s₃ : ℤ) - Fs m [s₁, s₂, s₃]) := by
    intro r; rw [eval_Q_int]; simp [P_cons]; ring
  set c : ℤ := (s₃ : ℤ) - Fs m [s₁, s₂, s₃]
  have hc : c < 0 := by
    have h1 := one_le_w (m := m) (show s₁ ≠ 0 by omega)
    have h2 := le_w' m s₃
    simp only [c, Fs_cons, Fs_nil]
    push_cast
    omega
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hroot' : (s₁ : ℤ) * p ^ 2 + s₂ * p * q + c * q ^ 2 = 0 := by
    have h := hroot
    rw [eval_Q] at h
    simp only [P_cons, P_nil, List.length_cons, List.length_nil, Fs_cons, Fs_nil] at h
    have : ((s₁ * p ^ 2 + s₂ * p * q + c * q ^ 2 : ℤ) : ℚ) = 0 := by
      calc ((s₁ * p ^ 2 + s₂ * p * q + c * q ^ 2 : ℤ) : ℚ)
          = (q : ℚ) ^ 2 * ((s₁ : ℚ) * ((p : ℚ) / q) ^ (0 + 1 + 1) +
              ((s₂ : ℚ) * ((p : ℚ) / q) ^ (0 + 1) + ((s₃ : ℚ) * ((p : ℚ) / q) ^ 0 + 0)) -
              ((w m s₁ + (w m s₂ + (w m s₃ + 0)) : ℕ) : ℚ)) := by
            simp only [c, Fs_cons, Fs_nil]
            push_cast
            field_simp
            ring
        _ = 0 := by rw [h, mul_zero]
    exact_mod_cast this
  obtain ⟨p', q', h1, h2, h3, h4⟩ :=
    prop16_15_quadratic (by exact_mod_cast hs) hc hq hcop hroot'
  exact ⟨p', q', h1, h2 ▸ hc, h3, fun r => (hQ r).trans (h4 r)⟩

end Munchausen
