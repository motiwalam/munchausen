import Munchausen.Polynomial

/-!
# Residues of `x^x - x` (sections 15.4 and 20.2)

* a periodicity lemma: for `x` prime to `n`, `x^x mod n` depends only on `x mod L` when `n`
  and `φ(n)` divide `L`;
* Lemma 15.12 (3): `x^x - x ≡ 2 (mod 27)` for `x ≡ 2 (mod 6)`;
* the inclusion `T(81) ⊆ 3ℤ ∪ {2, 29}` of Theorem 20.11 (the 3-adic law at `e = 4`), by a
  finite check over one period;
* Lemma 20.6: every multiple of `p` lies in `T(p^e)`;
* the covering theorems: Theorem 15.13 (modulus 27) and Corollary 20.13 (modulus 81), with
  the examples `(2, 1, x)` and `(8, 7, x)`.
-/

namespace Munchausen

/-! ### Periodicity -/

/-- For `x` prime to `n`, and `L` a common multiple of `n` and `φ(n)`, `x^x ≡ r^r (mod n)` with
`r = x mod L`: the residue of `x^x` depends only on `x mod L` (sections 15.4.1 and 20.2). -/
theorem pow_self_modEq_mod {n L x : ℕ} (hx : x.Coprime n) (hnL : n ∣ L) (hφL : n.totient ∣ L) :
    x ^ x ≡ (x % L) ^ (x % L) [MOD n] := by
  have hxr : x ≡ x % L [MOD n] := (Nat.mod_modEq x L).symm.of_dvd hnL
  have hφ : x ^ n.totient ≡ 1 [MOD n] := Nat.ModEq.pow_totient hx
  obtain ⟨c, hc⟩ := hφL
  have e : x ^ x = x ^ (x % L) * (x ^ n.totient) ^ (c * (x / L)) := by
    rw [← pow_mul, ← pow_add, ← mul_assoc, ← hc, Nat.mod_add_div]
  have h1 : x ^ x ≡ x ^ (x % L) [MOD n] := by
    rw [e]
    have : (x ^ n.totient) ^ (c * (x / L)) ≡ 1 [MOD n] := by
      simpa using hφ.pow (c * (x / L))
    simpa using (Nat.ModEq.refl (x ^ (x % L))).mul this
  exact h1.trans (hxr.pow _)

/-! ### Lemma 15.12 and the 3-adic law -/

lemma coprime_three_pow {x : ℕ} (h : x % 3 ≠ 0) (k : ℕ) : x.Coprime (3 ^ k) :=
  Nat.Coprime.pow_right k (Nat.coprime_comm.1
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)))

set_option maxRecDepth 100000 in
/-- **Lemma 15.12 (3)** (section 15.4.2). If `x ≡ 2 (mod 6)`, then `x^x - x ≡ 2 (mod 27)`. -/
theorem pow_self_modEq_27 {x : ℕ} (hx : x % 6 = 2) : x ^ x ≡ x + 2 [MOD 27] := by
  have hcop : x.Coprime 27 := coprime_three_pow (by omega) 3
  have hper := pow_self_modEq_mod (L := 54) hcop (by norm_num) (by decide)
  have hcheck : ∀ r < 54, r % 6 = 2 → r ^ r % 27 = (r + 2) % 27 := by decide
  have hr := hcheck (x % 54) (Nat.mod_lt _ (by norm_num)) (by omega)
  have hxr : x ≡ x % 54 [MOD 27] := (Nat.mod_modEq x 54).symm.of_dvd (by norm_num)
  exact hper.trans (hr.trans (hxr.add_right 2).symm)

/-- Lemma 15.12 (3), second half: if `x ≢ 2 (mod 6)` and `x ≥ 1`, then `3 ∣ x^x - x`. -/
theorem pow_self_modEq_three_of_ne {x : ℕ} (hx1 : 1 ≤ x) (hx : x % 6 ≠ 2) : x ^ x ≡ x [MOD 3] := by
  simpa [hx] using pow_self_modEq_three x hx1

set_option maxRecDepth 100000 in
/-- **The 3-adic law at `81`**, the inclusion part of Theorem 20.11 (section 20.2.2). If
`x ≡ 2 (mod 6)`, then `x^x - x ≡ 2` or `29 (mod 81)`; in particular `x^x - x ≢ 56 (mod 81)`. -/
theorem pow_self_modEq_81 {x : ℕ} (hx : x % 6 = 2) :
    x ^ x ≡ x + 2 [MOD 81] ∨ x ^ x ≡ x + 29 [MOD 81] := by
  have hcop : x.Coprime 81 := coprime_three_pow (by omega) 4
  have hper := pow_self_modEq_mod (L := 162) hcop (by norm_num) (by decide)
  have hcheck : ∀ r < 162, r % 6 = 2 →
      r ^ r % 81 = (r + 2) % 81 ∨ r ^ r % 81 = (r + 29) % 81 := by decide
  have hxr : x ≡ x % 162 [MOD 81] := (Nat.mod_modEq x 162).symm.of_dvd (by norm_num)
  rcases hcheck (x % 162) (Nat.mod_lt _ (by norm_num)) (by omega) with hr | hr
  · exact Or.inl (hper.trans (hr.trans (hxr.add_right 2).symm))
  · exact Or.inr (hper.trans (hr.trans (hxr.add_right 29).symm))

/-- **Lemma 20.6** (section 20.2.1). Every multiple of `p` is a residue of `x^x - x` modulo
`p^e`, for some `x ≥ 1`. -/
theorem multiple_mem_T {p e : ℕ} (hp : 2 ≤ p) (v : ℕ) :
    ∃ x : ℕ, 1 ≤ x ∧ (x : ZMod (p ^ e)) ^ x - x = ((p * v : ℕ) : ZMod (p ^ e)) := by
  have hpe : 1 ≤ p ^ e := Nat.one_le_pow e p (by omega)
  have hle : v ≤ p ^ e * (v + 1) := by nlinarith
  set y := p ^ e * (v + 1) - v with hy
  have hy1 : p ^ e ≤ y := by
    have h1 : v ≤ p ^ e * v := Nat.le_mul_of_pos_left v hpe
    have h2 : p ^ e * (v + 1) = p ^ e * v + p ^ e := by ring
    omega
  refine ⟨p * y, le_trans (by norm_num : 1 ≤ 1 * 1) (Nat.mul_le_mul (by omega) (by omega)), ?_⟩
  have hex : e ≤ p * y := by
    have := (Nat.lt_pow_self (by omega : 1 < p) : e < p ^ e)
    nlinarith
  have h0 : ((p * y : ℕ) : ZMod (p ^ e)) ^ (p * y) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow_self (dvd_mul_right p y) hex
  have hz : ((p : ZMod (p ^ e))) ^ e = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [h0, zero_sub, hy, Nat.cast_mul, Nat.cast_sub hle]
  push_cast
  rw [hz]
  ring

/-! ### Covering theorems -/

/-- From a solution `(t, x)` with last digit `x ≥ 1`: `b P_t(b) - F(t) = x^x - x`, read in any
commutative ring (proof of Theorem 15.13). -/
lemma prefix_eq_of_isSolution {R : Type*} [CommRing R] {b m x : ℕ} {t : List ℕ} (hx : 1 ≤ x)
    (h : IsSolution b m (t ++ [x])) :
    (b : R) * P (b : R) t - (Fs m t : R) = (x : R) ^ x - x := by
  have heq := h.eq
  rw [P_append_singleton, Fs_append, Fs_singleton, w_of_ne_zero m (by omega)] at heq
  have := congrArg (fun n : ℕ => (n : R)) heq
  simp only [Nat.cast_add, Nat.cast_mul, cast_P, Nat.cast_pow] at this
  linear_combination this

/-- **Theorem 15.13** (section 15.4.3). Let `t` be a prefix such that for every residue
`r mod 27` the value `A(r) - F(t) = r P_t(r) - F(t)` is neither `0 (mod 3)` nor `2 (mod 27)`.
Then no string `(t, x)` with `x ≥ 1` is a solution in any base, under either convention. -/
theorem covering_27 {m : ℕ} {t : List ℕ}
    (h : ∀ r : ZMod 27, (r * P r t - (Fs m t : ZMod 27)).val % 3 ≠ 0 ∧
      r * P r t - (Fs m t : ZMod 27) ≠ 2)
    (b x : ℕ) (hx : 1 ≤ x) : ¬ IsSolution b m (t ++ [x]) := by
  intro hs
  have key := prefix_eq_of_isSolution (R := ZMod 27) hx hs
  obtain ⟨h1, h2⟩ := h b
  rw [key] at h1 h2
  by_cases h6 : x % 6 = 2
  · apply h2
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (pow_self_modEq_27 h6)
    push_cast at this
    rw [this]; ring
  · apply h1
    have hle : x ≤ x ^ x := by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ x := Nat.pow_le_pow_right hx hx
    have h3 := pow_self_modEq_three_of_ne hx h6
    rw [← Nat.cast_pow, ← Nat.cast_sub hle, ZMod.val_natCast,
      Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 27)]
    exact Nat.sub_mod_eq_zero_of_mod_eq h3

/-- The prefix `(2, 1)` (section 15.4.3): `(2, 1, x)` is never a solution, for every `x ≥ 1`,
in every base and under either convention. -/
theorem not_isSolution_two_one (m b x : ℕ) (hx : 1 ≤ x) : ¬ IsSolution b m [2, 1, x] := by
  have hF : Fs m [2, 1] = 5 := by simp [w]
  exact covering_27 (t := [2, 1]) (by rw [hF]; decide) b x hx

/-- **Corollary 20.13** (section 20.2.3). If for every residue `r mod 81` the value
`r P_t(r) - F(t)` is neither `0 (mod 3)` nor `2` or `29 (mod 81)`, then no string `(t, x)` with
`x ≥ 1` is a solution in any base, under either convention. -/
theorem covering_81 {m : ℕ} {t : List ℕ}
    (h : ∀ r : ZMod 81, (r * P r t - (Fs m t : ZMod 81)).val % 3 ≠ 0 ∧
      r * P r t - (Fs m t : ZMod 81) ≠ 2 ∧ r * P r t - (Fs m t : ZMod 81) ≠ 29)
    (b x : ℕ) (hx : 1 ≤ x) : ¬ IsSolution b m (t ++ [x]) := by
  intro hs
  have key := prefix_eq_of_isSolution (R := ZMod 81) hx hs
  obtain ⟨h1, h2, h3⟩ := h b
  rw [key] at h1 h2 h3
  by_cases h6 : x % 6 = 2
  · rcases pow_self_modEq_81 h6 with h81 | h81
    · apply h2
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h81
      push_cast at this
      rw [this]; ring
    · apply h3
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h81
      push_cast at this
      rw [this]; ring
  · apply h1
    have hle : x ≤ x ^ x := by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ x := Nat.pow_le_pow_right hx hx
    have h3 := pow_self_modEq_three_of_ne hx h6
    rw [← Nat.cast_pow, ← Nat.cast_sub hle, ZMod.val_natCast,
      Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 81)]
    exact Nat.sub_mod_eq_zero_of_mod_eq h3

/-- The prefix `(8, 7)` (section 20.2.3): the modulus 81 excludes `(8, 7, x)` for every
`x ≥ 1`, while 27 does not. -/
theorem not_isSolution_eight_seven (m b x : ℕ) (hx : 1 ≤ x) : ¬ IsSolution b m [8, 7, x] := by
  have hF : Fs m [8, 7] = 8 ^ 8 + 7 ^ 7 := by simp [w]
  exact covering_81 (t := [8, 7]) (by rw [hF]; decide) b x hx

end Munchausen
