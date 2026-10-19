import Munchausen.Polynomial

/-!
# Residues of `x^x - x` (sections 15.4 and 20.2)

* a periodicity lemma: for `x` prime to `n`, `x^x mod n` depends only on `x mod L` when `n`
  and `φ(n)` divide `L`;
* Lemma 15.12 (3): `x^x - x ≡ 2 (mod 27)` for `x ≡ 2 (mod 6)`;
* the inclusion `T(81) ⊆ 3ℤ ∪ {2, 29}` of Theorem 20.11 (the 3-adic law at `e = 4`), by a
  finite check over one period;
* Lemma 20.6: every multiple of `p` lies in `T(p^e)`;
* Lemma 15.12 (2): `T(p)` is everything for primes `p ≥ 5`, and `T(3) = {0, 2}`;
* Lemma 20.7 (lifting) and Theorem 20.8: `T(p^e)` is everything for primes `p ≥ 7`;
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

/-! ### Lemma 15.12 (2): all residues modulo a prime `p ≥ 5` -/

/-- `u^x = u^(x mod (p-1))` for a nonzero `u` in `ZMod p`. -/
lemma pow_mod_sub_one {p : ℕ} [Fact p.Prime] {u : ZMod p} (hu : u ≠ 0) (x : ℕ) :
    u ^ x = u ^ (x % (p - 1)) := by
  conv_lhs => rw [← Nat.mod_add_div x (p - 1), pow_add, pow_mul,
    ZMod.pow_card_sub_one_eq_one hu, one_pow, mul_one]

/-- **Lemma 15.12 (2)** (section 15.4.2). For a prime `p ≥ 5`, every residue modulo `p` is a
value of `x^x - x` with `x ≥ 1`. -/
theorem T_prime_eq_univ {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (v : ZMod p) :
    ∃ x : ℕ, 1 ≤ x ∧ (x : ZMod p) ^ x - x = v := by
  by_cases hv : v = 0
  · refine ⟨p, by omega, ?_⟩
    rw [hv, ZMod.natCast_self, zero_pow (by omega), sub_zero]
  -- a generator `g` of the units
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  -- choose a generator `u` with `u ≠ -v`
  obtain ⟨u, hu_gen, hu_ne⟩ : ∃ u : (ZMod p)ˣ, (∀ y, y ∈ Subgroup.zpowers u) ∧
      (u : ZMod p) ≠ -v := by
    by_cases h : (g : ZMod p) = -v
    · refine ⟨g⁻¹, fun y => ?_, ?_⟩
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg y)
        exact Subgroup.mem_zpowers_iff.2 ⟨-k, by rw [zpow_neg, inv_zpow, inv_inv, hk]⟩
      · intro h'
        -- then `g^2 = 1`, so the group has at most 2 elements
        have hgg : g * g = 1 := by
          have : (g : ZMod p) = ((g⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [h, h']
          have := Units.ext this
          calc g * g = g * g⁻¹ := by rw [← this]
            _ = 1 := mul_inv_cancel g
        have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hgg)
        have h2 := orderOf_eq_card_of_forall_mem_zpowers hg
        rw [Nat.card_eq_fintype_card, ZMod.card_units] at h2
        have := Nat.le_of_dvd (by norm_num) h1
        omega
    · exact ⟨g, hg, h⟩
  -- `u + v` is a power `u^j`
  have huv : (u : ZMod p) + v ≠ 0 := fun h => hu_ne (by linear_combination h)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, u ^ j = Units.mk0 _ huv :=
    mem_powers_iff_mem_zpowers.2 (hu_gen _)
  have hj' : (u : ZMod p) ^ j = (u : ZMod p) + v := by
    have := congrArg Units.val hj; simpa using this
  -- `x ≡ u (mod p)` and `x ≡ j (mod p - 1)`
  have hcop : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right hp.out.one_le).2 (Nat.coprime_one_right p)
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop (u : ZMod p).val j
  set x := c + p * (p - 1)
  have hu0 : (u : ZMod p) ≠ 0 := u.ne_zero
  have hxu : (x : ZMod p) = u := by
    have : (x : ZMod p) = (c : ZMod p) := by simp [x]
    rw [this, (ZMod.natCast_eq_natCast_iff' c _ p).2 hc1, ZMod.natCast_zmod_val]
  have hxj : x % (p - 1) = j % (p - 1) := by
    have : x % (p - 1) = c % (p - 1) := by simp [x]
    rw [this]; exact hc2
  refine ⟨x, ?_, ?_⟩
  · have : 1 ≤ p * (p - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  · rw [hxu, pow_mod_sub_one hu0, hxj, ← pow_mod_sub_one hu0, hj']
    ring

/-- **Lemma 15.12 (2)**, the prime 3: `x^x - x` is `0` or `2` modulo 3, for `x ≥ 1`. -/
theorem T_three {x : ℕ} (hx : 1 ≤ x) : (x ^ x - x) % 3 = 0 ∨ (x ^ x - x) % 3 = 2 := by
  have h := pow_self_modEq_three x hx
  have hle : x ≤ x ^ x := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ x := Nat.pow_le_pow_right hx hx
  unfold Nat.ModEq at h
  split_ifs at h <;> omega

/-! ### Lemma 20.7 and Theorem 20.8: lifting to `p^e` -/

open Polynomial in
/-- `(a + d)^n ≡ a^n + n a^(n-1) d (mod d^2)` in `ℤ`. -/
lemma add_pow_modEq_sq (a d : ℤ) (n : ℕ) :
    d ^ 2 ∣ (a + d) ^ n - (a ^ n + n * a ^ (n - 1) * d) := by
  obtain ⟨k, hk⟩ := binomExpansion ((X : ℤ[X]) ^ n) a d
  simp only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_C] at hk
  exact ⟨k, by rw [hk]; ring⟩

/-- The key step of Lemma 20.7: for `x` prime to the odd prime `p`, `e ≥ 1` and
`d = p^e (p-1) s`, `f(x + d) ≡ f(x) + d (x^x - 1) (mod p^(e+1))`, where `f(x) = x^x - x`. -/
lemma step_lemma20_7 {p : ℕ} (hp : p.Prime) {x e s : ℕ} (hx : 1 ≤ x) (hxp : ¬ (p : ℤ) ∣ x)
    (he : 1 ≤ e) :
    ((p : ℤ) ^ (e + 1)) ∣ (((x + p ^ e * (p - 1) * s : ℕ) : ℤ) ^ (x + p ^ e * (p - 1) * s)
        - (x + p ^ e * (p - 1) * s : ℕ)) - (((x : ℤ) ^ x - x) +
        (p ^ e * (p - 1) * s : ℕ) * ((x : ℤ) ^ x - 1)) := by
  set d : ℕ := p ^ e * (p - 1) * s with hd
  have hp2 := hp.two_le
  -- `(x + d)^d ≡ 1 (mod p^(e+1))`
  have hy : (p : ℤ) ∣ ((x + d : ℕ) : ℤ) ^ ((p - 1) * s) - 1 := by
    have hd0 : (d : ZMod p) = 0 := by
      rw [hd, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega)]
      simp
    have hx0 : (x : ZMod p) ≠ 0 := by
      intro h0
      apply hxp
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 (by exact_mod_cast h0)
    have := Fact.mk hp
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hd0, add_zero, pow_mul, ZMod.pow_card_sub_one_eq_one hx0, one_pow, sub_self]
  have hd1 := dvd_sub_pow_of_dvd_sub hy e
  rw [one_pow, ← pow_mul] at hd1
  have hdexp : (p - 1) * s * p ^ e = d := by rw [hd]; ring
  rw [hdexp] at hd1
  -- `(x + d)^x ≡ x^x + x^x d (mod d^2)` and `p^(e+1) ∣ d^2`
  have hb := add_pow_modEq_sq (x : ℤ) (d : ℤ) x
  have hxx : (x : ℤ) * (x : ℤ) ^ (x - 1) = (x : ℤ) ^ x := by
    rw [← pow_succ']; congr 1; omega
  have hdd : (p : ℤ) ^ (e + 1) ∣ (d : ℤ) ^ 2 := by
    have h1 : (p : ℤ) ^ e ∣ (d : ℤ) := ⟨((p - 1) * s : ℕ), by rw [hd]; push_cast; ring⟩
    have h2 := pow_dvd_pow_of_dvd h1 2
    rw [← pow_mul] at h2
    exact (pow_dvd_pow _ (by omega)).trans h2
  obtain ⟨k, hk⟩ := hb
  obtain ⟨m, hm⟩ := hd1
  obtain ⟨c, hc⟩ := hdd
  have eY : ((x + d : ℕ) : ℤ) = (x : ℤ) + d := by push_cast; ring
  rw [eY, pow_add ((x : ℤ) + d) x d]
  have hYx : ((x : ℤ) + d) ^ x = (x : ℤ) ^ x + x * (x : ℤ) ^ (x - 1) * d + d ^ 2 * k := by
    linarith [hk]
  have hYd : ((x : ℤ) + d) ^ d = 1 + (p : ℤ) ^ (e + 1) * m := by
    rw [eY] at hm; linarith [hm]
  rw [hYx, hYd]
  refine ⟨((x : ℤ) ^ x + x * (x : ℤ) ^ (x - 1) * d) * m + c * k + c * k * (p : ℤ) ^ (e + 1) * m, ?_⟩
  linear_combination (d : ℤ) * hxx + k * (1 + (p : ℤ) ^ (e + 1) * m) * hc

/-- `x^x mod p` depends only on `x mod p (p - 1)` for `x` prime to `p`. -/
lemma pow_self_zmod_eq {p : ℕ} [Fact p.Prime] {x0 t : ℕ} (hx0 : (x0 : ZMod p) ≠ 0) :
    ((x0 + p * (p - 1) * t : ℕ) : ZMod p) ^ (x0 + p * (p - 1) * t) = (x0 : ZMod p) ^ x0 := by
  have h1 : ((x0 + p * (p - 1) * t : ℕ) : ZMod p) = x0 := by simp
  rw [h1, pow_mod_sub_one hx0, pow_mod_sub_one hx0 x0]
  congr 1
  rw [show p * (p - 1) * t = (p - 1) * (p * t) by ring, Nat.add_mul_mod_self_left]

/-- **Lemma 20.7** (section 20.2.1). Let `p` be a prime and `x₀ ≥ 1` prime to `p` with
`x₀^x₀ ≢ 1 (mod p)`. Then for every `e ≥ 1` and every `v ≡ f(x₀) (mod p)` there is
`x ≡ x₀ (mod p (p-1))` with `f(x) ≡ v (mod p^e)`, where `f(x) = x^x - x`. -/
theorem lemma20_7 {p : ℕ} (hp : p.Prime) {x0 : ℕ} (hx0 : 1 ≤ x0)
    (hx0p : ¬ (p : ℤ) ∣ x0) (hg : ¬ (p : ℤ) ∣ (x0 : ℤ) ^ x0 - 1) (v : ℤ)
    (hv : (p : ℤ) ∣ v - ((x0 : ℤ) ^ x0 - x0)) :
    ∀ e, 1 ≤ e → ∃ t : ℕ, (p : ℤ) ^ e ∣
      (((x0 + p * (p - 1) * t : ℕ) : ℤ) ^ (x0 + p * (p - 1) * t) - (x0 + p * (p - 1) * t : ℕ))
        - v := by
  have := Fact.mk hp
  have hp2 := hp.two_le
  have hx0z : (x0 : ZMod p) ≠ 0 := fun h0 =>
    hx0p ((ZMod.intCast_zmod_eq_zero_iff_dvd x0 p).1 (by exact_mod_cast h0))
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    refine ⟨0, ?_⟩
    simp only [mul_zero, add_zero, pow_one]
    rw [← dvd_neg]; convert hv using 1; ring
  | succ e he ih =>
    obtain ⟨t, T, hT⟩ := ih
    set x := x0 + p * (p - 1) * t with hxdef
    have hxp : ¬ (p : ℤ) ∣ x := by
      intro h
      apply hx0p
      have : (p : ℤ) ∣ (x : ℤ) - (p * (p - 1) * t : ℕ) := dvd_sub h ⟨((p - 1) * t : ℕ), by push_cast; ring⟩
      convert this using 1; rw [hxdef]; push_cast; ring
    -- `a = (p - 1)(x^x - 1)` is a unit mod `p`
    have hxx : ((x : ℤ) ^ x : ZMod p) = (x0 : ZMod p) ^ x0 := by
      push_cast; exact pow_self_zmod_eq hx0z
    set a : ZMod p := ((((p : ℤ) - 1) * ((x : ℤ) ^ x - 1) : ℤ) : ZMod p) with ha
    have ha0 : a ≠ 0 := by
      rw [ha]; push_cast
      rw [ZMod.natCast_self, zero_sub]
      have : ((x : ZMod p) ^ x - 1) ≠ 0 := by
        intro h0
        apply hg
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [← pow_self_zmod_eq (t := t) hx0z]
        exact h0
      exact mul_ne_zero (neg_ne_zero.2 one_ne_zero) this
    set s : ℕ := ((-(T : ZMod p)) * a⁻¹).val with hs
    have hsT : ((T + ((p : ℤ) - 1) * ((x : ℤ) ^ x - 1) * s : ℤ) : ZMod p) = 0 := by
      push_cast
      have : ((s : ℕ) : ZMod p) = -(T : ZMod p) * a⁻¹ := by rw [hs, ZMod.natCast_zmod_val]
      rw [this]
      have ha' : (((p : ℤ) - 1) * ((x : ℤ) ^ x - 1) : ZMod p) = a := by rw [ha]; push_cast; ring
      rw [show ((T : ZMod p) + ((p : ZMod p) - 1) * ((x : ZMod p) ^ x - 1) * (-(T : ZMod p) * a⁻¹))
          = (T : ZMod p) - (T : ZMod p) * ((((p : ZMod p) - 1) * ((x : ZMod p) ^ x - 1)) * a⁻¹)
          by ring]
      push_cast at ha'
      rw [ha', mul_inv_cancel₀ ha0, mul_one, sub_self]
    have hsT' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hsT
    -- the new `x`
    refine ⟨t + p ^ (e - 1) * s, ?_⟩
    have hx' : x0 + p * (p - 1) * (t + p ^ (e - 1) * s) = x + p ^ e * (p - 1) * s := by
      rw [hxdef]
      have : p * p ^ (e - 1) = p ^ e := by rw [← pow_succ']; congr 1; omega
      rw [← this]; ring
    rw [hx']
    have hstep := step_lemma20_7 hp (x := x) (e := e) (s := s) (by omega) hxp he
    obtain ⟨c, hc⟩ := hsT'
    -- combine
    have key : (((x + p ^ e * (p - 1) * s : ℕ) : ℤ) ^ (x + p ^ e * (p - 1) * s)
        - (x + p ^ e * (p - 1) * s : ℕ)) - v =
        ((((x + p ^ e * (p - 1) * s : ℕ) : ℤ) ^ (x + p ^ e * (p - 1) * s)
          - (x + p ^ e * (p - 1) * s : ℕ)) - (((x : ℤ) ^ x - x) +
          (p ^ e * (p - 1) * s : ℕ) * ((x : ℤ) ^ x - 1))) + (p : ℤ) ^ e * p * c := by
      have hpe : ((p ^ e * (p - 1) * s : ℕ) : ℤ) = (p : ℤ) ^ e * ((p : ℤ) - 1) * s := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
      rw [hpe]
      linear_combination hT + (p : ℤ) ^ e * hc
    rw [key]
    exact dvd_add hstep ⟨c, by ring⟩

/-- A power `g^k` of a generator with `k` prime to the order is again a generator. -/
lemma generator_pow {G : Type*} [Group G] [Fintype G] {g : G} (hg : ∀ y, ∃ i : ℕ, g ^ i = y)
    {k : ℕ} (hk : Nat.Coprime k (Fintype.card G)) (h1 : 1 < Fintype.card G) :
    ∀ y, ∃ i : ℕ, (g ^ k) ^ i = y := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk h1
  intro y
  obtain ⟨i, rfl⟩ := hg y
  refine ⟨m * i, ?_⟩
  rw [← pow_mul, ← mul_assoc, pow_mul]
  congr 1
  rw [← Nat.mod_add_div (k * m) (Fintype.card G), hm, pow_add, pow_mul, pow_card_eq_one,
    one_pow, mul_one, pow_one]

/-- A starting point for Lemma 20.7: a residue `r ≠ 0` mod `p ≥ 7` is `f(x₀)` for an `x₀`
prime to `p` with `x₀^x₀ ≢ 1`, if some generator `u` of the units avoids `-r` and `1 - r`. -/
lemma start_of_generator {p : ℕ} [hp : Fact p.Prime] {r : ZMod p} {u : (ZMod p)ˣ}
    (hu : ∀ y, ∃ i : ℕ, u ^ i = y) (h1 : (u : ZMod p) ≠ -r) (h2 : (u : ZMod p) ≠ 1 - r) :
    ∃ x0 : ℕ, 1 ≤ x0 ∧ (x0 : ZMod p) ≠ 0 ∧ (x0 : ZMod p) ^ x0 ≠ 1 ∧
      (x0 : ZMod p) ^ x0 - x0 = r := by
  have huv : (u : ZMod p) + r ≠ 0 := fun h => h1 (by linear_combination h)
  obtain ⟨j, hj⟩ := hu (Units.mk0 _ huv)
  have hj' : (u : ZMod p) ^ j = (u : ZMod p) + r := by
    have := congrArg Units.val hj; simpa using this
  have hcop : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right hp.out.one_le).2 (Nat.coprime_one_right p)
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop (u : ZMod p).val j
  set x := c + p * (p - 1)
  have hu0 : (u : ZMod p) ≠ 0 := u.ne_zero
  have hxu : (x : ZMod p) = u := by
    have : (x : ZMod p) = (c : ZMod p) := by simp [x]
    rw [this, (ZMod.natCast_eq_natCast_iff' c _ p).2 hc1, ZMod.natCast_zmod_val]
  have hxj : x % (p - 1) = j % (p - 1) := by
    have : x % (p - 1) = c % (p - 1) := by simp [x]
    rw [this]; exact hc2
  have hpow : (x : ZMod p) ^ x = (u : ZMod p) + r := by
    rw [hxu, pow_mod_sub_one hu0, hxj, ← pow_mod_sub_one hu0, hj']
  refine ⟨x, ?_, by rw [hxu]; exact hu0, ?_, ?_⟩
  · have : 1 ≤ p * (p - 1) := Nat.mul_pos (by have := hp.out.two_le; omega)
      (by have := hp.out.two_le; omega)
    omega
  · rw [hpow]; intro h; exact h2 (by linear_combination h)
  · rw [hpow, hxu]; ring

/-- For `p ≥ 11`, the units modulo `p` have three distinct generators `g`, `g^(n-1)`, `g^k`, so
one of them avoids any two given residues (proof of Theorem 20.8). -/
lemma exists_generator_avoiding {p : ℕ} [hp : Fact p.Prime] (hp11 : 11 ≤ p) (a b : ZMod p) :
    ∃ u : (ZMod p)ˣ, (∀ y, ∃ i : ℕ, u ^ i = y) ∧ (u : ZMod p) ≠ a ∧ (u : ZMod p) ≠ b := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgN : ∀ y, ∃ i : ℕ, g ^ i = y := fun y => mem_powers_iff_mem_zpowers.2 (hg y)
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  set n := p - 1 with hn
  have hn10 : 10 ≤ n := by omega
  have hord : orderOf g = n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
  have hpodd : p % 2 = 1 := hp.out.eq_one_or_self_of_dvd 2 |> fun h => by
    rcases Nat.even_or_odd p with he | ho
    · have := (Nat.Prime.even_iff hp.out).1 he; omega
    · exact Nat.odd_iff.1 ho
  -- the third exponent
  set h := n / 2 with hh
  have hn2 : n = 2 * h := by omega
  set k := if h % 2 = 0 then h + 1 else h + 2 with hk
  have hkodd : k % 2 = 1 := by simp only [hk]; split_ifs <;> omega
  have hkcop : Nat.Coprime k n := by
    have hd2 : Nat.gcd k n ∣ 4 := by
      have h1 : Nat.gcd k n ∣ 2 * k := Dvd.dvd.mul_left (Nat.gcd_dvd_left k n) 2
      have h2 : Nat.gcd k n ∣ n := Nat.gcd_dvd_right k n
      have h3 := Nat.dvd_sub h1 h2
      have : 2 * k - n ∣ 4 := by
        simp only [hk]; split_ifs <;> [exact ⟨2, by omega⟩; exact ⟨1, by omega⟩]
      exact h3.trans this
    have hodd : ¬ 2 ∣ Nat.gcd k n := fun h2 =>
      by have := (h2.trans (Nat.gcd_dvd_left k n)); omega
    have : Nat.gcd k n ∈ Nat.divisors 4 := Nat.mem_divisors.2 ⟨hd2, by norm_num⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h1 | h1 | h1
    · exact h1
    · exact absurd (by rw [h1]) hodd
    · exact absurd (by rw [h1]; norm_num) hodd
  have hcop1 : Nat.Coprime (n - 1) n := by
    have := (Nat.coprime_self_sub_right (by omega : 1 ≤ n)).2 (Nat.coprime_one_right n)
    exact this.symm
  have h1 : 1 < Fintype.card (ZMod p)ˣ := by omega
  have gen1 : ∀ y, ∃ i : ℕ, (g ^ 1) ^ i = y := by simpa using hgN
  have gen2 := generator_pow hgN (k := n - 1) (by rw [hcard]; exact hcop1) h1
  have gen3 := generator_pow hgN (k := k) (by rw [hcard]; exact hkcop) h1
  -- the three powers are distinct
  have hdist : ∀ i j : ℕ, i < n → j < n → g ^ i = g ^ j → i = j := by
    intro i j hi hj hij
    rw [pow_eq_pow_iff_modEq, hord] at hij
    unfold Nat.ModEq at hij
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hij
  have hk1 : 1 < k := by simp only [hk]; split_ifs <;> omega
  have hk2 : k < n - 1 := by simp only [hk]; split_ifs <;> omega
  have d12 : ((g ^ 1 : (ZMod p)ˣ) : ZMod p) ≠ ((g ^ (n - 1) : (ZMod p)ˣ) : ZMod p) := by
    intro h; have := hdist 1 (n - 1) (by omega) (by omega) (Units.ext h); omega
  have d13 : ((g ^ 1 : (ZMod p)ˣ) : ZMod p) ≠ ((g ^ k : (ZMod p)ˣ) : ZMod p) := by
    intro h; have := hdist 1 k (by omega) (by omega) (Units.ext h); omega
  have d23 : ((g ^ (n - 1) : (ZMod p)ˣ) : ZMod p) ≠ ((g ^ k : (ZMod p)ˣ) : ZMod p) := by
    intro h; have := hdist (n - 1) k (by omega) (by omega) (Units.ext h); omega
  by_cases c1 : ((g ^ 1 : (ZMod p)ˣ) : ZMod p) ≠ a ∧ ((g ^ 1 : (ZMod p)ˣ) : ZMod p) ≠ b
  · exact ⟨g ^ 1, gen1, c1⟩
  by_cases c2 : ((g ^ (n - 1) : (ZMod p)ˣ) : ZMod p) ≠ a ∧
      ((g ^ (n - 1) : (ZMod p)ˣ) : ZMod p) ≠ b
  · exact ⟨g ^ (n - 1), gen2, c2⟩
  refine ⟨g ^ k, gen3, ?_, ?_⟩ <;> intro h3 <;> rw [not_and_or, not_not, not_not] at c1 c2 <;>
    rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;>
    first | exact d12 (c1.trans c2.symm) | exact d13 (c1.trans h3.symm) |
      exact d23 (c2.trans h3.symm)

lemma start_seven : ∀ r : ZMod 7, r ≠ 0 → ∃ x0 : ℕ, x0 < 42 ∧ 1 ≤ x0 ∧ (x0 : ZMod 7) ≠ 0 ∧
    (x0 : ZMod 7) ^ x0 ≠ 1 ∧ (x0 : ZMod 7) ^ x0 - x0 = r := by decide

/-- A start for Lemma 20.7 for every nonzero residue modulo a prime `p ≥ 7`. -/
lemma exists_start {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) {r : ZMod p} (hr : r ≠ 0) :
    ∃ x0 : ℕ, 1 ≤ x0 ∧ (x0 : ZMod p) ≠ 0 ∧ (x0 : ZMod p) ^ x0 ≠ 1 ∧
      (x0 : ZMod p) ^ x0 - x0 = r := by
  rcases Nat.lt_or_ge p 11 with h | h
  · -- `p = 7`: a finite check
    have hpp := hp.out
    have hp7' : p = 7 := by interval_cases p <;> first | rfl | norm_num at hpp
    subst hp7'
    obtain ⟨x0, -, h⟩ := start_seven r hr
    exact ⟨x0, h⟩
  · obtain ⟨u, hu, h1, h2⟩ := exists_generator_avoiding h (-r) (1 - r)
    exact start_of_generator hu h1 h2

/-- **Theorem 20.8** (section 20.2.1). For every prime `p ≥ 7` and every `e ≥ 1`, every residue
modulo `p^e` is a value of `x^x - x` with `x ≥ 1`. -/
theorem theorem20_8 {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) {e : ℕ} (he : 1 ≤ e) (v : ℤ) :
    ∃ x : ℕ, 1 ≤ x ∧ (p : ℤ) ^ e ∣ ((x : ℤ) ^ x - x) - v := by
  have := Fact.mk hp
  by_cases hv : (p : ℤ) ∣ v
  · -- multiples of `p`: Lemma 20.6
    obtain ⟨w, hw⟩ := hv
    obtain ⟨x, hx, hxw⟩ := multiple_mem_T (p := p) (e := e) hp.two_le (w % (p : ℤ) ^ e).toNat
    refine ⟨x, hx, ?_⟩
    rw [show ((p : ℤ)) ^ e = ((p ^ e : ℕ) : ℤ) by push_cast; rfl,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxw, hw]
    have hnn : 0 ≤ w % (p : ℤ) ^ e := Int.emod_nonneg _ (by positivity)
    have h1 : (((w % (p : ℤ) ^ e).toNat : ℕ) : ZMod (p ^ e)) =
        ((w % (p : ℤ) ^ e : ℤ) : ZMod (p ^ e)) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    have h2 : ((w % (p : ℤ) ^ e : ℤ) : ZMod (p ^ e)) = (w : ZMod (p ^ e)) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨w / (p : ℤ) ^ e, by rw [Int.emod_def]; push_cast; ring⟩
    push_cast
    rw [h1, h2]; ring
  · set r : ZMod p := (v : ZMod p)
    have hr : r ≠ 0 := fun h => hv ((ZMod.intCast_zmod_eq_zero_iff_dvd v p).1 h)
    obtain ⟨x0, hx0, hx0p, hx0g, hx0r⟩ := exists_start hp7 hr
    have hx0p' : ¬ (p : ℤ) ∣ x0 := fun h =>
      hx0p (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd x0 p).2 h)
    have hg : ¬ (p : ℤ) ∣ (x0 : ℤ) ^ x0 - 1 := by
      intro h
      apply hx0g
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
      push_cast at this
      exact sub_eq_zero.1 this
    have hvx : (p : ℤ) ∣ v - ((x0 : ℤ) ^ x0 - x0) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hx0r]; simp [r]
    obtain ⟨t, ht⟩ := lemma20_7 hp hx0 hx0p' hg v hvx e he
    refine ⟨x0 + p * (p - 1) * t, by omega, ht⟩

end Munchausen
