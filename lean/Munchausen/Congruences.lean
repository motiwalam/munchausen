import Munchausen.Basic

/-!
# Congruences (section 1.6, Proposition 10.2, Theorem 15.2)

* `n ≡ digit sum (mod b-1)` and Proposition 1.5;
* the parity rules of section 1.6: zeros in odd bases under `0^0 = 1`, the rules modulo 4
  and modulo 3 under `0^0 = 0`, the last digit in even bases;
* Proposition 10.2: `b - 1` is the only modulus fixed by the digit multiset;
* Theorem 15.2 and Corollary 15.3: the parity invariant of `n ↦ F(n)`.
-/

namespace Munchausen

/-! ### The digit-sum identity -/

/-- In any commutative ring, `b - 1` divides `P_s(b) - (digit sum of s)` (section 1.6). -/
lemma sub_one_dvd_P_sub_sum {R : Type*} [CommRing R] (b : R) (s : List ℕ) :
    b - 1 ∣ P b s - (s.sum : R) := by
  have h := Nat.dvd_ofDigits_sub_ofDigits (k := b - 1) (a := b) (b := 1) (dvd_refl _) s.reverse
  have h1 : Nat.ofDigits (1 : R) s.reverse = (s.sum : R) := by
    rw [← Nat.cast_one, ← Nat.coe_ofDigits, Nat.ofDigits_one, List.sum_reverse]
  rwa [h1] at h

/-- Every number is congruent to its digit sum modulo `b - 1` (section 1.6). -/
lemma P_modEq_sum {b : ℕ} (hb : 1 ≤ b) (s : List ℕ) : P b s ≡ s.sum [MOD b - 1] := by
  have h := sub_one_dvd_P_sub_sum (b : ℤ) s
  rw [Nat.modEq_iff_dvd]
  have : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
  rw [this]
  have h2 := dvd_neg.2 h
  simpa [cast_P] using h2

/-- **Proposition 1.5** (section 1.6). For every solution, the weight sum is congruent to the
digit sum modulo `b - 1`; equivalently `sum (w(x) - x) ≡ 0 (mod b-1)`. -/
theorem Fs_modEq_sum {b m n : ℕ} (hb : 1 ≤ b) (h : IsMunchausen b m n) :
    F b m n ≡ (Nat.digits b n).sum [MOD b - 1] := by
  have := P_modEq_sum hb (Nat.digits b n).reverse
  rw [P_digits_reverse, List.sum_reverse] at this
  rw [h]
  exact this

/-- The string form of Proposition 1.5. -/
theorem IsSolution.Fs_modEq_sum {b m : ℕ} {s : List ℕ} (hb : 1 ≤ b) (h : IsSolution b m s) :
    Fs m s ≡ s.sum [MOD b - 1] := by
  rw [← h.eq]
  exact P_modEq_sum hb s

/-! ### Residues of `x ^ x` modulo 2, 4 and 3 -/

/-- If `a ∣ x` and `n ≤ x`, then `a ^ n ∣ x ^ x`. -/
lemma pow_dvd_pow_self {a x n : ℕ} (h : a ∣ x) (hn : n ≤ x) : a ^ n ∣ x ^ x :=
  (pow_dvd_pow_of_dvd h n).trans (pow_dvd_pow x hn)

private lemma three_pow_odd_mod_four (j : ℕ) : 3 ^ (2 * j + 1) % 4 = 3 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

private lemma two_pow_even_mod_three (j : ℕ) : 2 ^ (2 * j) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]; norm_num

private lemma two_pow_odd_mod_three (j : ℕ) : 2 ^ (2 * j + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

/-- `x ^ x ≡ x (mod 2)` for `x ≥ 1` (section 1.6). -/
lemma pow_self_modEq_two (x : ℕ) (hx : 1 ≤ x) : x ^ x ≡ x [MOD 2] := by
  unfold Nat.ModEq
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h]
  · rw [zero_pow (by omega)]; simp
  · simp

/-- `x ^ x ≡ x (mod 4)` unless `x ≡ 2 (mod 4)`, where `x ^ x ≡ x + 2` (section 1.6). -/
lemma pow_self_modEq_four (x : ℕ) (hx : 1 ≤ x) :
    x ^ x ≡ x + 2 * (if x % 4 = 2 then 1 else 0) [MOD 4] := by
  unfold Nat.ModEq
  rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with h | h | h | h
  · have := pow_dvd_pow_self (a := 2) (n := 2) (x := x) (by omega) (by omega)
    simp only [h, show (0:ℕ) ≠ 2 by norm_num, ite_false]; norm_num at this; omega
  · rw [Nat.pow_mod, h]; simp; omega
  · have := pow_dvd_pow_self (a := 2) (n := 2) (x := x) (by omega) (by omega)
    simp only [h, ite_true]; norm_num at this; omega
  · rw [Nat.pow_mod, h]
    obtain ⟨j, hj⟩ : ∃ j, x = 2 * j + 1 := ⟨x / 2, by omega⟩
    rw [hj, three_pow_odd_mod_four]; simp; omega

/-- `x ^ x ≡ x (mod 3)` unless `x ≡ 2 (mod 6)`, where `x ^ x ≡ x + 2` (section 1.6). -/
lemma pow_self_modEq_three (x : ℕ) (hx : 1 ≤ x) :
    x ^ x ≡ x + 2 * (if x % 6 = 2 then 1 else 0) [MOD 3] := by
  unfold Nat.ModEq
  rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 6 = 2 ∨ x % 6 = 5) with h | h | h | h
  · have := pow_dvd_pow_self (a := 3) (n := 1) (x := x) (by omega) (by omega)
    simp only [show ¬ x % 6 = 2 by omega, ite_false]; norm_num at this; omega
  · simp only [show ¬ x % 6 = 2 by omega, ite_false]
    rw [Nat.pow_mod, h]; simp; omega
  · simp only [h, ite_true]
    rw [Nat.pow_mod, show x % 3 = 2 by omega]
    obtain ⟨j, hj⟩ : ∃ j, x = 2 * j := ⟨x / 2, by omega⟩
    rw [hj, two_pow_even_mod_three]; omega
  · simp only [show ¬ x % 6 = 2 by omega, ite_false]
    rw [Nat.pow_mod, show x % 3 = 2 by omega]
    obtain ⟨j, hj⟩ : ∃ j, x = 2 * j + 1 := ⟨x / 2, by omega⟩
    rw [hj, two_pow_odd_mod_three]; omega

/-! ### Weight sums modulo small numbers -/

/-- If every digit weight is congruent to `g x`, the weight sum is congruent to the sum of
the `g x`. -/
lemma Fs_modEq_map {q m : ℕ} (g : ℕ → ℕ) (hg : ∀ x, w m x ≡ g x [MOD q]) (s : List ℕ) :
    Fs m s ≡ (s.map g).sum [MOD q] := by
  induction s with
  | nil => rfl
  | cons d s ih => simpa using Nat.ModEq.add (hg d) ih

lemma sum_map_add_two_mul_ite (p : ℕ → Prop) [DecidablePred p] (s : List ℕ) :
    (s.map (fun x => x + 2 * (if p x then 1 else 0))).sum = s.sum + 2 * s.countP p := by
  induction s with
  | nil => simp
  | cons d s ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.countP_cons]
    split_ifs <;> simp_all <;> ring

/-- Under `0^0 = 0`, `F(s) ≡ digit sum (mod 2)` for every string (section 1.6). -/
theorem Fs_zero_modEq_two (s : List ℕ) : Fs 0 s ≡ s.sum [MOD 2] := by
  have := Fs_modEq_map (q := 2) (m := 0) id (fun x => by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rfl
    · rw [w_of_ne_zero 0 hx.ne']; exact pow_self_modEq_two x hx) s
  simpa using this

/-- Under `0^0 = 0`, `F(s) ≡ digit sum + 2 * #{digits ≡ 2 (mod 4)} (mod 4)`. -/
lemma Fs_zero_modEq_four (s : List ℕ) :
    Fs 0 s ≡ s.sum + 2 * s.countP (fun x => x % 4 = 2) [MOD 4] := by
  rw [← sum_map_add_two_mul_ite]
  apply Fs_modEq_map
  intro x
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rfl
  · rw [w_of_ne_zero 0 hx.ne']; exact pow_self_modEq_four x hx

/-- Under `0^0 = 0`, `F(s) ≡ digit sum + 2 * #{digits ≡ 2 (mod 6)} (mod 3)`. -/
lemma Fs_zero_modEq_three (s : List ℕ) :
    Fs 0 s ≡ s.sum + 2 * s.countP (fun x => x % 6 = 2) [MOD 3] := by
  rw [← sum_map_add_two_mul_ite]
  apply Fs_modEq_map
  intro x
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rfl
  · rw [w_of_ne_zero 0 hx.ne']; exact pow_self_modEq_three x hx

/-! ### The rules of section 1.6 -/

lemma IsSolution.modEq_of_dvd {b m q : ℕ} {s : List ℕ} (hb : 1 ≤ b) (h : IsSolution b m s)
    (hq : q ∣ b - 1) : Fs m s ≡ s.sum [MOD q] :=
  Nat.ModEq.of_dvd hq (h.Fs_modEq_sum hb)

/-- **Section 1.6**, odd bases under `0^0 = 1`: a solution has an even number of zeros. -/
theorem IsSolution.even_count_zero {b : ℕ} {s : List ℕ} (hb : Odd b) (h : IsSolution b 1 s) :
    Even (s.count 0) := by
  have h2 : 2 ∣ b - 1 := by
    obtain ⟨k, rfl⟩ := hb
    simp
  have hmod := h.modEq_of_dvd (by obtain ⟨k, rfl⟩ := hb; omega) h2
  rw [Fs_one_eq] at hmod
  have := Fs_zero_modEq_two s
  rw [Nat.even_iff]
  unfold Nat.ModEq at hmod this
  omega

/-- **Section 1.6**, bases `b ≡ 1 (mod 4)` under `0^0 = 0`: a solution has an even number of
digits `≡ 2 (mod 4)`. -/
theorem IsSolution.even_countP_mod_four {b : ℕ} {s : List ℕ} (hb : b % 4 = 1)
    (h : IsSolution b 0 s) : Even (s.countP (fun x => x % 4 = 2)) := by
  have hmod := h.modEq_of_dvd (q := 4) (by omega) (by omega)
  have := Fs_zero_modEq_four s
  rw [Nat.even_iff]
  unfold Nat.ModEq at hmod this
  omega

/-- **Section 1.6**, bases `b ≡ 1 (mod 3)` under `0^0 = 0`: the number of digits
`≡ 2 (mod 6)` of a solution is a multiple of 3. -/
theorem IsSolution.three_dvd_countP_mod_six {b : ℕ} {s : List ℕ} (hb : b % 3 = 1)
    (h : IsSolution b 0 s) : 3 ∣ s.countP (fun x => x % 6 = 2) := by
  have hmod := h.modEq_of_dvd (q := 3) (by omega) (by omega)
  have := Fs_zero_modEq_three s
  unfold Nat.ModEq at hmod this
  omega

/-- The parity of a weight sum: `F(s) ≡ #{odd digits} + m * #{zeros} (mod 2)`. -/
lemma Fs_mod_two (m : ℕ) (s : List ℕ) :
    Fs m s % 2 = (s.countP (fun x => x % 2 = 1) + m * s.count 0) % 2 := by
  induction s with
  | nil => simp
  | cons d s ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have e1 : List.countP (fun x => x % 2 = 1) (0 :: s) = List.countP (fun x => x % 2 = 1) s := by
        simp
      have e2 : List.count 0 (0 :: s) = List.count 0 s + 1 := by simp
      rw [Fs_cons, e1, e2, w_zero, Nat.mul_add]
      omega
    · have h2 := pow_self_modEq_two d hd
      unfold Nat.ModEq at h2
      have e2 : List.count 0 (d :: s) = List.count 0 s := by
        rw [List.count_cons]; simp only [beq_iff_eq]; split_ifs <;> omega
      rw [Fs_cons, w_of_ne_zero m hd.ne', e2, List.countP_cons]
      rcases Nat.mod_two_eq_zero_or_one d with h | h
      · simp only [h, show ¬ (0 : ℕ) = 1 by norm_num, decide_false, Bool.false_eq_true, ite_false]
        omega
      · simp only [h, decide_true, ite_true]
        omega

/-- **Section 1.6**, even bases: the last digit of a solution is odd exactly when the number of
odd digits, plus the number of zeros under `0^0 = 1`, is odd. -/
theorem IsMunchausen.last_digit_parity {b m n : ℕ} (heven : Even b) (h : IsMunchausen b m n) :
    n % b % 2 =
      ((Nat.digits b n).countP (fun x => x % 2 = 1) + m * (Nat.digits b n).count 0) % 2 := by
  have h1 : n % b % 2 = n % 2 := Nat.mod_mod_of_dvd n (even_iff_two_dvd.1 heven)
  rw [h1, ← Fs_mod_two, ← F_def, h]

/-! ### Proposition 10.2: the only invariant residue -/

/-- **Proposition 10.2** (section 10.4). The residue of `n` modulo `M` depends only on the
digit multiset of `n`, for all numbers with at least 2 digits, exactly when `M ∣ b - 1`. -/
theorem residue_invariant_iff {b M : ℕ} (hb : 2 ≤ b) :
    (∀ s t : List ℕ, Valid b s → Valid b t → 2 ≤ s.length → s.Perm t →
        P b s ≡ P b t [MOD M]) ↔ M ∣ b - 1 := by
  constructor
  · intro h
    have hv1 : Valid b [1, 1, 0] := ⟨by simp; omega, by simp⟩
    have hv2 : Valid b [1, 0, 1] := ⟨by simp; omega, by simp⟩
    have := h [1, 1, 0] [1, 0, 1] hv1 hv2 (by simp) (by decide)
    have e1 : P b [1, 1, 0] = (b ^ 2 + 1) + (b - 1) := by
      simp [P_cons]; ring_nf; omega
    have e2 : P b [1, 0, 1] = (b ^ 2 + 1) + 0 := by simp [P_cons]
    rw [e1, e2] at this
    exact (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_left_cancel' _ this)
  · intro hM s t _ _ _ hst
    have h1 := (P_modEq_sum (by omega) s).of_dvd hM
    have h2 := (P_modEq_sum (by omega) t).of_dvd hM
    rw [hst.sum_eq] at h1
    exact h1.trans h2.symm

/-! ### Theorem 15.2: the parity invariant of `n ↦ F(n)` -/

/-- **Theorem 15.2** (section 15.1.3). Let `b ≥ 3`, `q ≥ 2` and `m ∈ {0, 1}`. Then
`F(n) ≡ n (mod q)` for every `n ≥ 1` if and only if `q = 2`, `b` is odd and `0^0 = 0`. -/
theorem F_modEq_self_iff {b m q : ℕ} (hb : 3 ≤ b) (hq : 2 ≤ q) (hm : m ≤ 1) :
    (∀ n, 1 ≤ n → F b m n ≡ n [MOD q]) ↔ q = 2 ∧ Odd b ∧ m = 0 := by
  constructor
  · intro H
    have v2 : Valid b [2] := ⟨by simp; omega, by simp⟩
    have v10 : Valid b [1, 0] := ⟨by simp; omega, by simp⟩
    have v11 : Valid b [1, 1] := ⟨by simp; omega, by simp⟩
    have h2 := H (P b [2]) (by simp)
    have h10 := H (P b [1, 0]) (by simp [P_cons]; omega)
    have h11 := H (P b [1, 1]) (by simp [P_cons])
    rw [F_P (by omega) v2] at h2
    rw [F_P (by omega) v10] at h10
    rw [F_P (by omega) v11] at h11
    simp [P_cons] at h2 h10 h11
    -- h2 : 4 ≡ 2, h10 : m + 1 ≡ b, h11 : 2 ≡ b + 1
    have hb1 : b ≡ 1 [MOD q] := Nat.ModEq.add_right_cancel' 1 (h11.symm.trans (by rfl))
    have hm0 : m ≡ 0 [MOD q] :=
      Nat.ModEq.add_left_cancel' 1 (by simpa [add_comm] using h10.trans hb1)
    have hm' : m = 0 := by
      unfold Nat.ModEq at hm0
      rwa [Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at hm0
    have hq2 : q ∣ 2 := by
      have : 2 + 2 ≡ 2 + 0 [MOD q] := by simpa using h2
      exact (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_left_cancel' 2 this)
    have hq' : q = 2 := le_antisymm (Nat.le_of_dvd (by norm_num) hq2) hq
    refine ⟨hq', ?_, hm'⟩
    subst hq'
    rw [Nat.odd_iff]
    exact hb1
  · rintro ⟨rfl, hodd, rfl⟩ n _
    have h1 := Fs_zero_modEq_two (Nat.digits b n)
    have h2 := (P_modEq_sum (b := b) (by omega) (Nat.digits b n).reverse).of_dvd
      (show 2 ∣ b - 1 by obtain ⟨k, rfl⟩ := hodd; omega)
    rw [P_digits_reverse, List.sum_reverse] at h2
    exact h1.trans h2.symm

/-- The weight sum of a positive number is positive: its leading digit weighs at least 1. -/
lemma one_le_F {b m n : ℕ} (hn : n ≠ 0) : 1 ≤ F b m n := by
  have hne : Nat.digits b n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hn
  exact (one_le_w (Nat.getLast_digit_ne_zero b hn)).trans (w_le_Fs (List.getLast_mem hne))

/-- `F` maps the numbers below `b ^ b` into themselves (proof of Proposition 15.1). -/
lemma F_lt_pow_self {b m n : ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) (hn : n < b ^ b) : F b m n < b ^ b := by
  have hlen : (Nat.digits b n).length ≤ b := (Nat.digits_length_le_iff (by omega) n).2 hn
  have h1 := Fs_le hm hb (s := Nat.digits b n) (fun x hx => Nat.digits_lt_base (by omega) hx)
  have h2 : (b - 1) ^ (b - 1) < b ^ (b - 1) := Nat.pow_lt_pow_left (by omega) (by omega)
  have h3 : b ^ b = b * b ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [F_def]
  calc Fs m (Nat.digits b n) ≤ (Nat.digits b n).length * (b - 1) ^ (b - 1) := h1
    _ ≤ b * (b - 1) ^ (b - 1) := Nat.mul_le_mul_right _ hlen
    _ < b * b ^ (b - 1) := Nat.mul_lt_mul_of_pos_left h2 (by omega)
    _ = b ^ b := h3.symm

/-- A map from a finite set into itself has a periodic point in it. -/
lemma exists_periodic_of_mapsTo {f : ℕ → ℕ} {S : Set ℕ} (hS : S.Finite) (hf : Set.MapsTo f S S)
    {x : ℕ} (hx : x ∈ S) : ∃ y ∈ S, ∃ k, 1 ≤ k ∧ f^[k] y = y := by
  have hmem : ∀ i, f^[i] x ∈ S := fun i => hf.iterate i hx
  have := hS.to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun i : ℕ => (⟨f^[i] x, hmem i⟩ : S))
  simp only [Subtype.mk.injEq] at heq
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨f^[i] x, hmem i, j - i, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le, heq]
  · refine ⟨f^[j] x, hmem j, i - j, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le, heq]

/-- **Corollary 15.3** (section 15.1.3). In an odd base under `0^0 = 0`, the map `n ↦ F(n)`
has a cycle of even positive numbers. So every odd base has a cycle besides the fixed point 1. -/
theorem exists_even_cycle {b : ℕ} (hb : 3 ≤ b) (hodd : Odd b) :
    ∃ n, 1 ≤ n ∧ Even n ∧ ∃ k, 1 ≤ k ∧ (F b 0)^[k] n = n := by
  let S : Set ℕ := {n | 1 ≤ n ∧ n < b ^ b ∧ Even n}
  have hS : S.Finite := (Set.finite_lt_nat (b ^ b)).subset fun n hn => hn.2.1
  have hmaps : Set.MapsTo (F b 0) S S := by
    rintro n ⟨h1, h2, h3⟩
    refine ⟨one_le_F (by omega), F_lt_pow_self (by omega) (by norm_num) h2, ?_⟩
    have := ((F_modEq_self_iff hb le_rfl (by norm_num)).2 ⟨rfl, hodd, rfl⟩) n h1
    rw [Nat.even_iff] at h3 ⊢
    unfold Nat.ModEq at this
    omega
  have h2S : 2 ∈ S := by
    refine ⟨by norm_num, ?_, even_two⟩
    calc 2 < b := by omega
      _ = b ^ 1 := (pow_one b).symm
      _ ≤ b ^ b := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨y, ⟨hy1, -, hy3⟩, k, hk, hyk⟩ := exists_periodic_of_mapsTo hS hmaps h2S
  exact ⟨y, hy1, hy3, k, hk, hyk⟩

end Munchausen
