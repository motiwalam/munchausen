import Munchausen.Defs

/-!
# Basic facts (chapter 1)

* digit strings against numbers: `isMunchausen_iff_isSolution`;
* the length bound, Proposition 1.1, and finitely many solutions per base;
* the digit bound, Proposition 1.2;
* one base per digit string, Proposition 1.3;
* the two conventions, Proposition 1.4;
* the top digit `b - 1` occurs at most twice in a `(b-1)`-digit solution (section 1.7);
* Proposition 1.6: a `b`-digit solution has the digit `b - 1` at least three times.
-/

namespace Munchausen

/-! ### Digit strings and numbers -/

/-- The digits of the value of a valid string are the string itself. -/
lemma digits_P {b : ℕ} (hb : 1 < b) {s : List ℕ} (hlt : ∀ d ∈ s, d < b)
    (hhead : ∀ h : s ≠ [], s.head h ≠ 0) : Nat.digits b (P b s) = s.reverse := by
  rw [P_eq_ofDigits]
  apply Nat.digits_ofDigits b hb
  · simpa using hlt
  · intro h
    rw [List.getLast_reverse]
    exact hhead _

/-- A string is valid in base `b`: its digits lie below `b` and its leading digit is not 0. -/
def Valid (b : ℕ) (s : List ℕ) : Prop := (∀ d ∈ s, d < b) ∧ ∀ h : s ≠ [], s.head h ≠ 0

/-- The Munchausen sum of the value of a valid string is the weight sum of the string. -/
lemma F_P {b m : ℕ} (hb : 1 < b) {s : List ℕ} (hv : Valid b s) : F b m (P b s) = Fs m s := by
  rw [F, digits_P hb hv.1 hv.2, Fs_reverse]

/-- A valid string that is a solution gives a Munchausen number (section 1.1). -/
lemma IsSolution.isMunchausen {b m : ℕ} (hb : 1 < b) {s : List ℕ} (h : IsSolution b m s) :
    IsMunchausen b m (P b s) := by
  rw [IsMunchausen, F, digits_P hb h.lt_base h.head_ne_zero, Fs_reverse, h.eq]

/-- `n` is a Munchausen number exactly when its digit string, most significant digit first,
is a Munchausen string. -/
lemma isMunchausen_iff_isSolution {b m n : ℕ} (hb : 1 < b) :
    IsMunchausen b m n ↔ IsSolution b m (Nat.digits b n).reverse := by
  constructor
  · intro h
    refine ⟨fun d hd => Nat.digits_lt_base hb (List.mem_reverse.1 hd), fun hne => ?_, ?_⟩
    · rw [List.head_reverse]
      exact Nat.getLast_digit_ne_zero b (Nat.digits_ne_nil_iff_ne_zero.1 (by simpa using hne))
    · rw [P_digits_reverse, Fs_reverse]
      exact h.symm
  · intro h
    simpa [P_digits_reverse] using h.isMunchausen hb

/-! ### The weight bound -/

/-- Each digit below `b` weighs at most `(b-1)^(b-1)` when `m ≤ 1`. -/
lemma w_le_of_lt {m b x : ℕ} (hm : m ≤ 1) (hb : 2 ≤ b) (hx : x < b) :
    w m x ≤ (b - 1) ^ (b - 1) := by
  calc w m x ≤ w m (b - 1) := w_le_of_le hm (by omega)
    _ = (b - 1) ^ (b - 1) := w_of_ne_zero m (by omega)

/-- `F(s) ≤ |s| * (b-1)^(b-1)` for a string with digits below `b` (section 1.2). -/
lemma Fs_le {m b : ℕ} (hm : m ≤ 1) (hb : 2 ≤ b) {s : List ℕ} (hs : ∀ d ∈ s, d < b) :
    Fs m s ≤ s.length * (b - 1) ^ (b - 1) := by
  induction s with
  | nil => simp
  | cons d s ih =>
    simp only [Fs_cons, List.length_cons]
    have h1 := w_le_of_lt hm hb (hs d (by simp))
    have h2 := ih (fun x hx => hs x (by simp [hx]))
    nlinarith

/-- A digit string weighs at least each of its digit weights. -/
lemma w_le_Fs {m d : ℕ} {s : List ℕ} (hd : d ∈ s) : w m d ≤ Fs m s := by
  induction s with
  | nil => simp at hd
  | cons e s ih =>
    simp only [Fs_cons]
    rcases List.mem_cons.1 hd with rfl | hd
    · omega
    · have := ih hd; omega

/-! ### Proposition 1.1: the length bound -/

/-- The key inequality of Proposition 1.1 in the form `(c+2) c^c < (c+1)^(c+1)`, `c ≥ 1`. -/
lemma key_ineq (c : ℕ) (hc : 1 ≤ c) : (c + 2) * c ^ c < (c + 1) ^ (c + 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
  have h1 : (e + 1) ^ e ≤ (e + 2) ^ e := Nat.pow_le_pow_left (by omega) e
  have h2 : (e + 1 + 2) * (e + 1) < (e + 2) ^ 2 := by nlinarith
  have h3 : 0 < (e + 1) ^ e := by positivity
  calc (e + 1 + 2) * (e + 1) ^ (e + 1) = ((e + 1 + 2) * (e + 1)) * (e + 1) ^ e := by ring
    _ < (e + 2) ^ 2 * (e + 1) ^ e := by
        exact Nat.mul_lt_mul_of_pos_right h2 h3
    _ ≤ (e + 2) ^ 2 * (e + 2) ^ e := Nat.mul_le_mul_left _ h1
    _ = (e + 1 + 1) ^ (e + 1 + 1) := by ring

/-- For `d ≥ b + 1`, `d (b-1)^(b-1) < b^(d-1)` (proof of Proposition 1.1). -/
lemma length_ineq {b d : ℕ} (hb : 2 ≤ b) (hd : b + 1 ≤ d) :
    d * (b - 1) ^ (b - 1) < b ^ (d - 1) := by
  induction d, hd using Nat.le_induction with
  | base =>
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    simpa using key_ineq c (by omega)
  | succ d hd ih =>
    have hpow : b ^ (d + 1 - 1) = b * b ^ (d - 1) := by
      rw [show d + 1 - 1 = (d - 1) + 1 by omega, pow_succ]; ring
    rw [hpow]
    have h1 : (d + 1) * (b - 1) ^ (b - 1) ≤ 2 * (d * (b - 1) ^ (b - 1)) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    have h2 : 2 * b ^ (d - 1) ≤ b * b ^ (d - 1) := Nat.mul_le_mul_right _ hb
    omega

/-- **Proposition 1.1** (section 1.2). Under `0^0 = 0` or `0^0 = 1`, a Munchausen number in
base `b ≥ 2` has at most `b` digits. -/
theorem length_digits_le {b m n : ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) (h : IsMunchausen b m n) :
    (Nat.digits b n).length ≤ b := by
  by_contra hlen
  replace hlen := not_le.1 hlen
  set d := (Nat.digits b n).length with hd
  have hpow : b ^ (d - 1) ≤ n := (Nat.lt_digits_length_iff (by omega) n).1 (by omega)
  have hF : F b m n ≤ d * (b - 1) ^ (b - 1) :=
    Fs_le hm hb (fun x hx => Nat.digits_lt_base (by omega) hx)
  have := length_ineq hb (show b + 1 ≤ d by omega)
  rw [IsMunchausen] at h
  omega

/-- A Munchausen number in base `b` is below `b ^ b` (Proposition 1.1). -/
lemma lt_pow_self {b m n : ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) (h : IsMunchausen b m n) :
    n < b ^ b :=
  (Nat.digits_length_le_iff (by omega) n).1 (length_digits_le hb hm h)

/-- **Every base has finitely many solutions** (consequence of Proposition 1.1, section 1.2
and section 4.6). -/
theorem finite_setOf_isMunchausen {b m : ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) :
    {n | IsMunchausen b m n}.Finite :=
  (Set.finite_lt_nat (b ^ b)).subset fun _ h => lt_pow_self hb hm h

/-! ### Proposition 1.2: the digit bound -/

/-- **Proposition 1.2** (section 1.2). A `k`-digit solution in base `b` only uses digits `x`
with `x ^ x < b ^ k`. -/
theorem pow_self_lt_of_mem_digits {b m n x : ℕ} (hb : 2 ≤ b) (h : IsMunchausen b m n)
    (hx : x ∈ Nat.digits b n) : x ^ x < b ^ (Nat.digits b n).length := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hx
  have hlt : n < b ^ (Nat.digits b n).length := Nat.lt_base_pow_length_digits (by omega)
  rcases Nat.eq_zero_or_pos x with rfl | hx0
  · have := Nat.pos_of_ne_zero hn
    simp only [pow_zero]
    omega
  · have h1 : w m x ≤ F b m n := w_le_Fs hx
    rw [w_of_ne_zero m hx0.ne'] at h1
    rw [IsMunchausen] at h
    omega

/-! ### Proposition 1.3: one base per digit string -/

/-- The value of a string with at least two digits and a nonzero leading digit grows strictly
with the base (proof of Proposition 1.3). -/
lemma P_strictMono {s : List ℕ} (hs : 2 ≤ s.length) (hhead : ∀ h : s ≠ [], s.head h ≠ 0)
    {b c : ℕ} (hbc : b < c) : P b s < P c s := by
  obtain ⟨d, t, rfl⟩ : ∃ d t, s = d :: t := by
    cases s with
    | nil => simp at hs
    | cons d t => exact ⟨d, t, rfl⟩
  have hd : d ≠ 0 := hhead (by simp)
  have ht : 1 ≤ t.length := by simp at hs; omega
  simp only [P_cons, Nat.cast_id]
  have h1 : b ^ t.length < c ^ t.length := Nat.pow_lt_pow_left hbc (by omega)
  have h2 : P b t ≤ P c t := by
    rw [P_eq_ofDigits, P_eq_ofDigits]
    exact Nat.ofDigits_monotone _ hbc.le
  have h3 : d * b ^ t.length < d * c ^ t.length := Nat.mul_lt_mul_of_pos_left h1 (by omega)
  omega

/-- **Proposition 1.3** (section 1.4). A digit string with at least two digits is a
Munchausen string in at most one base. -/
theorem IsSolution.base_unique {m b c : ℕ} {s : List ℕ} (hs : 2 ≤ s.length)
    (hb : IsSolution b m s) (hc : IsSolution c m s) : b = c := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := P_strictMono hs hb.head_ne_zero h
    rw [hb.eq, hc.eq] at this
    exact lt_irrefl _ this
  · have := P_strictMono hs hb.head_ne_zero h
    rw [hb.eq, hc.eq] at this
    exact lt_irrefl _ this

/-! ### Proposition 1.4: the two conventions -/

/-- **Proposition 1.4** (section 1.5), for strings: `F_1(s) = F_0(s) + z(s)`, where `z(s)` is
the number of zeros. -/
theorem Fs_one_eq (s : List ℕ) : Fs 1 s = Fs 0 s + s.count 0 := by
  induction s with
  | nil => simp
  | cons d s ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [ih]; ring
    · simp [w_of_ne_zero _ hd.ne', ih, hd.ne']; ring

/-- **Proposition 1.4** (section 1.5): `F_1(n) = F_0(n) + z(n)`. -/
theorem F_one_eq (b n : ℕ) : F b 1 n = F b 0 n + (Nat.digits b n).count 0 :=
  Fs_one_eq _

/-- A number without the digit 0 is a solution under both conventions or under neither
(section 1.5). -/
theorem isMunchausen_one_iff_zero {b n : ℕ} (h : 0 ∉ Nat.digits b n) :
    IsMunchausen b 1 n ↔ IsMunchausen b 0 n := by
  simp [IsMunchausen, F_one_eq, List.count_eq_zero_of_not_mem h]

/-- A number with a digit 0 is a solution under at most one convention (section 1.5). -/
theorem not_both_of_mem {b n : ℕ} (h : 0 ∈ Nat.digits b n) :
    ¬ (IsMunchausen b 1 n ∧ IsMunchausen b 0 n) := by
  rintro ⟨h1, h0⟩
  have hc : 0 < (Nat.digits b n).count 0 := List.count_pos_iff.2 h
  simp only [IsMunchausen, F_one_eq] at h1 h0
  omega

/-! ### Section 1.7: the top digit -/

/-- `b^(b-1) < 3 (b-1)^(b-1)` for `b ≥ 2`: `(1 + 1/n)^n < e < 3` (section 1.7). -/
lemma pow_lt_three_mul (b : ℕ) (hb : 2 ≤ b) : b ^ (b - 1) < 3 * (b - 1) ^ (b - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : ((n : ℝ) + 1) / n ≤ Real.exp (1 / n) := by
    have := Real.add_one_le_exp (1 / (n : ℝ))
    rw [div_add_one hn.ne', add_comm (1 : ℝ)] at this
    exact this
  have h2 : (((n : ℝ) + 1) / n) ^ n ≤ Real.exp 1 := by
    calc (((n : ℝ) + 1) / n) ^ n ≤ (Real.exp (1 / n)) ^ n :=
          pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h4 : ((n : ℝ) + 1) ^ n < 3 * (n : ℝ) ^ n := by
    have : (((n : ℝ) + 1) / n) ^ n < 3 := lt_of_le_of_lt h2 h3
    rw [div_pow, div_lt_iff₀ (by positivity)] at this
    exact this
  exact_mod_cast h4

/-- **Section 1.7**. A `(b-1)`-digit solution contains the digit `b-1` at most twice, because
`3 (b-1)^(b-1) > b^(b-1)`. -/
theorem count_top_digit_le_two {b m n : ℕ} (hb : 2 ≤ b) (h : IsMunchausen b m n)
    (hlen : (Nat.digits b n).length = b - 1) : (Nat.digits b n).count (b - 1) ≤ 2 := by
  by_contra hc
  replace hc := not_le.1 hc
  have hlt : n < b ^ (b - 1) := hlen ▸ Nat.lt_base_pow_length_digits (by omega)
  have hF : (Nat.digits b n).count (b - 1) * w m (b - 1) ≤ F b m n := by
    rw [F_def]
    generalize Nat.digits b n = l
    induction l with
    | nil => simp
    | cons x t ih =>
      rw [Fs_cons, List.count_cons]
      split_ifs with hx
      · simp only [beq_iff_eq] at hx; subst hx; nlinarith
      · simpa using ih.trans (Nat.le_add_left _ _)
  rw [w_of_ne_zero m (by omega)] at hF
  have := pow_lt_three_mul b hb
  rw [h] at hF
  nlinarith

/-! ### Proposition 1.6: `b`-digit solutions -/

open Real in
/-- The real inequality behind Proposition 1.6 for `b ≥ 61`:
`2 n^n + (n+1)(n-1)^(n-1) < (n+1)^n` for `n ≥ 60`. -/
lemma large_case (n : ℕ) (hn : 60 ≤ n) :
    2 * (n : ℝ) ^ n + ((n : ℝ) + 1) * ((n : ℝ) - 1) ^ (n - 1) < ((n : ℝ) + 1) ^ n := by
  have ht : (60 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) := by linarith
  -- `A = ((n+1)/n)^n ≥ exp(n/(n+1)) ≥ 1 + x + x^2/2`
  set x : ℝ := (n : ℝ) / ((n : ℝ) + 1) with hx
  have hlog : x ≤ (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + 1 / (n : ℝ) by positivity)
    have e : 1 - (1 + 1 / (n : ℝ))⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    rw [e] at this
    have := mul_le_mul_of_nonneg_left this hpos.le
    calc x = (n : ℝ) * (1 / ((n : ℝ) + 1)) := by rw [hx]; ring
      _ ≤ _ := this
  have hA : 1 + x + x ^ 2 / 2 ≤ (1 + 1 / (n : ℝ)) ^ n := by
    have h1 : (1 + 1 / (n : ℝ)) ^ n = Real.exp ((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [h1]
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    calc 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx0
      _ ≤ _ := Real.exp_le_exp.2 hlog
  -- `B = (1 - 1/n)^(n-1) ≤ exp(-(n-1)/n) ≤ 1/(1 + y + y^2/2)`
  set y : ℝ := ((n - 1 : ℕ) : ℝ) / (n : ℝ) with hy
  have hB : (1 - 1 / (n : ℝ)) ^ (n - 1) ≤ 1 / (1 + y + y ^ 2 / 2) := by
    have h0 : 0 ≤ 1 - 1 / (n : ℝ) := by
      have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hpos]; linarith
      linarith
    have h1 : 1 - 1 / (n : ℝ) ≤ Real.exp (-(1 / (n : ℝ))) := by
      have := Real.add_one_le_exp (-(1 / (n : ℝ))); linarith
    have h2 : (1 - 1 / (n : ℝ)) ^ (n - 1) ≤ Real.exp (-(1 / (n : ℝ))) ^ (n - 1) :=
      pow_le_pow_left₀ h0 h1 _
    have h3 : Real.exp (-(1 / (n : ℝ))) ^ (n - 1) = (Real.exp y)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg, hy]; congr 1; ring
    have hy0 : 0 ≤ y := by rw [hy]; positivity
    have h4 : 1 + y + y ^ 2 / 2 ≤ Real.exp y := Real.quadratic_le_exp_of_nonneg hy0
    have h5 : (Real.exp y)⁻¹ ≤ 1 / (1 + y + y ^ 2 / 2) := by
      rw [one_div]; exact inv_anti₀ (by positivity) h4
    linarith [h2, h3 ▸ h5]
  -- numerical bounds
  have hx60 : 60 / 61 ≤ x := by
    rw [hx, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hy60 : 59 / 60 ≤ y := by
    rw [hy, Nat.cast_sub (by omega), Nat.cast_one, le_div_iff₀ hpos]; linarith
  have hA' : 1 + 60 / 61 + (60 / 61) ^ 2 / 2 ≤ (1 + 1 / (n : ℝ)) ^ n := by
    have : (60 / 61 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by norm_num) hx60 2
    linarith
  have hB' : (1 - 1 / (n : ℝ)) ^ (n - 1) ≤ 1 / (1 + 59 / 60 + (59 / 60) ^ 2 / 2) := by
    refine hB.trans ?_
    apply one_div_le_one_div_of_le (by norm_num)
    have : (59 / 60 : ℝ) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) hy60 2
    linarith
  have hn1 : 1 + 1 / (n : ℝ) ≤ 61 / 60 := by
    have : 1 / (n : ℝ) ≤ 1 / 60 := one_div_le_one_div_of_le (by norm_num) ht
    linarith
  set A := (1 + 1 / (n : ℝ)) ^ n
  set B := (1 - 1 / (n : ℝ)) ^ (n - 1)
  have hB0 : 0 ≤ B := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hpos]; linarith
    exact pow_nonneg (by linarith) _
  have hkey : 2 + (1 + 1 / (n : ℝ)) * B < A := by
    have h1 : (1 + 1 / (n : ℝ)) * B ≤ 61 / 60 * (1 / (1 + 59 / 60 + (59 / 60) ^ 2 / 2)) :=
      mul_le_mul hn1 hB' hB0 (by norm_num)
    have h2 : (2 : ℝ) + 61 / 60 * (1 / (1 + 59 / 60 + (59 / 60) ^ 2 / 2)) <
        1 + 60 / 61 + (60 / 61) ^ 2 / 2 := by norm_num
    linarith
  -- back to the powers
  set N := (n : ℝ) ^ (n - 1)
  have hN : 0 < N := by positivity
  have e1 : ((n : ℝ) + 1) ^ n = (n : ℝ) * N * A := by
    have : ((n : ℝ) + 1) = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
    rw [this, mul_pow]
    have : (n : ℝ) ^ n = (n : ℝ) * N := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
  have e2 : ((n : ℝ) - 1) ^ (n - 1) = N * B := by
    have : ((n : ℝ) - 1) = (n : ℝ) * (1 - 1 / (n : ℝ)) := by field_simp
    rw [this, mul_pow]
  have e3 : (n : ℝ) ^ n = (n : ℝ) * N := by
    rw [← pow_succ']; congr 1; omega
  rw [e1, e2, e3]
  have e4 : ((n : ℝ) + 1) = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
  rw [e4]
  have hnN : 0 < (n : ℝ) * N := by positivity
  nlinarith [mul_lt_mul_of_pos_left hkey hnN]

set_option maxRecDepth 100000 in
lemma prop1_6_small : ∀ b, b < 61 → 7 ≤ b →
    2 * (b - 1) ^ (b - 1) + b * (b - 2) ^ (b - 2) < b ^ (b - 1) := by
  decide

/-- The inequality of Proposition 1.6: `2 (b-1)^(b-1) + b (b-2)^(b-2) < b^(b-1)` for `b ≥ 7`. -/
lemma prop1_6_ineq {b : ℕ} (hb : 7 ≤ b) :
    2 * (b - 1) ^ (b - 1) + b * (b - 2) ^ (b - 2) < b ^ (b - 1) := by
  rcases Nat.lt_or_ge b 61 with h | h
  · exact prop1_6_small b h hb
  · obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
    have := large_case n (by omega)
    simp only [Nat.add_sub_cancel, show n + 1 - 2 = n - 1 by omega]
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have : ((2 * n ^ n + (n + 1) * (n - 1) ^ (n - 1) : ℕ) : ℝ) < (((n + 1) ^ n : ℕ) : ℝ) := by
      push_cast; rw [hc]; exact this
    exact_mod_cast this

lemma Fs_le_count {m b : ℕ} (hm : m ≤ 1) (hb : 3 ≤ b) {l : List ℕ} (hl : ∀ d ∈ l, d < b) :
    Fs m l ≤ l.count (b - 1) * (b - 1) ^ (b - 1) + l.length * (b - 2) ^ (b - 2) := by
  induction l with
  | nil => simp
  | cons d t ih =>
    have ih' := ih (fun e he => hl e (by simp [he]))
    have hd := hl d (by simp)
    rw [Fs_cons, List.count_cons, List.length_cons]
    by_cases hdb : d = b - 1
    · subst hdb
      rw [w_of_ne_zero m (by omega)]
      simp only [beq_self_eq_true, ite_true]
      rw [add_mul, add_mul, one_mul, one_mul]
      omega
    · have : w m d ≤ (b - 2) ^ (b - 2) := by
        calc w m d ≤ w m (b - 2) := w_le_of_le hm (by omega)
          _ = (b - 2) ^ (b - 2) := w_of_ne_zero m (by omega)
      have : (d == b - 1) = false := by simpa using hdb
      rw [this]
      simp only [Bool.false_eq_true, ite_false, add_zero]
      rw [add_mul, one_mul]
      omega

/-- **Proposition 1.6** (section 1.8). For `b ≥ 7`, a `b`-digit solution contains the digit
`b - 1` at least three times. -/
theorem prop1_6 {b m n : ℕ} (hb : 7 ≤ b) (hm : m ≤ 1) (h : IsMunchausen b m n)
    (hlen : (Nat.digits b n).length = b) : 3 ≤ (Nat.digits b n).count (b - 1) := by
  by_contra hc
  have hF := Fs_le_count hm (by omega) (l := Nat.digits b n)
    (fun d hd => Nat.digits_lt_base (by omega) hd)
  rw [hlen] at hF
  have hn : b ^ (b - 1) ≤ n := (Nat.lt_digits_length_iff (by omega) n).1 (by omega)
  have hX : (Nat.digits b n).count (b - 1) * (b - 1) ^ (b - 1) ≤ 2 * (b - 1) ^ (b - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have := prop1_6_ineq hb
  rw [IsMunchausen, F_def] at h
  omega

end Munchausen
