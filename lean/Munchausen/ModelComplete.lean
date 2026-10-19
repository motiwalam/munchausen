import Munchausen.Congruences

/-!
# Is the refined model complete? (chapter 34)

Most of chapter 34 is computed or concerns the probabilistic model. Its exact facts are:

* Lemma 34.2: a string without the digit 0 has the same `F` under both conventions;
* Lemma 34.3: `F_1(n) = F_0(n) + c_0(n)`, so near-solutions with `c` zeros at offset `D` under
  `0^0 = 1` are those at offset `D + c` under `0^0 = 0`;
* Proposition 34.5 (2): `N_1(b) = #{x ≥ 1 : x^x < b}` is 2 for `5 ≤ b ≤ 27`, 3 for
  `28 ≤ b ≤ 256` and 4 for `257 ≤ b ≤ 3125`, and it is the number of 1-digit strings whose `F`
  has one digit;
* the first step of Proposition 34.10: among the `d`-digit numbers every residue modulo `b - 1`
  occurs exactly `b^(d-1)` times;
* the parity facts behind Corollary 34.11 and Theorem 34.12: for odd `b`,
  `F_0(n) ≡ n (mod 2)` and `F_1(n) ≡ n + c_0(n) (mod 2)`.
-/

namespace Munchausen

/-! ### Lemmas 34.2 and 34.3 -/

/-- **Lemma 34.2** (section 34.1.3). A string without the digit 0 has the same weight sum under
every convention. -/
theorem lemma34_2 {s : List ℕ} (h : 0 ∉ s) (m m' : ℕ) : Fs m s = Fs m' s := by
  induction s with
  | nil => rfl
  | cons d s ih =>
    simp only [List.mem_cons, not_or] at h
    rw [Fs_cons, Fs_cons, w_of_ne_zero m (Ne.symm h.1), w_of_ne_zero m' (Ne.symm h.1), ih h.2]

/-- **Lemma 34.2** for numbers: if `n` has no digit 0, then `F(n)` does not depend on the
convention. -/
theorem lemma34_2_F {b n : ℕ} (h : 0 ∉ Nat.digits b n) (m m' : ℕ) : F b m n = F b m' n :=
  lemma34_2 h m m'

/-- **Lemma 34.3** (section 34.1.3). `n` is a near-solution at offset `D` under `0^0 = 1`
exactly when it is a near-solution at offset `D + c_0(n)` under `0^0 = 0`. -/
theorem lemma34_3 (b n : ℕ) (D : ℤ) :
    (n : ℤ) = F b 1 n + D ↔ (n : ℤ) = F b 0 n + (D + (Nat.digits b n).count 0) := by
  rw [F_one_eq]; push_cast
  constructor <;> intro h <;> linarith

/-! ### Proposition 34.5 (2) -/

/-- `N_1(b)`, the number of digits `x ≥ 1` with `x^x < b` (section 34.3.1). -/
def N1 (b : ℕ) : ℕ := ((Finset.Icc 1 b).filter fun x => x ^ x < b).card

lemma pow_self_le_pow_self {x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) : x ^ x ≤ y ^ y :=
  (Nat.pow_le_pow_left hxy x).trans (Nat.pow_le_pow_right (by omega) hxy)

/-- `N_1(b) = k` when `k^k < b ≤ (k+1)^(k+1)`. -/
theorem N1_eq {b k : ℕ} (hk : 1 ≤ k) (h1 : k ^ k < b) (h2 : b ≤ (k + 1) ^ (k + 1)) :
    N1 b = k := by
  have hkb : k < b := lt_of_le_of_lt (by
    calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ k := Nat.pow_le_pow_right hk hk) h1
  have : (Finset.Icc 1 b).filter (fun x => x ^ x < b) = Finset.Icc 1 k := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx1, -⟩, hx⟩
      refine ⟨hx1, ?_⟩
      by_contra hxk
      have := pow_self_le_pow_self (by omega) (show k + 1 ≤ x by omega)
      omega
    · rintro ⟨hx1, hxk⟩
      exact ⟨⟨hx1, by omega⟩, lt_of_le_of_lt (pow_self_le_pow_self hx1 hxk) h1⟩
  rw [N1, this, Nat.card_Icc]; omega

/-- **Proposition 34.5 (2)** (section 34.3.1). `N_1(b) = 2` for `5 ≤ b ≤ 27`, `3` for
`28 ≤ b ≤ 256` and `4` for `257 ≤ b ≤ 3125`. -/
theorem prop34_5 (b : ℕ) :
    (5 ≤ b → b ≤ 27 → N1 b = 2) ∧ (28 ≤ b → b ≤ 256 → N1 b = 3) ∧
      (257 ≤ b → b ≤ 3125 → N1 b = 4) :=
  ⟨fun h1 h2 => N1_eq (k := 2) (by norm_num) (by norm_num; omega) (by norm_num; omega),
    fun h1 h2 => N1_eq (k := 3) (by norm_num) (by norm_num; omega) (by norm_num; omega),
    fun h1 h2 => N1_eq (k := 4) (by norm_num) (by norm_num; omega) (by norm_num; omega)⟩

/-- **Proposition 34.5 (2)**: the 1-digit strings `x` whose `F = x^x` has one digit are the
`N_1(b)` digits with `x^x < b`. -/
theorem prop34_5_one_digit {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    ((Finset.Icc 1 (b - 1)).filter fun x => F b m x < b).card = N1 b := by
  rw [N1]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hx1, hxb⟩, hF⟩
    have hd : Nat.digits b x = [x] := Nat.digits_of_lt b x (by omega) (by omega)
    rw [F, hd, Fs_singleton, w_of_ne_zero m (by omega)] at hF
    exact ⟨⟨hx1, by omega⟩, hF⟩
  · rintro ⟨⟨hx1, -⟩, hx⟩
    have hxb : x < b := lt_of_le_of_lt (by
      calc x = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ x := Nat.pow_le_pow_right hx1 hx1) hx
    have hd : Nat.digits b x = [x] := Nat.digits_of_lt b x (by omega) hxb
    refine ⟨⟨hx1, by omega⟩, ?_⟩
    rw [F, hd, Fs_singleton, w_of_ne_zero m (by omega)]
    exact hx

/-! ### Proposition 34.10: the residues of the `d`-digit numbers -/

/-- **Proposition 34.10** (section 34.3.4), the exact uniformity: the `d`-digit numbers are
`(b - 1) b^(d-1)` consecutive integers, so every residue modulo `b - 1` occurs exactly
`b^(d-1)` times among them. -/
theorem prop34_10_uniform {b d : ℕ} (hb : 2 ≤ b) (hd : 1 ≤ d) (v : ℕ) :
    ((Finset.Ico (b ^ (d - 1)) (b ^ d)).filter fun n => n ≡ v [MOD b - 1]).card =
      b ^ (d - 1) := by
  have hq : 0 < b - 1 := by omega
  have hlen : b ^ d = b ^ (d - 1) + (b - 1) * b ^ (d - 1) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [hlen, Nat.filter_Ico_card_eq_of_periodic]
  · rw [Nat.count_modEq_card _ hq]
    simp [Nat.mul_div_cancel_left _ hq, Nat.mul_mod_right]
  · intro n
    simp only [eq_iff_iff]
    exact Nat.add_modulus_mul_modEq_iff

/-! ### Corollary 34.11 and Theorem 34.12: the parity character -/

lemma sum_mod_two (s : List ℕ) : s.sum % 2 = (s.countP fun x => x % 2 = 1) % 2 := by
  induction s with
  | nil => simp
  | cons d s ih =>
    rw [List.sum_cons, List.countP_cons]
    rcases Nat.mod_two_eq_zero_or_one d with h | h
    · simp only [h, show ¬ (0 : ℕ) = 1 by norm_num, decide_false, Bool.false_eq_true, ite_false]
      omega
    · simp only [h, decide_true, ite_true]
      omega

/-- **Theorem 34.12** (section 34.3.4), the first step. For odd `b` and `0^0 = 1`,
`F(n) - n ≡ c_0(n) (mod 2)`: the character of order 2 of `Z/(b-1)` is `(-1)^(c_0)` on
`F(n) - n`. -/
theorem theorem34_12_parity {b : ℕ} (hb : Odd b) (n : ℕ) :
    F b 1 n ≡ n + (Nat.digits b n).count 0 [MOD 2] := by
  have h1 := Fs_mod_two 1 (Nat.digits b n)
  have h2 : n ≡ (Nat.digits b n).sum [MOD 2] := Nat.modEq_digits_sum 2 b (Nat.odd_iff.1 hb) n
  have h3 := sum_mod_two (Nat.digits b n)
  unfold Nat.ModEq at h2 ⊢
  rw [F]
  omega

/-- **Corollary 34.11** (section 34.3.4). For odd `b` and `0^0 = 0`, `F(n) ≡ n (mod 2)` for
every `n`, so the character of order 2 is constant on `F(n) - n`. By Theorem 15.2
(`F_modEq_self_iff`) this is the only nontrivial character with this property. -/
theorem corollary34_11 {b : ℕ} (hb : Odd b) (n : ℕ) : F b 0 n ≡ n [MOD 2] := by
  have h := theorem34_12_parity hb n
  rw [F_one_eq] at h
  unfold Nat.ModEq at h ⊢
  omega

end Munchausen
