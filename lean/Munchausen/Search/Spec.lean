import Munchausen.Search
import Munchausen.SearchRules

/-!
# The exact search: specification

This file states what the exact search of `fast/src/search.rs` must compute, and proves the
facts about solutions that the search relies on.

* `topDigits b d n L` lists the top `L` digits of a `d`-digit number `n`, leading digit
  first. `digitCount b d n x` counts the digit `x` among all `d` of them.
* A `d`-digit number is a solution exactly when its digit counts `c` satisfy
  `∑ c_x w(x) = n` (`isMunchausen_iff_sum`). This is why the search can visit count vectors
  instead of numbers.
* Proposition 1.1 bounds the length (`length_le_maxLen`), Proposition 1.2 bounds the digits
  (`pow_self_lt_of_digitCount_pos`), and Proposition 1.5 gives the residue condition on the
  counts (`sum_count_g_mod`).
* `solutions b m` is the specification: the positive solutions in base `b` under `0^0 = m`,
  as a `Finset`.

The number 0 is left out. Mathlib writes 0 with no digits, so `IsMunchausen b m 0` always
holds, while the Rust code writes it as the string `(0)`, a solution only under `0^0 = 0`.
`Examples.lean` adds it back when it compares with the Rust output.
-/

namespace Munchausen

namespace ExactSearch

open Finset

/-! ### Digits of a `d`-digit number, leading digit first -/

/-- The top `L` digits of a `d`-digit number `n` in base `b`, leading digit first. -/
def topDigits (b d n L : ℕ) : List ℕ := (List.range L).map (topDigit b d n)

/-- How often the digit `x` occurs among the `d` digits of `n`. For a solution these are the
counts `c_x` that the search enumerates. -/
def digitCount (b d n x : ℕ) : ℕ := (topDigits b d n d).count x

lemma topDigit_lt {b : ℕ} (hb : 0 < b) (d n j : ℕ) : topDigit b d n j < b :=
  Nat.mod_lt _ hb

@[simp] lemma length_topDigits (b d n L : ℕ) : (topDigits b d n L).length = L := by
  simp [topDigits]

lemma topDigits_add (b d n L s : ℕ) :
    topDigits b d n (L + s) =
      topDigits b d n L ++ (List.range s).map (fun i => topDigit b d n (L + i)) := by
  simp [topDigits, List.range_add, List.map_append, List.map_map, Function.comp_def]

lemma mem_topDigits_lt {b : ℕ} (hb : 0 < b) {d n L x : ℕ} (hx : x ∈ topDigits b d n L) :
    x < b := by
  simp only [topDigits, List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact topDigit_lt hb _ _ _

lemma count_topDigits_mono (b d n x : ℕ) {L L' : ℕ} (h : L ≤ L') :
    (topDigits b d n L).count x ≤ (topDigits b d n L').count x := by
  obtain ⟨s, rfl⟩ : ∃ s, L' = L + s := ⟨L' - L, by omega⟩
  rw [topDigits_add, List.count_append]
  omega

/-- The counts of a list of digits below `b`, weighted by `f`, add up to the sum of `f` over
the list. -/
lemma sum_range_count_mul {b : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < b) (f : ℕ → ℕ) :
    ∑ x ∈ range b, l.count x * f x = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∈ range b := mem_range.2 (hl a (by simp))
    simp only [List.count_cons, List.map_cons, List.sum_cons, beq_iff_eq]
    rw [← ih (fun x hx => hl x (by simp [hx]))]
    simp only [add_mul, sum_add_distrib, ite_mul, one_mul, zero_mul]
    simp only [sum_ite_eq, ha, ↓reduceIte]
    ring

lemma sum_range_count {b : ℕ} (l : List ℕ) (hl : ∀ x ∈ l, x < b) :
    ∑ x ∈ range b, l.count x = l.length := by
  have := sum_range_count_mul l hl (fun _ => 1)
  simpa using this

/-- The `L` top digits hold `L` digits below `b`. -/
lemma sum_count_topDigits {b : ℕ} (hb : 0 < b) (d n L : ℕ) :
    ∑ x ∈ range b, (topDigits b d n L).count x = L := by
  rw [sum_range_count _ (fun x hx => mem_topDigits_lt hb hx), length_topDigits]

lemma sum_digitCount {b : ℕ} (hb : 0 < b) (d n : ℕ) : ∑ x ∈ range b, digitCount b d n x = d :=
  sum_count_topDigits hb d n d

lemma digitCount_eq_zero {b : ℕ} (hb : 0 < b) {d n x : ℕ} (hx : b ≤ x) : digitCount b d n x = 0 :=
  List.count_eq_zero.2 fun h => by have := mem_topDigits_lt hb h; omega

lemma count_topDigits_le_digitCount (b d n x : ℕ) {L : ℕ} (hL : L ≤ d) :
    (topDigits b d n L).count x ≤ digitCount b d n x :=
  count_topDigits_mono b d n x hL

/-- Two numbers with the same quotient by `b^(d-L)` have the same top `L` digits. -/
lemma topDigits_eq_of_div_eq {b d n n' L : ℕ} (hL : L ≤ d)
    (h : n / b ^ (d - L) = n' / b ^ (d - L)) : topDigits b d n L = topDigits b d n' L := by
  simp only [topDigits]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  simp only [topDigit]
  rw [div_eq_of_div_eq (show d - L ≤ d - 1 - j by omega) h]

/-! ### From `Nat.digits` to the top digits -/

/-- The base-`b` digits of a `d`-digit number, leading digit first, are its `d` top digits. -/
lemma digits_reverse_eq_topDigits {b d n : ℕ} (hb : 2 ≤ b) (h1 : b ^ (d - 1) ≤ n)
    (h2 : n < b ^ d) (hd : 1 ≤ d) : (Nat.digits b n).reverse = topDigits b d n d := by
  have hlen : (Nat.digits b n).length = d := by
    have a := (Nat.digits_length_le_iff (by omega) n).2 h2
    have c := (Nat.lt_digits_length_iff (by omega) n).2 (show b ^ (d - 1) ≤ n from h1)
    omega
  refine List.ext_getElem (by simp [hlen]) fun i hi1 hi2 => ?_
  rw [List.getElem_reverse]
  have hi : i < d := by simpa using hi2
  have := Nat.getD_digits n (d - 1 - i) hb
  rw [List.getD_eq_getElem _ _ (by omega)] at this
  simp only [hlen, topDigits, List.getElem_map, List.getElem_range, topDigit]
  rw [← this]

/-- The number of digits of a positive number `n` puts `n` between `b^(d-1)` and `b^d`. -/
lemma pow_le_of_digits_length {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    b ^ ((Nat.digits b n).length - 1) ≤ n ∧ n < b ^ (Nat.digits b n).length ∧
      1 ≤ (Nat.digits b n).length := by
  have hpos : 1 ≤ (Nat.digits b n).length := by
    rw [Nat.digits_def' (by omega) hn]
    simp
  refine ⟨?_, Nat.lt_base_pow_length_digits (by omega), hpos⟩
  exact (Nat.lt_digits_length_iff (by omega) n).1 (by omega)

/-- **The count form of `F`.** For a `d`-digit number, `F(n) = ∑_x c_x w(x)`, where `c_x` is
the number of digits `x` of `n`. -/
lemma F_eq_sum_digitCount {b m d n : ℕ} (hb : 2 ≤ b) (h1 : b ^ (d - 1) ≤ n) (h2 : n < b ^ d)
    (hd : 1 ≤ d) : F b m n = ∑ x ∈ range b, digitCount b d n x * w m x := by
  unfold digitCount
  rw [F, ← Fs_reverse, digits_reverse_eq_topDigits hb h1 h2 hd, Fs,
    sum_range_count_mul _ (fun x hx => mem_topDigits_lt (by omega) hx)]

/-- A `d`-digit number is a solution exactly when its digit counts `c` satisfy
`∑ c_x w(x) = n`. -/
theorem isMunchausen_iff_sum {b m d n : ℕ} (hb : 2 ≤ b) (h1 : b ^ (d - 1) ≤ n) (h2 : n < b ^ d)
    (hd : 1 ≤ d) : IsMunchausen b m n ↔ ∑ x ∈ range b, digitCount b d n x * w m x = n := by
  rw [IsMunchausen, F_eq_sum_digitCount hb h1 h2 hd]

/-! ### The facts about solutions that the search uses -/

/-- **Proposition 1.2** in count form: a digit of a `d`-digit solution has `x^x < b^d`. -/
lemma pow_self_lt_of_digitCount_pos {b m d n x : ℕ} (hb : 2 ≤ b) (h1 : b ^ (d - 1) ≤ n)
    (h2 : n < b ^ d) (hd : 1 ≤ d) (hsol : IsMunchausen b m n) (hx : 0 < digitCount b d n x) :
    x ^ x < b ^ d := by
  have hmem : x ∈ Nat.digits b n := by
    rw [← List.mem_reverse, digits_reverse_eq_topDigits hb h1 h2 hd]
    exact List.count_pos_iff.1 hx
  have hlen : (Nat.digits b n).length = d := by
    have a := (Nat.digits_length_le_iff (by omega) n).2 h2
    have c := (Nat.lt_digits_length_iff (by omega) n).2 (show b ^ (d - 1) ≤ n from h1)
    omega
  simpa [hlen] using pow_self_lt_of_mem_digits hb hsol hmem

/-- **Proposition 1.5** in count form (section 31.2.1): the counts `c` of a `d`-digit solution
have `∑ c_x (w(x) - x) ≡ 0 (mod b - 1)`. -/
theorem sum_count_g_mod {b m d n : ℕ} (hb : 2 ≤ b) (h1 : b ^ (d - 1) ≤ n) (h2 : n < b ^ d)
    (hd : 1 ≤ d) (hsol : IsMunchausen b m n) :
    (∑ x ∈ range b, digitCount b d n x * g m x) % (b - 1) = 0 := by
  have hmod := Fs_modEq_sum (by omega) hsol
  have hsum : (Nat.digits b n).sum = ∑ x ∈ range b, digitCount b d n x * x := by
    unfold digitCount
    rw [← List.sum_reverse, digits_reverse_eq_topDigits hb h1 h2 hd,
      sum_range_count_mul _ (fun x hx => mem_topDigits_lt (by omega) hx)]
    simp
  rw [F_eq_sum_digitCount hb h1 h2 hd, hsum] at hmod
  have hsplit : ∑ x ∈ range b, digitCount b d n x * w m x =
      ∑ x ∈ range b, digitCount b d n x * g m x + ∑ x ∈ range b, digitCount b d n x * x := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [g, ← mul_add, Nat.sub_add_cancel (le_w' m x)]
  rw [hsplit] at hmod
  have := Nat.ModEq.add_right_cancel' _ (hmod.trans (by rw [zero_add]))
  exact this

/-! ### The length bound and the specification -/

/-- The largest length the search visits: `b` digits. `max_len` in `fast/src/search.rs` computes
the largest `d` with `d (b-1)^(b-1) ≥ b^(d-1)`, which is also `b` (`maxLen_tight` and
`length_le_maxLen`). -/
def maxLen (b : ℕ) : ℕ := b

/-- **Proposition 1.1**: a solution has at most `maxLen b = b` digits. -/
theorem length_le_maxLen {b m n : ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) (h : IsMunchausen b m n) :
    (Nat.digits b n).length ≤ maxLen b :=
  length_digits_le hb hm h

/-- The bound is the one of `max_len` in the Rust code: `b`-digit numbers pass the test
`d (b-1)^(b-1) ≥ b^(d-1)`, and `(b+1)`-digit numbers fail it. -/
theorem maxLen_tight {b : ℕ} (hb : 2 ≤ b) :
    b ^ (maxLen b - 1) ≤ maxLen b * (b - 1) ^ (b - 1) ∧
      (maxLen b + 1) * (b - 1) ^ (b - 1) < b ^ (maxLen b + 1 - 1) := by
  refine ⟨?_, length_ineq hb le_rfl⟩
  simp only [maxLen]
  rcases Nat.lt_or_ge b 3 with h | h
  · interval_cases b; simp
  · have := pow_lt_three_mul b hb
    have h3 : 3 * (b - 1) ^ (b - 1) ≤ b * (b - 1) ^ (b - 1) := Nat.mul_le_mul_right _ h
    omega

/-- **The specification.** The positive solutions in base `b` under `0^0 = m`. The range
`n < b^b` loses nothing (`mem_solutions`). -/
def solutions (b m : ℕ) : Finset ℕ :=
  (range (b ^ b)).filter fun n => 0 < n ∧ IsMunchausen b m n

theorem mem_solutions {b m n : ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) :
    n ∈ solutions b m ↔ 0 < n ∧ IsMunchausen b m n := by
  simp only [solutions, mem_filter, mem_range, and_iff_right_iff_imp, and_imp]
  exact fun _ h => lt_pow_self hb hm h

end ExactSearch

end Munchausen
