import Munchausen.Polynomial

/-!
# Examples

Concrete solutions from the library, checked by `decide` in the kernel (no `native_decide`).
Strings are written most significant digit first, as in the library.
-/

namespace Munchausen

/-! ### Chapter 3: short solutions under `0^0 = 1` (section 3.2) -/

/-- 3435 is a Munchausen number in base 10 under `0^0 = 1` (section 3.2). -/
example : IsMunchausen 10 1 3435 := by decide

/-- 3435 has no zero digit, so it is a solution under `0^0 = 0` too (section 1.5). -/
example : IsMunchausen 10 0 3435 := by decide

/-- The 3-digit solutions under `0^0 = 1` in all bases up to `10^51.5` (section 3.2). -/
example : IsSolution 4 1 [1, 3, 1] ∧ IsSolution 4 1 [3, 1, 3] ∧ IsSolution 25 1 [5, 1, 3] ∧
    IsSolution 91 1 [6, 1, 5] ∧ IsSolution 215 1 [1, 2, 6] ∧ IsSolution 904 1 [1, 7, 1] := by
  decide

/-- The two 4-digit solutions under `0^0 = 1` (section 3.2). -/
example : IsSolution 10 1 [3, 4, 3, 5] ∧ IsSolution 20 1 [6, 5, 3, 4] := by decide

/-- The 5-digit solutions under `0^0 = 1` (section 3.2). -/
example : IsSolution 6 1 [2, 2, 3, 5, 2] ∧ IsSolution 6 1 [2, 3, 4, 5, 2] ∧
    IsSolution 7 1 [1, 3, 4, 5, 4] ∧ IsSolution 13 1 [3, 3, 6, 6, 1] ∧
    IsSolution 14 1 [2, 6, 0, 3, 6] ∧ IsSolution 48 1 [3, 8, 6, 2, 0] := by decide

/-- The 6-digit and 7-digit solutions in base 9 (sections 3.2 and 11.5). -/
example : IsSolution 9 1 [1, 5, 6, 2, 6, 2] ∧ IsSolution 9 1 [1, 6, 5, 6, 5, 4, 7] := by decide

/-! ### Chapter 3: under `0^0 = 0` (section 3.3) -/

example : IsSolution 4 0 [1, 3, 0] ∧ IsSolution 5 0 [1, 0, 3] ∧ IsSolution 904 0 [1, 7, 0] ∧
    IsSolution 5 0 [2, 0, 2, 4] ∧ IsSolution 128 0 [8, 0, 2, 4] ∧
    IsSolution 11 0 [6, 6, 5, 0, 0] ∧ IsSolution 11 0 [5, 1, 7, 5, 0, 3] := by decide

/-! ### Chapter 2: constructions -/

/-- The twins `(4,0,0)` and `(4,0,1)` in base 8 (section 2.1). -/
example : IsSolution 8 0 [4, 0, 0] ∧ IsSolution 8 0 [4, 0, 1] := by decide

/-- The swap `(2, 4)` in base 128 (section 2.3). -/
example : IsSolution 128 0 [2, 4] :=
  isSolution_swap (a := 2) (k := 1) (by norm_num) le_rfl (by norm_num) (by norm_num)

/-- The 2-digit families (section 2.4): `(1,2)` in base 3, `(1,3)` in base 25, `(2,2)` in
base 3, `(3,3)` in base 17, `(4,4)` in base 127. -/
example : IsSolution 3 1 [1, 2] ∧ IsSolution 25 1 [1, 3] ∧ IsSolution 3 1 [2, 2] ∧
    IsSolution 17 1 [3, 3] ∧ IsSolution 127 1 [4, 4] := by decide

/-- The base-64 example under `0^0 = 1` that combines two self-paying digits with a swap
(section 2.3). -/
example : IsSolution 64 1 [16, 0, 0, 0, 0, 0, 1, 0, 0, 4, 8] := by decide

/-! ### Solutions with `b` digits under `0^0 = 0` (section 7.1) -/

example : IsSolution 15 0 [1, 2, 4, 3, 14, 14, 13, 3, 4, 1, 9, 1, 1, 0, 14] := by decide

example : IsSolution 16 0 [1, 2, 3, 11, 2, 3, 0, 9, 15, 15, 5, 7, 2, 15, 6, 11] := by decide

/-! ### Negative bases (section 12.3) -/

/-- 404201091 is a Munchausen number in base -10 under `0^0 = 1` (section 12.3). -/
example : IsNegSolution 10 1 [4, 0, 5, 8, 1, 9, 1, 1, 1] := by decide

example : P (-10 : ℤ) [4, 0, 5, 8, 1, 9, 1, 1, 1] = 404201091 := by decide

/-- The other negative-base solutions of section 12.3, under `0^0 = 1`. -/
example : IsNegSolution 2 1 [1, 1, 1] ∧ IsNegSolution 5 1 [1, 3, 4, 3, 3] ∧
    IsNegSolution 7 1 [1, 3, 1] ∧ IsNegSolution 7 1 [1, 2, 6, 6, 2, 5, 1] ∧
    IsNegSolution 7 1 [1, 4, 0, 1, 0, 6, 5] ∧ IsNegSolution 8 1 [7, 5, 7, 6, 2, 0, 3] ∧
    IsNegSolution 10 1 [5, 8, 1, 1, 8, 2, 4, 9, 2] ∧
    IsNegSolution 10 1 [1, 9, 2, 1, 7, 4, 5, 8, 9, 8, 9] ∧
    IsNegSolution 217 1 [1, 2, 6] ∧ IsNegSolution 911 1 [1, 7, 1] := by decide

/-- The partners of Proposition 12.3: `(1,3,1)` in bases 4 and -7. -/
example : IsNegSolution 7 1 [1, 3, 1] := by
  simpa using (show IsSolution 4 1 [1, 3, 1] by decide).negPartner (one_dvd 3)

/-! ### Chapter 22: the binomial families -/

/-- `(1, 2, 6)` in base 215 is the member `j = 2`, `c = e = 1` of Theorem 22.6. -/
example : IsSolution 215 1 [1, 2, 6] :=
  isSolution_binomial (j := 2) (c := 1) (e := 1) (x := 6) (y := 216) 1 le_rfl le_rfl le_rfl
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- `(1, 6, 46666)` is a solution in base `46666^23333 - 3` under both conventions
(Theorem 22.6 with `j = 2`, `c = 1`, `e = 3`). This base has about 108942 digits. -/
theorem isSolution_1_6_46666 (m : ℕ) : IsSolution (46666 ^ 23333 - 3) m [1, 6, 46666] := by
  have hbig : 46669 < 46666 ^ 23333 := by
    calc 46669 < 46666 ^ 2 := by norm_num
      _ ≤ 46666 ^ 23333 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hsq : 46666 ^ 46666 = (46666 ^ 23333) ^ 2 := by rw [← pow_mul]
  generalize 46666 ^ 23333 = Y at hbig hsq ⊢
  have hdig : binomDigits 2 1 3 = [1, 6] := by decide
  have h := isSolution_binomial (j := 2) (c := 1) (e := 3) (x := 46666) (y := Y) (b := Y - 3) m
    le_rfl le_rfl (by norm_num) (by rw [hdig]; norm_num) hsq (by omega) (by omega)
    (by rw [hdig]; intro t ht; simp at ht; omega)
  rwa [hdig] at h

end Munchausen
