import Mathlib

/-!
# Munchausen numbers: definitions

This file fixes the notation of chapter 1 of the library (`docs/library/1-basics.md`).

* `w m x` is the weight of a digit `x`: `x ^ x` for `x ≥ 1`, and `w m 0 = m`.
  The parameter `m` is the convention `0^0 = m`; the library uses `m = 0` and `m = 1`.
* `F b m n` is the Munchausen sum of `n` in base `b`: the sum of the weights of its
  base-`b` digits (`Nat.digits`).
* `IsMunchausen b m n` says `F b m n = n`.

Digit strings are lists written most significant digit first, as in the library:
the string `(3,4,3,5)` is the list `[3, 4, 3, 5]`.

* `P b s` is the value of the string `s` in base `b`, in any semiring.
* `Fs m s` is the sum of the weights of the digits of `s`.
* `IsSolution b m s` says that `s` is a Munchausen string in base `b`: its digits lie
  below `b`, its leading digit is not 0, and `P b s = Fs m s`.
* `Q m s` is the Munchausen polynomial `P_s(r) - F(s)` of chapter 12, in `ℤ[X]`.

Mathlib writes `0` with no digits at all, so `IsMunchausen b m 0` holds for every `m`.
The library calls 0 and 1 the trivial solutions; theorems about nontrivial solutions
assume `2 ≤ n` or a string of length at least 2.
-/

open Polynomial

namespace Munchausen

/-- The weight of a digit (section 1.1): `w m x = x ^ x` for `x ≥ 1`, and `w m 0 = m`,
the convention `0^0 = m`. -/
def w (m x : ℕ) : ℕ := if x = 0 then m else x ^ x

/-- The weight sum `F(s)` of a digit string (section 1.1): the sum of `w m x` over the
digits `x` of `s`. -/
def Fs (m : ℕ) (s : List ℕ) : ℕ := (s.map (w m)).sum

/-- The Munchausen sum `F(n)` of `n` in base `b` (section 1.1): the sum of the weights of
the base-`b` digits of `n`. -/
def F (b m n : ℕ) : ℕ := Fs m (Nat.digits b n)

/-- `n` is a Munchausen number in base `b` under the convention `0^0 = m` (section 1.1):
`F(n) = n`. -/
def IsMunchausen (b m n : ℕ) : Prop := F b m n = n

instance (b m n : ℕ) : Decidable (IsMunchausen b m n) :=
  inferInstanceAs (Decidable (F b m n = n))

/-- The value `P_s(b)` of a digit string `s`, written most significant digit first, in base
`b` (section 1.4). The base can lie in any semiring: `ℕ`, `ℤ` for negative bases, or `ℤ[X]`
for the polynomial `P_s(r)`. -/
def P {R : Type*} [Semiring R] (b : R) (s : List ℕ) : R := Nat.ofDigits b s.reverse

/-- A digit string `s` (most significant digit first) is a Munchausen string in base `b`
under `0^0 = m` (sections 1.1 and 3.1): every digit is below `b`, the leading digit is not 0,
and the value equals the weight sum, `P_s(b) = F(s)`. -/
structure IsSolution (b m : ℕ) (s : List ℕ) : Prop where
  lt_base : ∀ d ∈ s, d < b
  head_ne_zero : ∀ h : s ≠ [], s.head h ≠ 0
  eq : P b s = Fs m s

instance (b m : ℕ) (s : List ℕ) : Decidable (IsSolution b m s) :=
  decidable_of_iff ((∀ d ∈ s, d < b) ∧ (∀ h : s ≠ [], s.head h ≠ 0) ∧ P b s = Fs m s)
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-- The Munchausen polynomial `Q_s(r) = P_s(r) - F(s)` of a digit string (section 11.3 and
chapter 12). A string is a solution in base `b` exactly when `Q_s(b) = 0` and `b` exceeds
every digit. -/
noncomputable def Q (m : ℕ) (s : List ℕ) : ℤ[X] := P (X : ℤ[X]) s - C (Fs m s : ℤ)

/-- A digit `a` is self-paying at position `k` in base `b` (section 2.2): `a ≥ 2`, `k ≥ 1`,
`a < b` and `a * b ^ k = a ^ a`, that is, the balance of the placement is zero. -/
def SelfPaying (b a k : ℕ) : Prop := 2 ≤ a ∧ 1 ≤ k ∧ a < b ∧ a * b ^ k = a ^ a

/-! ### Basic lemmas on weights -/

@[simp] lemma w_zero (m : ℕ) : w m 0 = m := by simp [w]

lemma w_of_ne_zero (m : ℕ) {x : ℕ} (hx : x ≠ 0) : w m x = x ^ x := by simp [w, hx]

@[simp] lemma w_one (m : ℕ) : w m 1 = 1 := by simp [w]

@[simp] lemma w_succ (m x : ℕ) : w m (x + 1) = (x + 1) ^ (x + 1) := by simp [w]

/-- Under `0^0 = 1` the weight is Lean's `x ^ x`, since Lean also sets `0 ^ 0 = 1`. -/
lemma w_one_eq_pow (x : ℕ) : w 1 x = x ^ x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · exact w_of_ne_zero 1 hx.ne'

/-- Every digit weighs at least as much as its value: `x ≤ w m x` for `x ≥ 1`. -/
lemma le_w {m x : ℕ} (hx : x ≠ 0) : x ≤ w m x := by
  rw [w_of_ne_zero m hx]
  calc x = x ^ 1 := (pow_one x).symm
    _ ≤ x ^ x := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hx) (Nat.one_le_iff_ne_zero.2 hx)

lemma w_le_of_le {m x y : ℕ} (hm : m ≤ 1) (hxy : x ≤ y) : w m x ≤ w m y := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp
    · rw [w_zero, w_of_ne_zero m hy.ne']
      exact hm.trans (Nat.one_le_pow _ _ hy)
  · rw [w_of_ne_zero m hx.ne', w_of_ne_zero m (by omega)]
    calc x ^ x ≤ y ^ x := Nat.pow_le_pow_left hxy x
      _ ≤ y ^ y := Nat.pow_le_pow_right (by omega) hxy

lemma one_le_w {m x : ℕ} (hx : x ≠ 0) : 1 ≤ w m x :=
  (Nat.one_le_iff_ne_zero.2 hx).trans (le_w hx)

/-! ### Basic lemmas on weight sums -/

@[simp] lemma Fs_nil (m : ℕ) : Fs m [] = 0 := rfl

@[simp] lemma Fs_cons (m d : ℕ) (s : List ℕ) : Fs m (d :: s) = w m d + Fs m s := by
  simp [Fs]

@[simp] lemma Fs_append (m : ℕ) (s t : List ℕ) : Fs m (s ++ t) = Fs m s + Fs m t := by
  simp [Fs]

@[simp] lemma Fs_reverse (m : ℕ) (s : List ℕ) : Fs m s.reverse = Fs m s := by
  simp [Fs, List.map_reverse, List.sum_reverse]

lemma Fs_singleton (m d : ℕ) : Fs m [d] = w m d := by simp

@[simp] lemma Fs_replicate (m k d : ℕ) : Fs m (List.replicate k d) = k * w m d := by
  simp [Fs, List.map_replicate, List.sum_replicate]

lemma F_def (b m n : ℕ) : F b m n = Fs m (Nat.digits b n) := rfl

/-! ### Basic lemmas on values of strings -/

section P

variable {R : Type*} [CommSemiring R]

lemma ofDigits_cons' (b : R) (h : ℕ) (t : List ℕ) :
    Nat.ofDigits b (h :: t) = h + b * Nat.ofDigits b t := rfl

lemma ofDigits_append' (b : R) (l1 l2 : List ℕ) :
    Nat.ofDigits b (l1 ++ l2) = Nat.ofDigits b l1 + b ^ l1.length * Nat.ofDigits b l2 := by
  induction l1 with
  | nil => simp [Nat.ofDigits]
  | cons hd tl ih =>
    rw [List.cons_append, ofDigits_cons', ofDigits_cons', ih, List.length_cons]
    ring

@[simp] lemma P_nil (b : R) : P b [] = 0 := by simp [P, Nat.ofDigits]

/-- Appending a digit at the end multiplies the value by the base and adds the digit. -/
@[simp] lemma P_append_singleton (b : R) (s : List ℕ) (d : ℕ) :
    P b (s ++ [d]) = d + b * P b s := by
  simp only [P, List.reverse_append, List.reverse_singleton, List.singleton_append]
  rfl

@[simp] lemma P_singleton (b : R) (d : ℕ) : P b [d] = d := by
  simpa using P_append_singleton b [] d

/-- The value of a concatenation: `P_(t,u)(b) = b ^ |u| * P_t(b) + P_u(b)` (Lemma 22.1). -/
lemma P_append (b : R) (t u : List ℕ) : P b (t ++ u) = b ^ u.length * P b t + P b u := by
  simp only [P, List.reverse_append, ofDigits_append', List.length_reverse]
  ring

/-- A leading digit `d` contributes `d * b ^ |s|`. -/
@[simp] lemma P_cons (b : R) (d : ℕ) (s : List ℕ) : P b (d :: s) = d * b ^ s.length + P b s := by
  have := P_append b [d] s
  simp only [List.singleton_append] at this
  rw [this, P_singleton]
  ring

/-- Leading zeros do not change the value. -/
@[simp] lemma P_replicate_zero_append (b : R) (k : ℕ) (s : List ℕ) :
    P b (List.replicate k 0 ++ s) = P b s := by
  induction k with
  | zero => simp
  | succ k ih => simpa [List.replicate_succ] using ih

lemma P_replicate_zero (b : R) (k : ℕ) : P b (List.replicate k 0) = 0 := by
  simpa using P_replicate_zero_append b k []

/-- Ring homomorphisms commute with `P`. -/
lemma map_P {S : Type*} [CommSemiring S] (f : R →+* S) (b : R) (s : List ℕ) :
    f (P b s) = P (f b) s := by
  induction s using List.reverseRecOn with
  | nil => simp
  | append_singleton s d ih => simp [ih]

/-- The cast of a value in `ℕ` is the value in any semiring. -/
@[simp, norm_cast] lemma cast_P (b : ℕ) (s : List ℕ) : ((P b s : ℕ) : R) = P (b : R) s := by
  simpa using map_P (Nat.castRingHom R) b s

end P

/-- The value of a string read in base `b` is the number with these digits (`Nat.digits`
lists them least significant first). -/
lemma P_eq_ofDigits (b : ℕ) (s : List ℕ) : P b s = Nat.ofDigits b s.reverse := rfl

/-- The base-`b` digits of `n`, most significant first. -/
lemma P_digits_reverse (b n : ℕ) : P b (Nat.digits b n).reverse = n := by
  simp [P, Nat.ofDigits_digits]

end Munchausen
