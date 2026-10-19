import Munchausen.Examples

/-!
# Conjectures and open questions

Open problems of the library are stated here as named `Prop`s, with no claim about their
truth. Refuted conjectures come with a theorem that proves their negation.

The sources are chapter 7, the status tables of chapters 8 to 12, and `questions.md`.
-/

namespace Munchausen

/-! ### Finiteness tools -/

/-- A nonempty Munchausen string forces `b ≥ 2`. -/
lemma IsSolution.two_le_base {b m : ℕ} {s : List ℕ} (h : IsSolution b m s) (hs : s ≠ []) :
    2 ≤ b := by
  have h1 := h.lt_base (s.head hs) (List.head_mem hs)
  have h2 := h.head_ne_zero hs
  omega

/-- A base has finitely many Munchausen strings (Proposition 1.1). -/
theorem finite_setOf_isSolution {b m : ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) :
    {s | IsSolution b m s}.Finite := by
  apply ((Set.finite_lt_nat (b ^ b)).image fun n => (Nat.digits b n).reverse).subset
  intro s hs
  refine ⟨P b s, lt_pow_self hb hm (hs.isMunchausen (by omega)), ?_⟩
  simp [digits_P (by omega) hs.lt_base hs.head_ne_zero]

/-- The strings of a fixed length `k ≥ 1` whose base lies in a finite set are finite. -/
theorem finite_strings_of_finite_bases {k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ 1) {B : Set ℕ}
    (hB : B.Finite) :
    {s : List ℕ | s.length = k ∧ ∃ b ∈ B, IsSolution b m s}.Finite := by
  have hB' := hB.inter_of_left {b | 2 ≤ b}
  apply (hB'.biUnion fun b hb => finite_setOf_isSolution hb.2 hm).subset
  rintro s ⟨hlen, b, hbB, hs⟩
  have hne : s ≠ [] := by rintro rfl; simp at hlen; omega
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨b, ⟨hbB, hs.two_le_base hne⟩, hs⟩

/-! ### Refuted: finitely many short solutions under `0^0 = 1` -/

/-- **The finiteness conjecture** (sections 3.5 and 7.2, now refuted): under `0^0 = 1`, for
each `k ≥ 3` only finitely many bases have a `k`-digit solution. -/
def FinitenessConjecture : Prop :=
  ∀ k, 3 ≤ k → {b | ∃ s : List ℕ, s.length = k ∧ IsSolution b 1 s}.Finite

/-- **Corollary 22.7 refutes the finiteness conjecture** (sections 3.5, 7.2 and 22.3). -/
theorem not_finitenessConjecture : ¬ FinitenessConjecture := by
  intro h
  apply infinite_solutions_of_length 1 (le_refl 3)
  apply (finite_strings_of_finite_bases (k := 3) (by norm_num) le_rfl (h 3 le_rfl)).subset
  rintro s ⟨hlen, b, hs⟩
  exact ⟨hlen, b, ⟨s, hlen, hs⟩, hs⟩

/-- **Lengths without solutions** (section 7.3, refuted as stated): under `0^0 = 1` no base
has a solution with `k` digits, for `k` in {9, 18, 21, 22, 24, 26, 28}. -/
def MissingLengthsConjecture : Prop :=
  ∀ k ∈ ({9, 18, 21, 22, 24, 26, 28} : Set ℕ), ∀ b,
    ¬ ∃ s : List ℕ, s.length = k ∧ IsSolution b 1 s

/-- Corollary 22.7 refutes the conjecture of section 7.3: every length `k ≥ 3` occurs. -/
theorem not_missingLengthsConjecture : ¬ MissingLengthsConjecture := by
  intro h
  obtain ⟨s, ⟨hlen, b, hs⟩⟩ := (infinite_solutions_of_length 1 (k := 9) (by norm_num)).nonempty
  exact h 9 (by simp) b ⟨s, hlen, hs⟩

/-- **Conjecture 9.4** (section 9.9, refuted as stated): under `0^0 = 1`, for every `ε > 0`,
all but finitely many solutions with `k ≥ 3` digits lie in a base `b` with
`k < b ≤ k + (1 + ε) ln k`. The pairs `(b, s)` outside the window are counted. -/
def Conjecture_9_4 : Prop :=
  ∀ ε : ℝ, 0 < ε → {p : ℕ × List ℕ | 3 ≤ p.2.length ∧ IsSolution p.1 1 p.2 ∧
    ¬ ((p.2.length : ℝ) < p.1 ∧ (p.1 : ℝ) ≤ p.2.length + (1 + ε) * Real.log p.2.length)}.Finite

/-- Corollary 22.7 refutes Conjecture 9.4 as stated (correction in section 9.9). -/
theorem not_conjecture_9_4 : ¬ Conjecture_9_4 := by
  intro h
  have hC := h 1 one_pos
  apply infinite_solutions_of_length 1 (le_refl 3)
  have hW := finite_strings_of_finite_bases (k := 3) (m := 1) (by norm_num) le_rfl
    (Set.finite_le_nat 7)
  apply (hW.union (hC.image Prod.snd)).subset
  rintro s ⟨hlen, b, hs⟩
  by_cases hb : b ≤ 7
  · exact Or.inl ⟨hlen, b, hb, hs⟩
  · refine Or.inr ⟨(b, s), ⟨by simp [hlen], hs, ?_⟩, rfl⟩
    rintro ⟨-, h2⟩
    have hlog : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    rw [hlen] at h2
    have : (b : ℝ) ≥ 8 := by exact_mod_cast (show 8 ≤ b by omega)
    push_cast at h2
    nlinarith

/-! ### Refuted: no `b`-digit solutions (section 7.1) under `0^0 = 0` -/

/-- **The original conjecture** of section 7.1: for `b > 2`, no base has a `b`-digit solution,
under the convention `0^0 = m`. -/
def NoFullLengthConjecture (m : ℕ) : Prop :=
  ∀ b, 2 < b → ∀ n, (Nat.digits b n).length = b → ¬ IsMunchausen b m n

/-- Base 15 refutes the conjecture of section 7.1 under `0^0 = 0` (computed). -/
theorem not_noFullLengthConjecture_zero : ¬ NoFullLengthConjecture 0 := by
  intro h
  have hs : IsSolution 15 0 [1, 2, 4, 3, 14, 14, 13, 3, 4, 1, 9, 1, 1, 0, 14] := by decide
  apply h 15 (by norm_num) _ _ (hs.isMunchausen (by norm_num))
  rw [digits_P (by norm_num) hs.lt_base hs.head_ne_zero]
  rfl

/-- Section 7.1 under `0^0 = 1`: open. Bases 3 to 45 have no `b`-digit solution (computed);
the model expects one in about 8% of large bases. -/
def NoFullLengthConjecture_one : Prop := NoFullLengthConjecture 1

/-! ### Open: counts per base (sections 4.1, 7.4 and 8.5) -/

/-- The number of nontrivial solutions `N_m(b)` (section 1.1). -/
noncomputable def count (b m : ℕ) : ℕ := Set.ncard {n | 2 ≤ n ∧ IsMunchausen b m n}

/-- **Is `N_1(b)` bounded?** (sections 4.1, 7.4 and 8.4): open. -/
def BoundedCountOne : Prop := ∃ C, ∀ b, 2 ≤ b → count b 1 ≤ C

/-- **Infinitely many empty bases** (sections 4.6, 7.4 and 8.5): open under both conventions.
The model says that about 15% of bases are empty under both conventions together. -/
def InfinitelyManyEmptyBases (m : ℕ) : Prop := {b | 2 ≤ b ∧ count b m = 0}.Infinite

/-- **Does every `n` occur as `N_m(b)`?** (section 4.4): open under both conventions. -/
def EveryCountOccurs (m : ℕ) : Prop := ∀ n, ∃ b, 2 ≤ b ∧ count b m = n

/-! ### Open: short solutions and the length window -/

/-- **Conjecture 10.3**, second part (section 10.5): under `0^0 = 1`, for every `ε > 0`
infinitely many solutions with `k ≥ 3` digits have `b > k + ln k + (1 - ε) ln ln k`. The
first part excludes "algebraic families", which the library does not define, so it is not
stated here. -/
def Conjecture_10_3_lower : Prop :=
  ∀ ε : ℝ, 0 < ε → {p : ℕ × List ℕ | 3 ≤ p.2.length ∧ IsSolution p.1 1 p.2 ∧
    (p.1 : ℝ) > p.2.length + Real.log p.2.length +
      (1 - ε) * Real.log (Real.log p.2.length)}.Infinite

/-- **Question 65** (chapter 22): is `(1,6,46666)` in base `46666^23333 - 3` the next 3-digit
solution under `0^0 = 1` after `(1,7,1)` in base 904? -/
def Question65 : Prop :=
  ∀ b s, s.length = 3 → IsSolution b 1 s → 904 < b → 46666 ^ 23333 - 3 ≤ b

/-- **Question 50**: does every base have at most two 3-digit solutions under `0^0 = 1`? -/
def Question50 : Prop :=
  ∀ b, Set.ncard {s : List ℕ | s.length = 3 ∧ IsSolution b 1 s} ≤ 2

/-- **Question 36** (section 18.2): is base 25 the only base with both a 2-digit and a
3-digit solution under `0^0 = 1`? Computed for all bases below `10^51`. -/
def Question36 : Prop :=
  ∀ b, (∃ s t : List ℕ, s.length = 2 ∧ t.length = 3 ∧ IsSolution b 1 s ∧ IsSolution b 1 t) →
    b = 25

/-- **Question 39** (section 18.3): does some integer have three bases under `0^0 = 1`? -/
def Question39 : Prop :=
  ∃ N b₁ b₂ b₃, 2 ≤ N ∧ b₁ < b₂ ∧ b₂ < b₃ ∧ 2 ≤ b₁ ∧
    IsMunchausen b₁ 1 N ∧ IsMunchausen b₂ 1 N ∧ IsMunchausen b₃ 1 N

/-! ### Open: the equation `b (b + x) = x^n + 1` (chapters 16, 18 and 20) -/

/-- **Question 12** (sections 16.2 and 18.1): the equation `b (b + x) = x^x + 1`, which says
that `(1, x, 1)` is a solution under `0^0 = 1`, has only the solutions `x = 3` and `x = 7`.
Proven for prime powers `x` (Corollary 18.11) and computed for `x ≤ 4 * 10^9`. -/
def Question12 : Prop := ∀ x b : ℕ, 2 ≤ x → b * (b + x) = x ^ x + 1 → x = 3 ∨ x = 7

/-- **Question 32** (section 18.1): is the set of solutions `(x, n)` of
`b (b + x) = x^n + 1` with `n ≥ 4` finite? Only `(7, 7)` is known. -/
def Question32 : Prop :=
  {p : ℕ × ℕ | 2 ≤ p.1 ∧ 4 ≤ p.2 ∧ ∃ b : ℕ, b * (b + p.1) = p.1 ^ p.2 + 1}.Finite

/-- **Question 51** (section 20.4): `(1, x, 2)` is a solution under `0^0 = 1` in no base;
equivalently `b (b + x) = x^x + 3` has no solution. Computed for `x ≤ 10^9`. -/
def Question51_two : Prop := ∀ x b : ℕ, 2 ≤ x → b * (b + x) ≠ x ^ x + 3

/-- **Question 51** (section 20.4): `(1, x, 3)` is a solution under `0^0 = 1` in no base;
equivalently `b (b + x) = x^x + 25` has no solution with `x ≥ 4`. Proven for prime powers
(Theorem 20.26) and computed for `x ≤ 10^9`. -/
def Question51_three : Prop := ∀ x b : ℕ, 4 ≤ x → b * (b + x) ≠ x ^ x + 25

end Munchausen
