import Munchausen.OtherSystems

/-!
# Base-`B` expansions in `F_p[T]` (sections 21.1 and 24.2)

Over a field `K`, every polynomial `n` has exactly one expansion `n = sum d_i B^i` with digits
of degree below `deg B` and a nonzero last digit (section 21.1.1). `polyDigits B n` computes it
by repeated division with remainder, and `IsExpansion.eq_of_ringVal_eq` is the uniqueness.

In `F_p[T]` the weight of a digit is `w(d) = d^(p^deg d)` and `w(0) = m`. With expansions in
hand this file proves Proposition 21.3 for numbers, Corollary 21.2, a part of Theorem 21.7 and
Lemmas 24.7 and 24.8.
-/

open Polynomial

namespace Munchausen

section Expansion

variable {K : Type*} [Field K]

/-- A digit list (least significant first) is a base-`B` expansion: every digit has degree below
`deg B`, and the last digit is not 0 (section 21.1.1). -/
def IsExpansion (B : K[X]) (L : List K[X]) : Prop :=
  (∀ d ∈ L, d.degree < B.degree) ∧ ∀ h : L ≠ [], L.getLast h ≠ 0

lemma isExpansion_nil (B : K[X]) : IsExpansion B [] := ⟨by simp, by simp⟩

lemma isExpansion_cons {B d : K[X]} {t : List K[X]} :
    IsExpansion B (d :: t) ↔ d.degree < B.degree ∧ IsExpansion B t ∧ (t = [] → d ≠ 0) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 d (by simp), ⟨fun e he => h1 e (by simp [he]), fun ht => ?_⟩, fun ht => ?_⟩
    · have := h2 (by simp); rwa [List.getLast_cons ht] at this
    · subst ht; simpa using h2 (by simp)
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
    refine ⟨fun e he => ?_, fun _ => ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact h1
      · exact h2 e he
    · by_cases ht : t = []
      · subst ht; simpa using h4 rfl
      · rw [List.getLast_cons ht]; exact h3 ht

@[simp] lemma ringVal_nil (B : K[X]) : ringVal B [] = 0 := rfl

@[simp] lemma ringVal_cons (B d : K[X]) (t : List K[X]) :
    ringVal B (d :: t) = d + B * ringVal B t := rfl

/-- One step of the uniqueness: `d + B v = d' + B v'` with `deg d, deg d' < deg B` gives
`d = d'` and `v = v'`. -/
lemma eq_of_add_mul_eq {B d d' v v' : K[X]} (hd : d.degree < B.degree)
    (hd' : d'.degree < B.degree) (h : d + B * v = d' + B * v') : d = d' ∧ v = v' := by
  have hB : B ≠ 0 := by rintro rfl; simp at hd
  have hv : v = v' := by
    by_contra hne
    have h1 : B * (v - v') = d' - d := by linear_combination h
    have h2 : (d' - d).degree < B.degree :=
      lt_of_le_of_lt (degree_sub_le _ _) (max_lt hd' hd)
    have h3 : B.degree ≤ (B * (v - v')).degree := by
      rw [degree_mul]
      exact le_add_of_nonneg_right (zero_le_degree_iff.2 (sub_ne_zero.2 hne))
    rw [h1] at h3
    exact absurd h2 (not_lt.2 h3)
  subst hv
  exact ⟨by linear_combination h, rfl⟩

lemma IsExpansion.eq_nil_of_ringVal_eq_zero {B : K[X]} {L : List K[X]} (hL : IsExpansion B L)
    (h0 : ringVal B L = 0) : L = [] := by
  induction L with
  | nil => rfl
  | cons d t ih =>
    obtain ⟨hd, ht, hlast⟩ := isExpansion_cons.1 hL
    have hB0 : (0 : K[X]).degree < B.degree := lt_of_le_of_lt bot_le hd
    obtain ⟨rfl, hv⟩ := eq_of_add_mul_eq (v := ringVal B t) (v' := 0) hd hB0 (by simpa using h0)
    have := ih ht hv
    exact absurd rfl (hlast this)

/-- **Uniqueness of base-`B` expansions** (section 21.1.1). -/
theorem IsExpansion.eq_of_ringVal_eq {B : K[X]} {L L' : List K[X]} (hL : IsExpansion B L)
    (hL' : IsExpansion B L') (h : ringVal B L = ringVal B L') : L = L' := by
  induction L generalizing L' with
  | nil => exact (hL'.eq_nil_of_ringVal_eq_zero (by simpa using h.symm)).symm
  | cons d t ih =>
    cases L' with
    | nil => exact hL.eq_nil_of_ringVal_eq_zero (by simpa using h)
    | cons d' t' =>
      obtain ⟨hd, ht, -⟩ := isExpansion_cons.1 hL
      obtain ⟨hd', ht', -⟩ := isExpansion_cons.1 hL'
      obtain ⟨rfl, hv⟩ := eq_of_add_mul_eq hd hd' (by simpa using h)
      rw [ih ht ht' hv]

open Classical in
/-- Repeated division with remainder, with `k` steps of fuel. -/
noncomputable def digitsAux (B : K[X]) : ℕ → K[X] → List K[X]
  | 0, _ => []
  | k + 1, n => if n = 0 then [] else n % B :: digitsAux B k (n / B)

/-- The base-`B` digits of `n`, least significant first (section 21.1.1). -/
noncomputable def polyDigits (B n : K[X]) : List K[X] := digitsAux B (n.natDegree + 1) n

lemma digitsAux_spec {B : K[X]} (hB : 0 < B.degree) :
    ∀ k (n : K[X]), (n = 0 ∨ n.natDegree < k) →
      ringVal B (digitsAux B k n) = n ∧ IsExpansion B (digitsAux B k n) := by
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB
  intro k
  induction k with
  | zero =>
    rintro n (rfl | h)
    · exact ⟨rfl, isExpansion_nil B⟩
    · omega
  | succ k ih =>
    intro n hn
    by_cases h0 : n = 0
    · simp only [digitsAux, h0, ite_true]; exact ⟨rfl, isExpansion_nil B⟩
    simp only [digitsAux, h0, ite_false]
    have hn' : n.natDegree < k + 1 := hn.resolve_left h0
    have hdiv : n / B = 0 ∨ (n / B).natDegree < k := by
      by_cases hq : n / B = 0
      · exact Or.inl hq
      · right
        have := natDegree_lt_natDegree hq (degree_div_lt h0 hB)
        omega
    obtain ⟨hv, hexp⟩ := ih (n / B) hdiv
    have hval : n % B + B * (n / B) = n := EuclideanDomain.mod_add_div n B
    refine ⟨by rw [ringVal_cons, hv, hval], isExpansion_cons.2 ⟨degree_mod_lt n hB0, hexp, ?_⟩⟩
    intro ht hmod
    rw [ht] at hv
    rw [hmod, ← hv] at hval
    simp at hval
    exact h0 hval.symm

/-- The digits of `n` form an expansion of `n` (section 21.1.1). -/
theorem polyDigits_spec {B : K[X]} (hB : 0 < B.degree) (n : K[X]) :
    ringVal B (polyDigits B n) = n ∧ IsExpansion B (polyDigits B n) :=
  digitsAux_spec hB _ n (Or.inr (Nat.lt_succ_self _))

/-- Every expansion is the expansion: `polyDigits B (sum d_i B^i) = (d_i)`. -/
theorem polyDigits_ringVal {B : K[X]} (hB : 0 < B.degree) {L : List K[X]}
    (hL : IsExpansion B L) : polyDigits B (ringVal B L) = L :=
  (polyDigits_spec hB _).2.eq_of_ringVal_eq hL (polyDigits_spec hB _).1

/-- Prepending a digit: the digits of `d + B v` are `d` followed by the digits of `v`, unless
both are 0. -/
lemma polyDigits_add_mul {B d v : K[X]} (hB : 0 < B.degree) (hd : d.degree < B.degree)
    (hdv : d ≠ 0 ∨ v ≠ 0) : polyDigits B (d + B * v) = d :: polyDigits B v := by
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB v
  have : IsExpansion B (d :: polyDigits B v) := by
    refine isExpansion_cons.2 ⟨hd, hexp, fun ht => ?_⟩
    rw [ht] at hv
    rcases hdv with h | h
    · exact h
    · exact absurd hv.symm h
  conv_lhs => rw [← hv]
  exact polyDigits_ringVal hB this

@[simp] lemma polyDigits_zero (B : K[X]) : polyDigits B 0 = [] := by
  simp [polyDigits, digitsAux]

/-- An expansion with `k ≥ 1` digits has degree at least `(k - 1) deg B` (section 21.1.1). -/
lemma IsExpansion.natDegree_ge {B : K[X]} (hB : 0 < B.degree) {L : List K[X]}
    (hL : IsExpansion B L) : (L.length - 1) * B.natDegree ≤ (ringVal B L).natDegree := by
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB
  induction L with
  | nil => simp
  | cons d t ih =>
    obtain ⟨hd, ht, hlast⟩ := isExpansion_cons.1 hL
    by_cases htne : t = []
    · subst htne; simp
    · have hv : ringVal B t ≠ 0 := fun h => htne (ht.eq_nil_of_ringVal_eq_zero h)
      have hlt : d.degree < (B * ringVal B t).degree := by
        rw [degree_mul]
        exact lt_of_lt_of_le hd (le_add_of_nonneg_right (zero_le_degree_iff.2 hv))
      have h1 : (d + B * ringVal B t).natDegree = B.natDegree + (ringVal B t).natDegree := by
        rw [natDegree_add_eq_right_of_degree_lt hlt, natDegree_mul hB0 hv]
      have h2 := ih ht
      have hlen : t.length ≠ 0 := by simpa using htne
      simp only [ringVal_cons, List.length_cons, h1]
      have : (t.length + 1 - 1) * B.natDegree = B.natDegree + (t.length - 1) * B.natDegree := by
        rw [show t.length + 1 - 1 = (t.length - 1) + 1 by omega]; ring
      omega

end Expansion

/-! ### Solutions in `F_p[T]` -/

section Solutions

variable {p : ℕ} [Fact p.Prime]

/-- The weight of a digit in `F_p[T]` under `0^0 = m` (section 21.1.1): `w(d) = d^(p^deg d)`
for `d ≠ 0`, and `w(0) = m`. -/
noncomputable def ffw (m : ZMod p) (d : (ZMod p)[X]) : (ZMod p)[X] :=
  if d = 0 then C m else ffWeight d

/-- The Munchausen sum `F(n)` of `n` in base `B` in `F_p[T]`. -/
noncomputable def ffF (m : ZMod p) (B n : (ZMod p)[X]) : (ZMod p)[X] :=
  ((polyDigits B n).map (ffw m)).sum

/-- `n` is a solution in base `B` under `0^0 = m` (section 21.1.1): `F(n) = n`. The library
calls a solution nontrivial when it has at least 2 digits. -/
def IsFFSolution (m : ZMod p) (B n : (ZMod p)[X]) : Prop := ffF m B n = n

lemma ffWeight_zero : ffWeight (0 : (ZMod p)[X]) = 0 := by
  simp [ffWeight]

lemma ffw_zero_eq (d : (ZMod p)[X]) : ffw 0 d = ffWeight d := by
  by_cases h : d = 0
  · simp [ffw, h, ffWeight_zero]
  · simp [ffw, h]

/-- Under `0^0 = 0`, `F` can be read off any digit list, even with trailing zeros, since
`w(0) = 0`. -/
lemma ffF_zero_ringVal {B : (ZMod p)[X]} (hB : 0 < B.degree) {L : List (ZMod p)[X]}
    (hL : ∀ d ∈ L, d.degree < B.degree) : ffF 0 B (ringVal B L) = (L.map ffWeight).sum := by
  induction L with
  | nil => simp [ffF]
  | cons d t ih =>
    have ht := ih (fun e he => hL e (by simp [he]))
    by_cases h : d = 0 ∧ ringVal B t = 0
    · obtain ⟨rfl, h2⟩ := h
      simp only [ringVal_cons, h2, mul_zero, add_zero, List.map_cons, List.sum_cons,
        ffWeight_zero, zero_add]
      rw [← ht, h2]
    · have hdv : d ≠ 0 ∨ ringVal B t ≠ 0 := by tauto
      simp only [ffF, ringVal_cons] at ht ⊢
      rw [polyDigits_add_mul hB (hL d (by simp)) hdv, List.map_cons, List.sum_cons, ht,
        ffw_zero_eq, List.map_cons, List.sum_cons]

/-- **Proposition 21.3** for numbers (section 21.1.3). Under `0^0 = 0`, if `n` is a solution in
base `B` (`deg B ≥ 1`), so is `n + c` for every constant `c`: only the last digit changes. -/
theorem IsFFSolution.add_C {B n : (ZMod p)[X]} (hB : 0 < B.degree) (hn : IsFFSolution 0 B n)
    (c : ZMod p) : IsFFSolution 0 B (n + C c) := by
  have hC : (C c).degree < B.degree := lt_of_le_of_lt degree_C_le hB
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  unfold IsFFSolution at hn ⊢
  cases hL : polyDigits B n with
  | nil =>
    rw [hL] at hv
    rw [← hv, ringVal_nil, zero_add,
      show C c = ringVal B [C c] by simp]
    rw [ffF_zero_ringVal hB (by simpa using hC)]
    simp [ffWeight]
  | cons d t =>
    rw [hL] at hv hexp
    have hd := (isExpansion_cons.1 hexp).1
    have hdc : (d + C c).degree < B.degree :=
      lt_of_le_of_lt (degree_add_le _ _) (max_lt hd hC)
    have e : n + C c = ringVal B ((d + C c) :: t) := by rw [← hv]; simp; ring
    have hdig : ∀ e ∈ (d + C c) :: t, e.degree < B.degree := by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hdc
      · exact hexp.1 e (by simp [he])
    have hF : ffF 0 B n = ((d :: t).map ffWeight).sum := by
      conv_lhs => rw [← hv]
      exact ffF_zero_ringVal hB hexp.1
    rw [e, ffF_zero_ringVal hB hdig, ← e, List.map_cons, List.sum_cons, ffWeight_add_C,
      ← hn, hF, List.map_cons, List.sum_cons]
    ring

/-! ### Lemma 24.8: scaling -/

lemma ffWeight_C_mul {c : ZMod p} (hc : c ≠ 0) (d : (ZMod p)[X]) :
    ffWeight (C c * d) = C c * ffWeight d := by
  rw [ffWeight, ffWeight, natDegree_C_mul hc, mul_pow, ← C_pow, ZMod.pow_card_pow]

lemma ringVal_map_C_mul (B : (ZMod p)[X]) (c : ZMod p) (L : List (ZMod p)[X]) :
    ringVal B (L.map (C c * ·)) = C c * ringVal B L := by
  induction L with
  | nil => simp
  | cons d t ih => simp only [List.map_cons, ringVal_cons, ih]; ring

/-- **Lemma 24.8** (section 24.2.2). Under `0^0 = 0`, if `n` is a solution in base `B`, so is
`c n + a` for every `c ≠ 0` and `a` in `F_p`. -/
theorem IsFFSolution.C_mul_add_C {B n : (ZMod p)[X]} (hB : 0 < B.degree)
    (hn : IsFFSolution 0 B n) {c : ZMod p} (hc : c ≠ 0) (a : ZMod p) :
    IsFFSolution 0 B (C c * n + C a) := by
  apply IsFFSolution.add_C hB _ a
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  have hdig : ∀ d ∈ (polyDigits B n).map (C c * ·), d.degree < B.degree := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
    rw [degree_C_mul hc]; exact hexp.1 d' hd'
  have hF : ffF 0 B n = ((polyDigits B n).map ffWeight).sum := by
    conv_lhs => rw [← hv]
    exact ffF_zero_ringVal hB hexp.1
  unfold IsFFSolution at hn ⊢
  conv_lhs => rw [← hv, ← ringVal_map_C_mul]
  rw [ffF_zero_ringVal hB hdig, List.map_map]
  have : (ffWeight ∘ (C c * ·)) = fun d => C c * ffWeight d := by
    funext d; exact ffWeight_C_mul hc d
  rw [this, List.sum_map_mul_left, ← hF, hn]

/-- **Lemma 24.8**, distinctness (section 24.2.2). For a nonconstant `n`, the `p (p - 1)`
numbers `c n + a` with `c ≠ 0` are distinct. -/
theorem C_mul_add_C_injective {n : (ZMod p)[X]} (hn : 1 ≤ n.natDegree) :
    Function.Injective fun x : ZMod p × ZMod p => C x.1 * n + C x.2 := by
  rintro ⟨c, a⟩ ⟨c', a'⟩ h
  simp only at h
  have hcc : c = c' := by
    by_contra hne
    have h1 : C (c - c') * n = C (a' - a) := by rw [C_sub, C_sub]; linear_combination h
    have := congrArg natDegree h1
    rw [natDegree_C_mul (sub_ne_zero.2 hne), natDegree_C] at this
    omega
  subst hcc
  have : C a = C a' := by linear_combination h
  rw [C_inj] at this
  rw [this]

/-! ### Lemma 24.7: the symmetry `T ↦ a T + b` -/

section Symmetry

variable {a b : ZMod p}

lemma natDegree_comp_linear (ha : a ≠ 0) (f : (ZMod p)[X]) :
    (f.comp (C a * X + C b)).natDegree = f.natDegree := by
  rw [natDegree_comp, natDegree_linear ha, mul_one]

lemma comp_linear_eq_zero (ha : a ≠ 0) {f : (ZMod p)[X]} :
    f.comp (C a * X + C b) = 0 ↔ f = 0 := by
  constructor
  · intro h
    rcases comp_eq_zero_iff.1 h with h | ⟨-, h⟩
    · exact h
    · have := congrArg natDegree h
      rw [natDegree_linear ha, natDegree_C] at this
      exact absurd this one_ne_zero
  · rintro rfl; simp

lemma degree_comp_linear (ha : a ≠ 0) (f : (ZMod p)[X]) :
    (f.comp (C a * X + C b)).degree = f.degree := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [degree_eq_natDegree hf, degree_eq_natDegree ((comp_linear_eq_zero ha).not.2 hf),
      natDegree_comp_linear ha]

lemma ringVal_comp (B : (ZMod p)[X]) (q : (ZMod p)[X]) (L : List (ZMod p)[X]) :
    (ringVal B L).comp q = ringVal (B.comp q) (L.map fun d => d.comp q) := by
  induction L with
  | nil => simp
  | cons d t ih => simp only [List.map_cons, ringVal_cons, add_comp, mul_comp, ih]

lemma ffw_comp (ha : a ≠ 0) (m : ZMod p) (d : (ZMod p)[X]) :
    ffw m (d.comp (C a * X + C b)) = (ffw m d).comp (C a * X + C b) := by
  by_cases hd : d = 0
  · simp [ffw, hd]
  · have hd' : d.comp (C a * X + C b) ≠ 0 := (comp_linear_eq_zero ha).not.2 hd
    simp only [ffw, hd, hd', ite_false, ffWeight, natDegree_comp_linear ha, pow_comp]

/-- **Lemma 24.7** (section 24.2.2). For `a ≠ 0`, the map `ψ(f)(T) = f(a T + b)` sends the
solutions in base `B` to the solutions in base `ψ(B)`, under either convention. -/
theorem IsFFSolution.comp {m : ZMod p} {B n : (ZMod p)[X]} (hB : 0 < B.degree)
    (hn : IsFFSolution m B n) (ha : a ≠ 0) (b : ZMod p) :
    IsFFSolution m (B.comp (C a * X + C b)) (n.comp (C a * X + C b)) := by
  set ψ : (ZMod p)[X] → (ZMod p)[X] := fun f => f.comp (C a * X + C b) with hψ
  have hB' : 0 < (ψ B).degree := by rw [hψ, degree_comp_linear ha]; exact hB
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  have hexp' : IsExpansion (ψ B) ((polyDigits B n).map ψ) := by
    refine ⟨fun d hd => ?_, fun h => ?_⟩
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
      rw [hψ, degree_comp_linear ha, degree_comp_linear ha]; exact hexp.1 d' hd'
    · rw [List.getLast_map]
      exact (comp_linear_eq_zero ha).not.2 (hexp.2 (by simpa using h))
  have hdig : polyDigits (ψ B) (ψ n) = (polyDigits B n).map ψ := by
    have h1 : ψ n = ringVal (ψ B) ((polyDigits B n).map ψ) := by
      conv_lhs => rw [← hv]
      exact ringVal_comp _ _ _
    rw [h1]
    exact polyDigits_ringVal hB' hexp'
  unfold IsFFSolution ffF at hn ⊢
  rw [hdig, List.map_map]
  have : (ffw m ∘ ψ) = fun d => ψ (ffw m d) := by funext d; exact ffw_comp ha m d
  rw [this]
  conv_rhs => rw [← hn]
  simp only [hψ]
  induction polyDigits B n with
  | nil => simp
  | cons d t ih => simp [ih, add_comp]

end Symmetry

/-! ### Corollary 21.2: class sums, degree and count -/

/-- The class sum `D_j`: the sum of the nonzero digits of degree `j` (section 21.1.2). -/
noncomputable def classSum (L : List (ZMod p)[X]) (j : ℕ) : (ZMod p)[X] :=
  (L.filter fun d => d ≠ 0 ∧ d.natDegree = j).sum

/-- **Proposition 21.1**, regrouped (section 21.1.2): for digits of degree below `e`,
`F = sum_j D_j(T^(p^j)) + m z`, with `z` the number of zero digits. -/
lemma sum_ffw_eq (m : ZMod p) (e : ℕ) (L : List (ZMod p)[X])
    (hL : ∀ d ∈ L, d.natDegree < e) :
    (L.map (ffw m)).sum =
      ∑ j ∈ Finset.range e, expand (ZMod p) (p ^ j) (classSum L j) + C (m * L.count 0) := by
  induction L with
  | nil => simp [classSum]
  | cons d t ih =>
    have ht := ih (fun x hx => hL x (by simp [hx]))
    by_cases hd : d = 0
    · subst hd
      simp only [List.map_cons, List.sum_cons, ht, classSum, List.filter_cons, ne_eq,
        not_true_eq_false, false_and, decide_false, Bool.false_eq_true, ite_false,
        List.count_cons_self, ffw, ite_true]
      push_cast
      rw [mul_add, mul_one, C_add]; ring
    · have hcs : ∀ j, classSum (d :: t) j = (if d.natDegree = j then d else 0) + classSum t j := by
        intro j
        by_cases hj : d.natDegree = j
        · simp [classSum, hd, hj]
        · simp [classSum, hd, hj]
      simp only [List.map_cons, List.sum_cons, ht, hcs, map_add, Finset.sum_add_distrib]
      have hmem : d.natDegree ∈ Finset.range e := Finset.mem_range.2 (hL d (by simp))
      have hite : ∑ j ∈ Finset.range e, expand (ZMod p) (p ^ j) (if d.natDegree = j then d else 0)
          = ffWeight d := by
        rw [ffWeight_eq_expand]
        rw [Finset.sum_eq_single_of_mem _ hmem (fun j _ hj => by simp [Ne.symm hj])]
        simp
      rw [hite, List.count_cons_of_ne hd]
      simp only [ffw, hd, ite_false]
      ring

/-- The digit sum regrouped: `sum d_i = sum_j D_j` (zeros add nothing). -/
lemma sum_eq_classSum (e : ℕ) (L : List (ZMod p)[X]) (hL : ∀ d ∈ L, d.natDegree < e) :
    L.sum = ∑ j ∈ Finset.range e, classSum L j := by
  induction L with
  | nil => simp [classSum]
  | cons d t ih =>
    have ht := ih (fun x hx => hL x (by simp [hx]))
    by_cases hd : d = 0
    · subst hd; simp [classSum, ht]
    · have hcs : ∀ j, classSum (d :: t) j = (if d.natDegree = j then d else 0) + classSum t j := by
        intro j
        by_cases hj : d.natDegree = j
        · simp [classSum, hd, hj]
        · simp [classSum, hd, hj]
      simp only [List.sum_cons, ht, hcs, Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq (Finset.range e)]
      simp [hL d (by simp)]

lemma natDegree_classSum_le (L : List (ZMod p)[X]) (j : ℕ) : (classSum L j).natDegree ≤ j := by
  unfold classSum
  induction L with
  | nil => simp
  | cons d t ih =>
    rw [List.filter_cons]
    split_ifs with h
    · simp only [decide_eq_true_eq] at h
      rw [List.sum_cons]
      exact (natDegree_add_le _ _).trans (max_le h.2.le ih)
    · exact ih

lemma natDegree_lt_of_digit {B d : (ZMod p)[X]} (hd : d.degree < B.degree) (hB : 0 < B.degree) :
    d.natDegree < B.natDegree := by
  by_cases h0 : d = 0
  · subst h0; rw [natDegree_zero]; exact natDegree_pos_iff_degree_pos.2 hB
  · exact natDegree_lt_natDegree h0 hd

lemma natDegree_list_sum_le_of_forall {N : ℕ} (l : List (ZMod p)[X])
    (h : ∀ x ∈ l, x.natDegree ≤ N) : l.sum.natDegree ≤ N := by
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.sum_cons]
    exact (natDegree_add_le _ _).trans
      (max_le (h x (by simp)) (ih fun y hy => h y (by simp [hy])))

/-- **Corollary 21.2**, degree (section 21.1.2). A solution in base `B` of degree `e ≥ 1` has
degree at most `(e - 1) p^(e - 1)`. -/
theorem IsFFSolution.natDegree_le {m : ZMod p} {B n : (ZMod p)[X]} (hB : 0 < B.degree)
    (hn : IsFFSolution m B n) : n.natDegree ≤ (B.natDegree - 1) * p ^ (B.natDegree - 1) := by
  obtain ⟨-, hexp⟩ := polyDigits_spec hB n
  rw [← hn]
  unfold ffF
  apply natDegree_list_sum_le_of_forall
  intro w hw
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hw
  have hdeg := natDegree_lt_of_digit (hexp.1 d hd) hB
  by_cases h0 : d = 0
  · simp [ffw, h0]
  · simp only [ffw, h0, ite_false, ffWeight, natDegree_pow]
    rw [mul_comm]
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega))

/-- **Corollary 21.2**, length (section 21.1.2). A solution in base `B` of degree `e ≥ 1` has
at most `(e - 1) p^(e - 1) / e + 1` digits. -/
theorem IsFFSolution.length_le {m : ZMod p} {B n : (ZMod p)[X]} (hB : 0 < B.degree)
    (hn : IsFFSolution m B n) :
    (polyDigits B n).length ≤ (B.natDegree - 1) * p ^ (B.natDegree - 1) / B.natDegree + 1 := by
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  have h1 := hexp.natDegree_ge hB
  rw [hv] at h1
  have h2 := hn.natDegree_le hB
  have he : 0 < B.natDegree := natDegree_pos_iff_degree_pos.2 hB
  have : (polyDigits B n).length - 1 ≤
      (B.natDegree - 1) * p ^ (B.natDegree - 1) / B.natDegree :=
    (Nat.le_div_iff_mul_le he).2 (h1.trans h2)
  omega

lemma sum_range_succ_mul_two (e : ℕ) : (∑ j ∈ Finset.range e, (j + 1)) * 2 = e * (e + 1) := by
  induction e with
  | zero => simp
  | succ e ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

/-- **Corollary 21.2**, count (section 21.1.2). A solution is determined by its class sums
`(D_0, ..., D_(e-1))`, with `deg D_j ≤ j`, and its number of zero digits modulo `p`. So base
`B` of degree `e ≥ 1` has at most `p^(e(e+1)/2) · p` solutions. -/
theorem corollary21_2_card (m : ZMod p) {B : (ZMod p)[X]} (hB : 0 < B.degree) :
    {n | IsFFSolution m B n}.ncard ≤ p ^ (B.natDegree * (B.natDegree + 1) / 2) * p := by
  classical
  set e := B.natDegree with he
  have : ∀ j : Fin e, Finite (degreeLT (ZMod p) (j + 1)) := fun j =>
    Finite.of_equiv _ (degreeLTEquiv (ZMod p) (j + 1)).toEquiv.symm
  let T := (∀ j : Fin e, degreeLT (ZMod p) (j + 1)) × ZMod p
  have hmem : ∀ (L : List (ZMod p)[X]) (j : Fin e), classSum L j ∈ degreeLT (ZMod p) (j + 1) := by
    intro L j
    rw [mem_degreeLT]
    refine lt_of_le_of_lt (degree_le_natDegree) ?_
    exact_mod_cast Nat.lt_succ_of_le (natDegree_classSum_le L j)
  let f : (ZMod p)[X] → T := fun n =>
    (fun j => ⟨classSum (polyDigits B n) j, hmem _ j⟩, ((polyDigits B n).count 0 : ZMod p))
  -- a solution is determined by `f`
  have hval : ∀ n, IsFFSolution m B n → n = ∑ j : Fin e,
      expand (ZMod p) (p ^ (j : ℕ)) ((f n).1 j : (ZMod p)[X]) + C (m * (f n).2) := by
    intro n hn
    obtain ⟨-, hexp⟩ := polyDigits_spec hB n
    have h := sum_ffw_eq m e (polyDigits B n)
      (fun d hd => natDegree_lt_of_digit (hexp.1 d hd) hB)
    unfold IsFFSolution ffF at hn
    rw [hn] at h
    conv_lhs => rw [h, ← Fin.sum_univ_eq_sum_range (fun j => expand (ZMod p) (p ^ j)
      (classSum (polyDigits B n) j))]
  have hinj : Set.InjOn f {n | IsFFSolution m B n} := by
    intro n hn n' hn' hff
    rw [hval n hn, hval n' hn', hff]
  have hcard := Set.ncard_le_ncard_of_injOn f (t := Set.univ) (fun _ _ => Set.mem_univ _) hinj
  rw [Set.ncard_univ] at hcard
  refine hcard.trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_pi, Nat.card_zmod]
  have hj : ∀ j : Fin e, Nat.card (degreeLT (ZMod p) (j + 1)) = p ^ ((j : ℕ) + 1) := by
    intro j
    rw [Nat.card_congr (degreeLTEquiv (ZMod p) (j + 1)).toEquiv, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  simp only [hj]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun j => j + 1)]
  congr 2
  have := sum_range_succ_mul_two e
  omega

/-- **Theorem 21.7**, the necessary part (section 21.1.5). Let `deg B = 2` and `0^0 = 0`. A
nontrivial solution has the form `c + β T^p` with `β ≠ 0`, and then `B - 1` has two distinct
roots in `F_p`. -/
theorem theorem21_7_necessary {B n : (ZMod p)[X]} (hB2 : B.natDegree = 2)
    (hn : IsFFSolution 0 B n) (hlen : 2 ≤ (polyDigits B n).length) :
    (∃ c β : ZMod p, β ≠ 0 ∧ n = C c + C β * X ^ p) ∧
      ∃ a b : ZMod p, a ≠ b ∧ (B - 1).IsRoot a ∧ (B - 1).IsRoot b := by
  have hB : 0 < B.degree := natDegree_pos_iff_degree_pos.1 (by omega)
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  set L := polyDigits B n with hL
  have hdig : ∀ d ∈ L, d.natDegree < 2 := fun d hd => hB2 ▸ natDegree_lt_of_digit (hexp.1 d hd) hB
  have hF := sum_ffw_eq 0 2 L hdig
  have hS := sum_eq_classSum 2 L hdig
  have hn2 : (L.map (ffw 0)).sum = n := hn
  rw [hn2] at hF
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, expand_one,
    pow_one, zero_mul, C_0, add_zero] at hF hS
  -- `D_0 = d₀` is a constant and `D_1 = β T + α`
  set D0 := classSum L 0
  set D1 := classSum L 1
  have hD0 : D0 = C (D0.coeff 0) := eq_C_of_natDegree_le_zero (natDegree_classSum_le L 0)
  have hD1 : D1 = C (D1.coeff 1) * X + C (D1.coeff 0) :=
    eq_X_add_C_of_natDegree_le_one (natDegree_classSum_le L 1)
  set β := D1.coeff 1
  set c0 := D0.coeff 0
  set α := D1.coeff 0
  have hn' : n = C (c0 + α) + C β * X ^ p := by
    rw [hF, hD1, hD0]; simp; ring
  have hβ : β ≠ 0 := by
    intro h0
    have h1 := hexp.natDegree_ge hB
    rw [hv, hn', h0, C_0, zero_mul, add_zero, natDegree_C, hB2] at h1
    have : 2 ≤ L.length := hlen
    omega
  refine ⟨⟨_, β, hβ, hn'⟩, ?_⟩
  -- Proposition 21.5: `B - 1 ∣ n - sum d_i = β (T^p - T)`
  have hdvd := sub_one_dvd_ringVal_sub_sum B L
  rw [hv, hS, hn', hD0, hD1] at hdvd
  have e1 : C (c0 + α) + C β * X ^ p - (C c0 + (C β * X + C α)) = C β * (X ^ p - X) := by
    rw [C_add]; ring
  rw [e1] at hdvd
  have hdvd' : B - 1 ∣ (X ^ p - X : (ZMod p)[X]) := by
    have := dvd_mul_of_dvd_right hdvd (C β⁻¹)
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hβ, C_1, one_mul] at this
  -- `B - 1` divides `T^p - T`, whose roots are all of `F_p`, each once
  obtain ⟨h, hh⟩ := hdvd'
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hg0 : (X ^ p - X : (ZMod p)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hp1
  have hf0 : B - 1 ≠ 0 := fun h0 => hg0 (by rw [hh, h0, zero_mul])
  have hh0 : h ≠ 0 := fun h0 => hg0 (by rw [hh, h0, mul_zero])
  have hroots : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [ZMod.card] at this
  have hfdeg : (B - 1).natDegree = 2 := by
    rw [show (B - 1 : (ZMod p)[X]) = B - C 1 by simp, natDegree_sub_C, hB2]
  have hcard : Multiset.card (B - 1).roots = 2 := by
    have h1 := card_roots' (B - 1)
    have h2 := card_roots' h
    have h3 : Multiset.card (X ^ p - X : (ZMod p)[X]).roots = p := by
      rw [hroots, Finset.card_val, Finset.card_univ, ZMod.card]
    have h4 : (X ^ p - X : (ZMod p)[X]).natDegree = p :=
      FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1
    rw [hh, roots_mul (hh ▸ hg0), Multiset.card_add] at h3
    rw [hh, natDegree_mul hf0 hh0] at h4
    omega
  have hnodup : (B - 1).roots.Nodup := by
    have hle : (B - 1).roots ≤ (X ^ p - X : (ZMod p)[X]).roots := by
      rw [hh, roots_mul (hh ▸ hg0)]; exact Multiset.le_add_right _ _
    rw [hroots] at hle
    exact Multiset.nodup_of_le hle Finset.univ.nodup
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.1 hcard
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro hab'
    rw [hab, hab'] at hnodup
    simp at hnodup
  · exact (mem_roots hf0).1 (by rw [hab]; simp)
  · exact (mem_roots hf0).1 (by rw [hab]; simp)

end Solutions

end Munchausen
