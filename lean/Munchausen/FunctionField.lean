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

/-! ### Proposition 21.4: self-paying digits -/

/-- **Proposition 21.4** (section 21.1.3). A nonzero digit `d` of degree `j` pays for itself
at position `k`, `w(d) = d B^k`, exactly when `d^(p^j - 1) = B^k`. -/
theorem ffWeight_eq_mul_pow_iff {B d : (ZMod p)[X]} (hd : d ≠ 0) (k : ℕ) :
    ffWeight d = d * B ^ k ↔ d ^ (p ^ d.natDegree - 1) = B ^ k := by
  have hp : 1 ≤ p ^ d.natDegree := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have e : ffWeight d = d * d ^ (p ^ d.natDegree - 1) := by
    rw [ffWeight, ← pow_succ']; congr 1; omega
  rw [e]
  exact ⟨fun h => mul_left_cancel₀ hd h, fun h => by rw [h]⟩

/-- **Proposition 21.4**, base `T^e` (section 21.1.3). The digit `c T^j` (`c ≠ 0`) pays for
itself at position `k` in base `T^e` exactly when `e k = j (p^j - 1)`. -/
theorem ffWeight_C_mul_X_pow_iff {c : ZMod p} (hc : c ≠ 0) (j e k : ℕ) :
    ffWeight (C c * X ^ j) = C c * X ^ j * (X ^ e) ^ k ↔ e * k = j * (p ^ j - 1) := by
  rw [ffWeight, natDegree_C_mul_X_pow j c hc, mul_pow, ← C_pow, ZMod.pow_card_pow, ← pow_mul,
    ← pow_mul, mul_assoc, ← pow_add]
  have hp : 1 ≤ p ^ j := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  constructor
  · intro h
    have h1 := mul_left_cancel₀ (C_ne_zero.2 hc) h
    have h2 := congrArg natDegree h1
    rw [natDegree_X_pow, natDegree_X_pow] at h2
    rw [Nat.mul_sub_one]
    omega
  · intro h
    congr 2
    rw [Nat.mul_sub_one] at h
    have : j ≤ j * p ^ j := Nat.le_mul_of_pos_right _ hp
    omega

/-- Placing a digit at a zero position `k` (also above the leading digit) adds `d B^k` to the
value and `w(d)` to the weight sum (under `0^0 = 0`). -/
lemma exists_place_digit {B : (ZMod p)[X]} (hB : 0 < B.degree) {d : (ZMod p)[X]}
    (hd : d.degree < B.degree) :
    ∀ (k : ℕ) (L : List (ZMod p)[X]), (∀ e ∈ L, e.degree < B.degree) → L.getD k 0 = 0 →
      ∃ L' : List (ZMod p)[X], (∀ e ∈ L', e.degree < B.degree) ∧
        ringVal B L' = ringVal B L + d * B ^ k ∧
        (L'.map ffWeight).sum = (L.map ffWeight).sum + ffWeight d := by
  have h0 : (0 : (ZMod p)[X]).degree < B.degree := lt_of_le_of_lt bot_le hB
  intro k
  induction k with
  | zero =>
    intro L hL hk
    cases L with
    | nil => exact ⟨[d], by simpa using hd, by simp, by simp⟩
    | cons a t =>
      simp only [List.getD_cons_zero] at hk
      subst hk
      refine ⟨d :: t, ?_, by simp; ring, by simp [ffWeight_zero]; ring⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hd
      · exact hL e (by simp [he])
  | succ k ih =>
    intro L hL hk
    cases L with
    | nil =>
      obtain ⟨L', hL', hv, hs⟩ := ih [] (by simp) (by simp)
      refine ⟨0 :: L', ?_, by simp [hv]; ring, by simp [hs, ffWeight_zero]⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact h0
      · exact hL' e he
    | cons a t =>
      simp only [List.getD_cons_succ] at hk
      obtain ⟨L', hL', hv, hs⟩ := ih t (fun e he => hL e (by simp [he])) hk
      refine ⟨a :: L', ?_, by simp [hv]; ring, by simp [hs]; ring⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hL e (by simp)
      · exact hL' e he

/-- **Proposition 21.4**, placement (section 21.1.3). Under `0^0 = 0`, a digit `d` that pays
for itself at position `k` can be placed at any zero position `k` of a solution (also above
its leading digit), as in Proposition 2.3. -/
theorem IsFFSolution.add_selfPaying {B n d : (ZMod p)[X]} (hB : 0 < B.degree)
    (hn : IsFFSolution 0 B n) {k : ℕ} (hk : (polyDigits B n).getD k 0 = 0)
    (hd : d.degree < B.degree) (hpay : ffWeight d = d * B ^ k) :
    IsFFSolution 0 B (n + d * B ^ k) := by
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  obtain ⟨L', hL', hv', hs'⟩ := exists_place_digit hB hd k _ hexp.1 hk
  have hF : ffF 0 B n = ((polyDigits B n).map ffWeight).sum := by
    conv_lhs => rw [← hv]
    exact ffF_zero_ringVal hB hexp.1
  unfold IsFFSolution at hn ⊢
  rw [← hv, ← hv', ffF_zero_ringVal hB hL', hs', ← hF, hn, hv', hv, hpay]

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

/-- A polynomial of degree 2 with two distinct roots in `F_p` divides `T^p - T`. -/
lemma dvd_X_pow_sub_X_of_two_roots {f : (ZMod p)[X]} (hf : f.natDegree = 2) {a b : ZMod p}
    (hab : a ≠ b) (ha : f.IsRoot a) (hb : f.IsRoot b) : f ∣ (X ^ p - X : (ZMod p)[X]) := by
  classical
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hnd : ({a, b} : Multiset (ZMod p)).Nodup := by simp [hab]
  have hle : ({a, b} : Multiset (ZMod p)) ≤ f.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_roots hf0).2 ha
    · exact (mem_roots hf0).2 hb
  have hcard : Multiset.card f.roots = f.natDegree := by
    have h1 := card_roots' f
    have h2 := Multiset.card_le_card hle
    simp at h2
    omega
  have hroots : f.roots = {a, b} :=
    (Multiset.eq_of_le_of_card_le hle (by rw [hcard, hf]; simp)).symm
  have hroots' : (X ^ p - X : (ZMod p)[X]).roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [ZMod.card] at this
  have hP : (({a, b} : Multiset (ZMod p)).map fun x => X - C x).prod ∣
      (X ^ p - X : (ZMod p)[X]) := by
    refine dvd_trans (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map ?_))
      (hroots' ▸ prod_multiset_X_sub_C_dvd (X ^ p - X : (ZMod p)[X]))
    rw [Multiset.le_iff_subset hnd]
    intro x _
    exact Finset.mem_univ_val x
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard, hroots]
  exact (IsUnit.mul_left_dvd (isUnit_C.2 (leadingCoeff_ne_zero.2 hf0).isUnit)).2 hP

/-- **Theorem 21.7** (section 21.1.5). Let `deg B = 2` and `0^0 = 0`. The nontrivial
solutions in base `B` (at least 2 digits) are the numbers `c + β T^p` with `β ≠ 0`, when
`B - 1` has two distinct roots in `F_p`; otherwise there are none. -/
theorem theorem21_7 {B n : (ZMod p)[X]} (hB2 : B.natDegree = 2) :
    (IsFFSolution 0 B n ∧ 2 ≤ (polyDigits B n).length) ↔
      (∃ c β : ZMod p, β ≠ 0 ∧ n = C c + C β * X ^ p) ∧
        ∃ a b : ZMod p, a ≠ b ∧ (B - 1).IsRoot a ∧ (B - 1).IsRoot b := by
  constructor
  · rintro ⟨hn, hlen⟩; exact theorem21_7_necessary hB2 hn hlen
  rintro ⟨⟨c, β, hβ, rfl⟩, a, b, hab, ha, hb⟩
  have hB : 0 < B.degree := natDegree_pos_iff_degree_pos.1 (by omega)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hfdeg : (B - 1).natDegree = 2 := by
    rw [show (B - 1 : (ZMod p)[X]) = B - C 1 by simp, natDegree_sub_C, hB2]
  have hdvd := dvd_X_pow_sub_X_of_two_roots hfdeg hab ha hb
  set n := C c + C β * X ^ p with hn
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  set L := polyDigits B n with hL
  have hdig : ∀ d ∈ L, d.natDegree < 2 :=
    fun d hd => hB2 ▸ natDegree_lt_of_digit (hexp.1 d hd) hB
  have hndeg : n.natDegree = p := by
    rw [hn, add_comm, natDegree_add_C, natDegree_C_mul_X_pow p β hβ]
  constructor
  · -- the digit sum is `c + β T`
    have hS0 : L.sum = C c + C β * X := by
      have h1 := sub_one_dvd_ringVal_sub_sum B L
      rw [hv] at h1
      have h2 : B - 1 ∣ n - (C c + C β * X) := by
        rw [hn, show C c + C β * X ^ p - (C c + C β * X) = C β * (X ^ p - X) by ring]
        exact dvd_mul_of_dvd_right hdvd _
      have h3 : B - 1 ∣ L.sum - (C c + C β * X) := by
        have := dvd_sub h2 h1
        rwa [show n - (C c + C β * X) - (n - L.sum) = L.sum - (C c + C β * X) by ring] at this
      have h4 : (L.sum - (C c + C β * X)).natDegree < (B - 1).natDegree := by
        rw [hfdeg]
        refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt ?_ ?_)
        · exact Nat.lt_succ_of_le (natDegree_list_sum_le_of_forall L
            (fun d hd => Nat.le_of_lt_succ (hdig d hd)))
        · exact lt_of_le_of_lt (natDegree_add_le _ _)
            (max_lt (by simp) (lt_of_le_of_lt (natDegree_C_mul_le _ _) (by simp)))
      exact sub_eq_zero.1 (eq_zero_of_dvd_of_natDegree_lt h3 h4)
    have hF := sum_ffw_eq 0 2 L hdig
    have hS := sum_eq_classSum 2 L hdig
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, expand_one,
      pow_one, zero_mul, C_0, add_zero] at hF hS
    set D0 := classSum L 0
    set D1 := classSum L 1
    have hD0 : D0 = C (D0.coeff 0) := eq_C_of_natDegree_le_zero (natDegree_classSum_le L 0)
    have hD1 : D1 = C (D1.coeff 1) * X + C (D1.coeff 0) :=
      eq_X_add_C_of_natDegree_le_one (natDegree_classSum_le L 1)
    set c0 := D0.coeff 0
    set β' := D1.coeff 1
    set α := D1.coeff 0
    rw [hS, hD0, hD1] at hS0
    have e1 := congrArg (fun f => coeff f 1) hS0
    have e0 := congrArg (fun f => coeff f 0) hS0
    simp [coeff_C, coeff_X] at e1 e0
    unfold IsFFSolution ffF
    rw [← hL, hF, hD0, hD1]
    simp only [map_add, map_mul, expand_C, expand_X]
    rw [hn, e1, ← e0, C_add]
    ring
  · -- `n` has degree `p ≥ 2`, so at least 2 digits
    by_contra hlen
    have hlen' : L.length ≤ 1 := by omega
    have : n.natDegree < 2 := by
      rw [← hv]
      match L, hlen', hdig with
      | [], _, _ => simp
      | [d], _, hd => simpa using hd d (by simp)
    omega

/-- **Theorem 21.7**, the count (section 21.1.5). Let `deg B = 2`, `0^0 = 0`, and let `B - 1`
have two distinct roots in `F_p`. Then base `B` has exactly `p (p - 1)` nontrivial solutions. -/
theorem theorem21_7_card {B : (ZMod p)[X]} (hB2 : B.natDegree = 2) {a b : ZMod p} (hab : a ≠ b)
    (ha : (B - 1).IsRoot a) (hb : (B - 1).IsRoot b) :
    {n | IsFFSolution 0 B n ∧ 2 ≤ (polyDigits B n).length}.ncard = p * (p - 1) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hset : {n | IsFFSolution 0 B n ∧ 2 ≤ (polyDigits B n).length} =
      (fun x : ZMod p × ZMod p => C x.1 + C x.2 * X ^ p) '' (Set.univ ×ˢ {0}ᶜ) := by
    ext n
    simp only [Set.mem_ofPred_eq, theorem21_7 hB2, Set.mem_image, Set.mem_prod, Set.mem_univ,
      Set.mem_compl_iff, Set.mem_singleton_iff, true_and, Prod.exists]
    constructor
    · rintro ⟨⟨c, β, hβ, rfl⟩, -⟩; exact ⟨c, β, hβ, rfl⟩
    · rintro ⟨c, β, hβ, rfl⟩; exact ⟨⟨c, β, hβ, rfl⟩, a, b, hab, ha, hb⟩
  have hinj : Function.Injective fun x : ZMod p × ZMod p => C x.1 + C x.2 * X ^ p := by
    rintro ⟨c, β⟩ ⟨c', β'⟩ h
    simp only at h
    have h0 := congrArg (fun f => coeff f 0) h
    have hp := congrArg (fun f => coeff f p) h
    have hp0 : (0 : ℕ) ≠ p := by omega
    have hp0' : p ≠ 0 := by omega
    simp [coeff_C, coeff_X_pow, hp0, hp0'] at h0 hp
    exact Prod.ext h0 hp
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_prod, Set.ncard_univ, Set.ncard_compl,
    Set.ncard_singleton, Nat.card_zmod]

/-! ### Lemma 24.1: Frobenius replaces each digit by a block -/

lemma ringVal_append {R : Type*} [CommRing R] (B : R) (A C : List R) :
    ringVal B (A ++ C) = ringVal B A + B ^ A.length * ringVal B C := by
  induction A with
  | nil => simp [ringVal]
  | cons d t ih => simp only [List.cons_append, ringVal, ih, List.length_cons]; ring

lemma ringVal_replicate_zero {R : Type*} [CommRing R] (B : R) (k : ℕ) :
    ringVal B (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ringVal, ih]

/-- The digits of a value can be read off any digit list, trailing zeros allowed. -/
lemma getD_polyDigits_ringVal {B : (ZMod p)[X]} (hB : 0 < B.degree) {L : List (ZMod p)[X]}
    (hL : ∀ d ∈ L, d.degree < B.degree) (k : ℕ) :
    (polyDigits B (ringVal B L)).getD k 0 = L.getD k 0 := by
  induction L generalizing k with
  | nil => simp
  | cons d t ih =>
    have ht := ih (fun e he => hL e (by simp [he]))
    by_cases h : d = 0 ∧ ringVal B t = 0
    · obtain ⟨rfl, h2⟩ := h
      simp only [ringVal_cons, h2, mul_zero, add_zero, polyDigits_zero, List.getD_nil]
      cases k with
      | zero => simp
      | succ k => rw [List.getD_cons_succ, ← ht k, h2, polyDigits_zero, List.getD_nil]
    · rw [ringVal_cons, polyDigits_add_mul hB (hL d (by simp)) (by tauto)]
      cases k with
      | zero => simp
      | succ k => rw [List.getD_cons_succ, List.getD_cons_succ, ht k]

/-- The block of a digit: the base-`B` digits of `d(T^p)`, padded with zeros to length `p`. -/
noncomputable def frobBlock (B d : (ZMod p)[X]) : List (ZMod p)[X] :=
  polyDigits B (expand (ZMod p) p d) ++
    List.replicate (p - (polyDigits B (expand (ZMod p) p d)).length) 0

lemma length_polyDigits_expand_le {B d : (ZMod p)[X]} (hB : 0 < B.degree)
    (hd : d.degree < B.degree) : (polyDigits B (expand (ZMod p) p d)).length ≤ p := by
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB (expand (ZMod p) p d)
  have h1 := hexp.natDegree_ge hB
  rw [hv, natDegree_expand] at h1
  have h2 := natDegree_lt_of_digit hd hB
  by_contra hc
  have h3 : p * B.natDegree ≤ ((polyDigits B (expand (ZMod p) p d)).length - 1) * B.natDegree :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : d.natDegree * p < p * B.natDegree := by
    rw [mul_comm]; exact Nat.mul_lt_mul_of_pos_left h2 (Fact.out : p.Prime).pos
  omega

lemma length_frobBlock {B d : (ZMod p)[X]} (hB : 0 < B.degree) (hd : d.degree < B.degree) :
    (frobBlock B d).length = p := by
  have := length_polyDigits_expand_le hB hd
  simp only [frobBlock, List.length_append, List.length_replicate]
  omega

lemma ringVal_frobBlock {B : (ZMod p)[X]} (hB : 0 < B.degree) (d : (ZMod p)[X]) :
    ringVal B (frobBlock B d) = expand (ZMod p) p d := by
  rw [frobBlock, ringVal_append, ringVal_replicate_zero, mul_zero, add_zero,
    (polyDigits_spec hB _).1]

lemma getD_frobBlock (B d : (ZMod p)[X]) (r : ℕ) :
    (frobBlock B d).getD r 0 = (polyDigits B (expand (ZMod p) p d)).getD r 0 := by
  unfold frobBlock
  by_cases h : r < (polyDigits B (expand (ZMod p) p d)).length
  · exact List.getD_append _ _ _ _ h
  · have h0 : (polyDigits B (expand (ZMod p) p d)).getD r 0 = 0 :=
      List.getD_eq_default _ _ (by omega)
    rw [List.getD_append_right _ _ _ _ (by omega), h0, List.getD_eq_getElem?_getD,
      List.getElem?_getD_replicate_default_eq]

/-- **Lemma 24.1** (section 24.2.1). Let `deg B ≥ 1`. The base-`B` digit of `n(T^p)` at position
`p i + r`, `r < p`, is the digit at position `r` of `d_i(T^p)`, where `d_i` is the digit of `n`
at position `i`: Frobenius replaces each digit by a block of `p` digits and never carries. -/
theorem lemma24_1 {B : (ZMod p)[X]} (hB : 0 < B.degree) (n : (ZMod p)[X]) (i : ℕ) {r : ℕ}
    (hr : r < p) :
    (polyDigits B (expand (ZMod p) p n)).getD (p * i + r) 0 =
      (polyDigits B (expand (ZMod p) p ((polyDigits B n).getD i 0))).getD r 0 := by
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB n
  set L := polyDigits B n
  -- the concatenated blocks represent `n(T^p)`
  have hval : ∀ M : List (ZMod p)[X], (∀ d ∈ M, d.degree < B.degree) →
      ringVal B (M.flatMap (frobBlock B)) = expand (ZMod p) p (ringVal B M) := by
    intro M hM
    induction M with
    | nil => simp [ringVal]
    | cons d t ih =>
      rw [List.flatMap_cons, ringVal_append, length_frobBlock hB (hM d (by simp)),
        ringVal_frobBlock hB, ih (fun e he => hM e (by simp [he])), ringVal_cons, map_add,
        map_mul, ZMod.expand_card B]
  have hdig : ∀ d ∈ L.flatMap (frobBlock B), d.degree < B.degree := by
    intro d hd
    obtain ⟨d', hd', hdd⟩ := List.mem_flatMap.1 hd
    rcases List.mem_append.1 hdd with h | h
    · exact (polyDigits_spec hB _).2.1 d h
    · rw [(List.eq_of_mem_replicate h)]; exact lt_of_le_of_lt bot_le hB
  -- position `p i + r` of the concatenation lies in block `i`
  have hpos : ∀ M : List (ZMod p)[X], (∀ d ∈ M, d.degree < B.degree) → ∀ i,
      (M.flatMap (frobBlock B)).getD (p * i + r) 0 = (frobBlock B (M.getD i 0)).getD r 0 := by
    intro M hM
    induction M with
    | nil =>
      intro i
      simp only [List.flatMap_nil, List.getD_nil]
      rw [getD_frobBlock, map_zero, polyDigits_zero, List.getD_nil]
    | cons d t ih =>
      intro i
      have hlen := length_frobBlock hB (hM d (by simp))
      rw [List.flatMap_cons]
      cases i with
      | zero =>
        rw [mul_zero, zero_add, List.getD_append _ _ _ _ (by omega), List.getD_cons_zero]
      | succ i =>
        rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen,
          show p * (i + 1) + r - p = p * i + r by rw [mul_add, mul_one]; omega,
          ih (fun e he => hM e (by simp [he])) i, List.getD_cons_succ]
  rw [← hv, ← hval L hexp.1, getD_polyDigits_ringVal hB hdig, hpos L hexp.1 i, getD_frobBlock]

/-- **Lemma 24.1**, the zero digits (section 24.2.1). For a digit `d` and
`r > (deg B - 1) p / deg B`, the digit of `d(T^p)` at position `r` is 0. -/
theorem lemma24_1_zero {B d : (ZMod p)[X]} (hB : 0 < B.degree) (hd : d.degree < B.degree)
    {r : ℕ} (hr : (B.natDegree - 1) * p < r * B.natDegree) :
    (polyDigits B (expand (ZMod p) p d)).getD r 0 = 0 := by
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB (expand (ZMod p) p d)
  have h1 := hexp.natDegree_ge hB
  rw [hv, natDegree_expand] at h1
  have h2 := natDegree_lt_of_digit hd hB
  apply List.getD_eq_default
  by_contra hc
  have h3 : r * B.natDegree ≤ ((polyDigits B (expand (ZMod p) p d)).length - 1) * B.natDegree :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : d.natDegree * p ≤ (B.natDegree - 1) * p := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Proposition 24.2** (Horner form, section 24.2.1): `∑_j Φ^j(D_j) = D_0 + Φ(∑_j Φ^j(D_(j+1)))`
with `Φ(n) = n(T^p)`. Iterating gives `F(x) = D_0 + m z + Φ(D_1 + Φ(D_2 + ...))`. -/
theorem prop24_2 (e : ℕ) (D : ℕ → (ZMod p)[X]) :
    ∑ j ∈ Finset.range (e + 1), expand (ZMod p) (p ^ j) (D j) =
      D 0 + expand (ZMod p) p (∑ j ∈ Finset.range e, expand (ZMod p) (p ^ j) (D (j + 1))) := by
  rw [Finset.sum_range_succ', map_sum]
  simp only [pow_zero, expand_one, ← expand_mul, pow_succ']
  ring

/-- The `i`-th base-`B` digit of `n`. -/
noncomputable def ffDigit (B n : (ZMod p)[X]) (i : ℕ) : (ZMod p)[X] := (polyDigits B n).getD i 0

lemma ffDigit_zero_right {B : (ZMod p)[X]} (hB : 0 < B.degree) (n : (ZMod p)[X]) :
    ffDigit B n 0 = n % B := by
  by_cases hn : n = 0
  · simp [ffDigit, hn]
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB
  have h : n % B ≠ 0 ∨ n / B ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hn
    rw [← EuclideanDomain.mod_add_div n B, hc.1, hc.2, mul_zero, add_zero]
  have := polyDigits_add_mul hB (degree_mod_lt n hB0) h
  rw [EuclideanDomain.mod_add_div] at this
  simp [ffDigit, this]

lemma ffDigit_succ {B : (ZMod p)[X]} (hB : 0 < B.degree) (n : (ZMod p)[X]) (i : ℕ) :
    ffDigit B n (i + 1) = ffDigit B (n / B) i := by
  by_cases hn : n = 0
  · simp [ffDigit, hn]
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB
  have h : n % B ≠ 0 ∨ n / B ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hn
    rw [← EuclideanDomain.mod_add_div n B, hc.1, hc.2, mul_zero, add_zero]
  have := polyDigits_add_mul hB (degree_mod_lt n hB0) h
  rw [EuclideanDomain.mod_add_div] at this
  simp [ffDigit, this]

lemma add_div' (f g B : (ZMod p)[X]) : (f + g) / B = f / B + g / B := by
  simp [div_def, add_divByMonic, mul_add]

lemma C_mul_div' (c : ZMod p) (f B : (ZMod p)[X]) : (C c * f) / B = C c * (f / B) := by
  rw [div_def, div_def, show C c * f = c • f from (smul_eq_C_mul c).symm, smul_divByMonic,
    smul_eq_C_mul]
  ring

lemma C_mul_mod' (c : ZMod p) (f B : (ZMod p)[X]) : (C c * f) % B = C c * (f % B) := by
  rw [mod_def, mod_def, show C c * f = c • f from (smul_eq_C_mul c).symm, smul_modByMonic,
    smul_eq_C_mul]

/-- Base-`B` digits are additive (the expansion is `F_p`-linear). -/
lemma ffDigit_add {B : (ZMod p)[X]} (hB : 0 < B.degree) (f g : (ZMod p)[X]) (i : ℕ) :
    ffDigit B (f + g) i = ffDigit B f i + ffDigit B g i := by
  induction i generalizing f g with
  | zero => simp only [ffDigit_zero_right hB, add_mod]
  | succ i ih => simp only [ffDigit_succ hB, add_div', ih]

lemma ffDigit_C_mul {B : (ZMod p)[X]} (hB : 0 < B.degree) (c : ZMod p) (f : (ZMod p)[X])
    (i : ℕ) : ffDigit B (C c * f) i = C c * ffDigit B f i := by
  induction i generalizing f with
  | zero => simp only [ffDigit_zero_right hB, C_mul_mod']
  | succ i ih => simp only [ffDigit_succ hB, C_mul_div', ih]

lemma ffDigit_sum {B : (ZMod p)[X]} (hB : 0 < B.degree) (s : Finset ℕ)
    (f : ℕ → (ZMod p)[X]) (i : ℕ) : ffDigit B (∑ t ∈ s, f t) i = ∑ t ∈ s, ffDigit B (f t) i := by
  induction s using Finset.induction_on with
  | empty => simp [ffDigit]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ffDigit_add hB, ih]

/-- A polynomial of degree below `r deg B` has digit 0 at position `r`. -/
lemma ffDigit_eq_zero_of_natDegree_lt {B f : (ZMod p)[X]} (hB : 0 < B.degree) {r : ℕ}
    (hr : f.natDegree < r * B.natDegree) : ffDigit B f r = 0 := by
  obtain ⟨hv, hexp⟩ := polyDigits_spec hB f
  have h1 := hexp.natDegree_ge hB
  rw [hv] at h1
  apply List.getD_eq_default
  by_contra hc
  have : r * B.natDegree ≤ ((polyDigits B f).length - 1) * B.natDegree :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Lemma 24.5** (section 24.2.2). For a digit `d` of degree `j`, the digit `β_r(d)` of
`d(T^p)` vanishes for `r > j p / e`, `e = deg B`. -/
theorem lemma24_5 {B d : (ZMod p)[X]} (hB : 0 < B.degree) {r : ℕ}
    (hr : d.natDegree * p < r * B.natDegree) : ffDigit B (expand (ZMod p) p d) r = 0 := by
  apply ffDigit_eq_zero_of_natDegree_lt hB
  rwa [natDegree_expand]

/-- **Lemma 24.5**, the zero blocks: a zero digit at position `s` of `n` gives `p` zero digits at
the positions `p s, ..., p s + p - 1` of `n(T^p)`. -/
theorem lemma24_5_zero_block {B : (ZMod p)[X]} (hB : 0 < B.degree) (n : (ZMod p)[X]) {s r : ℕ}
    (hr : r < p) (hs : ffDigit B n s = 0) : ffDigit B (expand (ZMod p) p n) (p * s + r) = 0 := by
  unfold ffDigit at hs ⊢
  rw [lemma24_1 hB n s hr, hs, map_zero, polyDigits_zero, List.getD_nil]

/-- **Proposition 24.6 (1)** (rank one, section 24.2.2). Let `e = deg B` and
`(e - 2) p < r e` (that is `r > ⌊(e-2) p / e⌋`). For every digit `d`,
`β_r(d) = d_(e-1) τ_r`, where `d_(e-1)` is the coefficient of `T^(e-1)` in `d` and `τ_r` is the
digit at position `r` of `T^((e-1) p)`. -/
theorem prop24_6_one {B d : (ZMod p)[X]} (hB : 0 < B.degree) (hd : d.degree < B.degree)
    {r : ℕ} (hr : (B.natDegree - 2) * p < r * B.natDegree) :
    ffDigit B (expand (ZMod p) p d) r =
      C (d.coeff (B.natDegree - 1)) * ffDigit B (X ^ ((B.natDegree - 1) * p)) r := by
  set e := B.natDegree
  have he : 1 ≤ e := by
    have := natDegree_pos_iff_degree_pos.2 hB; omega
  have hde : d.natDegree < e := natDegree_lt_of_digit hd hB
  have hsum : expand (ZMod p) p d =
      ∑ t ∈ Finset.range e, C (d.coeff t) * X ^ (t * p) := by
    conv_lhs => rw [d.as_sum_range' e hde]
    simp only [map_sum, ← C_mul_X_pow_eq_monomial]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, expand_C, map_pow, expand_X, ← pow_mul, mul_comm p]
  rw [hsum, ffDigit_sum hB, show e = e - 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_eq_zero, zero_add, ffDigit_C_mul hB]
  · rw [show e - 1 + 1 - 1 = e - 1 by omega]
  intro t ht
  rw [Finset.mem_range] at ht
  rw [ffDigit_C_mul hB, ffDigit_eq_zero_of_natDegree_lt hB, mul_zero]
  rw [natDegree_X_pow]
  calc t * p ≤ (e - 2) * p := Nat.mul_le_mul_right _ (by omega)
    _ < r * e := hr

end Solutions

end Munchausen
