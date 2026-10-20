import Munchausen.Search.Algorithm

/-!
# The exact search is correct

The main results:

* `search_sound`: every pair `(m, n)` that `search b ms` returns has `m ∈ ms`, `0 < n` and
  `IsMunchausen b m n`. This holds for every `m`, since the leaf checks each candidate exactly.
* `mem_search_iff`: for `m ∈ ms` with `m ≤ 1`, `(m, n)` is returned exactly when `n` is a
  positive solution. This is completeness: no pruning rule loses a solution.
* `found_eq_solutions`: the same as an equality of `Finset`s with the specification
  `solutions b m`.

The search runs the last-digit tests of chapter 37 with the defaults of the Rust code. The
versions `searchWith_sound`, `mem_searchWith_iff` and `foundWith_eq_solutions` hold for any
numbers of tested digits, `0` (the tests off) included.

The proof of completeness fixes a solution `n` of length `d` under `0^0 = m` and follows it
down the tree. `IsCompletion P k N m n` says that `n` is a completion of the node `N` at level
`k`: the decided counts are the digit counts of `n`, the forced counts are the counts in the
top `pl` digits of `n`, and the known prefix is shared by the whole interval. The root has this
property (`root_isCompletion`), each pruning rule spares a node with this property (the lemmas
`*_of_isCompletion` in the section "The pruning rules"), the child that decides the true count
inherits it (`childAt_isCompletion`), and a leaf with it outputs `n` (`mem_leaf`). The abstract
lemma `dfs_complete` composes these.
-/

namespace Munchausen

namespace ExactSearch

open Finset

/-! ### Small lemmas -/

lemma w_le_w {m m' : ℕ} (h : m ≤ m') (x : ℕ) : w m x ≤ w m' x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa using h
  · rw [w_of_ne_zero m hx.ne', w_of_ne_zero m' hx.ne']

lemma mem_takeWhile_range' {p : ℕ → Bool} :
    ∀ {n s e : ℕ}, s ≤ e → e < s + n → (∀ e', s ≤ e' → e' ≤ e → p e' = true) →
      e ∈ (List.range' s n).takeWhile p
  | 0, s, e, h1, h2, _ => by omega
  | n + 1, s, e, h1, h2, hp => by
    rw [List.range'_succ, List.takeWhile_cons_of_pos (hp s le_rfl h1)]
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _
        (mem_takeWhile_range' (by omega) (by omega) fun e' h1' h2' => hp e' (by omega) h2')

/-- A candidate `e` survives the `takeWhile` if the condition holds up to `e`. -/
lemma mem_takeWhile_range {p : ℕ → Bool} {n e : ℕ} (he : e < n)
    (hp : ∀ e' ≤ e, p e' = true) : e ∈ (List.range n).takeWhile p := by
  rw [List.range_eq_range']
  exact mem_takeWhile_range' (Nat.zero_le e) (by omega) fun e' _ h => hp e' h

/-- A sum of 1 over `s` has one nonzero term, of value 1. -/
lemma exists_of_sum_eq_one {s : Finset ℕ} {f : ℕ → ℕ} (h : ∑ x ∈ s, f x = 1) :
    ∃ a ∈ s, f a ≠ 0 ∧ (∀ F : ℕ → ℕ, ∑ x ∈ s, f x * F x = F a) ∧
      ∀ x ∈ s, f x ≠ 0 → x = a := by
  obtain ⟨a, ha, hfa⟩ := exists_ne_zero_of_sum_ne_zero (s := s) (f := f) (by omega)
  have e := add_sum_erase s f ha
  have hrest : ∀ x ∈ s.erase a, f x = 0 := sum_eq_zero_iff.1 (by omega)
  have hfa1 : f a = 1 := by omega
  refine ⟨a, ha, hfa, fun F => ?_, fun x hx hfx => ?_⟩
  · have e' := add_sum_erase s (fun x => f x * F x) ha
    rw [← e', hfa1, one_mul, sum_eq_zero fun x hx => by rw [hrest x hx, zero_mul], add_zero]
  · by_contra hxa
    exact hfx (hrest x (mem_erase.2 ⟨hxa, hx⟩))

/-- A sum of 2 over `s` is `f a + f c` for at most two points `a`, `c` (equal if one term is 2). -/
lemma exists_of_sum_eq_two {s : Finset ℕ} {f : ℕ → ℕ} (h : ∑ x ∈ s, f x = 2) :
    ∃ a ∈ s, ∃ c ∈ s, f a ≠ 0 ∧ f c ≠ 0 ∧ (∀ F : ℕ → ℕ, ∑ x ∈ s, f x * F x = F a + F c) ∧
      ∀ x ∈ s, f x ≠ 0 → x = a ∨ x = c := by
  obtain ⟨a, ha, hfa⟩ := exists_ne_zero_of_sum_ne_zero (s := s) (f := f) (by omega)
  have e := add_sum_erase s f ha
  by_cases hfa2 : f a = 2
  · have hrest : ∀ x ∈ s.erase a, f x = 0 := sum_eq_zero_iff.1 (by omega)
    refine ⟨a, ha, a, ha, hfa, hfa, fun F => ?_, fun x hx hfx => ?_⟩
    · have e' := add_sum_erase s (fun x => f x * F x) ha
      rw [← e', hfa2, sum_eq_zero fun x hx => by rw [hrest x hx, zero_mul], add_zero, two_mul]
    · by_contra hxa
      exact hfx (hrest x (mem_erase.2 ⟨fun h' => hxa (Or.inl h'), hx⟩))
  · have hs1 : ∑ x ∈ s.erase a, f x = 1 := by omega
    have hfa1 : f a = 1 := by omega
    obtain ⟨c, hc, hfc, hF, hx⟩ := exists_of_sum_eq_one hs1
    refine ⟨a, ha, c, mem_of_mem_erase hc, hfa, hfc, fun F => ?_, fun x hxs hfx => ?_⟩
    · have e' := add_sum_erase s (fun x => f x * F x) ha
      rw [← e', hF F, hfa1, one_mul]
    · by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr (hx x (mem_erase.2 ⟨hxa, hxs⟩) hfx)

/-- A number between `lo` and `hi` shares the leading digits that `lo` and `hi` share. -/
lemma topDigits_eq_of_le_of_le {b d lo hi n L : ℕ} (hL : L ≤ d) (h1 : lo ≤ n) (h2 : n ≤ hi)
    (h : lo / b ^ (d - L) = hi / b ^ (d - L)) : topDigits b d lo L = topDigits b d n L := by
  refine topDigits_eq_of_div_eq hL ?_
  have a := Nat.div_le_div_right (c := b ^ (d - L)) h1
  have c := Nat.div_le_div_right (c := b ^ (d - L)) h2
  omega

/-- Common leading digits of `lo ≤ hi` stay common for every interval inside `[lo, hi]`. -/
lemma div_eq_of_subinterval {lo hi lo' hi' B : ℕ} (h1 : lo ≤ lo') (h2 : lo' ≤ hi')
    (h3 : hi' ≤ hi) (h : lo / B = hi / B) : lo' / B = hi' / B := by
  have a := Nat.div_le_div_right (c := B) h1
  have c := Nat.div_le_div_right (c := B) h2
  have e := Nat.div_le_div_right (c := B) h3
  omega

/-! ### Completions of a node -/

variable {P : Params}

/-- The part of `IsCompletion` that does not mention the interval: the solution `n` (with `d`
digits, under `0^0 = m`, `m ∈ ms`) has the decided counts of `N` as its digit counts for
`x ≥ k`, and the forced counts of `N` as the counts of `x < k` among its top `pl` digits. -/
structure Covers (P : Params) (k : ℕ) (N : Node) (m n : ℕ) : Prop where
  two_le_b : 2 ≤ P.b
  level_le : k ≤ P.b
  mem : m ∈ P.ms
  m_le : m ≤ 1
  low : P.b ^ (P.d - 1) ≤ n
  high : n < P.b ^ P.d
  sol : ∑ x ∈ range P.b, digitCount P.b P.d n x * w m x = n
  decided : ∀ x, k ≤ x → N.cnt x = digitCount P.b P.d n x
  forced : ∀ x, x < k → N.cnt x = (topDigits P.b P.d n N.pl).count x
  pl_le : N.pl ≤ P.d

/-- **The solution `n` is a completion of the node `N` at level `k`.** On top of `Covers`, the
known prefix of `N` is shared by both ends of its interval. -/
structure IsCompletion (P : Params) (k : ℕ) (N : Node) (m n : ℕ) : Prop extends
    Covers P k N m n where
  common : clo P N / P.b ^ (P.d - N.pl) = chi P k N / P.b ^ (P.d - N.pl)

namespace Covers

variable {k : ℕ} {N : Node} {m n : ℕ}

lemma b_pos (h : Covers P k N m n) : 0 < P.b := by have := h.two_le_b; omega

lemma one_le_d (h : Covers P k N m n) : 1 ≤ P.d := by
  by_contra hd
  have := h.low
  have := h.high
  simp_all [show P.d = 0 by omega]

/-- The placed counts never exceed the digit counts of `n`. -/
lemma cnt_le (h : Covers P k N m n) (x : ℕ) : N.cnt x ≤ digitCount P.b P.d n x := by
  rcases le_or_gt k x with hx | hx
  · exact (h.decided x hx).le
  · rw [h.forced x hx]
    exact count_topDigits_le_digitCount _ _ _ _ h.pl_le

/-- The free slots are the copies of `n`'s digits that are not placed yet. -/
lemma rf_eq (h : Covers P k N m n) :
    rf P N = ∑ x ∈ range P.b, (digitCount P.b P.d n x - N.cnt x) := by
  rw [sum_tsub_distrib _ fun x _ => h.cnt_le x, sum_digitCount h.b_pos, rf, placed]

lemma sub_eq_zero_of_le (h : Covers P k N m n) {x : ℕ} (hx : k ≤ x) :
    digitCount P.b P.d n x - N.cnt x = 0 := by
  rw [h.decided x hx, Nat.sub_self]

/-- `lo = t` is a lower bound (Lemma 31.4). -/
lemma t_le (h : Covers P k N m n) : t P N ≤ n := by
  calc t P N ≤ ∑ x ∈ range P.b, digitCount P.b P.d n x * w m x :=
        sum_le_sum fun x _ => Nat.mul_le_mul (h.cnt_le x) (w_le_w (Nat.zero_le m) x)
    _ = n := h.sol

/-- `hi` is an upper bound (Lemma 31.4). -/
lemma le_hi (h : Covers P k N m n) : n ≤ hi P k N := by
  have hsplit : ∑ x ∈ range P.b, digitCount P.b P.d n x * w 1 x =
      ∑ x ∈ range P.b, N.cnt x * w 1 x +
        ∑ x ∈ range P.b, (digitCount P.b P.d n x - N.cnt x) * w 1 x := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← add_mul, Nat.add_sub_cancel' (h.cnt_le x)]
  have hfree : ∑ x ∈ range P.b, (digitCount P.b P.d n x - N.cnt x) * w 1 x ≤
      rf P N * w 1 (k - 1) := by
    rw [h.rf_eq, sum_mul]
    refine sum_le_sum fun x _ => ?_
    rcases le_or_gt k x with hx | hx
    · rw [h.sub_eq_zero_of_le hx]; simp
    · exact Nat.mul_le_mul_left _ (w_le_of_le le_rfl (by omega))
  calc n = ∑ x ∈ range P.b, digitCount P.b P.d n x * w m x := h.sol.symm
    _ ≤ ∑ x ∈ range P.b, digitCount P.b P.d n x * w 1 x :=
        sum_le_sum fun x _ => Nat.mul_le_mul_left _ (w_le_w h.m_le x)
    _ ≤ hi P k N := by rw [hsplit, hi]; omega

lemma clo_le (h : Covers P k N m n) : clo P N ≤ n := max_le h.t_le h.low

lemma le_chi (h : Covers P k N m n) : n ≤ chi P k N := le_min h.le_hi (by have := h.high; omega)

lemma clo_lt (h : Covers P k N m n) : clo P N < P.b ^ P.d := lt_of_le_of_lt h.clo_le h.high

/-- A weighted digit count of `n` is the placed part plus the free part. -/
lemma sum_split (h : Covers P k N m n) (F : ℕ → ℕ) :
    ∑ x ∈ range P.b, digitCount P.b P.d n x * F x =
      ∑ x ∈ range P.b, N.cnt x * F x +
        ∑ x ∈ range P.b, (digitCount P.b P.d n x - N.cnt x) * F x := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← add_mul, Nat.add_sub_cancel' (h.cnt_le x)]

/-- A digit with more copies in `n` than placed is a digit below `b`. -/
lemma lt_b_of_cnt_lt (h : Covers P k N m n) {x : ℕ} (hx : N.cnt x < digitCount P.b P.d n x) :
    x < P.b := by
  by_contra hxb
  rw [digitCount_eq_zero h.b_pos (not_lt.1 hxb)] at hx
  omega

/-- **One free slot.** The solution has exactly one digit `y < k` beyond the placed counts. -/
lemma exists_free_one (h : Covers P k N m n) (hrf : rf P N = 1) :
    ∃ y < k, (∀ F : ℕ → ℕ, ∑ x ∈ range P.b, digitCount P.b P.d n x * F x =
        ∑ x ∈ range P.b, N.cnt x * F x + F y) ∧
      ∀ x, N.cnt x < digitCount P.b P.d n x → x = y := by
  have hsum : ∑ x ∈ range P.b, (digitCount P.b P.d n x - N.cnt x) = 1 := by rw [← hrf, h.rf_eq]
  obtain ⟨y, -, hfy, hF, hfree⟩ := exists_of_sum_eq_one hsum
  have hyk : y < k := by
    by_contra hyk
    exact hfy (h.sub_eq_zero_of_le (not_lt.1 hyk))
  refine ⟨y, hyk, fun F => by rw [h.sum_split F, hF F], fun x hx => ?_⟩
  exact hfree x (mem_range.2 (h.lt_b_of_cnt_lt hx)) (by omega)

/-- **Two free slots.** The solution has exactly two digits `y1 ≤ y2 < k` beyond the placed
counts, counted with multiplicity. -/
lemma exists_free_two (h : Covers P k N m n) (hrf : rf P N = 2) :
    ∃ y2 < k, ∃ y1 ≤ y2, (∀ F : ℕ → ℕ, ∑ x ∈ range P.b, digitCount P.b P.d n x * F x =
        ∑ x ∈ range P.b, N.cnt x * F x + F y1 + F y2) ∧
      ∀ x, N.cnt x < digitCount P.b P.d n x → x = y1 ∨ x = y2 := by
  have hsum : ∑ x ∈ range P.b, (digitCount P.b P.d n x - N.cnt x) = 2 := by rw [← hrf, h.rf_eq]
  obtain ⟨a, -, c, -, hfa, hfc, hF, hfree⟩ := exists_of_sum_eq_two hsum
  have hlt : ∀ y, digitCount P.b P.d n y - N.cnt y ≠ 0 → y < k := fun y hy => by
    by_contra hyk
    exact hy (h.sub_eq_zero_of_le (not_lt.1 hyk))
  have hfree' : ∀ x, N.cnt x < digitCount P.b P.d n x → x = a ∨ x = c := fun x hx =>
    hfree x (mem_range.2 (h.lt_b_of_cnt_lt hx)) (by omega)
  rcases le_total a c with hac | hca
  · exact ⟨c, hlt c hfc, a, hac, fun F => by rw [h.sum_split F, hF F, add_assoc], hfree'⟩
  · refine ⟨a, hlt a hfa, c, hca, fun F => by rw [h.sum_split F, hF F]; ring, fun x hx => ?_⟩
    rcases hfree' x hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl hx

end Covers

namespace IsCompletion

variable {k : ℕ} {N : Node} {m n : ℕ}

/-- The known prefix of `N`, read from `lo`, is the top of `n`. -/
lemma topDigits_clo (h : IsCompletion P k N m n) :
    topDigits P.b P.d (clo P N) N.pl = topDigits P.b P.d n N.pl :=
  topDigits_eq_of_le_of_le h.pl_le h.clo_le h.le_chi h.common

end IsCompletion

/-! ### The pruning rules

Each lemma says that a rule spares every node of which the solution is a completion. Read
contrapositively: if the rule prunes the node, no completion of it is a solution. -/

section Rules

variable {k : ℕ} {N : Node} {m n : ℕ}

/-- **The test `lo < b^d`** (the `break` in `next_child`). -/
theorem t_lt_of_covers (h : Covers P k N m n) : t P N < P.b ^ P.d :=
  lt_of_le_of_lt h.t_le h.high

/-- **The test `hi ≥ b^(d-1)`** (the `continue` on `hi` in `next_child`). -/
theorem pow_le_hi_of_covers (h : Covers P k N m n) : P.b ^ (P.d - 1) ≤ hi P k N :=
  h.low.trans h.le_hi

/-- **The residue rule** (Theorem 31.1). A node with one free slot, of which a solution is a
completion, passes the residue test. -/
theorem resOk_of_covers (h : Covers P k N m n) (hrf : rf P N = 1) : resOk P k N = true := by
  set c := digitCount P.b P.d n with hc
  set f : ℕ → ℕ := fun x => c x - N.cnt x with hf
  have hsum : ∑ x ∈ range P.b, f x = 1 := by rw [← hrf, h.rf_eq]
  obtain ⟨y, hy, hfy⟩ := exists_ne_zero_of_sum_ne_zero (s := range P.b) (f := f) (by omega)
  have hsplit := add_sum_erase (range P.b) f hy
  have hfy1 : f y = 1 := by omega
  have hrest : ∀ x ∈ (range P.b).erase y, f x = 0 :=
    (sum_eq_zero_iff).1 (by omega)
  have hyk : y < k := by
    by_contra hyk
    exact hfy (h.sub_eq_zero_of_le (not_lt.1 hyk))
  -- the residue of `n` is the residue of the node plus `g m y`
  have hres : ∑ x ∈ range P.b, c x * g m x = residue P m N + g m y := by
    have e1 : ∑ x ∈ range P.b, c x * g m x =
        ∑ x ∈ range P.b, N.cnt x * g m x + ∑ x ∈ range P.b, f x * g m x := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [hf, ← add_mul, Nat.add_sub_cancel' (h.cnt_le x)]
    have e2 : ∑ x ∈ range P.b, f x * g m x = g m y := by
      rw [sum_eq_single_of_mem y hy fun x hx hxy => by
        rw [hrest x (mem_erase.2 ⟨hxy, hx⟩), zero_mul], hfy1, one_mul]
    rw [e1, e2, residue]
  have hmod := sum_count_g_mod (m := m) h.two_le_b h.low h.high h.one_le_d
    ((isMunchausen_iff_sum h.two_le_b h.low h.high h.one_le_d).2 h.sol)
  rw [← hc, hres] at hmod
  simp only [resOk, List.any_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨m, h.mem, y, hyk, hmod⟩

/-- **Lemma 37.1** (the last digits). Let `n` be a completion of `N` at level `k`. The digit of
`n` in lane `i` (the digit of `b^i`), an unknown position, is an available digit, or a free
digit: below `k`, with more copies in `n` than placed. -/
theorem lowDigit_avail_or_free (h : IsCompletion P k N m n) {i : ℕ} (hi : i < P.d - N.pl) :
    avail P k N (n / P.b ^ i % P.b) = true ∨
      (n / P.b ^ i % P.b < k ∧
        N.cnt (n / P.b ^ i % P.b) < digitCount P.b P.d n (n / P.b ^ i % P.b)) := by
  -- lane `i` is the top digit at position `d - 1 - i`, at or after the end of the prefix
  have hpx : topDigit P.b P.d n (P.d - 1 - i) = n / P.b ^ i % P.b := by
    simp only [topDigit]
    rw [show P.d - 1 - (P.d - 1 - i) = i by omega]
  have hcount : (topDigits P.b P.d n N.pl).count (n / P.b ^ i % P.b) <
      digitCount P.b P.d n (n / P.b ^ i % P.b) := by
    have e := topDigits_add P.b P.d n N.pl (P.d - i - N.pl)
    rw [show N.pl + (P.d - i - N.pl) = P.d - i by omega] at e
    have hmem : n / P.b ^ i % P.b ∈
        (List.range (P.d - i - N.pl)).map (fun j => topDigit P.b P.d n (N.pl + j)) := by
      refine List.mem_map.2 ⟨P.d - 1 - i - N.pl, List.mem_range.2 (by omega), ?_⟩
      rw [show N.pl + (P.d - 1 - i - N.pl) = P.d - 1 - i by omega, hpx]
    have h1 := List.count_pos_iff.2 hmem
    have h2 := count_topDigits_le_digitCount P.b P.d n (n / P.b ^ i % P.b)
      (show P.d - i ≤ P.d by omega)
    rw [e, List.count_append] at h2
    omega
  rcases le_or_gt k (n / P.b ^ i % P.b) with hkx | hkx
  · left
    simp only [avail, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hkx, ?_⟩
    rw [h.topDigits_clo, h.decided _ hkx]
    exact hcount
  · right
    refine ⟨hkx, ?_⟩
    rw [h.forced _ hkx]
    exact hcount

/-- The last digits of a completion pass `lowDigitsOk` for every number `j` of digits, when `ys`
holds the free digits. -/
theorem lowDigitsOk_of_isCompletion (h : IsCompletion P k N m n) {ys : List ℕ}
    (hys : ∀ x, N.cnt x < digitCount P.b P.d n x → x ∈ ys) (j : ℕ) :
    lowDigitsOk P j k N n ys = true := by
  simp only [lowDigitsOk, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  intro i hi
  rcases lowDigit_avail_or_free h (show i < P.d - N.pl by omega) with ha | ⟨-, hc⟩
  · exact Or.inr ha
  · exact Or.inl (List.contains_iff_mem.2 (hys _ hc))

/-- **Proposition 37.2** (the last digits with one free slot, Rust: `low_ok`). A node with one
free slot, of which a solution is a completion, passes the last-digit test. -/
theorem lowOk_of_isCompletion (h : IsCompletion P k N m n) (hrf : rf P N = 1) :
    lowOk P k N = true := by
  obtain ⟨y, hyk, hsum, hfree⟩ := h.exists_free_one hrf
  have hmod := sum_count_g_mod (m := m) h.two_le_b h.low h.high h.one_le_d
    ((isMunchausen_iff_sum h.two_le_b h.low h.high h.one_le_d).2 h.sol)
  rw [hsum (g m)] at hmod
  have hn : sumW P m N + w m y = n := by rw [sumW, ← hsum (w m), h.sol]
  simp only [lowOk, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  refine ⟨m, h.mem, y, hyk, hmod, ?_⟩
  rw [hn]
  exact lowDigitsOk_of_isCompletion h (fun x hx => by simp [hfree x hx]) _

/-- **Proposition 37.4** (the last digits with two free slots, Rust: `pair_ok`). A node with two
free slots, of which a solution is a completion, passes the pair test. -/
theorem pairOk_of_isCompletion (h : IsCompletion P k N m n) (hrf : rf P N = 2) :
    pairOk P k N = true := by
  obtain ⟨y2, hy2k, y1, hy12, hsum, hfree⟩ := h.exists_free_two hrf
  have hmod := sum_count_g_mod (m := m) h.two_le_b h.low h.high h.one_le_d
    ((isMunchausen_iff_sum h.two_le_b h.low h.high h.one_le_d).2 h.sol)
  rw [hsum (g m)] at hmod
  have hn : sumW P m N + w m y1 + w m y2 = n := by rw [sumW, ← hsum (w m), h.sol]
  simp only [pairOk, List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
  refine ⟨m, h.mem, y2, hy2k, y1, by omega, hmod, ?_⟩
  rw [hn]
  exact lowDigitsOk_of_isCompletion h (fun x hx => by rcases hfree x hx with rfl | rfl <;> simp) _

/-- The tests on one free slot (residue and last digits) spare a node with a completion. -/
theorem oneSlotFails_eq_false (h : IsCompletion P k N m n) : oneSlotFails P k N = false := by
  by_cases hrf : rf P N = 1
  · simp [oneSlotFails, resOk_of_covers h.toCovers hrf, lowOk_of_isCompletion h hrf]
  · simp [oneSlotFails, hrf]

/-- The test on two free slots spares a node with a completion. -/
theorem pairFails_eq_false (h : IsCompletion P k N m n) : pairFails P k N = false := by
  by_cases hrf : rf P N = 2
  · simp [pairFails, pairOk_of_isCompletion h hrf]
  · simp [pairFails, hrf]

/-- **The first unknown digit** (`first_digit_ok`). The digit of `n` after the known prefix lies
between the digits of `lo` and `hi` there, and `n` has one more copy of it than the prefix. -/
theorem firstDigitOk_of_isCompletion (h : IsCompletion P k N m n) :
    firstDigitOk P k N = true := by
  simp only [firstDigitOk]
  split_ifs with hpl hx0
  · rfl
  · rfl
  simp only [List.any_eq_true, List.mem_range'_1, decide_eq_true_eq]
  have hb := h.two_le_b
  have key : ∀ u v, u ≤ v → u / P.b ^ (P.d - N.pl) = v / P.b ^ (P.d - N.pl) →
      topDigit P.b P.d u N.pl ≤ topDigit P.b P.d v N.pl := by
    intro u v huv he
    have hB : P.b ^ (P.d - N.pl) = P.b ^ (P.d - 1 - N.pl) * P.b := by
      rw [← pow_succ]; congr 1; omega
    rw [hB, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at he
    have h1 := Nat.div_le_div_right (c := P.b ^ (P.d - 1 - N.pl)) huv
    have h2 := Nat.div_add_mod (u / P.b ^ (P.d - 1 - N.pl)) P.b
    have h3 := Nat.div_add_mod (v / P.b ^ (P.d - 1 - N.pl)) P.b
    rw [he] at h2
    simp only [topDigit]
    omega
  have hlo := Nat.div_le_div_right (c := P.b ^ (P.d - N.pl)) h.clo_le
  have hhi := Nat.div_le_div_right (c := P.b ^ (P.d - N.pl)) h.le_chi
  have hpre := h.common
  have hy0 := key _ _ h.clo_le (by omega)
  have hy1 := key _ _ h.le_chi (by omega)
  refine ⟨topDigit P.b P.d n N.pl, ⟨hy0, by omega⟩, ?_⟩
  have hyk : k ≤ topDigit P.b P.d n N.pl := le_trans (not_lt.1 hx0) hy0
  rw [h.topDigits_clo, h.decided _ hyk]
  have := count_topDigits_le_digitCount P.b P.d n (topDigit P.b P.d n N.pl)
    (show N.pl + 1 ≤ P.d by omega)
  rw [topDigits_add] at this
  simp only [List.range_one, List.map_cons, List.map_nil, add_zero, List.count_append,
    List.count_singleton_self] at this
  omega

/-- **Forced digits** (`settle`). Every round keeps the solution as a completion: its top digits
are the common digits of the interval, a digit `x ≥ k` of them fits in `c_x`, and the digits
below `k` fit in the free slots. So `settle` never fails on such a node. -/
theorem settle_isCompletion (fuel : ℕ) :
    ∀ {N : Node}, IsCompletion P k N m n →
      ∃ N', settle P k fuel N = some N' ∧ IsCompletion P k N' m n := by
  induction fuel with
  | zero => exact fun h => ⟨_, rfl, h⟩
  | succ fuel ih =>
  intro N h
  have hb := h.two_le_b
  have hb0 : 0 < P.b := by omega
  simp only [settle]
  set lo := clo P N with hlo
  set L := prefixLen P lo (chi P k N) with hL
  by_cases hLpl : L ≤ N.pl
  · simp only [hLpl, ↓reduceIte]
    exact ⟨N, rfl, h⟩
  simp only [hLpl, ↓reduceIte]
  -- the new leading digits are digits of `n`
  have hLd : L ≤ P.d := Nat.findGreatest_le _
  have hLspec : lo / P.b ^ (P.d - L) = chi P k N / P.b ^ (P.d - L) := by
    refine Nat.findGreatest_spec (P := fun l => lo / P.b ^ (P.d - l) = chi P k N / P.b ^ (P.d - l))
      (Nat.zero_le _) ?_
    simp only [Nat.sub_zero]
    have h1 : chi P k N ≤ P.b ^ P.d - 1 := min_le_right _ _
    have h2 := h.clo_lt
    rw [Nat.div_eq_of_lt h2, Nat.div_eq_of_lt (by have := pow_pos hb0 P.d; omega)]
  have htop : topDigits P.b P.d lo L = topDigits P.b P.d n L :=
    topDigits_eq_of_le_of_le hLd h.clo_le h.le_chi hLspec
  set new := (List.range (L - N.pl)).map fun i => topDigit P.b P.d lo (N.pl + i) with hnew
  have hsplit : topDigits P.b P.d n L = topDigits P.b P.d n N.pl ++ new := by
    have e := topDigits_add P.b P.d lo N.pl (L - N.pl)
    rw [show N.pl + (L - N.pl) = L by omega, htop] at e
    rw [e, ← h.topDigits_clo]
  have hnew_lt : ∀ x ∈ new, x < P.b := by
    intro x hx
    simp only [hnew, List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact topDigit_lt hb0 _ _ _
  set forced := new.filter (· < k) with hforced
  have hfc : ∀ x, forced.count x = if x < k then new.count x else 0 := by
    intro x
    split_ifs with hx
    · exact List.count_filter (by simpa using hx)
    · exact List.count_eq_zero.2 fun hm => hx (by simpa using (List.mem_filter.1 hm).2)
  -- the forced digits fit in the free slots
  have hfc_le : ∀ x, forced.count x ≤ digitCount P.b P.d n x - N.cnt x := by
    intro x
    rw [hfc]
    split_ifs with hx
    · have e := congrArg (List.count x) hsplit
      rw [List.count_append, ← h.forced x hx] at e
      have := count_topDigits_le_digitCount P.b P.d n x hLd
      omega
    · exact Nat.zero_le _
  have hforced_lt : ∀ x ∈ forced, x < P.b := fun x hx => hnew_lt x (List.mem_filter.1 hx).1
  have hlen : forced.length = ∑ x ∈ range P.b, forced.count x :=
    (sum_range_count _ hforced_lt).symm
  have hlen_le : forced.length ≤ rf P N := by
    rw [hlen, h.rf_eq]
    exact sum_le_sum fun x _ => hfc_le x
  have hnot : ¬ rf P N < forced.length := by omega
  simp only [hnot, ↓reduceIte]
  -- a new digit `x ≥ k` fits in `c_x`
  have hbig : new.any (fun x => k ≤ x && N.cnt x < (topDigits P.b P.d lo L).count x) = false := by
    rw [List.any_eq_false]
    intro x _
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
    intro hx
    rw [htop, h.decided x hx]
    exact count_topDigits_le_digitCount P.b P.d n x hLd
  simp only [hbig, Bool.false_eq_true, ↓reduceIte]
  -- the node after this round
  set N' : Node := ⟨fun x => N.cnt x + forced.count x, L⟩ with hN'
  have hcov : Covers P k N' m n :=
    { h.toCovers with
      decided := fun x hx => by
        simp only [hN', hfc, not_lt.2 hx, ↓reduceIte, add_zero]
        exact h.decided x hx
      forced := fun x hx => by
        simp only [hN', hfc, hx, ↓reduceIte, hsplit, List.count_append]
        rw [h.forced x hx]
      pl_le := hLd }
  -- its interval lies inside the old one
  have ht : t P N ≤ t P N' :=
    sum_le_sum fun x _ => Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hplaced : placed P N' = placed P N + forced.length := by
    simp only [placed, hN', sum_add_distrib, hlen]
  have hhi : hi P k N' ≤ hi P k N := by
    have e1 : ∑ x ∈ range P.b, N'.cnt x * w 1 x =
        ∑ x ∈ range P.b, N.cnt x * w 1 x + ∑ x ∈ range P.b, forced.count x * w 1 x := by
      simp only [hN', add_mul, sum_add_distrib]
    have e2 : ∑ x ∈ range P.b, forced.count x * w 1 x ≤ forced.length * w 1 (k - 1) := by
      rw [hlen, sum_mul]
      refine sum_le_sum fun x _ => ?_
      rw [hfc]
      split_ifs with hx
      · exact Nat.mul_le_mul_left _ (w_le_of_le le_rfl (by omega))
      · simp
    have e3 : rf P N' = rf P N - forced.length := by
      simp only [rf, hplaced]; omega
    simp only [hi, e1, e3]
    have e4 : (rf P N - forced.length) * w 1 (k - 1) + forced.length * w 1 (k - 1) =
        rf P N * w 1 (k - 1) := by
      rw [← add_mul, Nat.sub_add_cancel hlen_le]
    omega
  have hcomp : IsCompletion P k N' m n :=
    { hcov with
      common := div_eq_of_subinterval (max_le_max_right _ ht)
        (hcov.clo_le.trans hcov.le_chi) (min_le_min_right _ hhi) hLspec }
  split_ifs with hempty hfail
  · exact ⟨N', rfl, hcomp⟩
  · exfalso
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hfail
    rcases hfail with hf | hf
    · exact absurd hf (not_le.2 (t_lt_of_covers hcov))
    · exact absurd hf (not_lt.2 (pow_le_hi_of_covers hcov))
  · exact ih hcomp

end Rules

/-! ### The tree -/

section Tree

variable {k : ℕ} {N : Node} {m n : ℕ}

lemma sum_update_mul {b : ℕ} (f g : ℕ → ℕ) {j : ℕ} (hj : j < b) (e : ℕ) :
    ∑ x ∈ range b, Function.update f j (f j + e) x * g x = ∑ x ∈ range b, f x * g x + e * g j := by
  have hx : ∀ x, Function.update f j (f j + e) x * g x =
      f x * g x + if x = j then e * g j else 0 := by
    intro x
    by_cases hxj : x = j
    · subst hxj
      simp [add_mul]
    · simp [hxj]
  simp only [hx, sum_add_distrib, sum_ite_eq', mem_range, hj, ↓reduceIte]

lemma t_childAt {j : ℕ} (hj : j < P.b) (e : ℕ) : t P (childAt j e N) = t P N + e * w 0 j :=
  sum_update_mul N.cnt (w 0) hj e

lemma placed_childAt {j : ℕ} (hj : j < P.b) (e : ℕ) :
    placed P (childAt j e N) = placed P N + e := by
  have := sum_update_mul N.cnt (fun _ => 1) hj e
  simpa [placed, childAt] using this

/-- **The child with the true count.** If `n` is a completion of `N` at level `k ≥ 1`, then the
child that gives the digit `j = k - 1` its count in `n` exists (`e ≤ rf`) and has `n` as a
completion. Its interval lies inside the interval of `N`, so the known prefix stays common. -/
theorem childAt_isCompletion (h : IsCompletion P k N m n) (hk : 1 ≤ k) :
    digitCount P.b P.d n (k - 1) - N.cnt (k - 1) ≤ rf P N ∧
      IsCompletion P (k - 1) (childAt (k - 1) (digitCount P.b P.d n (k - 1) - N.cnt (k - 1)) N)
        m n := by
  set j := k - 1 with hj
  set e := digitCount P.b P.d n j - N.cnt j with he
  have hjb : j < P.b := by have := h.level_le; omega
  have hcj := h.cnt_le j
  have herf : e ≤ rf P N := by
    rw [h.rf_eq]
    exact single_le_sum (f := fun x => digitCount P.b P.d n x - N.cnt x) (fun _ _ => Nat.zero_le _)
      (mem_range.2 hjb)
  refine ⟨herf, ?_⟩
  set N' := childAt j e N with hN'
  have hcov : Covers P j N' m n :=
    { h.toCovers with
      level_le := by have := h.level_le; omega
      decided := fun x hx => by
        rcases Nat.eq_or_lt_of_le hx with rfl | hx
        · simp only [hN', childAt, Function.update_self]
          omega
        · simp only [hN', childAt, Function.update_of_ne (Nat.ne_of_gt hx)]
          exact h.decided x (by omega)
      forced := fun x hx => by
        simp only [hN', childAt, Function.update_of_ne (Nat.ne_of_lt hx)]
        exact h.forced x (by omega) }
  have ht : t P N ≤ t P N' := by rw [hN', t_childAt hjb]; omega
  have hhi : hi P j N' ≤ hi P k N := by
    have e1 := sum_update_mul N.cnt (w 1) hjb e
    have e2 : rf P N' = rf P N - e := by
      simp only [rf, hN', placed_childAt hjb]; omega
    have hw : w 1 (j - 1) ≤ w 1 j := w_le_of_le le_rfl (by omega)
    have e1' : ∑ x ∈ range P.b, N'.cnt x * w 1 x = ∑ x ∈ range P.b, N.cnt x * w 1 x + e * w 1 j :=
      e1
    simp only [hi]
    rw [e1', e2, show k - 1 = j from rfl]
    have : (rf P N - e) * w 1 (j - 1) ≤ (rf P N - e) * w 1 j := Nat.mul_le_mul_left _ hw
    have e3 : e * w 1 j + (rf P N - e) * w 1 j = rf P N * w 1 j := by
      rw [← add_mul, Nat.add_sub_cancel' herf]
    omega
  exact { hcov with
    common := div_eq_of_subinterval (max_le_max_right _ ht)
      (hcov.clo_le.trans hcov.le_chi) (min_le_min_right _ hhi) h.common }

/-- **One step down the tree.** At an inner node with the completion `n`, the child with the
true count is among the candidates (the `break` on `lo ≥ b^d` comes later), survives every test
of `tryChild`, and has the completion `n`. -/
theorem step_of_isCompletion (h : IsCompletion P k N m n) (hk : 2 < k) :
    ∃ e ∈ childCands P k N, ∃ N', expandChild P k N e = some N' ∧
      IsCompletion P (k - 1) N' m n := by
  obtain ⟨herf, hc⟩ := childAt_isCompletion h (by omega)
  set e := digitCount P.b P.d n (k - 1) - N.cnt (k - 1)
  have hjb : k - 1 < P.b := by have := h.level_le; omega
  refine ⟨e, ?_, ?_⟩
  · refine mem_takeWhile_range (by omega) fun e' he' => ?_
    have h1 := t_lt_of_covers hc.toCovers
    rw [t_childAt hjb] at h1
    rw [decide_eq_true_eq, t_childAt hjb]
    have := Nat.mul_le_mul_right (w 0 (k - 1)) he'
    omega
  · obtain ⟨c', hs, hc'⟩ := settle_isCompletion (P.d + 1) hc
    refine ⟨c', ?_, hc'⟩
    have hhi := not_lt.2 (pow_le_hi_of_covers hc.toCovers)
    simp only [expandChild, tryChild, oneSlotFails_eq_false hc, Bool.false_eq_true,
      ↓reduceIte, hhi, hs, firstDigitOk_of_isCompletion hc', Bool.not_true,
      oneSlotFails_eq_false hc', pairFails_eq_false hc']

/-- **A leaf finds the solution.** At level 2 or below every digit from 2 up is decided, so the
completion `n` has `c_1 - cnt 1` extra ones and the rest of the free slots are zeros. -/
theorem mem_leaf (h : Covers P k N m n) (hk : k ≤ 2) : (m, n) ∈ leaf P N := by
  set c := digitCount P.b P.d n with hc
  have hb := h.two_le_b
  have hrf : rf P N = (c 0 - N.cnt 0) + (c 1 - N.cnt 1) := by
    rw [h.rf_eq]
    have hsub : ({0, 1} : Finset ℕ) ⊆ range P.b := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rw [mem_range]
      omega
    rw [← sum_subset hsub fun x _ hx => h.sub_eq_zero_of_le (by simp at hx; omega)]
    rw [sum_pair (by decide)]
  set e := c 1 - N.cnt 1 with he
  have hcnt : leafCnt N (rf P N) e = c := by
    funext x
    simp only [leafCnt]
    have h0 : N.cnt 0 ≤ c 0 := h.cnt_le 0
    have h1 : N.cnt 1 ≤ c 1 := h.cnt_le 1
    split_ifs with hx1 hx0
    · subst hx1; omega
    · subst hx0; omega
    · exact h.decided x (by omega)
  simp only [leaf, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  refine ⟨e, by omega, m, h.mem, ?_⟩
  rw [hcnt, h.sol]
  simp [leafCheck, h.low, h.high, hc, digitCount]

/-- **A leaf outputs only solutions.** Its exact check is the definition of a solution in count
form. -/
theorem leaf_sound (hb : 2 ≤ P.b) {p : ℕ × ℕ} (hp : p ∈ leaf P N) :
    p.1 ∈ P.ms ∧ 0 < p.2 ∧ IsMunchausen P.b p.1 p.2 := by
  simp only [leaf, List.mem_flatMap, List.mem_range, List.mem_filterMap] at hp
  obtain ⟨e, -, m, hm, hp⟩ := hp
  split_ifs at hp with hcheck
  cases hp
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hcheck
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcheck
  have hd : 1 ≤ P.d := by
    by_contra hd
    simp only [show P.d = 0 by omega, Nat.zero_sub, pow_zero] at h1 h2
    omega
  refine ⟨hm, lt_of_lt_of_le (pow_pos (by omega) _) h1, ?_⟩
  rw [isMunchausen_iff_sum hb h1 h2 hd]
  exact sum_congr rfl fun x hx => by rw [digitCount, h3 x (mem_range.1 hx)]

end Tree

/-! ### The search -/

/-- **The root** has every `d`-digit solution as a completion. The digits above `kmax` have count
0 by Proposition 1.2, nothing is forced, and nothing is known. -/
theorem root_isCompletion {b d m n low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hm : m ≤ 1)
    (hmem : m ∈ ms) (h1 : b ^ (d - 1) ≤ n) (h2 : n < b ^ d) (hsol : IsMunchausen b m n) :
    IsCompletion ⟨b, d, ms, low, pair⟩ (kmax b d + 1) root m n := by
  have hd : 1 ≤ d := by
    by_contra hd
    simp only [show d = 0 by omega, Nat.zero_sub, pow_zero] at h1 h2
    omega
  have hcov : Covers ⟨b, d, ms, low, pair⟩ (kmax b d + 1) root m n :=
    { two_le_b := hb
      level_le := by
        have := Nat.findGreatest_le (P := fun x => x ^ x < b ^ d) (b - 1)
        simp only [kmax]
        omega
      mem := hmem
      m_le := hm
      low := h1
      high := h2
      sol := (isMunchausen_iff_sum hb h1 h2 hd).1 hsol
      decided := fun x hx => by
        simp only [root]
        by_contra hne
        have hpos : 0 < digitCount b d n x := by omega
        have hxb : x < b := by
          by_contra hxb
          rw [digitCount_eq_zero (by omega) (not_lt.1 hxb)] at hpos
          omega
        have := Nat.le_findGreatest (P := fun x => x ^ x < b ^ d) (show x ≤ b - 1 by omega)
          (pow_self_lt_of_digitCount_pos hb h1 h2 hd hsol hpos)
        simp only [kmax] at hx
        omega
      forced := fun x _ => by simp [root, topDigits]
      pl_le := Nat.zero_le _ }
  refine { hcov with common := ?_ }
  have hlt : clo ⟨b, d, ms, low, pair⟩ root < b ^ d := hcov.clo_lt
  have hchi : chi ⟨b, d, ms, low, pair⟩ (kmax b d + 1) root ≤ b ^ d - 1 := min_le_right _ _
  have hpow := pow_pos (show 0 < b by omega) d
  change clo ⟨b, d, ms, low, pair⟩ root / b ^ (d - 0) =
    chi ⟨b, d, ms, low, pair⟩ (kmax b d + 1) root / b ^ (d - 0)
  rw [Nat.sub_zero, Nat.div_eq_of_lt hlt, Nat.div_eq_of_lt (by omega)]

/-- Every output for one length is a solution. -/
theorem searchLen_sound {b d low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) :
    ∀ p ∈ searchLen b d ms low pair, p.1 ∈ ms ∧ 0 < p.2 ∧ IsMunchausen b p.1 p.2 := by
  intro p hp
  exact dfs_sound (Q := fun p : ℕ × ℕ => p.1 ∈ ms ∧ 0 < p.2 ∧ IsMunchausen b p.1 p.2)
    (fun N q hq => leaf_sound (P := ⟨b, d, ms, low, pair⟩) (N := N) hb hq) _ _ p hp

/-- **Completeness for one length.** Every `d`-digit solution under a convention `m ∈ ms` is
found, with any numbers of digits in the last-digit tests. -/
theorem mem_searchLen {b d m n low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hm : m ≤ 1)
    (hmem : m ∈ ms) (h1 : b ^ (d - 1) ≤ n) (h2 : n < b ^ d) (hsol : IsMunchausen b m n) :
    (m, n) ∈ searchLen b d ms low pair :=
  dfs_complete (Inv := fun k N => IsCompletion ⟨b, d, ms, low, pair⟩ k N m n) (m, n)
    (fun _ _ hk h => step_of_isCompletion h hk) (fun _ _ hk h => mem_leaf h.toCovers hk) _ _
    (root_isCompletion hb hm hmem h1 h2 hsol)

/-- **Soundness**, for any numbers of digits in the last-digit tests. Every pair `(m, n)` returned
by the search is a positive solution under `0^0 = m`, for a convention `m ∈ ms`. -/
theorem searchWith_sound {b low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) :
    ∀ p ∈ searchWith b ms low pair, p.1 ∈ ms ∧ 0 < p.2 ∧ IsMunchausen b p.1 p.2 := by
  intro p hp
  simp only [searchWith, List.mem_append, List.mem_flatMap] at hp
  rcases hp with hp | ⟨d, -, hp⟩
  · simp only [oneDigit, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hp
    obtain ⟨m, hm, x, ⟨hxb, hx0, hwx⟩, rfl⟩ := hp
    refine ⟨hm, hx0, ?_⟩
    rw [IsMunchausen, F, Nat.digits_of_lt b x hx0.ne' hxb]
    simpa using hwx
  · exact searchLen_sound hb p hp

/-- **Soundness and completeness**, for any numbers `low` and `pair` of digits in the last-digit
tests. For a convention `m ∈ ms` with `m ≤ 1`, the search returns `(m, n)` exactly when `n` is a
positive solution in base `b` under `0^0 = m`. -/
theorem mem_searchWith_iff {b m n low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hm : m ≤ 1)
    (hmem : m ∈ ms) : (m, n) ∈ searchWith b ms low pair ↔ 0 < n ∧ IsMunchausen b m n := by
  refine ⟨fun h => (searchWith_sound hb _ h).2, fun ⟨hn, hsol⟩ => ?_⟩
  obtain ⟨h1, h2, hD⟩ := pow_le_of_digits_length hb hn
  have hDb := length_le_maxLen hb hm hsol
  set D := (Nat.digits b n).length with hDdef
  simp only [searchWith, List.mem_append, List.mem_flatMap, List.mem_range'_1]
  rcases Nat.eq_or_lt_of_le hD with hD1 | hD2
  · left
    rw [← hD1, pow_one] at h2
    have hw : w m n = n := by
      have := hsol
      rwa [IsMunchausen, F, Nat.digits_of_lt b n hn.ne' h2, Fs_singleton] at this
    simp only [oneDigit, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Prod.mk.injEq]
    exact ⟨m, hmem, n, ⟨h2, hn, hw⟩, rfl, rfl⟩
  · right
    exact ⟨D, ⟨by omega, by simp only [maxLen] at hDb ⊢; omega⟩,
      mem_searchLen hb hm hmem h1 h2 hsol⟩

/-- **The search computes the specification**, for any numbers of digits in the last-digit tests.
For `m ∈ ms` with `m ≤ 1`, the numbers found under `0^0 = m` are exactly the positive
solutions. -/
theorem foundWith_eq_solutions {b m low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hm : m ≤ 1)
    (hmem : m ∈ ms) : foundWith b ms low pair m = solutions b m := by
  ext n
  rw [mem_solutions hb hm, ← mem_searchWith_iff (low := low) (pair := pair) hb hm hmem]
  simp only [foundWith, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨m', n'⟩, ⟨hp, rfl⟩, rfl⟩
    exact hp
  · intro hp
    exact ⟨(m, n), ⟨hp, rfl⟩, rfl⟩

/-- **Soundness.** Every pair `(m, n)` returned by the search (with the default tests) is a
positive solution under `0^0 = m`, for a convention `m ∈ ms`. -/
theorem search_sound {b : ℕ} {ms : List ℕ} (hb : 2 ≤ b) :
    ∀ p ∈ search b ms, p.1 ∈ ms ∧ 0 < p.2 ∧ IsMunchausen b p.1 p.2 :=
  searchWith_sound hb

/-- **Soundness and completeness.** For a convention `m ∈ ms` with `m ≤ 1`, the search with the
default tests returns `(m, n)` exactly when `n` is a positive solution in base `b` under
`0^0 = m`. -/
theorem mem_search_iff {b m n : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) (hmem : m ∈ ms) :
    (m, n) ∈ search b ms ↔ 0 < n ∧ IsMunchausen b m n :=
  mem_searchWith_iff hb hm hmem

/-- **The search computes the specification.** For `m ∈ ms` with `m ≤ 1`, the numbers that
`search b ms` finds under `0^0 = m` are exactly the positive solutions. -/
theorem found_eq_solutions {b m : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hm : m ≤ 1) (hmem : m ∈ ms) :
    found b ms m = solutions b m :=
  foundWith_eq_solutions hb hm hmem

end ExactSearch

end Munchausen
