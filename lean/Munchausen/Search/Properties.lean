import Munchausen.Search.Correctness

/-!
# Further properties of the exact search

* `settle_eq_of_le`: the fuel `d + 1` that `tryChild` gives to `settle` is enough. More fuel
  gives the same result, so `settle` computes the fixed point of the Rust loop.
* `searchWith_nodup`, `search_nodup`: the search returns each solution once (for distinct
  conventions `ms`), with any numbers of digits in the last-digit tests. Two children of a node
  differ in the count of one digit, and every output below a child has that count, so the
  subtrees have disjoint outputs.
* `avail_childAt`: the available digits of a child are those of its parent, plus the digit of
  the child when it gets copies outside the prefix. This is how the Rust code updates its mask.
-/

namespace Munchausen

namespace ExactSearch

open Finset

variable {P : Params}

/-! ### `settle` reaches its fixed point -/

lemma prefixLen_le (lo hi : ℕ) : prefixLen P lo hi ≤ P.d := Nat.findGreatest_le _

/-- One more unit of fuel changes nothing once the fuel exceeds the number `d - pl` of unknown
digits: each round that goes on extends the known prefix. -/
theorem settle_succ_eq (k : ℕ) :
    ∀ (fuel : ℕ) (N : Node), P.d - N.pl < fuel → settle P k (fuel + 1) N = settle P k fuel N
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, N, h => by
    conv_lhs => rw [settle]
    conv_rhs => rw [settle]
    simp only
    split_ifs with h1 <;> try rfl
    apply settle_succ_eq
    have := prefixLen_le (P := P) (clo P N) (chi P k N)
    simp only
    omega

/-- **`settle` stops.** Any fuel above `d - pl` gives the same node; `tryChild` uses `d + 1`. -/
theorem settle_eq_of_le (k : ℕ) {fuel fuel' : ℕ} {N : Node} (h : P.d - N.pl < fuel)
    (h' : fuel ≤ fuel') : settle P k fuel' N = settle P k fuel N := by
  induction h' with
  | refl => rfl
  | step hle ih => rw [settle_succ_eq k _ N (lt_of_lt_of_le h hle), ih]

/-! ### No duplicates -/

lemma count_filter_lt_eq_zero (l : List ℕ) {k x : ℕ} (hx : k ≤ x) :
    (l.filter (· < k)).count x = 0 :=
  List.count_eq_zero.2 fun hm => by
    have := (List.mem_filter.1 hm).2
    simp only [decide_eq_true_eq] at this
    omega

/-- `settle` changes only the counts below the level. -/
lemma settle_cnt {k : ℕ} :
    ∀ {fuel : ℕ} {N N' : Node}, settle P k fuel N = some N' → ∀ x, k ≤ x → N'.cnt x = N.cnt x
  | 0, N, N', h, x, _ => by
    simp only [settle, Option.some.injEq] at h
    rw [h]
  | fuel + 1, N, N', h, x, hx => by
    simp only [settle] at h
    split_ifs at h
    · simp only [Option.some.injEq] at h
      rw [h]
    · simp only [Option.some.injEq] at h
      rw [← h]
      simp [count_filter_lt_eq_zero _ hx]
    · rw [settle_cnt h x hx]
      simp [count_filter_lt_eq_zero _ hx]

lemma settle_of_tryChild {j : ℕ} {c c' : Node} (h : tryChild P j c = some c') :
    settle P j (P.d + 1) c = some c' := by
  unfold tryChild at h
  split_ifs at h
  split at h
  · cases h
  · rename_i c'' hs
    split_ifs at h
    simp only [Option.some.injEq] at h
    rw [hs, h]

/-- **The mask of a child** (Rust: `n.avail | (e > 0) << k` in `next_child`). The child that
gives the digit `j` its forced copies plus `e` more, with the prefix of its parent, has the
available digits of its parent, and `j` when `e > 0`. The hypotheses hold in the tree: the
prefix of a candidate child is the prefix of its parent, and `cnt j` counts the copies of `j`
that the prefix forced. -/
theorem avail_childAt {j e : ℕ} {N : Node}
    (hpre : topDigits P.b P.d (clo P (childAt j e N)) N.pl = topDigits P.b P.d (clo P N) N.pl)
    (hocc : (topDigits P.b P.d (clo P N) N.pl).count j = N.cnt j) (x : ℕ) :
    avail P j (childAt j e N) x = (avail P (j + 1) N x || (x == j && decide (0 < e))) := by
  have hpl : (childAt j e N).pl = N.pl := rfl
  simp only [avail, hpl, hpre]
  by_cases hxj : x = j
  · subst hxj
    simp [childAt, hocc]
  · have hcnt : (childAt j e N).cnt x = N.cnt x := by
      simp only [childAt, Function.update_of_ne hxj]
    have hle : (j ≤ x) ↔ (j + 1 ≤ x) := by omega
    simp [hcnt, hxj, hle]

/-- A child of `N` at level `k` keeps the counts of the digits `x ≥ k` and gives the digit
`k - 1` the count `cnt (k - 1) + e`. -/
lemma expandChild_cnt {k e : ℕ} {N N' : Node} (hk : 1 ≤ k) (h : expandChild P k N e = some N') :
    (∀ x, k ≤ x → N'.cnt x = N.cnt x) ∧ N'.cnt (k - 1) = N.cnt (k - 1) + e := by
  have hs := settle_cnt (settle_of_tryChild h)
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hs x (by omega)]
    simp only [childAt, Function.update_of_ne (show x ≠ k - 1 by omega)]
  · rw [hs (k - 1) le_rfl]
    simp only [childAt, Function.update_self]

/-- What every output below a node satisfies: its convention is in `ms`, it has `d` digits, and
its digit counts agree with the decided counts of the node (from 2 up). -/
def Out (P : Params) (k : ℕ) (N : Node) (p : ℕ × ℕ) : Prop :=
  p.1 ∈ P.ms ∧ P.b ^ (P.d - 1) ≤ p.2 ∧ p.2 < P.b ^ P.d ∧
    ∀ x, k ≤ x → 2 ≤ x → x < P.b → digitCount P.b P.d p.2 x = N.cnt x

/-- The entries of a leaf for one number `e` of extra ones. -/
lemma mem_leaf_entry {N : Node} {e : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ P.ms.filterMap fun m =>
      if leafCheck P (leafCnt N (rf P N) e) (∑ x ∈ range P.b, leafCnt N (rf P N) e x * w m x)
      then some (m, ∑ x ∈ range P.b, leafCnt N (rf P N) e x * w m x) else none) :
    p.1 ∈ P.ms ∧ P.b ^ (P.d - 1) ≤ p.2 ∧ p.2 < P.b ^ P.d ∧
      ∀ x < P.b, digitCount P.b P.d p.2 x = leafCnt N (rf P N) e x := by
  obtain ⟨m, hm, hp⟩ := List.mem_filterMap.1 hp
  split_ifs at hp with hcheck
  simp only [Option.some.injEq] at hp
  subst hp
  simp only [leafCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hcheck
  exact ⟨hm, hcheck.1.1, hcheck.1.2, fun x hx => hcheck.2 x hx⟩

/-- A leaf has no duplicates, and its outputs satisfy `Out`. -/
lemma leaf_nodup (hb : 2 ≤ P.b) (hms : P.ms.Nodup) (k : ℕ) (N : Node) :
    (leaf P N).Nodup ∧ ∀ p ∈ leaf P N, Out P k N p := by
  refine ⟨?_, fun p hp => ?_⟩
  · unfold List.Nodup leaf
    rw [List.pairwise_flatMap]
    refine ⟨fun e _ => ?_, ?_⟩
    · rw [List.pairwise_filterMap]
      refine List.Pairwise.imp ?_ hms
      intro m m' hne p hp p' hp' heq
      dsimp only at hp hp'
      split_ifs at hp hp'
      simp only [Option.some.injEq] at hp hp'
      subst hp hp'
      exact hne (congrArg Prod.fst heq)
    · refine List.Pairwise.imp ?_ List.nodup_range
      intro e e' hne p hp p' hp' heq
      subst heq
      have h1 := (mem_leaf_entry hp).2.2.2 1 (by omega)
      have h2 := (mem_leaf_entry hp').2.2.2 1 (by omega)
      simp only [leafCnt, ↓reduceIte] at h1 h2
      omega
  · simp only [leaf, List.mem_flatMap] at hp
    obtain ⟨e, -, hp⟩ := hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_leaf_entry hp
    refine ⟨h1, h2, h3, fun x _ hx2 hxb => ?_⟩
    rw [h4 x hxb]
    simp only [leafCnt, show x ≠ 1 by omega, show x ≠ 0 by omega, ↓reduceIte]

/-- The search for one length has no duplicates, and its outputs have `d` digits. -/
theorem searchLen_nodup {b d low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hms : ms.Nodup) :
    (searchLen b d ms low pair).Nodup ∧
      ∀ p ∈ searchLen b d ms low pair, Out ⟨b, d, ms, low, pair⟩ (kmax b d + 1) root p := by
  refine dfs_nodup (Good := fun k _ => k ≤ b) (Out := Out ⟨b, d, ms, low, pair⟩)
    (fun k N _ _ => leaf_nodup (P := ⟨b, d, ms, low, pair⟩) hb hms k N)
    (fun k N _ _ => List.Nodup.sublist (List.takeWhile_sublist _) List.nodup_range)
    (fun k N e N' _ hkb he => ⟨by omega, fun p ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, fun x hx hx2 hxb => by
        rw [h4 x (by omega) hx2 hxb, (expandChild_cnt (by omega) he).1 x hx]⟩⟩)
    (fun k N e e' N₁ N₂ p hk hkb hne he₁ he₂ ho₁ ho₂ => hne ?_) _ _ ?_
  · have h1 := ho₁.2.2.2 (k - 1) le_rfl (by omega) (by dsimp only; omega)
    have h2 := ho₂.2.2.2 (k - 1) le_rfl (by omega) (by dsimp only; omega)
    rw [(expandChild_cnt (by omega) he₁).2] at h1
    rw [(expandChild_cnt (by omega) he₂).2] at h2
    omega
  · have := Nat.findGreatest_le (P := fun x => x ^ x < b ^ d) (b - 1)
    simp only [kmax]
    omega

/-- **No duplicates.** With distinct conventions, the search returns each pair `(m, n)` once,
for any numbers of digits in the last-digit tests. -/
theorem searchWith_nodup {b low pair : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hms : ms.Nodup) :
    (searchWith b ms low pair).Nodup := by
  unfold searchWith
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · unfold oneDigit List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun m _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne heq => hne (congrArg Prod.snd heq))
        (List.Nodup.sublist List.filter_sublist List.nodup_range)
    · refine List.Pairwise.imp ?_ hms
      intro m m' hne p hp p' hp' heq
      simp only [List.mem_map] at hp hp'
      obtain ⟨x, -, rfl⟩ := hp
      obtain ⟨x', -, rfl⟩ := hp'
      exact hne (congrArg Prod.fst heq)
  · unfold List.Nodup
    rw [List.pairwise_flatMap]
    refine ⟨fun d _ => (searchLen_nodup hb hms).1, ?_⟩
    refine List.Pairwise.imp ?_ List.nodup_range'
    intro d d' hne p hp p' hp' heq
    subst heq
    obtain ⟨-, h1, h2, -⟩ := (searchLen_nodup hb hms).2 p hp
    obtain ⟨-, h1', h2', -⟩ := (searchLen_nodup hb hms).2 p hp'
    apply hne
    by_contra hdd
    rcases Nat.lt_or_gt_of_ne hdd with h | h
    · have := Nat.pow_le_pow_right (show 0 < b by omega) (show d ≤ d' - 1 by omega)
      simp only at h2 h1'
      omega
    · have := Nat.pow_le_pow_right (show 0 < b by omega) (show d' ≤ d - 1 by omega)
      simp only at h2' h1
      omega
  · intro p hp p' hp' heq
    subst heq
    simp only [oneDigit, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at hp
    obtain ⟨m, -, x, ⟨hxb, -, -⟩, rfl⟩ := hp
    simp only [List.mem_flatMap, List.mem_range'_1] at hp'
    obtain ⟨d, ⟨hd, -⟩, hp'⟩ := hp'
    obtain ⟨-, h1, -, -⟩ := (searchLen_nodup hb hms).2 _ hp'
    have := Nat.pow_le_pow_right (show 0 < b by omega) (show 1 ≤ d - 1 by omega)
    simp only [pow_one] at this h1
    omega

/-- **No duplicates** for the search with the default tests. -/
theorem search_nodup {b : ℕ} {ms : List ℕ} (hb : 2 ≤ b) (hms : ms.Nodup) :
    (search b ms).Nodup :=
  searchWith_nodup hb hms

end ExactSearch

end Munchausen
