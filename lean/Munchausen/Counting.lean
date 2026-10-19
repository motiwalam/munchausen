import Munchausen.Basic

/-!
# Counting solutions and bases (sections 4.1, 10.5, 11.6)

* finite sets of digit strings with bounded digits, and their sizes;
* Proposition 10.4: at most `X (X+1)^(k-1)` bases up to `B` have a `k`-digit solution;
* the finite form of Theorem 11.2: the bases up to `B` with a solution of at most `K`
  digits number at most the sum of these bounds.
-/

namespace Munchausen

/-- The strings of length `n` with every digit at most `X`. -/
def stringsLE (X : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => ((Finset.range (X + 1)) ×ˢ stringsLE X n).image fun p => p.1 :: p.2

lemma mem_stringsLE {X n : ℕ} {l : List ℕ} :
    l ∈ stringsLE X n ↔ l.length = n ∧ ∀ d ∈ l, d ≤ X := by
  induction n generalizing l with
  | zero => simp [stringsLE, List.length_eq_zero_iff]; rintro rfl; simp
  | succ n ih =>
    simp only [stringsLE, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · rintro ⟨d, t, ⟨hd, ht⟩, rfl⟩
      rw [ih] at ht
      refine ⟨by simp [ht.1], fun e he => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · omega
      · exact ht.2 e he
    · rintro ⟨hlen, hall⟩
      match l, hlen with
      | d :: t, hlen =>
        refine ⟨d, t, ⟨by have := hall d (by simp); omega, ih.2 ⟨by simpa using hlen,
          fun e he => hall e (by simp [he])⟩⟩, rfl⟩

lemma card_stringsLE (X n : ℕ) : (stringsLE X n).card = (X + 1) ^ n := by
  induction n with
  | zero => simp [stringsLE]
  | succ n ih =>
    rw [stringsLE, Finset.card_image_of_injective _ (fun p q h => by
      simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2), Finset.card_product,
      Finset.card_range, ih, pow_succ]
    ring

/-- The strings of length `n + 1` with a leading digit from 1 to `X` and other digits at most
`X`. -/
def stringsLeadLE (X n : ℕ) : Finset (List ℕ) :=
  ((Finset.Icc 1 X) ×ˢ stringsLE X n).image fun p => p.1 :: p.2

lemma card_stringsLeadLE (X n : ℕ) : (stringsLeadLE X n).card = X * (X + 1) ^ n := by
  rw [stringsLeadLE, Finset.card_image_of_injective _ (fun p q h => by
    simp only [List.cons.injEq] at h; exact Prod.ext h.1 h.2), Finset.card_product,
    Nat.card_Icc, card_stringsLE]
  simp

lemma mem_stringsLeadLE {X n d : ℕ} {t : List ℕ} (hd : 1 ≤ d) (hdX : d ≤ X)
    (ht : t.length = n) (hall : ∀ e ∈ t, e ≤ X) : d :: t ∈ stringsLeadLE X n := by
  simp only [stringsLeadLE, Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Prod.exists]
  exact ⟨d, t, ⟨⟨hd, hdX⟩, mem_stringsLE.2 ⟨ht, hall⟩⟩, rfl⟩

/-- A string with digits below `b` has value below `b ^ length`. -/
lemma P_lt_pow {b : ℕ} (hb : 1 < b) {s : List ℕ} (hs : ∀ d ∈ s, d < b) :
    P b s < b ^ s.length := by
  rw [P_eq_ofDigits, ← List.length_reverse]
  exact Nat.ofDigits_lt_base_pow_length hb (by simpa using hs)

/-- **Proposition 1.2** for strings: every digit `d` of a `k`-digit solution in base `b ≤ B`
has `d^d < B^k`. -/
lemma IsSolution.pow_self_lt {b m B : ℕ} {s : List ℕ} (h : IsSolution b m s) (hb : 2 ≤ b)
    (hbB : b ≤ B) {d : ℕ} (hd : d ∈ s) : d ^ d < B ^ s.length := by
  have h1 : P b s < b ^ s.length := P_lt_pow (by omega) h.lt_base
  have h2 : b ^ s.length ≤ B ^ s.length := Nat.pow_le_pow_left hbB _
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · have hlen : 1 ≤ s.length := List.length_pos_of_mem hd
    have : 2 ≤ B ^ s.length :=
      le_trans (by rw [pow_one]; omega) (Nat.pow_le_pow_right (by omega) hlen)
    simp; omega
  · have := w_le_Fs (m := m) hd
    rw [w_of_ne_zero m hd0.ne', ← h.eq] at this
    omega

open Classical in
/-- The bases `2 ≤ b ≤ B` with a `k`-digit solution under `0^0 = m`. -/
noncomputable def basesWith (m B k : ℕ) : Finset ℕ :=
  (Finset.Icc 2 B).filter fun b => ∃ s : List ℕ, s.length = k ∧ IsSolution b m s

/-- **Proposition 10.4** (section 10.5). Let `X` bound every digit `x` with `x^x < B^k`. Then
at most `X (X+1)^(k-1)` bases `b ≤ B` have a `k`-digit solution, for `k ≥ 2`. -/
theorem prop10_4 {m B k X : ℕ} (hk : 2 ≤ k) (hX : ∀ x, x ^ x < B ^ k → x ≤ X) :
    (basesWith m B k).card ≤ X * (X + 1) ^ (k - 1) := by
  classical
  let f : ℕ → List ℕ := fun b =>
    if h : ∃ s : List ℕ, s.length = k ∧ IsSolution b m s then Classical.choose h else []
  have hf : ∀ b ∈ basesWith m B k, (f b).length = k ∧ IsSolution b m (f b) := by
    intro b hb
    unfold basesWith at hb
    rw [Finset.mem_filter] at hb
    simp only [f, dif_pos hb.2]
    exact Classical.choose_spec hb.2
  rw [← card_stringsLeadLE]
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    have hbB : 2 ≤ b ∧ b ≤ B := by
      have hb' := hb
      unfold basesWith at hb'
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hb'
      exact hb'.1
    obtain ⟨hlen, hs⟩ := hf b (Finset.mem_coe.1 hb)
    have hdig : ∀ d ∈ f b, d ≤ X := fun d hd =>
      hX d (by rw [← hlen]; exact hs.pow_self_lt hbB.1 hbB.2 hd)
    generalize f b = l at hlen hs hdig ⊢
    match l, hlen with
    | [], hlen => simp at hlen; omega
    | d :: t, hlen =>
      have hd := hs.head_ne_zero (by simp)
      simp only [List.head_cons] at hd
      exact mem_stringsLeadLE (by omega) (hdig d (by simp)) (by simp at hlen; omega)
        (fun e he => hdig e (by simp [he]))
  · intro b hb c hc hbc
    obtain ⟨hlen, hs⟩ := hf b (Finset.mem_coe.1 hb)
    obtain ⟨-, hs'⟩ := hf c (Finset.mem_coe.1 hc)
    rw [hbc] at hs hlen
    exact hs.base_unique (by omega) hs'

/-- **Theorem 11.2**, finite form (section 11.6). The bases `b ≤ B` with a solution of `k`
digits for some `2 ≤ k ≤ K` number at most `sum_k X_k (X_k + 1)^(k-1)`, where `X_k` bounds the
digits with `x^x < B^k`. The asymptotic form `B^(1 - 2 eps + o(1))` follows from the size of
`X_k`. -/
theorem theorem11_2_finite {m B K : ℕ} (X : ℕ → ℕ) (hX : ∀ k x, x ^ x < B ^ k → x ≤ X k) :
    ((Finset.Icc 2 K).biUnion fun k => basesWith m B k).card ≤
      ∑ k ∈ Finset.Icc 2 K, X k * (X k + 1) ^ (k - 1) := by
  refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun k hk => ?_)
  exact prop10_4 (Finset.mem_Icc.1 hk).1 (hX k)

/-! ### Proposition 4.1: a fixed length in one base -/

lemma lt_of_succ_lt {f : ℕ → ℤ} {n : ℕ} (h : ∀ x < n, f (x + 1) < f x) :
    ∀ i j, i < j → j ≤ n → f j < f i := by
  intro i j hij hjn
  induction j, hij using Nat.le_induction with
  | base => exact h i (by omega)
  | succ j hj ih => exact (h j (by omega)).trans (ih (by omega))

lemma lt_of_lt_succ {f : ℕ → ℤ} {n : ℕ} (h : ∀ x, n ≤ x → f x < f (x + 1)) :
    ∀ j k, n ≤ j → j < k → f j < f k := by
  intro j k hnj hjk
  induction k, hjk using Nat.le_induction with
  | base => exact h j hnj
  | succ k hk ih => exact ih.trans (h k (by omega))

/-- A function on `ℕ` with strictly increasing differences takes each value at most twice
(proof of Proposition 4.1). -/
lemma card_le_two_of_convex (f : ℕ → ℤ) (hf : ∀ a, f (a + 1) - f a < f (a + 2) - f (a + 1))
    (v : ℤ) (S : Finset ℕ) (hS : ∀ a ∈ S, f a = v) : S.card ≤ 2 := by
  by_contra hc
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.1 (not_le.1 hc)
  -- order the three elements
  have key : ∀ i j k, i < j → j < k → f i = f j → f j = f k → False := by
    intro i j k hij hjk e1 e2
    have hd : StrictMono fun a => f (a + 1) - f a := strictMono_nat_of_lt_succ fun a => hf a
    by_cases hneg : f j - f (j - 1) < 0
    · have h1 : ∀ x < j, f (x + 1) < f x := by
        intro x hx
        have : f (x + 1) - f x ≤ f (j - 1 + 1) - f (j - 1) := hd.monotone (by omega)
        rw [show j - 1 + 1 = j by omega] at this
        linarith
      have := lt_of_succ_lt h1 i j hij le_rfl
      linarith
    · have h1 : ∀ x, j ≤ x → f x < f (x + 1) := by
        intro x hx
        have : f (j - 1 + 1) - f (j - 1) < f (x + 1) - f x := hd (by omega)
        rw [show j - 1 + 1 = j by omega] at this
        linarith
      have := lt_of_lt_succ h1 j k le_rfl hjk
      linarith
  have ei := hS i hi
  have ej := hS j hj
  have ek := hS k hk
  rcases Nat.lt_or_gt_of_ne hij with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hik with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hjk with h3 | h3
  all_goals first
    | exact key i j k (by omega) (by omega) (by rw [ei, ej]) (by rw [ej, ek])
    | exact key i k j (by omega) (by omega) (by rw [ei, ek]) (by rw [ek, ej])
    | exact key j i k (by omega) (by omega) (by rw [ej, ei]) (by rw [ei, ek])
    | exact key j k i (by omega) (by omega) (by rw [ej, ek]) (by rw [ek, ei])
    | exact key k i j (by omega) (by omega) (by rw [ek, ei]) (by rw [ei, ej])
    | exact key k j i (by omega) (by omega) (by rw [ek, ej]) (by rw [ej, ei])
    | omega

/-- `a ↦ a^a - a c` has strictly increasing differences. -/
lemma pow_self_sub_convex (c : ℤ) (a : ℕ) :
    ((a + 1 : ℕ) : ℤ) ^ (a + 1) - (a + 1 : ℕ) * c - ((a : ℤ) ^ a - a * c) <
      ((a + 2 : ℕ) : ℤ) ^ (a + 2) - (a + 2 : ℕ) * c -
        (((a + 1 : ℕ) : ℤ) ^ (a + 1) - (a + 1 : ℕ) * c) := by
  have h1 : (a + 2) * (a + 1) ^ (a + 1) ≤ (a + 2) ^ (a + 2) := by
    have : (a + 1) ^ (a + 1) ≤ (a + 2) ^ (a + 1) := Nat.pow_le_pow_left (by omega) _
    calc (a + 2) * (a + 1) ^ (a + 1) ≤ (a + 2) * (a + 2) ^ (a + 1) := Nat.mul_le_mul_left _ this
      _ = (a + 2) ^ (a + 2) := by ring
  have h2 : 1 ≤ a ^ a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · exact Nat.one_le_pow _ _ ha
  have h1' : ((a : ℤ) + 2) * ((a : ℤ) + 1) ^ (a + 1) ≤ ((a : ℤ) + 2) ^ (a + 2) := by
    exact_mod_cast h1
  have h2' : (1 : ℤ) ≤ (a : ℤ) ^ a := by exact_mod_cast h2
  push_cast
  nlinarith [pow_pos (show (0 : ℤ) < (a : ℤ) + 1 by positivity) (a + 1)]

open Classical in
/-- The `k`-digit Munchausen strings in base `b` (all their digits are below `b`). -/
noncomputable def solStrings (b m k : ℕ) : Finset (List ℕ) :=
  (stringsLE (b - 1) k).filter fun s => IsSolution b m s

lemma mem_solStrings {b m k : ℕ} (hb : 1 ≤ b) {s : List ℕ} :
    s ∈ solStrings b m k ↔ s.length = k ∧ IsSolution b m s := by
  unfold solStrings
  rw [Finset.mem_filter, mem_stringsLE]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun d hd => by have := h2.lt_base d hd; omega⟩, h2⟩

/-- **Proposition 4.1** (section 4.1). Let `X` bound every digit `x` with `x^x < b^k`. Then
base `b` has at most `2 (X+1)^(k-1)` solutions with `k ≥ 1` digits: once the last `k - 1`
digits are fixed, the leading digit `a` solves `a^a - a b^(k-1) = R`, and a convex function
takes each value at most twice. -/
theorem prop4_1 {b m k X : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hX : ∀ x, x ^ x < b ^ k → x ≤ X) :
    (solStrings b m k).card ≤ 2 * (X + 1) ^ (k - 1) := by
  classical
  have hmem := fun s => mem_solStrings (b := b) (m := m) (k := k) (s := s) (by omega)
  refine (Finset.card_le_mul_card_image (f := List.tail) _ 2 ?_).trans ?_
  · intro t _
    -- all strings in the fiber are `a :: t` with `a^a - a b^(k-1) = P_t(b) - F(t)`
    let fib := (solStrings b m k).filter fun s => s.tail = t
    have hfib : ∀ s ∈ fib, ∃ a, s = a :: t ∧ 1 ≤ a ∧
        ((a : ℤ) ^ a - a * (b : ℤ) ^ (k - 1)) = P (b : ℤ) t - (Fs m t : ℤ) := by
      intro s hs
      rw [Finset.mem_filter, hmem] at hs
      obtain ⟨⟨hlen, hsol⟩, htail⟩ := hs
      match s, hlen, hsol, htail with
      | [], hlen, _, _ => simp at hlen; omega
      | a :: t', hlen, hsol, htail =>
        simp only [List.tail_cons] at htail
        rw [htail] at hlen hsol
        have ha : a ≠ 0 := hsol.head_ne_zero (by simp)
        refine ⟨a, by rw [htail], Nat.one_le_iff_ne_zero.2 ha, ?_⟩
        have heq := hsol.eq
        have := congrArg (fun n : ℕ => (n : ℤ)) heq
        simp only [P_cons, Fs_cons, Nat.cast_add, Nat.cast_mul, cast_P, Nat.cast_pow,
          Nat.cast_id] at this
        rw [w_of_ne_zero m ha] at this
        simp only [List.length_cons] at hlen
        rw [show t.length = k - 1 by omega] at this
        push_cast at this
        linarith
    have hinj : Set.InjOn List.head! (fib : Set (List ℕ)) := by
      intro s hs s' hs' h
      obtain ⟨a, rfl, -⟩ := hfib s hs
      obtain ⟨a', rfl, -⟩ := hfib s' hs'
      simp only [List.head!_cons] at h
      rw [h]
    rw [← Finset.card_image_of_injOn hinj]
    apply card_le_two_of_convex (fun a => (a : ℤ) ^ a - a * (b : ℤ) ^ (k - 1))
      (fun a => by simpa using pow_self_sub_convex ((b : ℤ) ^ (k - 1)) a)
      (P (b : ℤ) t - (Fs m t : ℤ))
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨a', rfl, -, h⟩ := hfib s hs
    simpa using h
  · rw [← card_stringsLE]
    apply Nat.mul_le_mul_left 2
    apply Finset.card_le_card
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [hmem] at hs
    obtain ⟨hlen, hsol⟩ := hs
    rw [mem_stringsLE]
    refine ⟨by rw [List.length_tail, hlen], fun d hd => hX d ?_⟩
    have := hsol.pow_self_lt hb le_rfl (List.mem_of_mem_tail hd)
    rwa [hlen] at this

end Munchausen
