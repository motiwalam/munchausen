import Munchausen.Congruences

/-!
# Constructions (chapter 2)

* twins under `0^0 = 0`, Proposition 2.1;
* the balance of a placement, and self-paying digits: Propositions 2.2 (sufficiency), 2.3
  and 2.5;
* swaps, section 2.3;
* the complete description of 2-digit solutions, Proposition 2.6, and its four families;
* solutions of every length under `0^0 = 0`, Proposition 2.7.
-/

namespace Munchausen

/-! ### Twins: Proposition 2.1 -/

/-- **Proposition 2.1** (section 2.1), for strings. Under `0^0 = 0`, a string ending in 0 is a
solution exactly when the same string ending in 1 is. -/
theorem isSolution_twin {b : ℕ} (hb : 2 ≤ b) {s : List ℕ} (hs : s ≠ []) :
    IsSolution b 0 (s ++ [0]) ↔ IsSolution b 0 (s ++ [1]) := by
  have hhead : ∀ d, ∀ h : s ++ [d] ≠ [], (s ++ [d]).head h = s.head hs := fun d h => by
    rw [List.head_append_of_ne_nil hs]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun d hd => ?_, fun h => ?_, ?_⟩
    · rcases List.mem_append.1 hd with hd | hd
      · exact h1 d (List.mem_append_left _ hd)
      · simp at hd; omega
    · rw [hhead]; have := h2 (by simp); rwa [hhead] at this
    · simp only [P_append_singleton, Fs_append, Fs_singleton] at h3 ⊢
      simp at h3 ⊢; omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun d hd => ?_, fun h => ?_, ?_⟩
    · rcases List.mem_append.1 hd with hd | hd
      · exact h1 d (List.mem_append_left _ hd)
      · simp at hd; omega
    · rw [hhead]; have := h2 (by simp); rwa [hhead] at this
    · simp only [P_append_singleton, Fs_append, Fs_singleton] at h3 ⊢
      simp at h3 ⊢; omega

/-- **Proposition 2.1** (section 2.1). Under `0^0 = 0`, a number `n ≥ 1` whose last digit is 0
is a solution if and only if `n + 1` is a solution. -/
theorem isMunchausen_twin {b n : ℕ} (hb : 2 ≤ b) (hn : n ≠ 0) (h0 : n % b = 0) :
    IsMunchausen b 0 n ↔ IsMunchausen b 0 (n + 1) := by
  have hd1 : Nat.digits b n = 0 :: Nat.digits b (n / b) := by
    rw [Nat.digits_def' (by omega) (Nat.pos_of_ne_zero hn), h0]
  have hd2 : Nat.digits b (n + 1) = 1 :: Nat.digits b (n / b) := by
    rw [Nat.digits_def' (by omega) (by omega)]
    have e1 : (n + 1) % b = 1 := by
      rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    have e2 : (n + 1) / b = n / b := by
      apply Nat.succ_div_of_not_dvd
      intro hdvd
      have := Nat.mod_eq_zero_of_dvd hdvd
      omega
    rw [e1, e2]
  simp only [IsMunchausen, F, hd1, hd2, Fs_cons, w_zero, w_one]
  omega

/-! ### Balance and self-paying digits -/

/-- Changing the digit at position `|u|` from `x` to `y` changes the value by
`(y - x) b ^ |u|` (section 1.3). -/
lemma P_middle {R : Type*} [CommSemiring R] (b : R) (t u : List ℕ) (x : ℕ) :
    P b (t ++ x :: u) = b ^ (u.length + 1) * P b t + x * b ^ u.length + P b u := by
  rw [P_append, P_cons, List.length_cons]
  ring

lemma Fs_middle (m : ℕ) (t u : List ℕ) (x : ℕ) :
    Fs m (t ++ x :: u) = Fs m t + w m x + Fs m u := by
  simp; ring

/-- A self-paying digit (section 2.2) is a digit `a` whose placement at position `k` has zero
balance: `a b^k = a^a = w(a)`. -/
lemma SelfPaying.balance {b a k m : ℕ} (h : SelfPaying b a k) : a * b ^ k = w m a := by
  rw [w_of_ne_zero m (by have := h.1; omega)]
  exact h.2.2.2

/-- **Proposition 2.3** (section 2.2). Under `0^0 = 0`, putting a self-paying digit on a
position that holds 0, below the leading digit, turns a solution into a solution, and setting
it back to 0 does the same. -/
theorem isSolution_selfPaying_iff {b a : ℕ} {t u : List ℕ} (ht : t ≠ [])
    (h : SelfPaying b a u.length) :
    IsSolution b 0 (t ++ 0 :: u) ↔ IsSolution b 0 (t ++ a :: u) := by
  have hbal := h.balance (m := 0)
  have hhead : ∀ x, ∀ hne : t ++ x :: u ≠ [], (t ++ x :: u).head hne = t.head ht := fun x hne => by
    rw [List.head_append_of_ne_nil ht]
  have hlt : a < b := h.2.2.1
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun d hd => ?_, fun hne => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_cons] at hd
      rcases hd with hd | rfl | hd
      · exact h1 d (by simp [hd])
      · exact hlt
      · exact h1 d (by simp [hd])
    · rw [hhead]; have := h2 (by simp); rwa [hhead] at this
    · rw [P_middle, Fs_middle] at h3 ⊢
      simp only [Nat.cast_id, w_zero, CharP.cast_eq_zero, zero_mul, add_zero] at h3 ⊢
      rw [hbal]; omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun d hd => ?_, fun hne => ?_, ?_⟩
    · simp only [List.mem_append, List.mem_cons] at hd
      rcases hd with hd | rfl | hd
      · exact h1 d (by simp [hd])
      · have := h1 a (by simp); omega
      · exact h1 d (by simp [hd])
    · rw [hhead]; have := h2 (by simp); rwa [hhead] at this
    · rw [P_middle, Fs_middle] at h3 ⊢
      simp only [Nat.cast_id, w_zero, CharP.cast_eq_zero, zero_mul, add_zero] at h3 ⊢
      rw [hbal] at h3; omega

/-- **Proposition 2.5** (section 2.2). Let `a` be self-paying at position `k` and let `u` be a
string of `k` digits (leading zeros allowed) with `p` zeros before its first nonzero digit.
Then `(a, u)` is a solution exactly when `u` without its leading zeros satisfies
`F(u') + p w(0) = P(u')`, that is, when `F(u) = P(u)` with every zero of `u` weighed. -/
theorem isSolution_selfPaying_cons_iff {b a m : ℕ} {u : List ℕ} (h : SelfPaying b a u.length)
    (hu : ∀ d ∈ u, d < b) :
    IsSolution b m (a :: u) ↔ P b u = Fs m u := by
  have hbal := h.balance (m := m)
  constructor
  · rintro ⟨-, -, h3⟩
    simp only [P_cons, Fs_cons, Nat.cast_id] at h3
    omega
  · intro h3
    refine ⟨fun d hd => ?_, fun _ => ?_, ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact h.2.2.1
      · exact hu d hd
    · simp only [List.head_cons]; have := h.1; omega
    · simp only [P_cons, Fs_cons, Nat.cast_id]
      omega

/-- **Proposition 2.2**, the construction (section 2.2). If `1 ≤ s < t` and
`t ∣ s (r^s - 1)`, then `r^s` is self-paying in base `r^t` at position `s (r^s - 1) / t`. -/
theorem selfPaying_of_dvd {r s t : ℕ} (hr : 2 ≤ r) (hs : 1 ≤ s) (hst : s < t)
    (hdvd : t ∣ s * (r ^ s - 1)) : SelfPaying (r ^ t) (r ^ s) (s * (r ^ s - 1) / t) := by
  have hrs : 2 ≤ r ^ s := le_trans hr (Nat.le_self_pow (by omega) r)
  refine ⟨hrs, ?_, Nat.pow_lt_pow_right (by omega) hst, ?_⟩
  · apply Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd) (by omega)
  · rw [← pow_mul, Nat.mul_div_cancel' hdvd, ← pow_add, ← pow_mul]
    congr 1
    have : s ≤ s * r ^ s := Nat.le_mul_of_pos_right _ (by omega)
    rw [Nat.mul_sub, mul_one]
    omega

/-! ### Swaps: section 2.3 -/

/-- **Swaps** (section 2.3). Under `0^0 = 0`, if `b ^ k = a ^ (a ^ (a+1) - 1)` with `k ≥ 1`,
`a ≥ 1` and `a ^ a < b`, then `(a, 0, ..., 0, a^a)` with `k + 1` digits is a solution in base
`b`: each of the two digits pays for the weight of the other. -/
theorem isSolution_swap {a b k : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k)
    (hbk : b ^ k = a ^ (a ^ (a + 1) - 1)) (hab : a ^ a < b) :
    IsSolution b 0 (a :: (List.replicate (k - 1) 0 ++ [a ^ a])) := by
  have hle : a ≤ a ^ a := by
    calc a = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ a := Nat.pow_le_pow_right (by omega) ha
  refine ⟨fun d hd => ?_, fun _ => by simp; omega, ?_⟩
  · simp at hd
    rcases hd with rfl | ⟨-, rfl⟩ | rfl <;> omega
  · simp only [P_cons, Nat.cast_id, P_append_singleton, P_replicate_zero, mul_zero, add_zero,
      List.length_append, List.length_replicate, List.length_singleton, Fs_cons, Fs_append,
      Fs_replicate, w_zero, Fs_nil]
    rw [show k - 1 + 1 = k by omega, hbk, w_of_ne_zero 0 (by omega),
      w_of_ne_zero 0 (by positivity), ← pow_mul, ← _root_.pow_succ']
    have h1 : 1 ≤ a ^ (a + 1) := Nat.one_le_pow _ _ (by omega)
    rw [show a ^ (a + 1) - 1 + 1 = a ^ (a + 1) by omega, pow_succ]
    ring

/-! ### Two-digit solutions: Proposition 2.6 -/

@[simp] lemma P_pair {R : Type*} [CommSemiring R] (b : R) (a c : ℕ) : P b [a, c] = a * b + c := by
  simp [P_cons]

@[simp] lemma Fs_pair (m a c : ℕ) : Fs m [a, c] = w m a + w m c := by simp

/-- `w(c) ≥ c` for every digit, so `w(c) - c` is a natural number. -/
lemma le_w' (m c : ℕ) : c ≤ w m c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  · exact le_w hc.ne'

/-- **Proposition 2.6** (section 2.4). The 2-digit string `(a, c)` with `a ≥ 1` is a solution in
base `b` exactly when `a, c < b` and `a b = a^a + w(c) - c`. -/
theorem isSolution_two_iff {a b c m : ℕ} (ha : 1 ≤ a) :
    IsSolution b m [a, c] ↔ a < b ∧ c < b ∧ a * b = a ^ a + (w m c - c) := by
  have hc := le_w' m c
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨h1 a (by simp), h1 c (by simp), ?_⟩
    simp only [P_pair, Fs_pair, Nat.cast_id] at h3
    rw [w_of_ne_zero m (by omega)] at h3
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun d hd => ?_, fun _ => by simp; omega, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> assumption
    · simp only [P_pair, Fs_pair, Nat.cast_id]
      rw [w_of_ne_zero m (by omega)]
      omega

/-- **Proposition 2.6** (section 2.4), existence form. `(a, c)` with `a ≥ 1` is a solution in
some base exactly when `a ∣ w(c) - c` and `b = (a^a + w(c) - c) / a` exceeds `a` and `c`; the
base is then this `b`. -/
theorem exists_isSolution_two_iff {a c m : ℕ} (ha : 1 ≤ a) :
    (∃ b, IsSolution b m [a, c]) ↔
      a ∣ w m c - c ∧ a < (a ^ a + (w m c - c)) / a ∧ c < (a ^ a + (w m c - c)) / a := by
  have hdiv : a ∣ a ^ a := dvd_pow_self a (by omega)
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨h1, h2, h3⟩ := (isSolution_two_iff ha).1 hb
    have hb' : (a ^ a + (w m c - c)) / a = b := by
      rw [← h3, Nat.mul_div_cancel_left _ (by omega)]
    refine ⟨(Nat.dvd_add_right hdiv).1 ⟨b, h3.symm⟩, ?_, ?_⟩ <;> omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨_, (isSolution_two_iff ha).2 ⟨h2, h3, ?_⟩⟩
    exact Nat.mul_div_cancel' (dvd_add hdiv h1)

/-- The family `(1, c)` in base `c^c - c + 1`, `c ≥ 2`, under both conventions (section 2.4). -/
theorem isSolution_one_c {c m : ℕ} (hc : 2 ≤ c) : IsSolution (c ^ c - c + 1) m [1, c] := by
  have h1 : c ^ 2 ≤ c ^ c := Nat.pow_le_pow_right (by omega) hc
  have h2 : c * 2 ≤ c ^ 2 := by nlinarith
  rw [isSolution_two_iff le_rfl, w_of_ne_zero m (by omega)]
  refine ⟨by omega, by omega, by simp; omega⟩

/-- The family `(c, c)` in base `2 c^(c-1) - 1`, `c ≥ 2`, under both conventions
(section 2.4). -/
theorem isSolution_c_c {c m : ℕ} (hc : 2 ≤ c) : IsSolution (2 * c ^ (c - 1) - 1) m [c, c] := by
  have hcc : c ^ c = c * c ^ (c - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : c ≤ c ^ (c - 1) := by
    calc c = c ^ 1 := (pow_one c).symm
      _ ≤ c ^ (c - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [isSolution_two_iff (by omega), w_of_ne_zero m (by omega)]
  refine ⟨by omega, by omega, ?_⟩
  have e : 2 * c ^ (c - 1) - 1 + 1 = 2 * c ^ (c - 1) := by omega
  have h2 : c * (2 * c ^ (c - 1) - 1) + c = c * c ^ (c - 1) + c * c ^ (c - 1) := by
    rw [← mul_add_one, e]; ring
  have h3 : c ≤ c * c ^ (c - 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [hcc]
  omega

/-- The family `(a, 1)` in base `a^(a-1)`, `a ≥ 3`, under both conventions; the digit `a` is
self-paying (section 2.4). -/
theorem isSolution_a_one {a m : ℕ} (ha : 3 ≤ a) : IsSolution (a ^ (a - 1)) m [a, 1] := by
  have haa : a ^ a = a * a ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : a ^ 2 ≤ a ^ (a - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : a < a ^ 2 := by nlinarith
  rw [isSolution_two_iff (by omega)]
  refine ⟨by omega, by omega, by simp [haa]⟩

/-- The family `(a, 0)` in base `a^(a-1)`, `a ≥ 3`, under `0^0 = 0` (section 2.4). -/
theorem isSolution_a_zero {a : ℕ} (ha : 3 ≤ a) : IsSolution (a ^ (a - 1)) 0 [a, 0] := by
  have haa : a ^ a = a * a ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : a ^ 2 ≤ a ^ (a - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : a < a ^ 2 := by nlinarith
  rw [isSolution_two_iff (by omega)]
  refine ⟨by omega, by omega, by simp [haa]⟩

/-- Under `0^0 = 1`, `(1, 0)` is a solution in base 2 (section 2.4). -/
theorem isSolution_one_zero : IsSolution 2 1 [1, 0] := by
  rw [isSolution_two_iff le_rfl]; decide

/-- The family `(2, c)` in base `(c^c - c + 4) / 2`, `c ≥ 2`, under both conventions
(section 2.4): `2` divides `c^c - c`. -/
theorem isSolution_two_c {c m : ℕ} (hc : 2 ≤ c) : IsSolution ((c ^ c - c + 4) / 2) m [2, c] := by
  have h1 : c ^ 2 ≤ c ^ c := Nat.pow_le_pow_right (by omega) hc
  have h2 : c * 3 ≤ c ^ 2 + 3 := by nlinarith
  have hpar : (c ^ c - c) % 2 = 0 := by
    have := pow_self_modEq_two c (by omega)
    unfold Nat.ModEq at this; omega
  rw [isSolution_two_iff (by omega), w_of_ne_zero m (by omega)]
  refine ⟨by omega, by omega, by norm_num; omega⟩

/-! ### Solutions of every length under `0^0 = 0`: Proposition 2.7 -/

/-- The digit `r = t (k-1) + 1` is self-paying at position `k - 1` in base `r ^ t`
(proof of Proposition 2.7). -/
lemma selfPaying_prop27 {k t : ℕ} (hk : 2 ≤ k) (ht : 2 ≤ t) :
    SelfPaying ((t * (k - 1) + 1) ^ t) (t * (k - 1) + 1) (k - 1) := by
  set r := t * (k - 1) + 1 with hr
  have hr2 : 3 ≤ r := by
    have : 2 ≤ t * (k - 1) := by nlinarith [show 1 ≤ k - 1 by omega]
    omega
  refine ⟨by omega, by omega, ?_, ?_⟩
  · calc r = r ^ 1 := (pow_one r).symm
      _ < r ^ t := Nat.pow_lt_pow_right (by omega) (by omega)
  · rw [← pow_mul, ← pow_succ']

/-- **Proposition 2.7** (section 2.5). Under `0^0 = 0`, with `k ≥ 2`, `t ≥ 2` and
`r = t (k-1) + 1`, the strings `(r, 0, ..., 0)` and `(r, 0, ..., 0, 1)` of `k` digits are
solutions in base `r ^ t`. -/
theorem isSolution_prop27 {k t : ℕ} (hk : 2 ≤ k) (ht : 2 ≤ t) :
    IsSolution ((t * (k - 1) + 1) ^ t) 0 ((t * (k - 1) + 1) :: List.replicate (k - 1) 0) ∧
    IsSolution ((t * (k - 1) + 1) ^ t) 0
      ((t * (k - 1) + 1) :: (List.replicate (k - 2) 0 ++ [1])) := by
  have h := selfPaying_prop27 hk ht
  have hb : 2 ≤ (t * (k - 1) + 1) ^ t := by have := h.1; have := h.2.2.1; omega
  constructor
  · rw [isSolution_selfPaying_cons_iff (by simpa using h)]
    · simp [P_replicate_zero]
    · intro d hd; simp at hd; omega
  · rw [isSolution_selfPaying_cons_iff (by simpa [show k - 2 + 1 = k - 1 by omega] using h)]
    · simp [P_replicate_zero]
    · intro d hd; simp at hd; omega

/-- **Proposition 2.7** (section 2.5). Under `0^0 = 0`, every length `k ≥ 2` has infinitely
many bases with a `k`-digit solution. -/
theorem infinite_bases_of_length {k : ℕ} (hk : 2 ≤ k) :
    {b | ∃ s : List ℕ, s.length = k ∧ IsSolution b 0 s}.Infinite := by
  have hmono : StrictMono (fun t : ℕ => (t * (k - 1) + 1) ^ t) := by
    apply strictMono_nat_of_lt_succ
    intro t
    calc (t * (k - 1) + 1) ^ t ≤ ((t + 1) * (k - 1) + 1) ^ t :=
          Nat.pow_le_pow_left (by nlinarith) t
      _ < ((t + 1) * (k - 1) + 1) ^ (t + 1) :=
          Nat.pow_lt_pow_right (by nlinarith [show 1 ≤ k - 1 by omega]) (by omega)
  have hinj : Function.Injective (fun t : ℕ => ((t + 2) * (k - 1) + 1) ^ (t + 2)) :=
    fun x y hxy => by simpa using hmono.injective hxy
  refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
  refine ⟨_, ?_, (isSolution_prop27 hk (by omega : 2 ≤ t + 2)).1⟩
  simp; omega

/-! ### Splits and blocks: Lemmas 22.1, 22.3, 22.4 and 22.9 -/

/-- **Lemma 22.1** (section 22.1.1). For a split `s = (t, u)` with `u` of `m` digits, put
`R_m = b^m P_t(b) - F(t)`. Then `P_s(b) = F(s)` exactly when `R_m = F(u) - P_u(b)`; here the
equation is written in `ℤ`. -/
theorem split_iff (b m : ℕ) (t u : List ℕ) :
    P b (t ++ u) = Fs m (t ++ u) ↔
      (b : ℤ) ^ u.length * P (b : ℤ) t - Fs m t = Fs m u - P (b : ℤ) u := by
  rw [← Nat.cast_inj (R := ℤ), cast_P, P_append, Fs_append]
  push_cast
  constructor <;> intro h <;> linarith

/-- **Lemma 22.3** (section 22.2.1). Trailing zeros add nothing to the value and `m` each to
the weight sum, so `(t, 0, ..., 0)` with `k` zeros has `P = b^k P_t(b)` and
`F = F(t) + k w(0)`. In particular, under `0^0 = 0` a block `b^k P_t(b) = F(t)` is the same as
the solution `(t, 0, ..., 0)`, and under `0^0 = 1` it means `F - P = k`. -/
theorem P_Fs_append_zeros (b m k : ℕ) (t : List ℕ) :
    P b (t ++ List.replicate k 0) = b ^ k * P b t ∧
      Fs m (t ++ List.replicate k 0) = Fs m t + k * m := by
  constructor
  · rw [P_append, P_replicate_zero, List.length_replicate, add_zero]
  · simp

/-- **Lemma 22.4** (section 22.2.1). If `b^k P_t(b) = F(t)` (a self-paying block at shift `k`)
and the tail `u` of `k` digits pays for itself, `P_u(b) = F(u)`, then `P = F` holds for the
string `(t, u)`. -/
theorem block_append {b m : ℕ} {t u : List ℕ} (hblock : b ^ u.length * P b t = Fs m t)
    (hu : P b u = Fs m u) : P b (t ++ u) = Fs m (t ++ u) := by
  rw [P_append, Fs_append, hblock, hu]

/-- **Lemma 22.9** (section 22.4.2). Under `0^0 = 1`, the polynomial of `(t, 1)` is
`r P_t(r) - F(t)`, the polynomial of the block `(t, r, 1)`; the value at an integer `r` is
written here. Under `0^0 = 0` the same holds for `(t, 0)`. -/
theorem P_sub_Fs_append_one (r : ℤ) (t : List ℕ) :
    P r (t ++ [1]) - (Fs 1 (t ++ [1]) : ℤ) = r * P r t - Fs 1 t := by
  simp; ring

theorem P_sub_Fs_append_zero (r : ℤ) (t : List ℕ) :
    P r (t ++ [0]) - (Fs 0 (t ++ [0]) : ℤ) = r * P r t - Fs 0 t := by
  simp

/-! ### Binomial families: Theorem 22.6 and Corollary 22.7 -/

/-- The digits `t_i = c^(j-i) C(j,i) e^i`, `i = 0, ..., j-1`, of Theorem 22.6: the
coefficients of `(c r + e)^j` without the constant term, leading coefficient first. -/
def binomDigits (j c e : ℕ) : List ℕ :=
  (List.range j).map fun i => c ^ (j - i) * j.choose i * e ^ i

lemma mul_P_map_range {R : Type*} [CommSemiring R] (b : R) (f : ℕ → ℕ) (j : ℕ) :
    b * P b ((List.range j).map f) = ∑ i ∈ Finset.range j, (f i : R) * b ^ (j - i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, P_append_singleton,
      Finset.sum_range_succ, mul_add, mul_left_comm, ih, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]
      ring
    · simp [mul_comm]

/-- The binomial identity behind Theorem 22.6:
`b * P_t(b) + e^j = (c b + e)^j` for `t = binomDigits j c e`. -/
lemma mul_P_binomDigits {R : Type*} [CommSemiring R] (b : R) (j c e : ℕ) :
    b * P b (binomDigits j c e) + (e : R) ^ j = ((c : R) * b + e) ^ j := by
  rw [binomDigits, mul_P_map_range, add_comm ((c : R) * b), add_pow, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

lemma binomDigits_pos {j c e t : ℕ} (hc : 1 ≤ c) (he : 1 ≤ e) (ht : t ∈ binomDigits j c e) :
    1 ≤ t := by
  simp only [binomDigits, List.mem_map, List.mem_range] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  have h1 := Nat.choose_pos (n := j) (k := i) hi.le
  have h2 : 1 ≤ c ^ (j - i) := Nat.one_le_pow _ _ hc
  have h3 : 1 ≤ e ^ i := Nat.one_le_pow _ _ he
  have : 1 ≤ c ^ (j - i) * j.choose i := Nat.one_le_iff_ne_zero.2 (by positivity)
  nlinarith

/-- A string of positive digits weighs the same under both conventions. -/
lemma Fs_of_pos {m : ℕ} {s : List ℕ} (hs : ∀ d ∈ s, 1 ≤ d) :
    Fs m s = (s.map fun t => t ^ t).sum := by
  induction s with
  | nil => simp
  | cons d s ih =>
    simp only [Fs_cons, List.map_cons, List.sum_cons]
    rw [w_of_ne_zero m (by have := hs d (by simp); omega), ih (fun x hx => hs x (by simp [hx]))]

lemma binomDigits_ne_nil {j c e : ℕ} (hj : 1 ≤ j) : binomDigits j c e ≠ [] := by
  simp [binomDigits]; omega

lemma binomDigits_head {j c e : ℕ} (hj : 1 ≤ j) :
    (binomDigits j c e).head (binomDigits_ne_nil hj) = c ^ j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp [binomDigits, List.range_succ_eq_map]

/-- **Theorem 22.6** (section 22.3.1). Let `j ≥ 2`, `c, e ≥ 1`,
`t_i = c^(j-i) C(j,i) e^i` for `i < j`, and `x = e^j + sum t_i^(t_i)`. Suppose that
`x^x = y^j`, that `c b + e = y`, and that `b` exceeds `x` and every `t_i`. Then
`(t_0, ..., t_(j-1), x)` is a `(j+1)`-digit solution in base `b` under both conventions. -/
theorem isSolution_binomial {j c e x y b : ℕ} (m : ℕ) (hj : 2 ≤ j) (hc : 1 ≤ c) (he : 1 ≤ e)
    (hx : x = e ^ j + ((binomDigits j c e).map fun t => t ^ t).sum) (hxy : x ^ x = y ^ j)
    (hy : c * b + e = y) (hxb : x < b) (htb : ∀ t ∈ binomDigits j c e, t < b) :
    IsSolution b m (binomDigits j c e ++ [x]) := by
  have hpos := fun t (ht : t ∈ binomDigits j c e) => binomDigits_pos hc he ht
  have hej : 1 ≤ e ^ j := Nat.one_le_pow _ _ he
  have hx1 : 1 ≤ x := by omega
  refine ⟨fun d hd => ?_, fun hne => ?_, ?_⟩
  · rcases List.mem_append.1 hd with hd | hd
    · exact htb d hd
    · simp at hd; omega
  · rw [List.head_append_of_ne_nil (binomDigits_ne_nil (by omega)), binomDigits_head (by omega)]
    have := Nat.one_le_pow j c hc
    omega
  · have key := mul_P_binomDigits b j c e
    push_cast at key
    rw [hy, ← hxy] at key
    rw [P_append_singleton, Fs_append, Fs_singleton, Fs_of_pos hpos, w_of_ne_zero m (by omega)]
    simp only [Nat.cast_id]
    omega

/-- The second digit of `binomDigits j c e` is `c^(j-1) j e`. -/
lemma binomDigits_getElem_one {j c e : ℕ} (hj : 2 ≤ j) :
    (binomDigits j c e)[1]? = some (c ^ (j - 1) * j * e) := by
  simp [binomDigits, List.getElem?_map, List.getElem?_range (show 1 < j by omega)]

/-- The members of Corollary 22.7: `j = k - 1`, `c = j`, `e = j u`. -/
def corDigits (j u : ℕ) : List ℕ := binomDigits j j (j * u)

/-- The large last digit `x = e^j + sum t_i^(t_i)` of Corollary 22.7. -/
def corX (j u : ℕ) : ℕ := (j * u) ^ j + ((corDigits j u).map fun t => t ^ t).sum

lemma dvd_corDigits {j u t : ℕ} (ht : t ∈ corDigits j u) : j ∣ t := by
  simp only [corDigits, binomDigits, List.mem_map, List.mem_range] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self j (by omega)) _) _

lemma dvd_corX {j u : ℕ} (hj : 1 ≤ j) (hu : 1 ≤ u) : j ∣ corX j u := by
  unfold corX
  apply dvd_add (Dvd.dvd.pow (dvd_mul_right j u) (by omega))
  apply List.dvd_sum
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨t, ht, rfl⟩ := ha
  have h1 := binomDigits_pos (j := j) (c := j) (e := j * u) hj (Nat.one_le_iff_ne_zero.2
    (by positivity)) ht
  exact Dvd.dvd.pow (dvd_corDigits ht) (by omega)

lemma le_corX {j u t : ℕ} (ht : t ∈ corDigits j u) : t ^ t ≤ corX j u := by
  unfold corX
  have : t ^ t ≤ ((corDigits j u).map fun t => t ^ t).sum :=
    List.le_sum_of_mem (List.mem_map.2 ⟨t, ht, rfl⟩)
  omega

/-- **Corollary 22.7** (section 22.3.1), one member for each `u ≥ 1`. -/
theorem isSolution_corollary_22_7 {j u : ℕ} (m : ℕ) (hj : 2 ≤ j) (hu : 1 ≤ u) :
    IsSolution ((corX j u) ^ (corX j u / j) / j - u) m (corDigits j u ++ [corX j u]) := by
  set x := corX j u with hxdef
  set e := j * u with he
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hjx : j ∣ x := dvd_corX (by omega) hu
  -- the leading digit `t_0 = j^j` gives `x ≥ (j^j)^(j^j) ≥ 2 j`
  have ht0 : j ^ j ∈ corDigits j u := by
    have := List.head_mem (binomDigits_ne_nil (j := j) (c := j) (e := j * u) (by omega))
    rwa [binomDigits_head (by omega)] at this
  have hjj : 2 * j ≤ j ^ j := by
    calc 2 * j ≤ j * j := Nat.mul_le_mul_right _ hj
      _ = j ^ 2 := (sq j).symm
      _ ≤ j ^ j := Nat.pow_le_pow_right (by omega) hj
  have hx2j : 2 * j ≤ x := by
    have h1 : j ^ j ≤ (j ^ j) ^ (j ^ j) := Nat.le_self_pow (by omega) _
    have := le_corX ht0
    omega
  have hxe : e < x := by
    have h1 : e ≤ e ^ j := Nat.le_self_pow (by omega) e
    have h2 : 1 ≤ (j ^ j) ^ (j ^ j) := Nat.one_le_pow _ _ (by positivity)
    have := le_corX ht0
    have h3 : (j ^ j) ^ (j ^ j) ≤ ((corDigits j u).map fun t => t ^ t).sum :=
      List.le_sum_of_mem (List.mem_map.2 ⟨_, ht0, rfl⟩)
    change e < e ^ j + _
    omega
  set y := x ^ (x / j) with hydef
  have hxy : x ^ x = y ^ j := by
    rw [hydef, ← pow_mul, Nat.div_mul_cancel hjx]
  have hxj2 : 2 ≤ x / j := (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)
  have hyx : x * x ≤ y := by
    calc x * x = x ^ 2 := (sq x).symm
      _ ≤ x ^ (x / j) := Nat.pow_le_pow_right (by omega) hxj2
  have hjy : j ∣ y := (hjx.trans (dvd_pow_self x (by omega)))
  obtain ⟨Y, hY⟩ := hjy
  have hYu : u ≤ Y := by
    have : e ≤ y := by nlinarith
    rw [hY, he] at this
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hb : y / j - u = Y - u := by rw [hY, Nat.mul_div_cancel_left _ (by omega)]
  rw [hb]
  have hcy : j * (Y - u) + e = y := by
    rw [hY, he, Nat.mul_sub]
    have : j * u ≤ j * Y := Nat.mul_le_mul_left _ hYu
    omega
  have hxb : x < Y - u := by
    by_contra hcon
    have h1 : j * (Y - u) ≤ j * x := Nat.mul_le_mul_left _ (by omega)
    have h2 : x * (j + 1) ≤ x * x := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  refine isSolution_binomial m hj (by omega) he1 rfl hxy hcy hxb fun t ht => ?_
  have h0 := binomDigits_pos (j := j) (c := j) (e := j * u) (by omega) he1 ht
  have h1 : t ≤ t ^ t := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ t := Nat.pow_le_pow_right h0 h0
  have := le_corX ht
  omega

lemma length_binomDigits (j c e : ℕ) : (binomDigits j c e).length = j := by simp [binomDigits]

/-- **Corollary 22.7** (section 22.3.1). For every `k ≥ 3` there are infinitely many `k`-digit
Munchausen strings, under `0^0 = 1` and under `0^0 = 0`. This refutes the finiteness
conjecture of sections 3.5 and 7.2. -/
theorem infinite_solutions_of_length (m : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    {s : List ℕ | s.length = k ∧ ∃ b, IsSolution b m s}.Infinite := by
  set j := k - 1 with hjdef
  have hj : 2 ≤ j := by omega
  let f : ℕ → List ℕ := fun u => corDigits j (u + 1) ++ [corX j (u + 1)]
  have hf : Function.Injective f := by
    intro u v huv
    have h1 : (f u)[1]? = (f v)[1]? := by rw [huv]
    simp only [f, corDigits] at h1
    rw [List.getElem?_append_left (by rw [length_binomDigits]; omega),
      List.getElem?_append_left (by rw [length_binomDigits]; omega),
      binomDigits_getElem_one hj, binomDigits_getElem_one hj] at h1
    simp only [Option.some.injEq] at h1
    have hpos : 0 < j ^ (j - 1) * j * j := by positivity
    have : j ^ (j - 1) * j * j * (u + 1) = j ^ (j - 1) * j * j * (v + 1) := by
      simpa only [mul_assoc] using h1
    have := Nat.eq_of_mul_eq_mul_left hpos this
    omega
  refine Set.infinite_of_injective_forall_mem hf fun u => ⟨?_, _,
    isSolution_corollary_22_7 m hj (by omega : 1 ≤ u + 1)⟩
  simp [f, corDigits, length_binomDigits]
  omega

end Munchausen
