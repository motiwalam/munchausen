import Munchausen.Congruences

/-!
# Constructions (chapter 2)

* twins under `0^0 = 0`, Proposition 2.1;
* the balance of a placement, and self-paying digits: Propositions 2.2 (sufficiency), 2.3
  and 2.5;
* swaps, section 2.3;
* the complete description of 2-digit solutions, Proposition 2.6, and its four families;
* solutions of every length under `0^0 = 0`, Proposition 2.7;
* Corollary 2.4, Proposition 4.2 and Theorem 9.2 (many solutions in one base);
* Theorem 15.9 (a swap with a self-paying digit on top) and Theorem 25.5 (the identity
  family `(c^j, 0, ..., 0, x)` under `0^0 = 1`);
* the converse of Proposition 2.2, Proposition 8.5 and its corollary in section 8.3;
* splits and blocks (Lemmas 22.1, 22.3, 22.4, 22.9), Theorem 22.6 and Corollary 22.7.
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

/-! ### Self-paying digits: the converse of Proposition 2.2 and Proposition 8.5 -/

/-- **Proposition 2.2**, converse (section 2.2). A self-paying digit and its base are powers of
one integer `c ≥ 2`: `a = c^s`, `b = c^t` with `1 ≤ s < t` and `t k = s (c^s - 1)`. -/
theorem SelfPaying.exists_pow {b a k : ℕ} (h : SelfPaying b a k) :
    ∃ c s t, 2 ≤ c ∧ 1 ≤ s ∧ s < t ∧ a = c ^ s ∧ b = c ^ t ∧ t * k = s * (c ^ s - 1) := by
  obtain ⟨ha, hk, hab, heq⟩ := h
  have hpow : a ^ (a - 1) = b ^ k := by
    have haa : a ^ a = a * a ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
    rw [haa] at heq
    exact (Nat.eq_of_mul_eq_mul_left (by omega) heq).symm
  obtain ⟨c, hac, hbc⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl (by omega : a - 1 ≠ 0)) hpow
  set g := Nat.gcd (a - 1) k with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hs : 1 ≤ k / g := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hg0
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c
      · rw [zero_pow (by omega)] at hac; omega
      · rw [one_pow] at hac; omega
    · exact hc
  refine ⟨c, k / g, (a - 1) / g, hc2, hs, ?_, hac, hbc, ?_⟩
  · have : c ^ (k / g) < c ^ ((a - 1) / g) := by rw [← hac, ← hbc]; exact hab
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 this
  · rw [← hac]
    have h1 : g ∣ a - 1 := Nat.gcd_dvd_left _ _
    have h2 : g ∣ k := Nat.gcd_dvd_right _ _
    obtain ⟨A', hA'⟩ := h1
    obtain ⟨K', hK'⟩ := h2
    rw [hA', hK', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0]
    ring

/-- Every `b ≥ 2` has a root `r` such that every `c ≥ 2` with a power equal to `b` is a power
of `r` (the `r` of Proposition 2.2, not a perfect power). -/
theorem exists_primitive_root {b : ℕ} (hb : 2 ≤ b) :
    ∃ r t, 2 ≤ r ∧ 1 ≤ t ∧ r ^ t = b ∧
      ∀ c j, 2 ≤ c → 1 ≤ j → c ^ j = b → ∃ i, c = r ^ i := by
  classical
  have hex : ∃ r, 2 ≤ r ∧ ∃ t, 1 ≤ t ∧ r ^ t = b := ⟨b, hb, 1, le_rfl, pow_one b⟩
  set r := Nat.find hex with hr
  obtain ⟨hr2, t, ht, hrt⟩ := Nat.find_spec hex
  refine ⟨r, t, hr2, ht, hrt, fun c j hc hj hcj => ?_⟩
  have h : c ^ j = r ^ t := hcj.trans hrt.symm
  obtain ⟨e, hce, hre⟩ := Nat.exists_eq_pow_of_pow_eq_pow (Or.inl (by omega : j ≠ 0)) h
  set g := Nat.gcd j t
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hjg : 1 ≤ j / g := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hg0
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with he | he
    · interval_cases e
      · rw [zero_pow (by omega)] at hre; omega
      · rw [one_pow] at hre; omega
    · exact he
  -- `e` is a root of `b`, so `r ≤ e` by minimality; and `r = e ^ (j/g) ≥ e`
  have hroot : 2 ≤ e ∧ ∃ t', 1 ≤ t' ∧ e ^ t' = b :=
    ⟨he2, (j / g) * t, Nat.mul_pos hjg ht, by rw [pow_mul, ← hre, hrt]⟩
  have hle : r ≤ e := Nat.find_min' hex hroot
  have hre' : r = e := by
    have : e ^ 1 ≤ e ^ (j / g) := Nat.pow_le_pow_right (by omega) hjg
    rw [pow_one, ← hre] at this
    omega
  exact ⟨t / g, by rw [hce, hre']⟩

/-- **Proposition 8.5**, arithmetic core (section 8.3). For `r ≥ 2` and `1 ≤ s < u`,
`u (r^u - 1) > r s (r^s - 1)`. -/
lemma prop8_5_ineq {r s u : ℕ} (hr : 2 ≤ r) (hs : 1 ≤ s) (hsu : s < u) :
    r * (s * (r ^ s - 1)) < u * (r ^ u - 1) := by
  have h1 : r ^ (s + 1) ≤ r ^ u := Nat.pow_le_pow_right (by omega) hsu
  have h2 : s + 1 < r ^ (s + 1) := Nat.lt_pow_self (by omega)
  have h3 : 1 ≤ r ^ s := Nat.one_le_pow _ _ (by omega)
  have e : r ^ (s + 1) = r * r ^ s := by ring
  zify [h3, (show 1 ≤ r ^ u from Nat.one_le_pow _ _ (by omega))]
  have h1' : (r : ℤ) ^ (s + 1) ≤ (r : ℤ) ^ u := by exact_mod_cast h1
  have h2' : (s : ℤ) + 1 < (r : ℤ) ^ (s + 1) := by exact_mod_cast h2
  have e' : (r : ℤ) ^ (s + 1) = r * (r : ℤ) ^ s := by ring
  have hu : (s : ℤ) + 1 ≤ u := by exact_mod_cast hsu
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith

/-- **Proposition 8.5** (section 8.3). If `a < a'` are self-paying in base `b` at positions `k`
and `k'`, then `k' ≥ 2 k + 1`. So no two self-paying digits sit at adjacent positions. -/
theorem SelfPaying.position_gt {b a a' k k' : ℕ} (h : SelfPaying b a k) (h' : SelfPaying b a' k')
    (haa : a < a') : 2 * k + 1 ≤ k' := by
  have hb : 2 ≤ b := by have := h.1; have := h.2.2.1; omega
  obtain ⟨r, T, hr, hT, hrT, hroot⟩ := exists_primitive_root hb
  obtain ⟨c, s, t, hc, hs, hst, rfl, hbc, htk⟩ := h.exists_pow
  obtain ⟨c', s', t', hc', hs', hst', rfl, hbc', htk'⟩ := h'.exists_pow
  obtain ⟨i, rfl⟩ := hroot c t hc (by omega) hbc.symm
  obtain ⟨i', rfl⟩ := hroot c' t' hc' (by omega) hbc'.symm
  have hi : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h; · simp at hc
    exact h
  have hi' : 1 ≤ i' := by
    rcases Nat.eq_zero_or_pos i' with rfl | h; · simp at hc'
    exact h
  simp only [← pow_mul] at hbc hbc' htk htk' haa
  -- the exponents of `b`
  have hinj := Nat.pow_right_injective hr
  have hτ : i * t = i' * t' := hinj (hbc.symm.trans hbc')
  have hσ : i * s < i' * s' := (Nat.pow_lt_pow_iff_right (by omega)).1 haa
  have e1 : (i * t) * k = (i * s) * (r ^ (i * s) - 1) := by rw [mul_assoc, htk]; ring
  have e2 : (i * t) * k' = (i' * s') * (r ^ (i' * s') - 1) := by rw [hτ, mul_assoc, htk']; ring
  have hineq := prop8_5_ineq hr (Nat.mul_pos hi hs) hσ
  rw [← e1, ← e2] at hineq
  have hτ0 : 0 < i * t := Nat.mul_pos hi (by omega)
  have : r * k < k' := by
    have : (i * t) * (r * k) < (i * t) * k' := by linarith [hineq]
    exact Nat.lt_of_mul_lt_mul_left this
  nlinarith

/-- Under `0^0 = 1`, a placement of `d` at position `e ≥ 1` has zero balance only when `d` is
self-paying there. -/
lemma selfPaying_of_balance {b d e : ℕ} (hb : 2 ≤ b) (hdb : d < b) (he : 1 ≤ e)
    (h : d * b ^ e = w 1 d) : SelfPaying b d e := by
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · simp at h
    · simp only [w_one, one_mul] at h
      have : b ^ 1 ≤ b ^ e := Nat.pow_le_pow_right (by omega) he
      simp at this; omega
  · exact ⟨hd, he, hdb, by rwa [w_of_ne_zero 1 (by omega)] at h⟩

/-- **Section 8.3**, corollary of Proposition 8.5. Under `0^0 = 1`, a solution made only of
zero-balance placements is `(1)` or `(a, 1)` with `a` self-paying at position 1, that is in
base `a^(a-1)`. -/
theorem zero_balance_solution {b : ℕ} {s : List ℕ} (hb : 2 ≤ b) (hs : IsSolution b 1 s)
    (hbal : ∀ i (hi : i < s.length), s[i] * b ^ (s.length - 1 - i) = w 1 s[i]) :
    s = [] ∨ s = [1] ∨ ∃ a, s = [a, 1] ∧ SelfPaying b a 1 := by
  -- the last digit is 1
  have hlast : ∀ (hne : 0 < s.length), s[s.length - 1] = 1 := by
    intro hne
    have h := hbal (s.length - 1) (by omega)
    rw [show s.length - 1 - (s.length - 1) = 0 by omega, pow_zero, mul_one] at h
    set d := s[s.length - 1]
    rcases Nat.lt_or_ge d 2 with hd | hd
    · interval_cases d
      · simp at h
      · rfl
    · rw [w_of_ne_zero 1 (by omega)] at h
      have : d ^ 1 < d ^ d := Nat.pow_lt_pow_right (by omega) (by omega)
      simp at this; omega
  have hsp : ∀ i (hi : i + 1 < s.length), SelfPaying b s[i] (s.length - 1 - i) := fun i hi =>
    selfPaying_of_balance hb (hs.lt_base _ (List.getElem_mem _)) (by omega) (hbal i (by omega))
  match s, hs, hlast, hsp with
  | [], _, _, _ => exact Or.inl rfl
  | [d], _, hl, _ => right; left; simpa using hl (by simp)
  | [a, d], _, hl, hsp' =>
    right; right
    refine ⟨a, ?_, by simpa using hsp' 0 (by simp)⟩
    simpa using hl (by simp)
  | d₁ :: d₂ :: d₃ :: t, _, _, hsp' =>
    exfalso
    -- the digits at positions 2 and 1 would be adjacent self-paying digits
    have hx := hsp' t.length (by simp)
    have hy := hsp' (t.length + 1) (by simp)
    simp only [List.length_cons] at hx hy
    rw [show t.length + 1 + 1 + 1 - 1 - t.length = 2 by omega] at hx
    rw [show t.length + 1 + 1 + 1 - 1 - (t.length + 1) = 1 by omega] at hy
    generalize (d₁ :: d₂ :: d₃ :: t)[t.length] = x at hx
    generalize (d₁ :: d₂ :: d₃ :: t)[t.length + 1] = y at hy
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have := hx.position_gt hy hxy; omega
    · have h2 := hx.2.2.2
      have h1 := hy.2.2.2
      rw [← h1] at h2
      have hx2 := hx.1
      have : b ^ 2 = b ^ 1 := Nat.eq_of_mul_eq_mul_left (by omega) h2
      have := Nat.pow_right_injective hb this
      omega
    · have := hy.position_gt hx hxy; omega

/-! ### Many solutions in one base: Corollary 2.4, Proposition 4.2, Theorem 9.2 -/

/-- Under `0^0 = 0`, leading zeros do not change the weight sum: `F(ofDigits l) = F(l)` for a
little-endian list `l` of digits below `b`, even if it ends in zeros. -/
lemma F_ofDigits_zero {b : ℕ} (hb : 1 < b) (l : List ℕ) (hl : ∀ d ∈ l, d < b) :
    F b 0 (Nat.ofDigits b l) = Fs 0 l := by
  induction l with
  | nil => simp [F, Nat.ofDigits]
  | cons d t ih =>
    have ih' := ih (fun x hx => hl x (by simp [hx]))
    rw [Nat.ofDigits_cons]
    by_cases h : d = 0 ∧ Nat.ofDigits b t = 0
    · obtain ⟨rfl, h2⟩ := h
      rw [h2] at ih' ⊢
      simp only [mul_zero, add_zero, Fs_cons, w_zero, zero_add]
      exact ih'
    · have hor : d ≠ 0 ∨ Nat.ofDigits b t ≠ 0 := by tauto
      rw [F, Nat.digits_add b hb d _ (hl d (by simp)) hor, Fs_cons, Fs_cons, ← F, ih']

/-- `ofDigits` of the digits `f 0, ..., f (L-1)` is `sum f i * b^i`. -/
lemma ofDigits_map_range (b : ℕ) (f : ℕ → ℕ) (L : ℕ) :
    Nat.ofDigits b ((List.range L).map f) = ∑ i ∈ Finset.range L, f i * b ^ i := by
  induction L with
  | zero => simp [Nat.ofDigits]
  | succ L ih =>
    rw [List.range_succ, List.map_append, ofDigits_append', ih, Finset.sum_range_succ]
    simp
    ring

lemma Fs_map_range (m : ℕ) (f : ℕ → ℕ) (L : ℕ) :
    Fs m ((List.range L).map f) = ∑ i ∈ Finset.range L, w m (f i) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, Fs_append, ih, Finset.sum_range_succ]
    simp

section Combine

variable {ι : Type*} [DecidableEq ι]

/-- The digit at position `k` of the number built from the self-paying digits `d i` at the
positions `pos i`, `i ∈ S`. -/
def spDigit (S : Finset ι) (d pos : ι → ℕ) (k : ℕ) : ℕ := ∑ i ∈ S with pos i = k, d i

/-- The number `sum_{i ∈ S} d i * b^(pos i)` (proof of Corollary 2.4). -/
def spNum (b : ℕ) (S : Finset ι) (d pos : ι → ℕ) : ℕ := ∑ i ∈ S, d i * b ^ pos i

lemma spDigit_fiber {S : Finset ι} {pos : ι → ℕ} (hinj : Set.InjOn pos S) (k : ℕ) :
    (S.filter fun i => pos i = k) = ∅ ∨
      ∃ i ∈ S, pos i = k ∧ (S.filter fun i => pos i = k) = {i} := by
  by_cases h : (S.filter fun i => pos i = k) = ∅
  · exact Or.inl h
  · right
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
    rw [Finset.mem_filter] at hi
    refine ⟨i, hi.1, hi.2, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hjk⟩; exact hinj hj hi.1 (hjk.trans hi.2.symm)
    · rintro rfl; exact hi

lemma w_spDigit {S : Finset ι} {d pos : ι → ℕ} (hinj : Set.InjOn pos S) (k : ℕ) :
    w 0 (spDigit S d pos k) = ∑ i ∈ S with pos i = k, w 0 (d i) := by
  unfold spDigit
  rcases spDigit_fiber hinj k with h | ⟨i, -, -, h⟩ <;> rw [h] <;> simp

variable {b : ℕ} {I : Finset ι} {d pos : ι → ℕ}

omit [DecidableEq ι] in
lemma spNum_eq_ofDigits {S : Finset ι} (hS : S ⊆ I) :
    spNum b S d pos = Nat.ofDigits b ((List.range (I.sup pos + 1)).map (spDigit S d pos)) := by
  have hmaps : ∀ i ∈ S, pos i ∈ Finset.range (I.sup pos + 1) := fun i hi =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (hS hi)))
  rw [ofDigits_map_range, spNum]
  simp only [spDigit, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.1 hi).2]

lemma spDigit_lt (hb : 2 ≤ b) (hinj : Set.InjOn pos I)
    (hsp : ∀ i ∈ I, SelfPaying b (d i) (pos i)) {S : Finset ι} (hS : S ⊆ I) (k : ℕ) :
    spDigit S d pos k < b := by
  have hinjS : Set.InjOn pos S := hinj.mono (by simpa using hS)
  unfold spDigit
  rcases spDigit_fiber hinjS k with h | ⟨i, hi, -, h⟩ <;> rw [h]
  · simp; omega
  · simpa using (hsp i (hS hi)).2.2.1

/-- **Corollary 2.4**, construction (section 2.2). Under `0^0 = 0`, self-paying digits at
distinct positions, all placed on zeros, form a solution. -/
theorem isMunchausen_spNum (hb : 2 ≤ b) (hinj : Set.InjOn pos I)
    (hsp : ∀ i ∈ I, SelfPaying b (d i) (pos i)) {S : Finset ι} (hS : S ⊆ I) :
    IsMunchausen b 0 (spNum b S d pos) := by
  have hmaps : ∀ i ∈ S, pos i ∈ Finset.range (I.sup pos + 1) := fun i hi =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (hS hi)))
  have hinjS : Set.InjOn pos S := hinj.mono (by simpa using hS)
  have hlt : ∀ x ∈ (List.range (I.sup pos + 1)).map (spDigit S d pos), x < b := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact spDigit_lt hb hinj hsp hS k
  unfold IsMunchausen
  rw [spNum_eq_ofDigits hS, F_ofDigits_zero (by omega) _ hlt, Fs_map_range]
  simp only [w_spDigit hinjS]
  rw [Finset.sum_fiberwise_of_maps_to hmaps (fun i => w 0 (d i)), ← spNum_eq_ofDigits hS, spNum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ((hsp i (hS hi)).balance).symm

omit [DecidableEq ι] in
lemma spNum_mod (hsp : ∀ i ∈ I, SelfPaying b (d i) (pos i)) {S : Finset ι} (hS : S ⊆ I) :
    spNum b S d pos % b = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  apply Finset.dvd_sum
  intro i hi
  exact Dvd.dvd.mul_left (dvd_pow_self b (by have := (hsp i (hS hi)).2.1; omega)) _

omit [DecidableEq ι] in
lemma two_le_spNum (hsp : ∀ i ∈ I, SelfPaying b (d i) (pos i)) {S : Finset ι} (hS : S ⊆ I)
    (hne : S.Nonempty) : 2 ≤ spNum b S d pos := by
  obtain ⟨i, hi⟩ := hne
  have h1 := (hsp i (hS hi)).1
  have hb : 1 ≤ b ^ pos i := Nat.one_le_pow _ _ (by have := (hsp i (hS hi)).2.2.1; omega)
  calc 2 ≤ d i * b ^ pos i := by nlinarith
    _ ≤ spNum b S d pos := Finset.single_le_sum (f := fun i => d i * b ^ pos i)
        (fun _ _ => Nat.zero_le _) hi

lemma spNum_injOn (hb : 2 ≤ b) (hinj : Set.InjOn pos I)
    (hsp : ∀ i ∈ I, SelfPaying b (d i) (pos i)) {S T : Finset ι} (hS : S ⊆ I) (hT : T ⊆ I)
    (h : spNum b S d pos = spNum b T d pos) : S = T := by
  rw [spNum_eq_ofDigits hS, spNum_eq_ofDigits hT] at h
  have hl := Nat.ofDigits_inj_of_len_eq (by omega) (by simp)
    (fun x hx => by obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx; exact spDigit_lt hb hinj hsp hS k)
    (fun x hx => by obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx; exact spDigit_lt hb hinj hsp hT k) h
  have hdig : ∀ k < I.sup pos + 1, spDigit S d pos k = spDigit T d pos k := by
    intro k hk
    have := congrArg (fun l => l[k]?) hl
    simpa [List.getElem?_map, List.getElem?_range hk] using this
  -- `i ∈ S` iff the digit at `pos i` is nonzero
  have key : ∀ (U : Finset ι), U ⊆ I → ∀ i ∈ I, (i ∈ U ↔ spDigit U d pos (pos i) ≠ 0) := by
    intro U hU i hi
    have hinjU : Set.InjOn pos U := hinj.mono (by simpa using hU)
    unfold spDigit
    constructor
    · intro hiU
      rcases spDigit_fiber hinjU (pos i) with h | ⟨j, hj, -, h⟩
      · exfalso
        have : i ∈ U.filter (fun j => pos j = pos i) := Finset.mem_filter.2 ⟨hiU, rfl⟩
        rw [h] at this; simp at this
      · rw [h]; simp; have := (hsp j (hU hj)).1; omega
    · intro hne
      by_contra hiU
      apply hne
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_filter] at hj
      exact absurd (hinj (hU hj.1) hi hj.2 ▸ hj.1) hiU
  ext i
  constructor
  · intro hi
    have hiI := hS hi
    rw [key T hT i hiI, ← hdig _ (Nat.lt_succ_of_le (Finset.le_sup hiI))]
    exact (key S hS i hiI).1 hi
  · intro hi
    have hiI := hT hi
    rw [key S hS i hiI, hdig _ (Nat.lt_succ_of_le (Finset.le_sup hiI))]
    exact (key T hT i hiI).1 hi

/-- **Corollary 2.4** (section 2.2). Under `0^0 = 0`, a base with `C` self-paying digits at
distinct positions has at least `2^(C+1) - 2` nontrivial solutions: every nonempty set of
them, with or without a final 1. -/
theorem corollary_2_4 (hb : 2 ≤ b) (hinj : Set.InjOn pos I)
    (hsp : ∀ i ∈ I, SelfPaying b (d i) (pos i)) :
    ∃ T : Finset ℕ, T.card = 2 ^ (I.card + 1) - 2 ∧ ∀ n ∈ T, 2 ≤ n ∧ IsMunchausen b 0 n := by
  let f : Finset ι × ℕ → ℕ := fun p => spNum b p.1 d pos + p.2
  refine ⟨((I.powerset.erase ∅) ×ˢ Finset.range 2).image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_erase_of_mem
      (Finset.empty_mem_powerset I), Finset.card_powerset, Finset.card_range]
    · have : 1 ≤ 2 ^ I.card := Nat.one_le_two_pow
      rw [pow_succ]; omega
    · rintro ⟨S, e⟩ hSe ⟨T, e'⟩ hTe' hST
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_erase,
        Finset.mem_powerset, Finset.mem_range] at hSe hTe'
      simp only [f] at hST
      have hmS := spNum_mod hsp hSe.1.2
      have hmT := spNum_mod hsp hTe'.1.2
      have hee : e = e' := by
        have := congrArg (· % b) hST
        simp only [Nat.add_mod, hmS, hmT, zero_add, Nat.mod_mod] at this
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      subst hee
      have := spNum_injOn hb hinj hsp hSe.1.2 hTe'.1.2 (by omega)
      rw [this]
  · intro n hn
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_erase, Finset.mem_powerset,
      Finset.mem_range, Prod.exists] at hn
    obtain ⟨S, e, ⟨⟨hSne, hSI⟩, he⟩, rfl⟩ := hn
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hSne
    have h2 := two_le_spNum hsp hSI hne
    have hm := isMunchausen_spNum hb hinj hsp hSI
    refine ⟨by simp only [f]; omega, ?_⟩
    interval_cases e
    · simpa [f] using hm
    · exact (isMunchausen_twin hb (by omega) (spNum_mod hsp hSI)).1 hm

end Combine

/-- A strictly increasing position function on `ℕ`, from `t * pos s = s (r^s - 1)`. -/
lemma pos_strictMono {r t : ℕ} (hr : 2 ≤ r) (_ht : 1 ≤ t) {pos : ℕ → ℕ}
    (hpos : ∀ s, t * pos s = s * (r ^ s - 1)) {s s' : ℕ} (hs : 1 ≤ s) (hss : s < s') :
    pos s < pos s' := by
  have h1 : r ^ s < r ^ s' := Nat.pow_lt_pow_right (by omega) hss
  have h2 : 1 ≤ r ^ s := Nat.one_le_pow _ _ (by omega)
  have h3 : s * (r ^ s - 1) < s' * (r ^ s' - 1) :=
    Nat.mul_lt_mul_of_le_of_lt hss.le (by omega) (by omega)
  rw [← hpos, ← hpos] at h3
  exact Nat.lt_of_mul_lt_mul_left h3

/-- **Theorem 9.2** (section 9.8). For every `n ≥ 3`, base `n^(n-1)` has at least
`2^(n-1) - 2` nontrivial solutions under `0^0 = 0`. -/
theorem theorem9_2 {n : ℕ} (hn : 3 ≤ n) :
    ∃ T : Finset ℕ, T.card = 2 ^ (n - 1) - 2 ∧
      ∀ x ∈ T, 2 ≤ x ∧ IsMunchausen (n ^ (n - 1)) 0 x := by
  have hdvd : ∀ s, (n - 1) ∣ s * (n ^ s - 1) := fun s =>
    Dvd.dvd.mul_left (by simpa using Nat.sub_dvd_pow_sub_pow n 1 s) s
  let pos : ℕ → ℕ := fun s => s * (n ^ s - 1) / (n - 1)
  have hpos : ∀ s, (n - 1) * pos s = s * (n ^ s - 1) := fun s => Nat.mul_div_cancel' (hdvd s)
  have hb : 2 ≤ n ^ (n - 1) :=
    le_trans (by omega) (Nat.le_self_pow (by omega) n)
  have hinj : Set.InjOn pos (Finset.Icc 1 (n - 2)) := by
    intro s hs s' hs' h
    simp only [Finset.coe_Icc, Set.mem_Icc] at hs hs'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd h (pos_strictMono (by omega) (by omega) hpos hs.1 hlt).ne
    · exact absurd h (pos_strictMono (by omega) (by omega) hpos hs'.1 hlt).ne'
  have hsp : ∀ s ∈ Finset.Icc 1 (n - 2), SelfPaying (n ^ (n - 1)) (n ^ s) (pos s) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    exact selfPaying_of_dvd (by omega) hs.1 (by omega) (hdvd s)
  obtain ⟨T, hT, hmem⟩ := corollary_2_4 hb hinj hsp
  refine ⟨T, ?_, hmem⟩
  rw [hT, Nat.card_Icc]
  congr 2
  omega

/-- `s ↦ s (r^s - 1)` is strictly increasing. -/
lemma mul_pow_sub_one_strictMono {r : ℕ} (hr : 2 ≤ r) :
    StrictMono fun s : ℕ => s * (r ^ s - 1) := by
  intro s s' hss
  have h1 : r ^ s < r ^ s' := Nat.pow_lt_pow_right (by omega) hss
  have h2 : 1 ≤ r ^ s := Nat.one_le_pow _ _ (by omega)
  exact Nat.mul_lt_mul_of_le_of_lt hss.le (by omega) (by omega)

/-- **Proposition 4.2** (section 4.1). Under `0^0 = 0`, for every `L ≥ 2` the base
`2^(L (2^L - 1))` has at least `2^(2^L - 1) - 2` nontrivial solutions: the digits `2^(j L)`,
`1 ≤ j ≤ 2^L - 2`, are self-paying. -/
theorem prop4_2 {L : ℕ} (hL : 2 ≤ L) :
    ∃ T : Finset ℕ, T.card = 2 ^ (2 ^ L - 1) - 2 ∧
      ∀ x ∈ T, 2 ≤ x ∧ IsMunchausen (2 ^ (L * (2 ^ L - 1))) 0 x := by
  set N := L * (2 ^ L - 1) with hN
  have h4 : 4 ≤ 2 ^ L := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hdvd : ∀ j, N ∣ (j * L) * (2 ^ (j * L) - 1) := by
    intro j
    have h : 2 ^ L - 1 ∣ 2 ^ (j * L) - 1 := by
      rw [mul_comm j L, pow_mul]; simpa using Nat.sub_dvd_pow_sub_pow (2 ^ L) 1 j
    obtain ⟨c, hc⟩ := h
    exact ⟨j * c, by rw [hc, hN]; ring⟩
  let pos : ℕ → ℕ := fun j => (j * L) * (2 ^ (j * L) - 1) / N
  have hpos : ∀ j, N * pos j = (j * L) * (2 ^ (j * L) - 1) := fun j => Nat.mul_div_cancel' (hdvd j)
  have hN0 : 0 < N := Nat.mul_pos (by omega) (by omega)
  have hb : 2 ≤ 2 ^ N := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN0
  have hinj : Set.InjOn pos (Finset.Icc 1 (2 ^ L - 2)) := by
    intro j _ j' _ h
    have : (j * L) * (2 ^ (j * L) - 1) = (j' * L) * (2 ^ (j' * L) - 1) := by
      rw [← hpos, ← hpos, show pos j = pos j' from h]
    have := (mul_pow_sub_one_strictMono (r := 2) le_rfl).injective this
    exact Nat.eq_of_mul_eq_mul_right (by omega) this
  have hsp : ∀ j ∈ Finset.Icc 1 (2 ^ L - 2), SelfPaying (2 ^ N) (2 ^ (j * L)) (pos j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hlt : j * L < N := by
      rw [hN, mul_comm L]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    exact selfPaying_of_dvd le_rfl (Nat.mul_pos (by omega) (by omega)) hlt (hdvd j)
  obtain ⟨T, hT, hmem⟩ := corollary_2_4 hb hinj hsp
  refine ⟨T, ?_, hmem⟩
  rw [hT, Nat.card_Icc]
  congr 2
  omega

/-- **Proposition 4.2**, unboundedness (section 4.1). Under `0^0 = 0` the number of solutions
in a base is unbounded. -/
theorem count_zero_unbounded (C : ℕ) :
    ∃ b, 2 ≤ b ∧ ∃ T : Finset ℕ, C ≤ T.card ∧ ∀ x ∈ T, 2 ≤ x ∧ IsMunchausen b 0 x := by
  obtain ⟨T, hT, hmem⟩ := theorem9_2 (n := C + 3) (by omega)
  refine ⟨(C + 3) ^ (C + 3 - 1), le_trans (by omega) (Nat.le_self_pow (by omega) _), T, ?_, hmem⟩
  rw [hT]
  have : C + 2 < 2 ^ (C + 2) := Nat.lt_two_pow_self
  rw [show C + 3 - 1 = C + 2 by omega]
  omega

/-! ### Theorem 15.9 and Theorem 25.5 -/

/-- **Theorem 15.9** (section 15.3). For every `a ≥ 2`, the string
`(a^(a+1), 0, ..., 0, a, a^a)` with `a + 2` digits is a solution in base `a^(a^(a+1) - 1)`
under `0^0 = 0`: the swap `(a, a^a)` with the self-paying digit `a^(a+1)` at position `a + 1`
on top. For `a = 2` it is `(8, 0, 2, 4)` in base 128. The library states it for `a` not a
perfect power; the direct proof needs no such condition. -/
theorem theorem15_9 {a : ℕ} (ha : 2 ≤ a) :
    IsSolution (a ^ (a ^ (a + 1) - 1)) 0
      (a ^ (a + 1) :: (List.replicate (a - 1) 0 ++ [a, a ^ a])) := by
  set B := a ^ (a ^ (a + 1) - 1) with hB
  have hA : a + 3 ≤ a ^ (a + 1) := by
    have h1 : a ^ 3 ≤ a ^ (a + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : a + 3 ≤ a ^ 3 := by
      have : a ^ 3 = a * a * a := by ring
      rw [this]; nlinarith
    omega
  have haa : a ^ a < B := Nat.pow_lt_pow_right (by omega) (by omega)
  have ha1 : a ^ (a + 1) < B := Nat.pow_lt_pow_right (by omega) (by omega)
  have hlen : (List.replicate (a - 1) 0 ++ [a, a ^ a]).length = a + 1 := by simp; omega
  have hsp : SelfPaying B (a ^ (a + 1)) (List.replicate (a - 1) 0 ++ [a, a ^ a]).length := by
    rw [hlen]
    refine ⟨by omega, by omega, ha1, ?_⟩
    rw [hB, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    rw [Nat.sub_mul, one_mul]
    have : a + 1 ≤ a ^ (a + 1) * (a + 1) := Nat.le_mul_of_pos_left _ (by omega)
    rw [mul_comm (a + 1) (a ^ (a + 1))]
    omega
  rw [isSolution_selfPaying_cons_iff hsp]
  · simp only [P_replicate_zero_append, P_cons, P_singleton, List.length_cons, List.length_nil,
      Fs_append, Fs_replicate, w_zero, mul_zero, zero_add, Fs_cons, Fs_nil, add_zero, Nat.cast_id,
      pow_one]
    rw [w_of_ne_zero 0 (by omega), w_of_ne_zero 0 (by positivity)]
    have : a * B = (a ^ a) ^ (a ^ a) := by
      rw [hB, ← pow_mul, ← pow_succ', ← pow_succ']
      congr 1
      have : 1 ≤ a ^ (a + 1) := by omega
      omega
    simp only [pow_zero, mul_one, P_nil, add_zero]
    rw [this]; ring
  · intro d hd
    simp at hd
    rcases hd with ⟨-, rfl⟩ | rfl | rfl <;> omega

/-- **Theorem 25.5** (section 25.1.2). Let `j ≥ 3` and `c ≥ 2` with `c ∣ (j-1)^c` (every prime
factor of `c` divides `j - 1`) and `c^(j c^j) ≡ 1 (mod j)`. Put `x = c^(j c^j) + j - 1` and
`y = x^(x/j)`. Then `c ∣ y`, and `(c^j, 0, ..., 0, x)` with `j - 1` zeros is a solution in base
`y / c` under `0^0 = 1`. -/
theorem theorem25_5 {j c : ℕ} (hj : 3 ≤ j) (hc : 2 ≤ c) (hcj : c ∣ (j - 1) ^ c)
    (hmod : c ^ (j * c ^ j) % j = 1) :
    c ∣ (c ^ (j * c ^ j) + j - 1) ^ ((c ^ (j * c ^ j) + j - 1) / j) ∧
    IsSolution ((c ^ (j * c ^ j) + j - 1) ^ ((c ^ (j * c ^ j) + j - 1) / j) / c) 1
      (c ^ j :: (List.replicate (j - 1) 0 ++ [c ^ (j * c ^ j) + j - 1])) := by
  set N := j * c ^ j with hN
  set x := c ^ N + j - 1 with hx
  set y := x ^ (x / j) with hy
  have hjx : j ∣ x := by
    have : (c ^ N + (j - 1)) % j = 0 := by
      rw [Nat.add_mod, hmod, Nat.mod_eq_of_lt (show j - 1 < j by omega)]
      rw [show 1 + (j - 1) = j by omega, Nat.mod_self]
    have e : x = c ^ N + (j - 1) := by omega
    rw [e]; exact Nat.dvd_of_mod_eq_zero this
  -- size: `x ≥ N = j c^j ≥ j (c + 1)`
  have hcj1 : c + 1 ≤ c ^ j := by
    calc c + 1 ≤ c * c := by nlinarith
      _ = c ^ 2 := (sq c).symm
      _ ≤ c ^ j := Nat.pow_le_pow_right (by omega) (by omega)
  have hNx : N < c ^ N := Nat.lt_pow_self (by omega)
  have hxN : N ≤ x := by omega
  have hq : c + 1 ≤ x / j := by
    rw [Nat.le_div_iff_mul_le (by omega)]
    calc (c + 1) * j ≤ c ^ j * j := Nat.mul_le_mul_right _ hcj1
      _ = N := by rw [hN]; ring
      _ ≤ x := hxN
  -- `c ∣ y`
  have hN1 : 1 ≤ N := by rw [hN]; nlinarith
  have hcy : c ∣ y := by
    have h1 : x ≡ j - 1 [MOD c] := by
      have e : x = (j - 1) + c * c ^ (N - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hN1]; omega
      show x % c = (j - 1) % c
      rw [e, Nat.add_mul_mod_self_left]
    have h2 : x ^ c % c = 0 := by
      have := h1.pow c
      unfold Nat.ModEq at this
      rw [this]; exact Nat.mod_eq_zero_of_dvd hcj
    exact (Nat.dvd_of_mod_eq_zero h2).trans (pow_dvd_pow x (by omega))
  refine ⟨hcy, ?_⟩
  obtain ⟨b, hb⟩ := hcy
  have hbdiv : y / c = b := by rw [hb, Nat.mul_div_cancel_left _ (by omega)]
  rw [hbdiv]
  -- `b > x`
  have hcx : c < x := by
    have : c < c ^ j := by omega
    have : c ^ j ≤ c ^ N :=
      Nat.pow_le_pow_right (by omega) (by rw [hN]; nlinarith [Nat.one_le_pow j c (by omega)])
    omega
  have hyx : x * x ≤ y := by
    calc x * x = x ^ 2 := (sq x).symm
      _ ≤ x ^ (x / j) := Nat.pow_le_pow_right (by omega) (by omega)
  have hbx : x < b := by
    by_contra h
    replace h := not_lt.1 h
    have : c * b ≤ c * x := Nat.mul_le_mul_left _ h
    nlinarith
  have hcjN : c ^ j ≤ c ^ N :=
    Nat.pow_le_pow_right (by omega) (by rw [hN]; nlinarith [Nat.one_le_pow j c (by omega)])
  refine ⟨fun d hd => ?_, fun _ => by simp; omega, ?_⟩
  · simp at hd
    rcases hd with rfl | ⟨-, rfl⟩ | rfl <;> omega
  · simp only [P_cons, P_append_singleton, P_replicate_zero, mul_zero, add_zero, Nat.cast_id,
      List.length_append, List.length_replicate, List.length_singleton, Fs_cons, Fs_append,
      Fs_replicate, w_zero, mul_one]
    rw [w_of_ne_zero 1 (by positivity), w_of_ne_zero 1 (by omega), show j - 1 + 1 = j by omega,
      ← pow_mul, ← hN]
    have hyj : (c * b) ^ j = x ^ x := by
      rw [← hb, hy, ← pow_mul, Nat.div_mul_cancel hjx]
    rw [mul_pow] at hyj
    rw [hyj, Fs_nil]
    omega

/-- The conditions of Theorem 25.5 hold for `c = (j - 1)^a`, `a ≥ 1` (section 25.1.2). -/
theorem theorem25_5_conditions {j a : ℕ} (hj : 3 ≤ j) (ha : 1 ≤ a) :
    (j - 1) ^ a ∣ (j - 1) ^ ((j - 1) ^ a) ∧
      ((j - 1) ^ a) ^ (j * ((j - 1) ^ a) ^ j) % j = 1 := by
  constructor
  · exact pow_dvd_pow _ (Nat.lt_pow_self (by omega)).le
  · set c := (j - 1) ^ a with hc
    have heven : Even (a * (j * c ^ j)) := by
      rcases Nat.even_or_odd j with hje | hjo
      · exact (hje.mul_right _).mul_left _
      · have : Even (j - 1) := by
          obtain ⟨k, hk⟩ := hjo; exact ⟨k, by omega⟩
        have hce : Even c := by rw [hc]; exact this.pow_of_ne_zero (by omega)
        exact ((hce.pow_of_ne_zero (by omega)).mul_left _).mul_left _
    have hneg : ((j - 1 : ℕ) : ZMod j) = -1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; simp
    have h1 : ((c ^ (j * c ^ j) : ℕ) : ZMod j) = ((1 : ℕ) : ZMod j) := by
      rw [Nat.cast_pow, hc, Nat.cast_pow, hneg, ← pow_mul, heven.neg_one_pow, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    rw [h1, Nat.mod_eq_of_lt (by omega)]

/-! ### Proposition 15.15: one integer in many bases -/

/-- **Proposition 15.15** (section 15.6). Under `0^0 = 0`, let `c = r^u` with `r ≥ 2`, `u ≥ 1`.
In every base `r^t` with `u < t` and `t ∣ u (c - 1)` the string `(c, 0, ..., 0, 1)` with `c` at
the self-paying position `k = u (c - 1)/t` is a solution, of value `c^c + 1`; and `(1, c)` is a
solution of the same value in base `c^c - c + 1`. -/
theorem prop15_15 {r u t : ℕ} (hr : 2 ≤ r) (hu : 1 ≤ u) (hut : u < t)
    (hdvd : t ∣ u * (r ^ u - 1)) :
    IsSolution (r ^ t) 0 (r ^ u :: (List.replicate (u * (r ^ u - 1) / t - 1) 0 ++ [1])) ∧
      P (r ^ t) (r ^ u :: (List.replicate (u * (r ^ u - 1) / t - 1) 0 ++ [1])) =
        (r ^ u) ^ (r ^ u) + 1 ∧
      IsSolution ((r ^ u) ^ (r ^ u) - r ^ u + 1) 0 [1, r ^ u] := by
  have hsp := selfPaying_of_dvd hr hu hut hdvd
  set c := r ^ u
  set k := u * (c - 1) / t
  obtain ⟨hc2, hk1, hcb, hbal⟩ := hsp
  have hb : 2 ≤ r ^ t := by omega
  have hlen : (List.replicate (k - 1) 0 ++ [1]).length = k := by simp; omega
  have hP : P (r ^ t) (c :: (List.replicate (k - 1) 0 ++ [1])) = c ^ c + 1 := by
    rw [P_cons, hlen, P_replicate_zero_append, P_singleton, Nat.cast_id, Nat.cast_one, hbal]
  refine ⟨⟨?_, fun _ => by simp; omega, ?_⟩, hP, isSolution_one_c hc2⟩
  · intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hcb
    rcases List.mem_append.1 hd with hd | hd
    · rw [List.eq_of_mem_replicate hd]; omega
    · rw [List.mem_singleton.1 hd]; omega
  · rw [hP]
    simp [Fs_append, w_of_ne_zero 0 (show c ≠ 0 by omega)]

/-- **Proposition 15.15**, the unbounded count (section 15.6). Under `0^0 = 0`, for every `n`
some integer is a solution in at least `n` bases: `N = c^c + 1` with `c = 2^u`, `u = 2^n`, in
the bases `2^(u (2^(2^i) - 1))`, `1 ≤ i ≤ n`, since `2^(2^i) - 1` divides `2^u - 1`. -/
theorem prop15_15_unbounded (n : ℕ) :
    ∃ N : ℕ, ∃ S : Finset ℕ, S.card = n ∧ ∀ b ∈ S, IsMunchausen b 0 N := by
  set u := 2 ^ n with hu
  have hu1 : 1 ≤ u := Nat.one_le_two_pow
  let t : ℕ → ℕ := fun i => u * (2 ^ (2 ^ i) - 1)
  have hd3 : ∀ i, 1 ≤ i → 3 ≤ 2 ^ (2 ^ i) - 1 := by
    intro i hi
    have : 4 ≤ 2 ^ (2 ^ i) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 ^ i) := Nat.pow_le_pow_right (by norm_num)
            (by calc 2 = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi)
    omega
  have ht : ∀ i, 1 ≤ i → i ≤ n → u < t i ∧ t i ∣ u * (2 ^ u - 1) := by
    intro i hi hin
    refine ⟨?_, Nat.mul_dvd_mul_left u ?_⟩
    · have := hd3 i hi
      simp only [t]; nlinarith
    · have e : 2 ^ u = (2 ^ (2 ^ i)) ^ (2 ^ (n - i)) := by
        rw [← pow_mul, ← pow_add, show i + (n - i) = n by omega]
      rw [e]
      simpa using Nat.sub_dvd_pow_sub_pow (x := 2 ^ (2 ^ i)) (y := 1) (n := 2 ^ (n - i))
  have htinj : Set.InjOn t (Finset.Icc 1 n : Set ℕ) := by
    intro i _ j _ h
    simp only [t] at h
    have h1 : 2 ^ (2 ^ i) - 1 = 2 ^ (2 ^ j) - 1 := Nat.eq_of_mul_eq_mul_left (by omega) h
    have h2 : 2 ^ (2 ^ i) = 2 ^ (2 ^ j) := by
      have := Nat.one_le_two_pow (n := 2 ^ i)
      have := Nat.one_le_two_pow (n := 2 ^ j)
      omega
    exact Nat.pow_right_injective le_rfl (Nat.pow_right_injective le_rfl h2)
  refine ⟨(2 ^ u) ^ (2 ^ u) + 1, (Finset.Icc 1 n).image (fun i => 2 ^ t i), ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Nat.card_Icc, Nat.add_sub_cancel]
    intro i hi j hj h
    exact htinj hi hj (Nat.pow_right_injective le_rfl h)
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨hi1, hin⟩ := Finset.mem_Icc.1 hi
    obtain ⟨hut, hdvd⟩ := ht i hi1 hin
    obtain ⟨hs, hP, -⟩ := prop15_15 (r := 2) le_rfl hu1 hut hdvd
    have hb : 1 < 2 ^ t i := Nat.one_lt_two_pow (by omega)
    have := hs.isMunchausen hb
    rwa [hP] at this

end Munchausen
