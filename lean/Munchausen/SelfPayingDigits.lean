import Munchausen.Constructions

/-!
# Self-paying digits: moves and counts (sections 2.2, 8.3, 9.8 and 15.3)

* Proposition 2.3: under `0^0 = 0`, self-paying digits can be added to or removed from zero
  positions of a solution, one at a time or all at once (the core);

* a base with `C` self-paying digits is `r^t` with `t ≥ C + 1`, where `r` is its primitive
  root; so `C < log2 b` (Proposition 8.5) and the base is an `r^t` with `t ≥ C + 1`
  (Proposition 9.3, corrected form);
* Proposition 15.8: `r^t`, with `r` not a perfect power, has a self-paying digit exactly when
  `t` has a prime factor that does not divide `r`;
* Propositions 15.4 and 15.5: cycles under both conventions, and shifted cycles.
-/

namespace Munchausen

/-- `r` is not a perfect power: it is no `e`-th power with `e ≥ 2`. -/
def NotPerfectPower (r : ℕ) : Prop := ∀ c e, 2 ≤ e → c ^ e ≠ r

/-- Every self-paying digit of base `b` is `r^s` with `1 ≤ s < t`, where `b = r^t` and `r` is the
primitive root of `exists_primitive_root` (Proposition 2.2). -/
lemma SelfPaying.eq_root_pow {b r t a k : ℕ} (hr : 2 ≤ r) (hrt : r ^ t = b)
    (hroot : ∀ c j, 2 ≤ c → 1 ≤ j → c ^ j = b → ∃ i, c = r ^ i) (h : SelfPaying b a k) :
    ∃ s, 1 ≤ s ∧ s < t ∧ a = r ^ s := by
  obtain ⟨c, s, T, hc, hs, hsT, rfl, hbc, -⟩ := h.exists_pow
  obtain ⟨i, rfl⟩ := hroot c T hc (by omega) hbc.symm
  have hi : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h; · simp at hc
    exact h
  refine ⟨i * s, Nat.mul_pos hi hs, ?_, by rw [pow_mul]⟩
  have h1 := h.2.2.1
  rw [← pow_mul, ← hrt] at h1
  exact (Nat.pow_lt_pow_iff_right (by omega)).1 h1

/-- **Propositions 8.5 and 9.3**, the count. If the digits in `D` are all self-paying in base
`b = r^t` (`r` the primitive root), then `|D| ≤ t - 1`. -/
theorem card_selfPaying_le {b r t : ℕ} (hr : 2 ≤ r) (hrt : r ^ t = b)
    (hroot : ∀ c j, 2 ≤ c → 1 ≤ j → c ^ j = b → ∃ i, c = r ^ i) (D : Finset ℕ)
    (hD : ∀ a ∈ D, ∃ k, SelfPaying b a k) : D.card ≤ t - 1 := by
  have hexp : ∀ a ∈ D, ∃ s, 1 ≤ s ∧ s < t ∧ a = r ^ s := fun a ha => by
    obtain ⟨k, hk⟩ := hD a ha
    exact hk.eq_root_pow hr hrt hroot
  have hmaps : ∀ a ∈ D, Nat.log r a ∈ Finset.Icc 1 (t - 1) := by
    intro a ha
    obtain ⟨s, hs1, hst, rfl⟩ := hexp a ha
    rw [Nat.log_pow (by omega), Finset.mem_Icc]
    omega
  have hinj : Set.InjOn (Nat.log r) D := by
    intro a ha a' ha' h
    obtain ⟨s, -, -, rfl⟩ := hexp a ha
    obtain ⟨s', -, -, rfl⟩ := hexp a' ha'
    rw [Nat.log_pow (by omega), Nat.log_pow (by omega)] at h
    rw [h]
  have := Finset.card_le_card_of_injOn (Nat.log r) hmaps hinj
  simpa using this

/-- **Proposition 8.5**, second part (section 8.3). A base has fewer than `log2 b`
self-paying digits: `|D| + 1 ≤ log2 b`. -/
theorem card_selfPaying_lt_log {b : ℕ} (hb : 2 ≤ b) (D : Finset ℕ)
    (hD : ∀ a ∈ D, ∃ k, SelfPaying b a k) : D.card + 1 ≤ Nat.log 2 b := by
  obtain ⟨r, t, hr, ht, hrt, hroot⟩ := exists_primitive_root hb
  have h1 := card_selfPaying_le hr hrt hroot D hD
  have h2 : t ≤ Nat.log 2 b := by
    rw [← hrt]
    calc t = Nat.log 2 (2 ^ t) := (Nat.log_pow (by norm_num) t).symm
      _ ≤ Nat.log 2 (r ^ t) := Nat.log_mono_right (Nat.pow_le_pow_left hr t)
  omega

/-- **Proposition 9.3**, the structure (section 9.8, corrected form). A base with `C ≥ 1`
self-paying digits is `r^t` with `r ≥ 2` and `t ≥ C + 1`. Counting the `r^t ≤ X` for
`C + 1 ≤ t ≤ log2 X` gives the bound `X^(1/(C+1)) + X^(1/(C+2)) log2 X`. -/
theorem selfPaying_base_pow {b : ℕ} (hb : 2 ≤ b) (D : Finset ℕ)
    (hD : ∀ a ∈ D, ∃ k, SelfPaying b a k) : ∃ r t, 2 ≤ r ∧ D.card + 1 ≤ t ∧ r ^ t = b := by
  obtain ⟨r, t, hr, ht, hrt, hroot⟩ := exists_primitive_root hb
  have := card_selfPaying_le hr hrt hroot D hD
  exact ⟨r, t, hr, by omega, hrt⟩

/-- If `r` is not a perfect power, it is the primitive root of every power `r^t`. -/
lemma root_of_notPerfectPower {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t) (hnp : NotPerfectPower r) :
    ∀ c j, 2 ≤ c → 1 ≤ j → c ^ j = r ^ t → ∃ i, c = r ^ i := by
  obtain ⟨r0, t0, hr0, ht0, hrt0, hroot⟩ := exists_primitive_root (b := r ^ t)
    (le_trans hr (Nat.le_self_pow (by omega) r))
  obtain ⟨i, hi⟩ := hroot r t hr ht rfl
  have hi1 : i = 1 := by
    rcases Nat.lt_trichotomy i 1 with h | h | h
    · interval_cases i; simp at hi; omega
    · exact h
    · exact absurd hi.symm (hnp r0 i (by omega))
  subst hi1
  rw [pow_one] at hi
  subst hi
  exact hroot

/-- **Proposition 15.8** (section 15.3). Let `r ≥ 2` not be a perfect power and `t ≥ 1`. Base
`r^t` has a self-paying digit if and only if `t` has a prime factor that does not divide `r`. -/
theorem prop15_8 {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t) (hnp : NotPerfectPower r) :
    (∃ a k, SelfPaying (r ^ t) a k) ↔ ∃ p, p.Prime ∧ p ∣ t ∧ ¬ p ∣ r := by
  constructor
  · rintro ⟨a, k, h⟩
    by_contra hall
    push Not at hall
    obtain ⟨c, s, T, hc, hs, hsT, rfl, hbc, hTk⟩ := h.exists_pow
    obtain ⟨i, rfl⟩ := root_of_notPerfectPower hr ht hnp c T hc (by omega) hbc.symm
    rw [← pow_mul] at hbc hTk
    have hτ : t = i * T := Nat.pow_right_injective hr hbc
    have hi : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | h; · simp at hc
      exact h
    -- `t ∣ (i s) (r^(i s) - 1)` with `i s < t`
    have hdvd : t ∣ (i * s) * (r ^ (i * s) - 1) := ⟨k, by rw [hτ]; nlinarith [hTk]⟩
    have hcop : Nat.Coprime t (r ^ (i * s) - 1) := by
      apply Nat.coprime_of_dvd
      intro p hp hpt hp1
      have hpr := hall p hp hpt
      have : p ∣ r ^ (i * s) := dvd_pow hpr (by positivity)
      have h1 : 1 ≤ r ^ (i * s) := Nat.one_le_pow _ _ (by omega)
      have : p ∣ 1 := by
        have := Nat.dvd_sub this hp1
        rwa [Nat.sub_sub_self h1] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    have := Nat.le_of_dvd (Nat.mul_pos hi hs) (hcop.dvd_of_dvd_mul_right hdvd)
    have : i * s < i * T := Nat.mul_lt_mul_of_pos_left hsT hi
    omega
  · rintro ⟨p, hp, hpt, hpr⟩
    -- the digit `r^s` with `s = (t / p) (p - 1)`
    obtain ⟨q, rfl⟩ := hpt
    have hq : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | h; · simp at ht
      exact h
    have hp2 := hp.two_le
    have hferm : p ∣ r ^ (q * (p - 1)) - 1 := by
      have : r ^ (p - 1) ≡ 1 [MOD p] := by
        have := Nat.ModEq.pow_totient
          ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpr)))
        rwa [Nat.totient_prime hp] at this
      have h2 : r ^ (q * (p - 1)) ≡ 1 [MOD p] := by
        rw [mul_comm, pow_mul]; simpa using this.pow q
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h2.symm
    refine ⟨_, _, selfPaying_of_dvd hr (s := q * (p - 1)) (Nat.mul_pos hq (by omega))
      (by rw [mul_comm p q]; exact Nat.mul_lt_mul_of_pos_left (by omega) hq) ?_⟩
    obtain ⟨u, hu⟩ := hferm
    exact ⟨u * (p - 1), by rw [hu]; ring⟩

/-! ### Proposition 2.3: moves of self-paying digits -/

/-- The digit of `n` at position `i` in base `b`. -/
def digitAt (b n i : ℕ) : ℕ := n / b ^ i % b

lemma sum_digitAt (b n L : ℕ) :
    ∑ i ∈ Finset.range L, digitAt b n i * b ^ i = n % b ^ L := by
  induction L with
  | zero => simp [Nat.mod_one]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul, digitAt]
    ring

/-- `F` in terms of the digits up to any position `L` with `n < b^L` (under `0^0 = 0`). -/
lemma F_zero_eq_sum {b n L : ℕ} (hb : 2 ≤ b) (hn : n < b ^ L) :
    F b 0 n = ∑ i ∈ Finset.range L, w 0 (digitAt b n i) := by
  have h1 : Nat.ofDigits b ((List.range L).map (digitAt b n)) = n := by
    rw [ofDigits_map_range, sum_digitAt, Nat.mod_eq_of_lt hn]
  have h2 := F_ofDigits_zero (b := b) (by omega) ((List.range L).map (digitAt b n))
    (fun d hd => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd
      exact Nat.mod_lt _ (by omega))
  rw [h1, Fs_map_range] at h2
  exact h2

/-- Placing a self-paying digit `a` at a zero position `k` adds `a b^k = a^a` to both `n` and
`F(n)` (under `0^0 = 0`, proof of Proposition 2.3). -/
lemma F_add_selfPaying {b n a k : ℕ} (hb : 2 ≤ b) (hk : digitAt b n k = 0)
    (h : SelfPaying b a k) : F b 0 (n + a * b ^ k) = F b 0 n + a * b ^ k := by
  classical
  -- a common length `L` for both numbers
  obtain ⟨L, hL, hkL⟩ : ∃ L, n + a * b ^ k < b ^ L ∧ k < L := by
    refine ⟨n + a * b ^ k + k + 1, ?_, by omega⟩
    exact lt_of_lt_of_le (by omega) (Nat.lt_pow_self (by omega)).le
  have hnL : n < b ^ L := by omega
  -- the digits of `n + a b^k` are those of `n` with `a` at position `k`
  let f := Function.update (digitAt b n) k a
  have hf : ∀ i, f i < b := by
    intro i
    by_cases hi : i = k
    · subst hi; simp [f, h.2.2.1]
    · simp [f, hi, digitAt]; exact Nat.mod_lt _ (by omega)
  have hmem : k ∈ Finset.range L := Finset.mem_range.2 hkL
  have hoff : ∀ g : ℕ → ℕ, ∑ i ∈ (Finset.range L).erase k, g (f i) * b ^ i =
      ∑ i ∈ (Finset.range L).erase k, g (digitAt b n i) * b ^ i := fun g =>
    Finset.sum_congr rfl fun i hi => by
      simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hval : ∑ i ∈ Finset.range L, f i * b ^ i = n + a * b ^ k := by
    rw [← Finset.add_sum_erase _ _ hmem]
    have e2 := Finset.add_sum_erase _ (fun i => digitAt b n i * b ^ i) hmem
    rw [sum_digitAt, Nat.mod_eq_of_lt hnL, hk, zero_mul, zero_add] at e2
    have := hoff id
    simp only [id] at this
    rw [this, e2]
    simp [f]; ring
  have hw : ∑ i ∈ Finset.range L, w 0 (f i) = F b 0 n + w 0 a := by
    rw [F_zero_eq_sum hb hnL, ← Finset.add_sum_erase _ _ hmem,
      ← Finset.add_sum_erase _ (fun i => w 0 (digitAt b n i)) hmem]
    have : ∑ i ∈ (Finset.range L).erase k, w 0 (f i) =
        ∑ i ∈ (Finset.range L).erase k, w 0 (digitAt b n i) :=
      Finset.sum_congr rfl fun i hi => by
        simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [this, hk]
    simp [f]; ring
  have h2 := F_ofDigits_zero (b := b) (by omega) ((List.range L).map f)
    (fun d hd => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd; exact hf i)
  rw [ofDigits_map_range, hval, Fs_map_range, hw, ← h.balance] at h2
  exact h2

/-- **Proposition 2.3**, one move (section 2.2). Under `0^0 = 0`, if `n` has the digit 0 at
position `k` and `a` is self-paying at `k`, then `n` is a solution exactly when `n + a b^k`
is. Self-paying digits can be added to and removed from zero positions freely. -/
theorem isMunchausen_add_selfPaying {b n a k : ℕ} (hb : 2 ≤ b) (hk : digitAt b n k = 0)
    (h : SelfPaying b a k) : IsMunchausen b 0 n ↔ IsMunchausen b 0 (n + a * b ^ k) := by
  unfold IsMunchausen
  rw [F_add_selfPaying hb hk h]
  omega

/-! ### Propositions 15.4 and 15.5: cycles under both conventions -/

/-- **Proposition 15.4** (section 15.1.4). On numbers without the digit 0 the two conventions
give the same map `F`, so a cycle whose members have no digit 0 is a cycle under both
conventions. -/
theorem prop15_4 {b : ℕ} {c : ℕ → ℕ} (h0 : ∀ i, 0 ∉ Nat.digits b (c i))
    (hc : ∀ i, F b 0 (c i) = c (i + 1)) : ∀ i, F b 1 (c i) = c (i + 1) := by
  intro i
  rw [F_one_eq, List.count_eq_zero_of_not_mem (h0 i), add_zero, hc i]

/-- Under `0^0 = 0`, a number ending in 0 has `F(n + 1) = F(n) + 1` (proof of
Proposition 2.1). -/
lemma F_succ_of_mod_eq_zero {b n : ℕ} (hb : 2 ≤ b) (h0 : n % b = 0) :
    F b 0 (n + 1) = F b 0 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [F, show 1 < b by omega]
  have hd1 : Nat.digits b n = 0 :: Nat.digits b (n / b) := by
    rw [Nat.digits_def' (by omega) hn, h0]
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
  simp only [F, hd1, hd2, Fs_cons, w_zero, w_one]
  omega

/-- **Proposition 15.5** (section 15.1.4). Under `0^0 = 0`: if every member of a cycle ends in
0, adding 1 to every member gives a cycle of the same length; if every member has the digit 0
at position `k` and `a` is self-paying at `k`, adding `a b^k` to every member gives a cycle of
the same length (the shift is injective, so the length is kept). -/
theorem prop15_5 {b : ℕ} (hb : 2 ≤ b) {c : ℕ → ℕ} (hc : ∀ i, F b 0 (c i) = c (i + 1)) :
    ((∀ i, c i % b = 0) → ∀ i, F b 0 (c i + 1) = c (i + 1) + 1) ∧
      ∀ {a k : ℕ}, SelfPaying b a k → (∀ i, digitAt b (c i) k = 0) →
        ∀ i, F b 0 (c i + a * b ^ k) = c (i + 1) + a * b ^ k := by
  refine ⟨fun h0 i => ?_, fun hsp hk i => ?_⟩
  · rw [F_succ_of_mod_eq_zero hb (h0 i), hc i]
  · rw [F_add_selfPaying hb (hk i) hsp, hc i]

/-- **Proposition 2.3**, the core (section 2.2). Under `0^0 = 0`, let `S` be a set of
positions below `L` (with `n < b^L`) that hold self-paying digits of `n`. Removing them all
gives the number `c = sum_{i ∉ S} d_i b^i`, and `n` is a solution exactly when `c` is (or
`c = 0`). With Proposition 2.1 for a final 1, this is the decomposition of a solution into a
core, self-paying digits and an optional final 1. -/
theorem isMunchausen_iff_core {b n L : ℕ} (hb : 2 ≤ b) (hn : n < b ^ L) (S : Finset ℕ)
    (hS : S ⊆ Finset.range L) (hsp : ∀ k ∈ S, SelfPaying b (digitAt b n k) k) :
    IsMunchausen b 0 n ↔
      IsMunchausen b 0 (∑ i ∈ (Finset.range L).filter (· ∉ S), digitAt b n i * b ^ i) := by
  classical
  let g : ℕ → ℕ := fun i => if i ∈ S then 0 else digitAt b n i
  have hg : ∀ i, g i < b := fun i => by
    simp only [g]; split_ifs
    · omega
    · exact Nat.mod_lt _ (by omega)
  have hcval : ∑ i ∈ Finset.range L, g i * b ^ i =
      ∑ i ∈ (Finset.range L).filter (· ∉ S), digitAt b n i * b ^ i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    simp only [g]; split_ifs <;> simp
  have hFc := F_ofDigits_zero (b := b) (by omega) ((List.range L).map g)
    (fun d hd => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd; exact hg i)
  rw [ofDigits_map_range, hcval, Fs_map_range] at hFc
  -- split `n` and `F(n)` into the part on `S` and the rest
  have hsplit : ∀ h : ℕ → ℕ, ∑ i ∈ Finset.range L, h i =
      ∑ i ∈ (Finset.range L).filter (· ∈ S), h i +
        ∑ i ∈ (Finset.range L).filter (· ∉ S), h i := fun h =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hfilter : (Finset.range L).filter (· ∈ S) = S := by
    ext i; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hn' : n = ∑ i ∈ S, digitAt b n i * b ^ i +
      ∑ i ∈ (Finset.range L).filter (· ∉ S), digitAt b n i * b ^ i := by
    have := hsplit (fun i => digitAt b n i * b ^ i)
    rw [hfilter, sum_digitAt, Nat.mod_eq_of_lt hn] at this
    exact this
  have hwg : ∑ i ∈ Finset.range L, w 0 (g i) =
      ∑ i ∈ (Finset.range L).filter (· ∉ S), w 0 (digitAt b n i) := by
    rw [hsplit (fun i => w 0 (g i))]
    have h1 : ∑ i ∈ (Finset.range L).filter (· ∈ S), w 0 (g i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [g, (Finset.mem_filter.1 hi).2]
    rw [h1, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, (Finset.mem_filter.1 hi).2]
  have hFn : F b 0 n = ∑ i ∈ S, digitAt b n i * b ^ i +
      ∑ i ∈ (Finset.range L).filter (· ∉ S), w 0 (digitAt b n i) := by
    rw [F_zero_eq_sum hb hn, hsplit, hfilter]
    congr 1
    exact Finset.sum_congr rfl fun k hk => ((hsp k hk).balance).symm
  rw [hwg] at hFc
  unfold IsMunchausen
  rw [hFn, hFc]
  constructor <;> intro h <;> omega

/-! ### Proposition 9.3: the count -/

/-- At most `X^(1/t)` integers `r ≥ 2` have `r^t ≤ X`. -/
lemma card_pow_le (X t : ℕ) (ht : 1 ≤ t) :
    (((Finset.Icc 2 X).filter fun r => r ^ t ≤ X).card : ℝ) ≤ (X : ℝ) ^ (1 / (t : ℝ)) := by
  set N := ⌊(X : ℝ) ^ (1 / (t : ℝ))⌋₊
  have hsub : ((Finset.Icc 2 X).filter fun r => r ^ t ≤ X) ⊆ Finset.Icc 1 N := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    rw [Finset.mem_Icc]
    refine ⟨by omega, Nat.le_floor ?_⟩
    have h1 : ((r : ℝ) ^ t) ^ (1 / (t : ℝ)) = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_one_div_cancel (by positivity),
        Real.rpow_one]
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hr.2) (by positivity)
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  calc (((Finset.Icc 2 X).filter fun r => r ^ t ≤ X).card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (by omega : _ ≤ N)
    _ ≤ _ := Nat.floor_le (by positivity)

open Classical in
/-- **Proposition 9.3** (section 9.8, corrected form). At most
`X^(1/(c+1)) + X^(1/(c+2)) log2 X` bases `2 ≤ b ≤ X` have `c ≥ 1` or more self-paying digits. -/
theorem prop9_3 (X c : ℕ) (hc : 1 ≤ c) :
    (((Finset.Icc 2 X).filter fun b => ∃ D : Finset ℕ, c ≤ D.card ∧
        ∀ a ∈ D, ∃ k, SelfPaying b a k).card : ℝ) ≤
      (X : ℝ) ^ (1 / ((c : ℝ) + 1)) + (X : ℝ) ^ (1 / ((c : ℝ) + 2)) * Nat.log 2 X := by
  set L := Nat.log 2 X
  set S := (Finset.Icc 2 X).filter fun b => ∃ D : Finset ℕ, c ≤ D.card ∧
    ∀ a ∈ D, ∃ k, SelfPaying b a k
  let T : ℕ → Finset ℕ := fun t => (Finset.Icc 2 X).filter fun r => r ^ t ≤ X
  have hsub : S ⊆ (Finset.Icc (c + 1) L).biUnion fun t => (T t).image (· ^ t) := by
    intro b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    obtain ⟨⟨hb2, hbX⟩, D, hD, hDsp⟩ := hb
    obtain ⟨r, t, hr, ht, hrt⟩ := selfPaying_base_pow hb2 D hDsp
    rw [Finset.mem_biUnion]
    have ht1 : 1 ≤ t := by omega
    have hrb : r ≤ b := by rw [← hrt]; exact Nat.le_self_pow (by omega) r
    have htL : t ≤ L := by
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ t ≤ r ^ t := Nat.pow_le_pow_left hr t
        _ = b := hrt
        _ ≤ X := hbX
    refine ⟨t, Finset.mem_Icc.2 ⟨by omega, htL⟩, Finset.mem_image.2 ⟨r, ?_, hrt⟩⟩
    simp only [T, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hr, by omega⟩, by omega⟩
  have hcard : (S.card : ℝ) ≤ ∑ t ∈ Finset.Icc (c + 1) L, (X : ℝ) ^ (1 / (t : ℝ)) := by
    calc (S.card : ℝ) ≤ (((Finset.Icc (c + 1) L).biUnion fun t => (T t).image (· ^ t)).card : ℝ) :=
          by exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ t ∈ Finset.Icc (c + 1) L, (((T t).image (· ^ t)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ t ∈ Finset.Icc (c + 1) L, ((T t).card : ℝ) := by
          apply Finset.sum_le_sum; intro t _; exact_mod_cast Finset.card_image_le
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro t ht
          exact card_pow_le X t (by rw [Finset.mem_Icc] at ht; omega)
  refine hcard.trans ?_
  rcases Nat.lt_or_ge L (c + 1) with hL | hL
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
  · have hX1 : (1 : ℝ) ≤ X := by
      have : 1 ≤ X := by
        by_contra h
        have : X = 0 := by omega
        simp [L, this] at hL
      exact_mod_cast this
    have hsplit : Finset.Icc (c + 1) L = insert (c + 1) (Finset.Icc (c + 2) L) := by
      ext t; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    push_cast
    have h1 : ∑ t ∈ Finset.Icc (c + 2) L, (X : ℝ) ^ (1 / (t : ℝ)) ≤
        ∑ _t ∈ Finset.Icc (c + 2) L, (X : ℝ) ^ (1 / ((c : ℝ) + 2)) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.mem_Icc] at ht
      apply Real.rpow_le_rpow_of_exponent_le hX1
      have : (c : ℝ) + 2 ≤ t := by exact_mod_cast ht.1
      exact one_div_le_one_div_of_le (by positivity) this
    have h2 : ∑ _t ∈ Finset.Icc (c + 2) L, (X : ℝ) ^ (1 / ((c : ℝ) + 2)) ≤
        (X : ℝ) ^ (1 / ((c : ℝ) + 2)) * L := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast (by omega : L + 1 - (c + 2) ≤ L)
    linarith

/-! ### Proposition 8.6: self-paying digits and near-solutions under `0^0 = 1` -/

/-- `SPFill b s s' j`: the string `s'` arises from `s` by replacing `j` zeros with digits that
are self-paying at their positions (section 8.4). -/
inductive SPFill (b : ℕ) : List ℕ → List ℕ → ℕ → Prop
  | nil : SPFill b [] [] 0
  | keep {x : ℕ} {t t' : List ℕ} {j : ℕ} : SPFill b t t' j → SPFill b (x :: t) (x :: t') j
  | place {a : ℕ} {t t' : List ℕ} {j : ℕ} :
      SelfPaying b a t.length → SPFill b t t' j → SPFill b (0 :: t) (a :: t') (j + 1)

lemma SPFill.length_eq {b : ℕ} {s s' : List ℕ} {j : ℕ} (h : SPFill b s s' j) :
    s.length = s'.length := by
  induction h with
  | nil => rfl
  | keep _ ih => simp [ih]
  | place _ _ ih => simp [ih]

/-- **Proposition 8.6** (section 8.4). Under `0^0 = 1`, each self-paying digit placed on a 0
lowers the defect `F(s) - s` by exactly 1. -/
theorem prop8_6 {b : ℕ} {s s' : List ℕ} {j : ℕ} (h : SPFill b s s' j) :
    (Fs 1 s' : ℤ) - P (b : ℤ) s' = ((Fs 1 s : ℤ) - P (b : ℤ) s) - j := by
  induction h with
  | nil => simp
  | @keep x t t' j hf ih =>
    have hl := hf.length_eq
    simp only [Fs_cons, P_cons, ← hl]
    push_cast
    linarith
  | @place a t t' j hsp hf ih =>
    have hl := hf.length_eq
    have hbal : ((a : ℤ) * (b : ℤ) ^ t.length) = ((a ^ a : ℕ) : ℤ) := by
      exact_mod_cast hsp.2.2.2
    simp only [Fs_cons, P_cons, ← hl, w_zero, w_of_ne_zero 1 (show a ≠ 0 by have := hsp.1; omega)]
    push_cast at hbal ⊢
    linarith

/-- **Proposition 8.6**, the correspondence: if `s'` arises from `s` by placing `j` self-paying
digits on zeros, then `s'` satisfies the solution equation `P(s') = F(s')` under `0^0 = 1`
exactly when `s` is a near-solution with defect `j`, `F(s) = P(s) + j`. -/
theorem prop8_6_iff {b : ℕ} {s s' : List ℕ} {j : ℕ} (h : SPFill b s s' j) :
    P b s' = Fs 1 s' ↔ Fs 1 s = P b s + j := by
  have key := prop8_6 h
  have e1 : ((P b s : ℕ) : ℤ) = P (b : ℤ) s := cast_P b s
  have e2 : ((P b s' : ℕ) : ℤ) = P (b : ℤ) s' := cast_P b s'
  constructor
  · intro hs
    have h1 : ((P b s' : ℕ) : ℤ) = ((Fs 1 s' : ℕ) : ℤ) := by rw [hs]
    have h2 : ((Fs 1 s : ℕ) : ℤ) = ((P b s + j : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h2
  · intro hs
    have h1 : ((Fs 1 s : ℕ) : ℤ) = ((P b s + j : ℕ) : ℤ) := by rw [hs]
    push_cast at h1
    have h2 : ((P b s' : ℕ) : ℤ) = ((Fs 1 s' : ℕ) : ℤ) := by linarith
    exact_mod_cast h2

/-! ### Theorem 15.14: chains and cycles of power digits -/

/-- The digits of the construction of Theorem 15.14 in base `r^t`: `r^(u_0)` at position 0 and
`r^(φ x)` at position `π x` for `x ∈ X`, where `φ x = x r^x mod t` and `π x = ⌊x r^x / t⌋`
(written as a sum over the at most one `x` with `π x = k`), and 0 elsewhere. -/
def chainDigit (r t u0 : ℕ) (X : Finset ℕ) (k : ℕ) : ℕ :=
  if k = 0 then r ^ u0 else ∑ x ∈ X.filter (fun x => x * r ^ x / t = k), r ^ (x * r ^ x % t)

lemma P_map_range (b : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    P b ((List.range n).reverse.map f) = ∑ k ∈ Finset.range n, f k * b ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, P_cons, List.length_map, List.length_reverse, List.length_range, ih,
      Finset.sum_range_succ]
    push_cast; ring

lemma Fs_reverse_map_range (m : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    Fs m ((List.range n).reverse.map f) = ∑ k ∈ Finset.range n, w m (f k) := by
  rw [List.map_reverse, Fs_reverse, Fs_map_range]

/-- **Theorem 15.14** (section 15.5). Let `b = r^t`, `φ x = x r^x mod t`, `π x = ⌊x r^x / t⌋`,
and let `X ⊆ [1, t)` contain `u_0`, with `φ` injective on `X` and `φ(X) = (X \ {u_0}) ∪ {0}`:
this is exactly a chain `u_0 → u_1 → ... → 0` of `φ` together with cycles of `φ`. Place `r^(u_0)`
at position 0 and `r^(φ x)` at position `π x` for `x ∈ X`. If the positions `π x` are distinct
and positive, `T` is the largest one, and the string has exactly `r^(u_0) - 1` zeros
(`T + 1 = r^(u_0) + |X|`), then it is a solution under `0^0 = 1`: the digit `r^(φ x)` at
`π x` is worth `r^(x r^x) = w(r^x)`. -/
theorem theorem15_14 {r t u0 T : ℕ} {X : Finset ℕ} (hr : 2 ≤ r) (hu0 : u0 ∈ X)
    (hX : ∀ x ∈ X, 1 ≤ x ∧ x < t)
    (hpos : ∀ x ∈ X, 1 ≤ x * r ^ x / t ∧ x * r ^ x / t ≤ T)
    (hπ : Set.InjOn (fun x => x * r ^ x / t) X) (hφ : Set.InjOn (fun x => x * r ^ x % t) X)
    (himage : X.image (fun x => x * r ^ x % t) = insert 0 (X.erase u0))
    (hT : ∃ x ∈ X, x * r ^ x / t = T) (hlen : T + 1 = r ^ u0 + X.card) :
    IsSolution (r ^ t) 1 ((List.range (T + 1)).reverse.map (chainDigit r t u0 X)) := by
  set b := r ^ t with hb
  set f := chainDigit r t u0 X with hfdef
  set φ : ℕ → ℕ := fun x => x * r ^ x % t with hφdef
  set π : ℕ → ℕ := fun x => x * r ^ x / t with hπdef
  have hr0 : 0 < r := by omega
  have ht : 1 ≤ t := by have := hX u0 hu0; omega
  have hφt : ∀ x, φ x < t := fun x => Nat.mod_lt _ (by omega)
  -- the fibre of a position has at most one element
  have hfib : ∀ k, X.filter (fun x => π x = k) = ∅ ∨
      ∃ a ∈ X, π a = k ∧ X.filter (fun x => π x = k) = {a} := by
    intro k
    rcases (X.filter (fun x => π x = k)).eq_empty_or_nonempty with h | ⟨a, ha⟩
    · exact Or.inl h
    · obtain ⟨haX, hak⟩ := Finset.mem_filter.1 ha
      refine Or.inr ⟨a, haX, hak, Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun y hy => ?_⟩⟩
      obtain ⟨hyX, hyk⟩ := Finset.mem_filter.1 hy
      exact hπ hyX haX (hyk.trans hak.symm)
  have hfib0 : X.filter (fun x => π x = 0) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun x hx => by have := (hpos x hx).1; simp only [π]; omega
  have hf : ∀ k, f k = (if k = 0 then r ^ u0 else 0) + ∑ x ∈ X.filter (fun x => π x = k),
      r ^ φ x := by
    intro k
    by_cases hk : k = 0
    · subst hk; simp [hfdef, chainDigit, hfib0]
    · simp [hfdef, chainDigit, hk, φ, π]
  -- the value of a placed digit
  have hval : ∀ x, r ^ φ x * b ^ π x = w 1 (r ^ x) := by
    intro x
    rw [w_one_eq_pow, hb, ← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    simp only [φ, π]
    exact Nat.mod_add_div _ _
  have hmaps : ∀ x ∈ X, π x ∈ Finset.range (T + 1) := fun x hx =>
    Finset.mem_range.2 (by have := (hpos x hx).2; simp only [π]; omega)
  -- `P = r^(u_0) + ∑_X w(r^x)`
  have hP : P b ((List.range (T + 1)).reverse.map f) = r ^ u0 + ∑ x ∈ X, w 1 (r ^ x) := by
    rw [P_map_range]
    simp only [hf, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    have h1 : ∑ k ∈ Finset.range (T + 1), (if k = 0 then r ^ u0 else 0) * b ^ k = r ^ u0 := by
      simp [ite_mul]
    rw [h1, ← Finset.sum_fiberwise_of_maps_to hmaps (fun x => w 1 (r ^ x))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x hx => ?_
    rw [← hval x, (Finset.mem_filter.1 hx).2]
  -- `F + |X| = w(r^(u_0)) + ∑_X w(r^(φ x)) + T`
  have hcardX : ∑ k ∈ Finset.range (T + 1), (X.filter (fun x => π x = k)).card = X.card :=
    (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hpoint : ∀ k ∈ Finset.range (T + 1),
      w 1 (f k) + (X.filter (fun x => π x = k)).card =
        (if k = 0 then w 1 (r ^ u0) else 0) +
          ∑ x ∈ X.filter (fun x => π x = k), w 1 (r ^ φ x) + (if k = 0 then 0 else 1) := by
    intro k _
    by_cases hk : k = 0
    · subst hk; simp [hf, hfib0]
    rcases hfib k with h | ⟨a, -, -, h⟩
    · simp [hf, hk, h, w_zero]
    · simp [hf, hk, h]
  have hF : Fs 1 ((List.range (T + 1)).reverse.map f) + X.card =
      w 1 (r ^ u0) + ∑ x ∈ X, w 1 (r ^ φ x) + T := by
    rw [Fs_reverse_map_range, ← hcardX, ← Finset.sum_add_distrib, Finset.sum_congr rfl hpoint,
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_fiberwise_of_maps_to hmaps (fun x => w 1 (r ^ φ x))]
    have h1 : ∑ k ∈ Finset.range (T + 1), (if k = 0 then w 1 (r ^ u0) else 0) = w 1 (r ^ u0) := by
      simp
    have h2 : ∑ k ∈ Finset.range (T + 1), (if k = 0 then 0 else 1) = T := by
      rw [Finset.sum_range_succ']; simp
    rw [h1, h2]
  -- `∑_X w(r^(φ x)) + w(r^(u_0)) = 1 + ∑_X w(r^x)`
  have hpay : ∑ x ∈ X, w 1 (r ^ φ x) + w 1 (r ^ u0) = 1 + ∑ x ∈ X, w 1 (r ^ x) := by
    have h1 : ∑ x ∈ X, w 1 (r ^ φ x) = ∑ y ∈ X.image φ, w 1 (r ^ y) :=
      (Finset.sum_image (f := fun y => w 1 (r ^ y)) fun x hx y hy h => hφ hx hy h).symm
    have h0 : (0 : ℕ) ∉ X.erase u0 := fun h => by
      have := (hX 0 (Finset.mem_of_mem_erase h)).1; omega
    rw [h1, himage, Finset.sum_insert h0, pow_zero, w_one, add_assoc,
      Finset.sum_erase_add _ _ hu0]
  obtain ⟨x0, hx0, hx0T⟩ := hT
  refine ⟨fun d hd => ?_, fun h => ?_, ?_⟩
  · -- digits are below `b`
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hd
    rw [hf]
    by_cases hk : k = 0
    · subst hk
      simp only [ite_true, hfib0, Finset.sum_empty, add_zero]
      exact Nat.pow_lt_pow_right (by omega) (hX u0 hu0).2
    · simp only [hk, ite_false, zero_add]
      rcases hfib k with h | ⟨a, -, -, h⟩
      · rw [h, Finset.sum_empty]; exact pow_pos hr0 _
      · rw [h, Finset.sum_singleton]; exact Nat.pow_lt_pow_right (by omega) (hφt a)
  · -- the leading digit is `f T ≠ 0`
    have hT1 : 1 ≤ T := hx0T ▸ (hpos x0 hx0).1
    have hhead : ((List.range (T + 1)).reverse.map f).head h = f T := by
      simp [List.range_succ]
    rw [hhead, hf]
    simp only [show T ≠ 0 by omega, ite_false, zero_add]
    rcases hfib T with h' | ⟨a, -, -, h'⟩
    · exact absurd (Finset.mem_filter.2 ⟨hx0, hx0T⟩) (by rw [h']; simp)
    · rw [h', Finset.sum_singleton]; exact (pow_pos hr0 _).ne'
  · -- the value equals the weight sum
    rw [hP]
    omega

/-- The 11-digit solution of base 64 (section 15.5): the chain `3 → 0` (`8` at position 0, `1`
at position 4) with the self-paying digits 4 and 16 (the 1-cycles 2 and 4 of `φ`), and 7 zeros. -/
example : IsSolution (2 ^ 6) 1
    ((List.range (10 + 1)).reverse.map (chainDigit 2 6 3 {2, 3, 4})) := by
  refine theorem15_14 (u0 := 3) (by norm_num) (by decide) (by decide) (by decide) ?_ ?_ (by decide)
    ⟨4, by decide, by decide⟩ (by decide)
  · intro x hx y hy h
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
  · intro x hx y hy h
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all

end Munchausen
