import Munchausen.Constructions

/-!
# Self-paying digits: moves and counts (sections 2.2, 8.3, 9.8 and 15.3)

* Proposition 2.3: under `0^0 = 0`, self-paying digits can be added to or removed from zero
  positions of a solution, one at a time or all at once (the core);

* a base with `C` self-paying digits is `r^t` with `t ≥ C + 1`, where `r` is its primitive
  root; so `C < log2 b` (Proposition 8.5) and the base is an `r^t` with `t ≥ C + 1`
  (Proposition 9.3, corrected form);
* Proposition 15.8: `r^t`, with `r` not a perfect power, has a self-paying digit exactly when
  `t` has a prime factor that does not divide `r`.
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

/-- **Proposition 2.3**, one move (section 2.2). Under `0^0 = 0`, if `n` has the digit 0 at
position `k` and `a` is self-paying at `k`, then `n` is a solution exactly when `n + a b^k`
is. Self-paying digits can be added to and removed from zero positions freely. -/
theorem isMunchausen_add_selfPaying {b n a k : ℕ} (hb : 2 ≤ b) (hk : digitAt b n k = 0)
    (h : SelfPaying b a k) : IsMunchausen b 0 n ↔ IsMunchausen b 0 (n + a * b ^ k) := by
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
  have hF : F b 0 (n + a * b ^ k) = F b 0 n + a * b ^ k := by
    have h2 := F_ofDigits_zero (b := b) (by omega) ((List.range L).map f)
      (fun d hd => by obtain ⟨i, -, rfl⟩ := List.mem_map.1 hd; exact hf i)
    rw [ofDigits_map_range, hval, Fs_map_range, hw, ← h.balance] at h2
    exact h2
  unfold IsMunchausen
  rw [hF]
  omega

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

end Munchausen
