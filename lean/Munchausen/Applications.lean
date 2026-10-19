import Munchausen.ThreeDigits

/-!
# Connections to other fields: the elementary results of chapter 30

* Section 30.1: the shifted weights `g(x) = w(x) - x` grow faster than `2 x g(x - 1)`
  (Lemma 30.1), so the small digits are dissociated (Lemma 30.2), and the largest digit
  allowed at length `d` lies between `d - 1` and `2 d - 5` (Lemma 30.4).
* Section 30.2: the collision bound behind Proposition 30.7, and the primes `p` of
  Corollary 30.11 (2), for which no `(p, c)` with `2 ≤ c ≤ p - 1` is a solution.
* Section 30.3: two-digit narcissistic numbers and the representations of `b^2 + 1` as a
  sum of two squares (Theorem 30.12, partial), and the divisor pairing of Proposition 30.14.
-/

open Finset

namespace Munchausen

/-! ### Section 30.1: dissociation of the small digits -/

/-- The shifted weight `g(x) = w(x) - x` of section 30.1.1: `g(0) = m`, `g(1) = 0` and
`g(x) = x^x - x` for `x ≥ 2`. -/
def g (m x : ℕ) : ℕ := w m x - x

lemma g_of_ne_zero (m : ℕ) {x : ℕ} (hx : x ≠ 0) : g m x = x ^ x - x := by
  rw [g, w_of_ne_zero m hx]

/-- `2 k^k ≤ (k + 1)^k`, that is `(1 + 1/k)^k ≥ 2`. -/
lemma two_mul_pow_le_succ_pow (k : ℕ) (hk : 1 ≤ k) : 2 * k ^ k ≤ (k + 1) ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have := pow_succ_ge (n + 1) n
  have e : (n + 1) * (n + 1) ^ n = (n + 1) ^ (n + 1) := by ring
  omega

/-- **Lemma 30.1** (section 30.1.2). For `z ≥ 3`, `g(z) ≥ 2 z g(z - 1)`. -/
theorem lemma30_1 (m : ℕ) {z : ℕ} (hz : 3 ≤ z) : 2 * z * g m (z - 1) ≤ g m z := by
  obtain ⟨k, rfl⟩ : ∃ k, z = k + 1 := ⟨z - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [g_of_ne_zero m (by omega), g_of_ne_zero m (by omega)]
  have h1 := two_mul_pow_le_succ_pow k (by omega)
  have h2 : (k + 1) ^ (k + 1) = (k + 1) * (k + 1) ^ k := by ring
  have h3 : k ≤ k ^ k := by
    calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 2 * (k + 1) * k ^ k ≤ (k + 1) ^ (k + 1) := by rw [h2]; nlinarith
  have h5 : 2 * (k + 1) * (k ^ k - k) + 2 * (k + 1) * k = 2 * (k + 1) * k ^ k := by
    rw [← mul_add, Nat.sub_add_cancel h3]
  have h6 : k + 1 ≤ 2 * (k + 1) * k := by nlinarith
  omega

lemma g_pos {m z : ℕ} (hz : 2 ≤ z) : 0 < g m z := by
  rw [g_of_ne_zero m (by omega)]
  have : z ^ 1 < z ^ z := Nat.pow_lt_pow_right (by omega) (by omega)
  simp only [pow_one] at this
  omega

/-- `g` is monotone from 2 on. -/
lemma g_mono {m a c : ℕ} (ha : 2 ≤ a) (hac : a ≤ c) : g m a ≤ g m c := by
  induction c, hac using Nat.le_induction with
  | base => exact le_rfl
  | succ c hc ih =>
    have := lemma30_1 m (z := c + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    calc g m a ≤ g m c := ih
      _ ≤ 2 * (c + 1) * g m c := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ g m (c + 1) := this

/-- A sum of `S ≤ 2 z0 + 1` weights from `[z0, y]` stays below `g(y + 1)`. -/
lemma sum_lt_g_succ {m z0 y S : ℕ} (hz0 : 2 ≤ z0) (hy : z0 ≤ y) (hS : S ≤ 2 * z0 + 1) :
    S * g m y < g m (y + 1) := by
  have h1 := lemma30_1 m (z := y + 1) (by omega)
  simp only [Nat.add_sub_cancel] at h1
  have hpos := g_pos (m := m) (z := y + 1) (by omega)
  rcases Nat.eq_zero_or_pos (g m y) with h0 | h0
  · rw [h0, mul_zero]; exact hpos
  · calc S * g m y < 2 * (y + 1) * g m y := Nat.mul_lt_mul_of_pos_right (by omega) h0
      _ ≤ g m (y + 1) := h1

lemma sum_mul_g_le {m z0 y : ℕ} (hz0 : 2 ≤ z0) (c : ℕ → ℕ) :
    ∑ z ∈ Icc z0 y, c z * g m z ≤ (∑ z ∈ Icc z0 y, c z) * g m y := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun z hz => ?_
  rw [Finset.mem_Icc] at hz
  exact Nat.mul_le_mul_left _ (g_mono (by omega) hz.2)

/-- **Lemma 30.2** (dissociation, section 30.1.2). Let `2 ≤ z0` and let `c, c'` be count vectors
on `Z = {z0, ..., y}` with the same total `n ≤ 2 z0 + 1`. If their weighted sums
`∑ c_z g(z)` agree, then `c = c'` on `Z`. -/
theorem lemma30_2 {m z0 : ℕ} (hz0 : 2 ≤ z0) {c c' : ℕ → ℕ} (y : ℕ)
    (hn : ∑ z ∈ Icc z0 y, c z = ∑ z ∈ Icc z0 y, c' z)
    (hle : ∑ z ∈ Icc z0 y, c z ≤ 2 * z0 + 1)
    (hg : ∑ z ∈ Icc z0 y, c z * g m z = ∑ z ∈ Icc z0 y, c' z * g m z) :
    ∀ z ∈ Icc z0 y, c z = c' z := by
  induction y with
  | zero => intro z hz; simp only [Finset.mem_Icc] at hz; omega
  | succ y ih =>
    rcases Nat.lt_or_ge (y + 1) z0 with hlt | hge
    · intro z hz; simp only [Finset.mem_Icc] at hz; omega
    rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · subst heq
      intro z hz
      have hz' : z = y + 1 := by simp only [Finset.mem_Icc] at hz; omega
      rw [Finset.Icc_self, Finset.sum_singleton, Finset.sum_singleton] at hn
      rw [hz']; exact hn
    have hy : z0 ≤ y := by omega
    simp only [Finset.sum_Icc_succ_top (show z0 ≤ y + 1 by omega)] at hn hle hg
    set S := ∑ z ∈ Icc z0 y, c z
    set S' := ∑ z ∈ Icc z0 y, c' z
    set G := ∑ z ∈ Icc z0 y, c z * g m z
    set G' := ∑ z ∈ Icc z0 y, c' z * g m z
    have hG : G ≤ S * g m y := sum_mul_g_le hz0 c
    have hG' : G' ≤ S' * g m y := sum_mul_g_le hz0 c'
    have hS : S * g m y < g m (y + 1) := sum_lt_g_succ hz0 hy (by omega)
    have hS' : S' * g m y < g m (y + 1) := sum_lt_g_succ hz0 hy (by omega)
    have htop : c (y + 1) = c' (y + 1) := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : G' + (c (y + 1) + 1) * g m (y + 1) ≤ G + c' (y + 1) * g m (y + 1) := by
          have := Nat.mul_le_mul_right (g m (y + 1)) (show c (y + 1) + 1 ≤ c' (y + 1) by omega)
          nlinarith
        nlinarith
      · have : G + (c' (y + 1) + 1) * g m (y + 1) ≤ G' + c (y + 1) * g m (y + 1) := by
          have := Nat.mul_le_mul_right (g m (y + 1)) (show c' (y + 1) + 1 ≤ c (y + 1) by omega)
          nlinarith
        nlinarith
    rw [htop] at hn hg
    have ih' := ih (by omega) (by omega) (by omega)
    intro z hz
    rcases Nat.lt_or_ge z (y + 1) with hz1 | hz1
    · exact ih' z (by simp only [Finset.mem_Icc] at hz ⊢; omega)
    · have : z = y + 1 := by simp only [Finset.mem_Icc] at hz; omega
      rw [this]; exact htop

/-- **Lemma 30.2**, modulo `Q`: if moreover `n g(y) < Q`, congruent weighted sums are equal, so
the count vectors agree. -/
theorem lemma30_2_mod {m z0 Q : ℕ} (hz0 : 2 ≤ z0) {c c' : ℕ → ℕ} (y : ℕ)
    (hn : ∑ z ∈ Icc z0 y, c z = ∑ z ∈ Icc z0 y, c' z)
    (hle : ∑ z ∈ Icc z0 y, c z ≤ 2 * z0 + 1)
    (hQ : (∑ z ∈ Icc z0 y, c z) * g m y < Q)
    (hg : ∑ z ∈ Icc z0 y, c z * g m z ≡ ∑ z ∈ Icc z0 y, c' z * g m z [MOD Q]) :
    ∀ z ∈ Icc z0 y, c z = c' z := by
  refine lemma30_2 hz0 y hn hle (Nat.ModEq.eq_of_lt_of_lt hg ?_ ?_)
  · exact (sum_mul_g_le hz0 c).trans_lt hQ
  · exact (sum_mul_g_le hz0 c').trans_lt (by rwa [← hn])

/-- **Lemma 30.4**, upper part (section 30.1.4). Let `b ≥ 12` and `b ≤ 2 d`. A digit `x` with
`x^x < b^d` satisfies `x ≤ 2 d - 5`, that is `(M_d + 1)/2 ≤ d - 2`. -/
theorem lemma30_4 {b d x : ℕ} (hb : 12 ≤ b) (hbd : b ≤ 2 * d) (hx : x ^ x < b ^ d) :
    x + 4 < 2 * d := by
  by_contra hcon
  have hx8 : 8 ≤ x := by omega
  -- `x^(2x) < b^(2d) ≤ b^(x+4) ≤ (2x)^(x+4)`
  have h1 : x ^ (2 * x) < b ^ (x + 4) := by
    calc x ^ (2 * x) = (x ^ x) ^ 2 := by ring
      _ < (b ^ d) ^ 2 := Nat.pow_lt_pow_left hx (by norm_num)
      _ = b ^ (2 * d) := by ring
      _ ≤ b ^ (x + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : b ^ (x + 4) ≤ (2 * x) ^ (x + 4) := Nat.pow_le_pow_left (by omega) _
  have h3 : x ^ (2 * x) = x ^ (x + 4) * x ^ (x - 4) := by
    rw [← pow_add]; congr 1; omega
  have h4 : (2 * x) ^ (x + 4) = 2 ^ (x + 4) * x ^ (x + 4) := mul_pow _ _ _
  have hpos : 0 < x ^ (x + 4) := by positivity
  have h5 : x ^ (x - 4) < 2 ^ (x + 4) := by
    have : x ^ (x + 4) * x ^ (x - 4) < x ^ (x + 4) * 2 ^ (x + 4) := by
      rw [← h3, mul_comm (x ^ (x + 4)), ← h4]; exact h1.trans_le h2
    exact Nat.lt_of_mul_lt_mul_left this
  have h6 : 2 ^ (x + 4) ≤ x ^ (x - 4) := by
    calc 2 ^ (x + 4) ≤ 2 ^ (3 * (x - 4)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 ^ (x - 4) := by rw [pow_mul]; norm_num
      _ ≤ x ^ (x - 4) := Nat.pow_le_pow_left hx8 _
  omega

/-- **Lemma 30.4**, lower part: in a base `b ≥ 2`, every digit `x < b` with `x ≤ d` (and
`d ≥ 1`) has `x^x < b^d`, so `M_d ≥ d - 1` and, for `d ≥ ⌈b/2⌉`, `M_d ≥ b/2`. -/
theorem lemma30_4_allowed {b d x : ℕ} (hb : 2 ≤ b) (hxb : x < b) (hxd : x ≤ d) (hd : 1 ≤ d) :
    x ^ x < b ^ d := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp only [pow_zero]; exact Nat.one_lt_pow (by omega) (by omega)
  · calc x ^ x ≤ x ^ d := Nat.pow_le_pow_right hx hxd
      _ < b ^ d := Nat.pow_lt_pow_left hxb (by omega)

/-! ### Section 30.2: the self-power map modulo a prime -/

/-- Section 30.2.4: for `c ≥ 1`, the 2-digit string `(a, c)` has `a ∣ w(c) - c` exactly when
`c` is a fixed point of `x ↦ x^x` modulo `a`. -/
theorem dvd_g_iff_modEq {a c : ℕ} (m : ℕ) (hc : c ≠ 0) : a ∣ g m c ↔ c ^ c ≡ c [MOD a] := by
  rw [g_of_ne_zero m hc]
  have : c ≤ c ^ c := le_w hc |>.trans_eq (w_of_ne_zero 1 hc)
  exact (Nat.modEq_iff_dvd' this).symm.trans Nat.ModEq.comm

/-- A divisor of `2 q` with `q` prime is `1`, `2`, `q` or `2 q`. -/
lemma dvd_two_mul_prime {d q : ℕ} (hq : q.Prime) (hd : d ∣ 2 * q) :
    d = 1 ∨ d = 2 ∨ d = q ∨ d = 2 * q := by
  rcases (Nat.dvd_mul.1 hd) with ⟨d1, d2, h1, h2, rfl⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).1 h2 with rfl | rfl <;> simp

/-- **Corollary 30.11 (2)** (section 30.2.4), the argument of Kurlberg, Luca and Shparlinski.
If `p ≡ 3 (mod 8)` and `(p - 1)/2` is prime, then `x ↦ x^x` has no fixed point modulo `p` in
`2 ≤ c ≤ p - 1`. -/
theorem corollary30_11_two {p c : ℕ} [hp : Fact p.Prime] (h8 : p % 8 = 3)
    (hq : ((p - 1) / 2).Prime) (hc2 : 2 ≤ c) (hcp : c ≤ p - 1) : ¬ c ^ c ≡ c [MOD p] := by
  intro hfix
  set q := (p - 1) / 2 with hqdef
  have hpq : p = 2 * q + 1 := by omega
  have hp2 : p ≠ 2 := by omega
  set u : ZMod p := (c : ZMod p) with hu
  have hu0 : u ≠ 0 := by
    rw [hu, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  -- `u^(c-1) = 1`
  have hfix' : u ^ (c - 1) = 1 := by
    have h1 : u ^ c = u := by
      rw [hu, ← Nat.cast_pow]; exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hfix
    have h2 : u ^ c = u ^ (c - 1) * u := by rw [← pow_succ]; congr 1; omega
    rw [h2] at h1
    exact mul_right_cancel₀ hu0 (h1.trans (one_mul u).symm)
  have hcard : u ^ (2 * q) = 1 := by
    have := ZMod.pow_card_sub_one_eq_one hu0
    rwa [show p - 1 = 2 * q by omega] at this
  have hd1 : orderOf u ∣ c - 1 := orderOf_dvd_of_pow_eq_one hfix'
  have hd2 : orderOf u ∣ 2 * q := orderOf_dvd_of_pow_eq_one hcard
  have hcast : ∀ n : ℕ, n < p → (n : ZMod p) = 1 → n = 1 := by
    intro n hn h
    have := (ZMod.natCast_eq_natCast_iff' n 1 p).1 (by simpa using h)
    rwa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)] at this
  rcases dvd_two_mul_prime hq hd2 with h | h | h | h
  · -- `u = 1`
    rw [orderOf_eq_one_iff] at h
    have := hcast c (by omega) h
    omega
  · -- `u^2 = 1`, so `u = -1` and `c = p - 1`, but then `c - 1` is odd
    have hsq : u ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one u
    have hsq' : u * u = 1 := by rw [← sq]; exact hsq
    rcases mul_self_eq_one_iff.1 hsq' with h1 | h1
    · have := hcast c (by omega) h1; omega
    · have hc : u + 1 = 0 := by rw [h1]; ring
      have : p ∣ c + 1 :=
        (ZMod.natCast_eq_zero_iff (c + 1) p).1 (by push_cast; exact hc)
      have hcp' : c = p - 1 := by
        have := Nat.le_of_dvd (by omega) this
        omega
      rw [h] at hd1
      omega
  · -- `ord u = q`, so `c = q + 1 = 1/2`, and `2^q = 1` makes 2 a square
    rw [h] at hd1
    have hc : c = q + 1 := by
      obtain ⟨t, ht⟩ := hd1
      rcases t with _ | _ | t
      · omega
      · omega
      · have : 2 * q ≤ q * (t + 1 + 1) := by nlinarith
        omega
    have huq : u ^ q = 1 := by rw [← h]; exact pow_orderOf_eq_one u
    have h2u : (2 : ZMod p) * u = 1 := by
      rw [hu, hc]
      have : ((2 * (q + 1) : ℕ) : ZMod p) = ((1 + 1 * p : ℕ) : ZMod p) := by
        congr 1; omega
      push_cast at this
      rw [ZMod.natCast_self] at this
      simpa using this
    have h2q : (2 : ZMod p) ^ (p / 2) = 1 := by
      have : (2 : ZMod p) ^ q * u ^ q = 1 := by rw [← mul_pow, h2u, one_pow]
      rw [huq, mul_one] at this
      rwa [show p / 2 = q by omega]
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h0)
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hsq := (ZMod.euler_criterion p h20).2 h2q
    rw [ZMod.exists_sq_eq_two_iff hp2] at hsq
    omega
  · rw [h] at hd1
    have := Nat.le_of_dvd (by omega) hd1
    omega

/-- **Corollary 30.11 (2)** for solutions: if `p ≡ 3 (mod 8)` and `(p - 1)/2` is prime, then
no string `(p, c)` with `2 ≤ c ≤ p - 1` is a solution, in any base, under either convention. -/
theorem corollary30_11_two_solution {p c b m : ℕ} [Fact p.Prime] (h8 : p % 8 = 3)
    (hq : ((p - 1) / 2).Prime) (hc2 : 2 ≤ c) (hcp : c ≤ p - 1) : ¬ IsSolution b m [p, c] := by
  intro hs
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  obtain ⟨-, -, h⟩ := (isSolution_two_iff hp1).1 hs
  have hdvd : p ∣ g m c := by
    rw [g]
    have hpp : p ∣ p ^ p := dvd_pow_self p (by omega)
    exact (Nat.dvd_add_right hpp).1 (h ▸ dvd_mul_right p b)
  exact corollary30_11_two h8 hq hc2 hcp ((dvd_g_iff_modEq m (by omega)).1 hdvd)

/-- The units of `ZMod p` with order `t` contribute `(p - 1)/t` exponents: for `1 ≤ u < p`,
the `v < p - 1` with `u^v ≡ u (mod p)` are the `v ≡ 1` modulo the order of `u`. -/
lemma card_pow_modEq_self {p u : ℕ} [hp : Fact p.Prime] (hu1 : 1 ≤ u) (hup : u < p) :
    ((Finset.range (p - 1)).filter (fun v => u ^ v ≡ u [MOD p])).card =
      (p - 1) / orderOf (u : ZMod p) := by
  have hu0 : (u : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  set t := orderOf (u : ZMod p)
  have htd : t ∣ p - 1 := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hu0)
  have ht0 : 0 < t := Nat.pos_of_ne_zero fun h => by
    have := Nat.eq_zero_of_zero_dvd (h ▸ htd)
    have := hp.out.two_le
    omega
  obtain ⟨g, hg⟩ := hu0.isUnit
  have ht : t = orderOf g := by simp only [t, ← hg, orderOf_units]
  have hiff : ∀ v, u ^ v ≡ u [MOD p] ↔ v ≡ 1 [MOD t] := by
    intro v
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, ← hg, ht, ← pow_eq_pow_iff_modEq,
      ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_one]
  simp_rw [hiff]
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ ht0, Nat.mod_eq_zero_of_dvd htd]
  simp

/-- The units of `ZMod p`, grouped by their order: `∑_{1 ≤ u < p} (p-1)/ord(u)` is
`∑_{d ∣ p-1} φ(d) (p-1)/d`. -/
lemma sum_div_orderOf {p : ℕ} [hp : Fact p.Prime] :
    ∑ u ∈ Finset.Ico 1 p, (p - 1) / orderOf (u : ZMod p) =
      ∑ d ∈ (p - 1).divisors, d.totient * ((p - 1) / d) := by
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  -- reindex by the units
  have h1 : ∑ u ∈ Finset.Ico 1 p, (p - 1) / orderOf (u : ZMod p) =
      ∑ g : (ZMod p)ˣ, (p - 1) / orderOf g := by
    refine Finset.sum_nbij' (fun u => if h : (u : ZMod p) = 0 then 1 else Units.mk0 _ h)
      (fun g => (g : ZMod p).val) ?_ ?_ ?_ ?_ ?_
    · intro u _; exact Finset.mem_univ _
    · intro g _
      rw [Finset.mem_Ico]
      refine ⟨Nat.pos_of_ne_zero fun h => g.ne_zero ?_, ZMod.val_lt _⟩
      rwa [ZMod.val_eq_zero] at h
    · intro u hu
      rw [Finset.mem_Ico] at hu
      have hu0 : (u : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
      simp only [hu0, dite_false, Units.val_mk0, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt hu.2
    · intro g _
      have : ((g : ZMod p).val : ZMod p) ≠ 0 := by rw [ZMod.natCast_zmod_val]; exact g.ne_zero
      simp only [this, dite_false]
      ext; simp
    · intro u hu
      rw [Finset.mem_Ico] at hu
      have hu0 : (u : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
      simp only [hu0, dite_false]
      rw [← orderOf_units, Units.val_mk0]
  rw [h1]
  -- group by the order
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := (p - 1).divisors)
    (g := fun g : (ZMod p)ˣ => orderOf g)]
  · refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.sum_congr rfl (fun g hg => by rw [(Finset.mem_filter.1 hg).2]), Finset.sum_const,
      smul_eq_mul]
    congr 1
    exact IsCyclic.card_orderOf_eq_totient (hcard ▸ Nat.dvd_of_mem_divisors hd)
  · intro g _
    rw [Nat.mem_divisors]
    exact ⟨hcard ▸ orderOf_dvd_card, by have := hp.out.two_le; omega⟩

/-- Section 30.2.4: for `c ≥ 1`, whether `c^c ≡ c (mod p)` depends only on `u = c mod p` and
`c mod (p - 1)`: it holds when `u = 0`, and otherwise exactly when `u^(c mod (p-1)) ≡ u`. So
the solutions are periodic modulo `p (p - 1)`. -/
lemma pow_self_modEq_self_iff {p c : ℕ} [hp : Fact p.Prime] (hc : 1 ≤ c) :
    c ^ c ≡ c [MOD p] ↔ c % p = 0 ∨ (c % p) ^ (c % (p - 1)) ≡ c % p [MOD p] := by
  have hp2 := hp.out.two_le
  rcases Nat.eq_zero_or_pos (c % p) with h0 | hpos
  · simp only [h0, true_or, iff_true]
    have hdvd : p ∣ c := Nat.dvd_of_mod_eq_zero h0
    exact ((Nat.modEq_zero_iff_dvd.2 (hdvd.trans (dvd_pow_self c (by omega)))).trans
      (Nat.modEq_zero_iff_dvd.2 hdvd).symm)
  · simp only [hpos.ne', false_or]
    have hcop' : Nat.Coprime (c % p) p := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h =>
        absurd (Nat.le_of_dvd hpos h) (by have := Nat.mod_lt c (show p > 0 by omega); omega)
    -- `u^(p-1) ≡ 1`, so `u^c ≡ u^(c mod (p-1))`
    have hferm : (c % p) ^ (p - 1) ≡ 1 [MOD p] := by
      have := Nat.ModEq.pow_totient hcop'
      rwa [Nat.totient_prime hp.out] at this
    have hpow : (c % p) ^ c ≡ (c % p) ^ (c % (p - 1)) [MOD p] := by
      have e : (c % p) ^ c = ((c % p) ^ (p - 1)) ^ (c / (p - 1)) * (c % p) ^ (c % (p - 1)) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      rw [e]
      have := (hferm.pow (c / (p - 1))).mul_right ((c % p) ^ (c % (p - 1)))
      rwa [one_pow, one_mul] at this
    have hcc : c ^ c ≡ (c % p) ^ c [MOD p] := ((Nat.mod_modEq c p).symm).pow c
    have hcu : c ≡ c % p [MOD p] := (Nat.mod_modEq c p).symm
    constructor
    · intro h
      exact (hpow.symm.trans hcc.symm).trans (h.trans hcu)
    · intro h
      exact (hcc.trans hpow).trans (h.trans hcu.symm)

/-- **Proposition 30.10** (section 30.2.4). Let `p` be prime. Among `1 ≤ c ≤ p (p - 1)`, one
period, the number of `c` with `c^c ≡ c (mod p)` is `(p - 1) (1 + ∑_{d ∣ p-1} φ(d)/d)`. -/
theorem prop30_10 (p : ℕ) [hp : Fact p.Prime] :
    ((Finset.Icc 1 (p * (p - 1))).filter (fun c => c ^ c ≡ c [MOD p])).card =
      (p - 1) + ∑ d ∈ (p - 1).divisors, d.totient * ((p - 1) / d) := by
  have hp2 := hp.out.two_le
  have hcop : Nat.Coprime p (p - 1) := by
    have : Nat.Coprime (p - 1) p := by
      have := Nat.coprime_self_add_right.2 (Nat.coprime_one_right (p - 1))
      rwa [show p - 1 + 1 = p by omega] at this
    exact this.symm
  -- a residue condition: `c^c ≡ c` depends on `c mod p` and `c mod (p - 1)`
  set R : ℕ × ℕ → Prop := fun uv => uv.1 = 0 ∨ uv.1 ^ uv.2 ≡ uv.1 [MOD p]
  have hR : ∀ c, 1 ≤ c → (c ^ c ≡ c [MOD p] ↔ R (c % p, c % (p - 1))) :=
    fun c hc => pow_self_modEq_self_iff hc
  -- count the pairs `(u, v)`
  set N := p * (p - 1)
  have hN : 0 < N := Nat.mul_pos (by omega) (by omega)
  have hpairs : ((Finset.Icc 1 N).filter (fun c => c ^ c ≡ c [MOD p])).card =
      ((Finset.range p ×ˢ Finset.range (p - 1)).filter R).card := by
    have hmodN : ∀ c, 1 ≤ c → c ≤ N → (c % N = c ∧ c < N) ∨ (c = N ∧ c % N = 0) := by
      intro c h1 h2
      rcases Nat.lt_or_ge c N with h | h
      · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
      · exact Or.inr ⟨by omega, by rw [show c = N by omega, Nat.mod_self]⟩
    refine Finset.card_bij (fun c _ => (c % p, c % (p - 1))) ?_ ?_ ?_
    · intro c hc
      rw [Finset.mem_filter, Finset.mem_Icc] at hc
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩, (hR c hc.1.1).1 hc.2⟩
    · intro c hc c' hc' h
      rw [Finset.mem_filter, Finset.mem_Icc] at hc hc'
      simp only [Prod.mk.injEq] at h
      have hN' : c ≡ c' [MOD N] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h.1, h.2⟩
      unfold Nat.ModEq at hN'
      rcases hmodN c hc.1.1 hc.1.2 with h1 | h1 <;> rcases hmodN c' hc'.1.1 hc'.1.2 with h2 | h2 <;>
        omega
    · rintro ⟨u, v⟩ huv
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at huv
      set k := Nat.chineseRemainder hcop u v
      have hk : (k : ℕ) < N := Nat.chineseRemainder_lt_mul hcop u v (by omega) (by omega)
      set c := if (k : ℕ) = 0 then N else (k : ℕ)
      have hck : c ≡ k [MOD N] := by
        simp only [c]
        split_ifs with h0
        · rw [h0]; exact Nat.modEq_zero_iff_dvd.2 (dvd_refl N)
        · rfl
      have hcp : c % p = u := by
        have := ((Nat.modEq_and_modEq_iff_modEq_mul hcop).2 hck).1.trans k.2.1
        rw [Nat.ModEq, Nat.mod_eq_of_lt huv.1.1] at this
        exact this
      have hcq : c % (p - 1) = v := by
        have := ((Nat.modEq_and_modEq_iff_modEq_mul hcop).2 hck).2.trans k.2.2
        rw [Nat.ModEq, Nat.mod_eq_of_lt huv.1.2] at this
        exact this
      have hc1 : 1 ≤ c := by simp only [c]; split_ifs <;> omega
      have hcN : c ≤ N := by simp only [c]; split_ifs <;> omega
      refine ⟨c, ?_, by rw [hcp, hcq]⟩
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hc1, hcN⟩, (hR c hc1).2 (by rw [hcp, hcq]; exact huv.2)⟩
  rw [hpairs]
  -- sum over `u`
  have hrow : ((Finset.range p ×ˢ Finset.range (p - 1)).filter R).card =
      ∑ u ∈ Finset.range p, ((Finset.range (p - 1)).filter (fun v => R (u, v))).card := by
    rw [Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
    rfl
  rw [hrow, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h0 : ((Finset.range (p - 1)).filter (fun v => R (0, v))).card = p - 1 := by
    simp [R]
  rw [h0, ← sum_div_orderOf]
  congr 1
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_Ico] at hu
  rw [← card_pow_modEq_self hu.1 hu.2]
  congr 1
  have hu0 : u ≠ 0 := by omega
  exact Finset.filter_congr fun v _ => by simp only [R, hu0, false_or]

/-- The list of section 30.2.4 printed by Kurlberg, Luca and Shparlinski includes 7, but
`4^4 ≡ 4 (mod 7)`, so 7 has a small partner: `(7, 4)` is a solution in base
`(7^7 + 4^4 - 4)/7 = 117685`. -/
example : 4 ^ 4 ≡ 4 [MOD 7] := by decide

/-- **Proposition 30.7**, the counting core (section 30.2.2). For any map `f` from a finite set
`X` to an additive group, the pairs `(x, y)` with `f x + f y = r` are at most the collisions
`f x = f y`. Dividing by `|X|^2` gives `P(g(X_1) + g(X_2) = r) ≤ N_M(Q)/(M+1)^2`. -/
theorem prop30_7 {α A : Type*} [DecidableEq A] [AddCommGroup A] (X : Finset α) (f : α → A)
    (r : A) : ((X ×ˢ X).filter (fun xy => f xy.1 + f xy.2 = r)).card ≤
      ((X ×ˢ X).filter (fun xy => f xy.1 = f xy.2)).card := by
  classical
  set n : A → ℕ := fun a => (X.filter (fun y => f y = a)).card with hn
  have hrow : ∀ P : α → α → Prop, [∀ x y, Decidable (P x y)] →
      ((X ×ˢ X).filter (fun xy => P xy.1 xy.2)).card =
        ∑ x ∈ X, (X.filter (fun y => P x y)).card := by
    intro P _
    rw [Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  have h1 : ((X ×ˢ X).filter (fun xy => f xy.1 + f xy.2 = r)).card = ∑ x ∈ X, n (r - f x) := by
    rw [hrow (fun x y => f x + f y = r)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hn]
    congr 1
    ext y; simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h, h'⟩ <;> refine ⟨h, ?_⟩
    · rw [← h']; abel
    · rw [h']; abel
  have h2 : ((X ×ˢ X).filter (fun xy => f xy.1 = f xy.2)).card = ∑ x ∈ X, n (f x) := by
    rw [hrow (fun x y => f x = f y)]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hn]
    congr 1
    ext y; simp only [Finset.mem_filter]
    exact and_congr_right fun _ => eq_comm
  rw [h1, h2, Finset.sum_comp (fun a => n (r - a)) f, Finset.sum_comp n f]
  set T := X.image f
  simp only [smul_eq_mul]
  -- `2 n(a) n(r - a) ≤ n(a)^2 + n(r - a)^2`, and the second sum is at most the first
  have hsq : ∑ a ∈ T, n (r - a) * n (r - a) ≤ ∑ a ∈ T, n a * n a := by
    have hinj : Set.InjOn (fun a => r - a) T := fun a _ c _ h => by simpa using h
    rw [← Finset.sum_image (f := fun a => n a * n a) hinj]
    refine Finset.sum_le_sum_of_ne_zero fun a _ ha => ?_
    have : n a ≠ 0 := fun h => ha (by rw [h, zero_mul])
    obtain ⟨y, hy⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero this)
    rw [Finset.mem_filter] at hy
    exact Finset.mem_image.2 ⟨y, hy.1, hy.2⟩
  have hfib : ∀ a, (X.filter (fun x => f x = a)).card = n a := fun a => rfl
  simp only [hfib]
  have hamgm : ∀ a ∈ T, 2 * (n a * n (r - a)) ≤ n a * n a + n (r - a) * n (r - a) :=
    fun a _ => by nlinarith [sq_nonneg ((n a : ℤ) - n (r - a))]
  have := Finset.sum_le_sum hamgm
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at this
  omega

/-- **Proposition 30.6**, the forced primes (section 30.1.5): for a prime `p` and `d ≥ 1`,
`x^d ≡ x (mod p)` for every `x` exactly when `p - 1` divides `d - 1`. -/
theorem prop30_6_forced {p d : ℕ} [hp : Fact p.Prime] (hd : 1 ≤ d) :
    (∀ x : ZMod p, x ^ d = x) ↔ p - 1 ∣ d - 1 := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
    have h1 : (g : ZMod p) ^ (d - 1) = 1 := by
      have := h g
      rw [show d = d - 1 + 1 by omega, pow_succ] at this
      exact mul_right_cancel₀ g.ne_zero (this.trans (one_mul _).symm)
    have h2 : g ^ (d - 1) = 1 := Units.ext (by simpa using h1)
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h2
  · rintro ⟨t, ht⟩ x
    rcases eq_or_ne x 0 with rfl | hx
    · exact zero_pow (by omega)
    · rw [show d = (p - 1) * t + 1 by omega, pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one hx,
        one_pow, one_mul]

/-- **Proposition 30.6**, the size of the step: `p^d - p ≡ -p (mod p^2)` for `d ≥ 2`, so the
steps `x^d - x` generate exactly `p Z/p^e` when `p - 1 ∣ d - 1`. -/
theorem prop30_6_step {p d : ℕ} (hd : 2 ≤ d) : ((p : ℤ) ^ d - p) ≡ -p [ZMOD p ^ 2] := by
  have : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ d := pow_dvd_pow _ hd
  have h := (Int.modEq_zero_iff_dvd.2 this).sub_right (p : ℤ)
  rwa [zero_sub] at h

/-! ### Section 30.3: two-digit narcissistic numbers -/

/-- A 2-digit narcissistic number `(s1, s0)` in base `b` (section 30.3.1): `1 ≤ s1 < b`,
`s0 < b` and `s1 b + s0 = s1^2 + s0^2`, a 2-digit fixed point of the happy-number map. -/
def IsNarc2 (b s1 s0 : ℕ) : Prop := 1 ≤ s1 ∧ s1 < b ∧ s0 < b ∧ s1 * b + s0 = s1 ^ 2 + s0 ^ 2

instance (b s1 s0 : ℕ) : Decidable (IsNarc2 b s1 s0) := by unfold IsNarc2; infer_instance

/-- **Theorem 30.12**, the completed square (section 30.3.1). `(s1, s0)` is a 2-digit
narcissistic number in base `b` exactly when `s0 ≥ 2` and
`(2 s1 - b)^2 + (2 s0 - 1)^2 = b^2 + 1`. So these numbers correspond to the representations
`b^2 + 1 = A^2 + B^2` with `B ≥ 3` odd and `A ≡ b (mod 2)`. -/
theorem isNarc2_iff (b s1 s0 : ℕ) : IsNarc2 b s1 s0 ↔
    2 ≤ s0 ∧ (2 * s1 - b : ℤ) ^ 2 + (2 * s0 - 1) ^ 2 = b ^ 2 + 1 := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have h4' : (s1 : ℤ) * b + s0 = s1 ^ 2 + s0 ^ 2 := by exact_mod_cast h4
    refine ⟨?_, by linear_combination (-4) * h4'⟩
    by_contra hs0
    have : (s1 : ℤ) * b = s1 ^ 2 := by
      rcases (by omega : s0 = 0 ∨ s0 = 1) with rfl | rfl <;> push_cast at h4' <;> linarith
    have hs1 : (1 : ℤ) ≤ s1 := by exact_mod_cast h1
    have hb : (s1 : ℤ) < b := by exact_mod_cast h2
    nlinarith
  · rintro ⟨h0, h⟩
    have hs0 : (2 : ℤ) ≤ s0 := by exact_mod_cast h0
    have hs1 : (0 : ℤ) ≤ s1 := by positivity
    have hb0 : (0 : ℤ) ≤ b := by positivity
    -- `(2 s1 - b)^2 ≤ b^2 - 8`, so `|2 s1 - b| < b`
    have hA : (2 * s1 - b : ℤ) ^ 2 < b ^ 2 := by nlinarith
    have hB : (2 * s0 - 1 : ℤ) ^ 2 ≤ b ^ 2 + 1 := by nlinarith
    have hlt1 : (0 : ℤ) < s1 := by nlinarith [abs_lt_of_sq_lt_sq' hA hb0]
    have hlt2 : (s1 : ℤ) < b := by nlinarith [abs_lt_of_sq_lt_sq' hA hb0]
    have hlt3 : (s0 : ℤ) < b := by nlinarith
    refine ⟨by exact_mod_cast hlt1, by exact_mod_cast hlt2, by exact_mod_cast hlt3, ?_⟩
    have h4 : 4 * ((s1 : ℤ) * b + s0) = 4 * (s1 ^ 2 + s0 ^ 2) := by linear_combination (-1) * h
    have : (s1 : ℤ) * b + s0 = s1 ^ 2 + s0 ^ 2 := by linarith
    exact_mod_cast this

/-- Section 30.3.1: the solutions pair up by `s1 ↦ b - s1`, since `s1 b + s0 = s1^2 + s0^2`
reads `s0 (s0 - 1) = s1 (b - s1)`. -/
theorem IsNarc2.swap {b s1 s0 : ℕ} (h : IsNarc2 b s1 s0) : IsNarc2 b (b - s1) s0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by omega, by omega, h3, ?_⟩
  have h4' : (s1 : ℤ) * b + s0 = s1 ^ 2 + s0 ^ 2 := by exact_mod_cast h4
  have : ((b - s1 : ℕ) : ℤ) * b + s0 = ((b - s1 : ℕ) : ℤ) ^ 2 + s0 ^ 2 := by
    push_cast [Nat.cast_sub h2.le]; linear_combination h4'
  exact_mod_cast this

/-- **Corollary 30.13 (1)**. Every odd base `b ≥ 3` has the two 2-digit narcissistic numbers
`((b-1)/2, (b+1)/2)` and `((b+1)/2, (b+1)/2)`. -/
theorem corollary30_13_one {b : ℕ} (hb : 3 ≤ b) (hodd : Odd b) :
    IsNarc2 b ((b - 1) / 2) ((b + 1) / 2) ∧ IsNarc2 b ((b + 1) / 2) ((b + 1) / 2) := by
  obtain ⟨k, rfl⟩ := hodd
  have e1 : (2 * k + 1 - 1) / 2 = k := by omega
  have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [e1, e2]
  refine ⟨⟨by omega, by omega, by omega, by ring⟩, ⟨by omega, by omega, by omega, by ring⟩⟩

/-- The core of Corollary 30.13 (2): a representation `p = A^2 + B^2` of the prime
`p = b^2 + 1` with `|A| ≤ b - 2`, `B ≠ 0, ±b` cannot have `p ∣ A b - B`. -/
lemma not_dvd_of_prime_sq_add_sq {A B b p : ℤ} (hp : Prime p) (hpb : p = b ^ 2 + 1)
    (hAB : A ^ 2 + B ^ 2 = p) (hA1 : -(b - 2) ≤ A) (hA2 : A ≤ b - 2) (hB0 : B ≠ 0)
    (hBb : B ≠ b) (hBb' : B ≠ -b) (hdvd : p ∣ A * b - B) : False := by
  obtain ⟨t, ht⟩ := hdvd
  have hp1 : 1 < p := by
    rcases lt_or_ge p 2 with h | h
    · exfalso
      have : p = 1 := by nlinarith
      exact hp.not_isUnit (this ▸ isUnit_one)
    · omega
  -- `(A b - B)^2 + (A + B b)^2 = p^2`
  have hid : (A * b - B) ^ 2 + (A + B * b) ^ 2 = p ^ 2 := by rw [hpb] at hAB ⊢; nlinarith
  rw [ht] at hid
  have ht1 : t ^ 2 ≤ 1 := by
    by_contra h
    have : p ^ 2 * 2 ≤ p ^ 2 * t ^ 2 := by
      have : (2 : ℤ) ≤ t ^ 2 := by omega
      nlinarith
    nlinarith [sq_nonneg (A + B * b)]
  have htc : t = -1 ∨ t = 0 ∨ t = 1 := by
    have : -1 ≤ t ∧ t ≤ 1 := by constructor <;> nlinarith
    omega
  rcases htc with rfl | rfl | rfl
  · -- `A = -B b`, too large
    have : (A + B * b) ^ 2 = 0 := by nlinarith
    have hAB' : A = -(B * b) := by linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this]
    rcases lt_or_gt_of_ne hB0 with h | h <;> nlinarith
  · -- `A b = B`, then `A^2 = 1` and `B = ±b`
    have hAb : A * b = B := by linarith
    have hA : A ^ 2 * p = p := by rw [hpb] at hAB ⊢; rw [← hAb] at hAB; nlinarith
    have hA2' : A ^ 2 = 1 := by
      have := mul_right_cancel₀ (show p ≠ 0 by omega) (hA.trans (one_mul p).symm)
      exact this
    have hfac : (A - 1) * (A + 1) = 0 := by linear_combination hA2'
    rcases mul_eq_zero.1 hfac with h | h
    · exact hBb (by rw [← hAb, show A = 1 by linarith]; ring)
    · exact hBb' (by rw [← hAb, show A = -1 by linarith]; ring)
  · have : (A + B * b) ^ 2 = 0 := by nlinarith
    have hAB' : A = -(B * b) := by linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this]
    rcases lt_or_gt_of_ne hB0 with h | h <;> nlinarith

/-- **Corollary 30.13 (2)**, the direction that needs no factorization: if `b` is even and
`b^2 + 1` is prime, base `b` has no 2-digit narcissistic number. (The converse, a solution
for every even `b` with `b^2 + 1` composite, needs the count of Theorem 30.12.) -/
theorem corollary30_13_two {b s1 s0 : ℕ} (hb : Even b) (hp : (b ^ 2 + 1).Prime) :
    ¬ IsNarc2 b s1 s0 := by
  intro h
  obtain ⟨-, hsq⟩ := (isNarc2_iff b s1 s0).1 h
  obtain ⟨h1, h2, -, -⟩ := h
  obtain ⟨k, rfl⟩ := hb
  set p : ℤ := ((k + k : ℕ) : ℤ) ^ 2 + 1 with hpdef
  have hpZ : Prime p := by
    rw [hpdef]; exact_mod_cast Nat.prime_iff_prime_int.1 hp
  set A : ℤ := 2 * s1 - (k + k : ℕ)
  set B : ℤ := 2 * s0 - 1
  have hA1 : -(((k + k : ℕ) : ℤ) - 2) ≤ A := by simp only [A]; push_cast; omega
  have hA2 : A ≤ ((k + k : ℕ) : ℤ) - 2 := by simp only [A]; push_cast; omega
  have hB0 : B ≠ 0 := by simp only [B]; omega
  have hBb : B ≠ ((k + k : ℕ) : ℤ) := by simp only [B]; push_cast; omega
  have hBb' : B ≠ -((k + k : ℕ) : ℤ) := by simp only [B]; push_cast; omega
  have hprod : p ∣ (A * (k + k : ℕ) - B) * (A * (k + k : ℕ) + B) :=
    ⟨p - 1 - B ^ 2, by rw [hpdef] at hsq ⊢; linear_combination (((k + k : ℕ) : ℤ) ^ 2) * hsq⟩
  rcases hpZ.dvd_or_dvd hprod with hd | hd
  · exact not_dvd_of_prime_sq_add_sq hpZ rfl hsq hA1 hA2 hB0 hBb hBb' hd
  · refine not_dvd_of_prime_sq_add_sq (B := -B) hpZ rfl (by rw [neg_sq]; exact hsq) hA1 hA2
      (neg_ne_zero.2 hB0) (fun h => hBb' (by linarith)) (fun h => hBb (by linarith)) ?_
    rwa [sub_neg_eq_add]

/-- Base 10 has no 2-digit narcissistic number, since 101 is prime (section 30.3.1). -/
example (s1 s0 : ℕ) : ¬ IsNarc2 10 s1 s0 :=
  corollary30_13_two (by decide) (by norm_num)

/-- The divisor pairing in the proof of **Proposition 30.14**: `n^2 + 1` is not a square, so
its divisors pair up as `d, (n^2 + 1)/d` with exactly one of them at most `n`, and
`τ(n^2 + 1) = 2 #{d ≤ n : d ∣ n^2 + 1}`. -/
theorem card_divisors_sq_add_one {n : ℕ} (hn : 1 ≤ n) :
    (n ^ 2 + 1).divisors.card = 2 * ((n ^ 2 + 1).divisors.filter (· ≤ n)).card := by
  set N := n ^ 2 + 1 with hN
  have hcard := Finset.card_filter_add_card_filter_not (s := N.divisors) (· ≤ n)
  have hpair : ((N.divisors).filter (fun d => ¬ d ≤ n)).card =
      ((N.divisors).filter (· ≤ n)).card := by
    refine Finset.card_nbij' (N / ·) (N / ·) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd ⊢
      obtain ⟨⟨hdN, hN0⟩, hdn⟩ := hd
      refine ⟨⟨Nat.div_dvd_of_dvd hdN, hN0⟩, ?_⟩
      by_contra h
      have := Nat.div_mul_cancel hdN
      have : (n + 1) * (n + 1) ≤ N / d * d := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · intro d hd
      simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd ⊢
      obtain ⟨⟨hdN, hN0⟩, hdn⟩ := hd
      refine ⟨⟨Nat.div_dvd_of_dvd hdN, hN0⟩, ?_⟩
      intro h
      have := Nat.div_mul_cancel hdN
      have : N / d * d ≤ n * n := Nat.mul_le_mul h hdn
      nlinarith
    · intro d hd
      simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd
      exact Nat.div_div_self hd.1.1 hd.1.2
    · intro d hd
      simp only [Finset.coe_filter, Nat.mem_divisors, Set.mem_ofPred_eq] at hd
      exact Nat.div_div_self hd.1.1 hd.1.2
  omega

end Munchausen
