import Munchausen.ThreeDigits
import Munchausen.Counting

/-!
# The members of the square class and 3-digit solutions in one base

Section 25.1.4 and 25.3 of the library. A 3-digit string `(p, q, x)` with
`R = 4 p (w(p) + w(q) - x) + q^2 = 0` is a *member*: `p = lam c^2`, `q = 2 lam c e` with `lam`
squarefree, and it is a solution in base `b` exactly when `x^x = lam (c b + e)^2`.

* Theorem 25.7 (i) for every `x`, with the parity conditions on `lam`;
* Proposition 25.16: a base has at most one member;
* Proposition 25.17: a base with a member has at most 3 three-digit solutions.
-/

namespace Munchausen

/-! ### Squarefree parts -/

/-- If `a^2 lam ∣ q^2` with `lam` squarefree, then `a lam ∣ q`. -/
lemma mul_dvd_of_sq_mul_dvd_sq {a lam q : ℕ} (hlam : Squarefree lam)
    (h : a ^ 2 * lam ∣ q ^ 2) : a * lam ∣ q := by
  obtain ⟨t, rfl⟩ : a ∣ q :=
    (Nat.pow_dvd_pow_iff two_ne_zero).1 (dvd_trans (Dvd.intro _ rfl) h)
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · have : lam ∣ t ^ 2 := by
      rw [mul_pow] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h
    exact Nat.mul_dvd_mul_left a ((hlam.dvd_pow_iff_dvd two_ne_zero).1 this)

/-- Two squarefree numbers whose ratio is a rational square are equal: `a Y^2 = b Z^2` with
`Y ≠ 0` gives `a = b`. -/
lemma squarefree_eq_of_mul_sq {a b Y Z : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hY : Y ≠ 0) (h : a * Y ^ 2 = b * Z ^ 2) : a = b := by
  obtain ⟨d, hd, -⟩ := isSquare_of_mul_sq hY
    (show (a * b) * Y ^ 2 = (b * Z) ^ 2 by
      calc (a * b) * Y ^ 2 = b * (a * Y ^ 2) := by ring
        _ = b * (b * Z ^ 2) := by rw [h]
        _ = (b * Z) ^ 2 := by ring)
  -- `a b = d^2`, so `a ∣ d`, `d = a k` and `b = a k^2`
  obtain ⟨k, rfl⟩ : a ∣ d := (ha.dvd_pow_iff_dvd two_ne_zero).1 ⟨b, by rw [← hd]⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  have hbk : b = a * k ^ 2 := by
    have : a * b = a * (a * k ^ 2) := by rw [hd]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) this
  have hk : IsUnit k := hb k ⟨a, by rw [hbk]; ring⟩
  rw [hbk, Nat.isUnit_iff.1 hk]
  ring

/-! ### Theorem 25.7 (i) -/

/-- **Theorem 25.7 (i)** (section 25.1.4). Let `(p, q, x)` be a 3-digit solution in base `b`
with `R = 0`, that is `4 p x = 4 p (w(p) + w(q)) + q^2`. Then `p = lam c^2` and
`q = 2 lam c e` with `lam` squarefree and `c ≥ 1`, `x = w(p) + w(q) + lam e^2`, and
`x^x = lam (c b + e)^2`. (That `x` is the last digit when `R = 0` is `R_pos_middle` and
`R_pos_leading`.) -/
theorem theorem25_7_i {b m p q x : ℕ} (hs : IsSolution b m [p, q, x])
    (hR : 4 * p * x = 4 * p * (w m p + w m q) + q ^ 2) :
    ∃ lam c e, Squarefree lam ∧ 1 ≤ c ∧ p = lam * c ^ 2 ∧ q = 2 * lam * c * e ∧
      x = w m p + w m q + lam * e ^ 2 ∧ x ^ x = lam * (c * b + e) ^ 2 := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  obtain ⟨lam, c, -, hc, hpc, hlam⟩ := Nat.sq_mul_squarefree_of_pos hp1
  -- `4 p ∣ q^2`, so `2 c lam ∣ q`
  have hdvd : 4 * p ∣ q ^ 2 := by
    have : 4 * p ∣ 4 * p * (w m p + w m q) + q ^ 2 := hR ▸ dvd_mul_right _ _
    exact (Nat.dvd_add_right (dvd_mul_right _ _)).1 this
  obtain ⟨e, he⟩ : 2 * c * lam ∣ q :=
    mul_dvd_of_sq_mul_dvd_sq hlam (by rw [← hpc] at hdvd; convert hdvd using 1; ring)
  have hq : q = 2 * lam * c * e := by rw [he]; ring
  have hp : p = lam * c ^ 2 := by rw [← hpc]; ring
  -- cancel `4 p` in `R = 0`
  have hx : x = w m p + w m q + lam * e ^ 2 := by
    have h4 : 4 * p * x = 4 * p * (w m p + w m q + lam * e ^ 2) := by
      rw [hR, hq, hp]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  have hx0 : x ≠ 0 := by
    have := one_le_w (m := m) (show p ≠ 0 by omega)
    omega
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one, w_of_ne_zero m hx0] at heq
  rw [show (1 : ℕ) + 1 = 2 from rfl] at heq
  refine ⟨lam, c, e, hlam, hc, hp, hq, hx, ?_⟩
  have : x ^ x = p * b ^ 2 + q * b + lam * e ^ 2 := by omega
  rw [this, hp, hq]
  ring

/-- **Theorem 25.7 (i)**, the parity conditions (section 25.1.4). If `x^x = lam Z^2` with
`lam` squarefree, then `lam = 1` for even `x`, and `x / lam` is a perfect square
for odd `x`. -/
theorem theorem25_7_i_parity {x lam Z : ℕ} (hx : x ≠ 0) (hlam : Squarefree lam)
    (h : x ^ x = lam * Z ^ 2) : (Even x → lam = 1) ∧ (Odd x → ∃ d, x = lam * d ^ 2) := by
  constructor
  · rintro ⟨k, hk⟩
    refine (squarefree_eq_of_mul_sq (Z := Z) squarefree_one hlam (pow_ne_zero k hx) ?_).symm
    rw [← h, one_mul, ← pow_mul, hk]
    ring_nf
  · rintro ⟨k, hk⟩
    obtain ⟨mu, f, -, hf, hfx, hmu⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hx)
    have hmu_eq : mu = lam := by
      refine squarefree_eq_of_mul_sq hmu hlam (Y := f * x ^ k) (Z := Z)
        (mul_ne_zero hf.ne' (pow_ne_zero k hx)) ?_
      rw [← h]
      calc mu * (f * x ^ k) ^ 2 = (f ^ 2 * mu) * (x ^ k) ^ 2 := by ring
        _ = x * (x ^ k) ^ 2 := by rw [hfx]
        _ = x ^ x := by rw [← pow_mul, ← pow_succ']; congr 1; omega
    exact ⟨f, by rw [← hfx, hmu_eq]; ring⟩

/-! ### Proposition 25.16 -/

/-- The value of a 3-digit member: `p b^2 ≤ x^x < (p + 1) b^2`, used for Propositions 25.16
and 25.17. -/
lemma member_bounds {b p q x lam c e : ℕ} (hs : IsSolution b 1 [p, q, x])
    (hp : p = lam * c ^ 2) (hq : q = 2 * lam * c * e) (hx : x = w 1 p + w 1 q + lam * e ^ 2)
    (hY : x ^ x = lam * (c * b + e) ^ 2) :
    x ^ x = p * b ^ 2 + q * b + lam * e ^ 2 ∧ p * b ^ 2 ≤ x ^ x ∧ x ^ x < (p + 1) * b ^ 2 := by
  have hxx : x ^ x = p * b ^ 2 + q * b + lam * e ^ 2 := by rw [hY, hp, hq]; ring
  have hqb := hs.lt_base q (by simp)
  have hxb := hs.lt_base x (by simp)
  have hL : lam * e ^ 2 ≤ x := by omega
  refine ⟨hxx, by omega, ?_⟩
  have e1 : (q + 1) * b ≤ b * b := Nat.mul_le_mul_right _ (by omega)
  have e2 : (p + 1) * b ^ 2 = p * b ^ 2 + b * b := by ring
  have e3 : (q + 1) * b = q * b + b := by ring
  omega

/-- **Proposition 25.16** (section 25.3.3). Under `0^0 = 1`, a base has at most one 3-digit
power-identity member: two 3-digit solutions `(p, q, x)`, `(p', q', x')` in base `b` with
`R = 0` are equal. -/
theorem prop25_16 {b p q x p' q' x' : ℕ} (hs : IsSolution b 1 [p, q, x])
    (hR : 4 * p * x = 4 * p * (w 1 p + w 1 q) + q ^ 2)
    (hs' : IsSolution b 1 [p', q', x'])
    (hR' : 4 * p' * x' = 4 * p' * (w 1 p' + w 1 q') + q' ^ 2) :
    [p, q, x] = [p', q', x'] := by
  obtain ⟨lam, c, e, hlam, hc, hpc, hqc, hxw, hY⟩ := theorem25_7_i hs hR
  obtain ⟨lam', c', e', hlam', hc', hpc', hqc', hxw', hY'⟩ := theorem25_7_i hs' hR'
  have hb := hs.lt_base x (by simp)
  have hqb := hs.lt_base q (by simp)
  have hqb' := hs'.lt_base q' (by simp)
  have hlam1 : 1 ≤ lam := Nat.pos_of_ne_zero hlam.ne_zero
  have hlam1' : 1 ≤ lam' := Nat.pos_of_ne_zero hlam'.ne_zero
  have heb : e < b := by
    have : e ≤ q := by rw [hqc]; nlinarith [Nat.mul_le_mul hlam1 hc]
    omega
  have heb' : e' < b := by
    have : e' ≤ q' := by rw [hqc']; nlinarith [Nat.mul_le_mul hlam1' hc']
    omega
  -- equal last digits give equal members
  have key : x = x' → [p, q, x] = [p', q', x'] := by
    intro hxx
    subst hxx
    have hZ : c * b + e ≠ 0 := by
      have : c * b ≠ 0 := mul_ne_zero (by omega) (by omega)
      omega
    have hll : lam = lam' := squarefree_eq_of_mul_sq hlam hlam' hZ (hY.symm.trans hY')
    subst hll
    have h1 : c * b + e = c' * b + e' :=
      Nat.pow_left_injective two_ne_zero
        (Nat.eq_of_mul_eq_mul_left (by omega) (hY.symm.trans hY'))
    have hcc : c = c' := by
      have := congrArg (· / b) h1
      rwa [Nat.mul_comm c, Nat.mul_comm c', Nat.mul_add_div (by omega),
        Nat.mul_add_div (by omega), Nat.div_eq_of_lt heb, Nat.div_eq_of_lt heb'] at this
    subst hcc
    have hee : e = e' := by omega
    subst hee
    rw [hpc, hqc, hpc', hqc']
  by_contra hne
  have hxx : x ≠ x' := fun h => hne (key h)
  -- a larger last digit weighs too much: `x' x^x ≤ x'^x'`, but `x'^x' < (p' + 1) b^2`
  have bound : ∀ {p x p' q' x' : ℕ}, IsSolution b 1 [p', q', x'] → 1 ≤ p → 1 ≤ x →
      p * b ^ 2 ≤ x ^ x → p' + 1 ≤ x' → x < x' → False := by
    intro p x p' q' x' hs' hp1 hx1 h1 hpx' hlt
    have h2 : x' * x ^ x ≤ x' ^ x' := mul_pow_self_le hx1 hlt
    have heq := hs'.eq
    simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
      add_zero, zero_add, pow_zero, pow_one, mul_one, w_one_eq_pow] at heq
    rw [show (1 : ℕ) + 1 = 2 from rfl] at heq
    have hqb := hs'.lt_base q' (by simp)
    have hxb := hs'.lt_base x' (by simp)
    have e1 : (q' + 1) * b ≤ b * b := Nat.mul_le_mul_right _ (by omega)
    have e2 : (p' + 1) * b ^ 2 = p' * b ^ 2 + b * b := by ring
    have e3 : (q' + 1) * b = q' * b + b := by ring
    have h5 : x' * (p * b ^ 2) < (p' + 1) * b ^ 2 := by
      calc x' * (p * b ^ 2) ≤ x' * x ^ x := Nat.mul_le_mul_left _ h1
        _ ≤ x' ^ x' := h2
        _ < (p' + 1) * b ^ 2 := by omega
    have h6 : x' * b ^ 2 ≤ x' * (p * b ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    have := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h6 h5)
    omega
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have hp1' : 1 ≤ p' := Nat.one_le_iff_ne_zero.2 (hs'.head_ne_zero (by simp))
  have hpx : p + 1 ≤ x := by
    have := le_w (m := 1) (show p ≠ 0 by omega)
    have : 1 ≤ w 1 q := by rw [w_one_eq_pow]; exact one_le_pow_self q
    omega
  have hpx' : p' + 1 ≤ x' := by
    have := le_w (m := 1) (show p' ≠ 0 by omega)
    have : 1 ≤ w 1 q' := by rw [w_one_eq_pow]; exact one_le_pow_self q'
    omega
  have hb1 := (member_bounds hs hpc hqc hxw hY).2.1
  have hb1' := (member_bounds hs' hpc' hqc' hxw' hY').2.1
  rcases Nat.lt_or_gt_of_ne hxx with h | h
  · exact bound hs' hp1 (by omega) hb1 hpx' h
  · exact bound hs hp1' (by omega) hb1' hpx h

/-! ### Proposition 25.17 -/

/-- `2 M x^x ≤ M^M` for `1 ≤ x < M`: one more in the base at least doubles the weight. -/
lemma two_mul_pow_self_le {x M : ℕ} (hx : 1 ≤ x) (hxM : x < M) : 2 * M * x ^ x ≤ M ^ M := by
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  have h1 := pow_succ_ge (n + 1) n
  have h2 : (n + 1 + 1) ^ (n + 1) ≤ M ^ (M - 1) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : M ^ M = M * M ^ (M - 1) := by rw [← pow_succ']; congr 1; omega
  have h4 : (n + 1) * (n + 1) ^ n = (n + 1) ^ (n + 1) := by ring
  rw [h3]
  calc 2 * M * (n + 1) ^ (n + 1) = M * ((n + 1) ^ (n + 1) + (n + 1) * (n + 1) ^ n) := by
        rw [h4]; ring
    _ ≤ M * M ^ (M - 1) := Nat.mul_le_mul_left _ (h1.trans h2)

/-- A member has `e ≥ 1` (proof of Theorem 25.10): with `e = 0` the last digit
`x = p^p + 1` is prime to `p`, so `x^x = p b^2` forces `p = 1`, `x = 2` and `b = 2`. -/
lemma member_e_pos {b p q x lam c e : ℕ} (hs : IsSolution b 1 [p, q, x])
    (hp : p = lam * c ^ 2) (hq : q = 2 * lam * c * e) (hx : x = w 1 p + w 1 q + lam * e ^ 2)
    (hY : x ^ x = lam * (c * b + e) ^ 2) : 1 ≤ e := by
  by_contra he
  obtain rfl : e = 0 := by omega
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have hq0 : q = 0 := by simpa using hq
  have hxp : x = p ^ p + 1 := by rw [hx, hq0, w_one_eq_pow]; simp
  have hxx : x ^ x = p * b ^ 2 := by
    have := (member_bounds hs hp hq hx hY).1
    rw [hq0] at this; simpa using this
  have hcop : Nat.Coprime p x := by
    have : p ^ p + 1 = 1 + p ^ (p - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel hp1]; ring
    rw [hxp, this, Nat.coprime_add_mul_right_right]
    exact Nat.coprime_one_right p
  have hp1' : p = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop.pow_right x) ⟨b ^ 2, hxx⟩
  subst hp1'
  have hx2 : x = 2 := by simpa using hxp
  subst hx2
  have hb := hs.lt_base 2 (by simp)
  have : 3 ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hb 2
  norm_num at hxx
  omega

/-- The sizes in a member `(p, q, x)` used for Proposition 25.17: `q ≥ 2`, `x ≥ 4 p + 2`,
`x > 2 q`, `b > 3 q`, `b > w(2p) + x` and `3 w(x - 1) < b^2`. -/
lemma member_facts {b p q x lam c e : ℕ} (hs : IsSolution b 1 [p, q, x])
    (hp : p = lam * c ^ 2) (hq : q = 2 * lam * c * e) (hx : x = w 1 p + w 1 q + lam * e ^ 2)
    (hY : x ^ x = lam * (c * b + e) ^ 2) :
    2 ≤ q ∧ 4 * p + 2 ≤ x ∧ 2 * q < x ∧ 3 * q < b ∧ (2 * p) ^ (2 * p) + x < b ∧
      3 * (x - 1) ^ (x - 1) < b ^ 2 := by
  have he := member_e_pos hs hp hq hx hY
  obtain ⟨-, -, hWlt⟩ := member_bounds hs hp hq hx hY
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have hxb := hs.lt_base x (by simp)
  have hlam : 1 ≤ lam := by
    rcases Nat.eq_zero_or_pos lam with h | h
    · rw [h] at hp; omega
    · exact h
  have hc : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hp; simp at hp; omega
    · exact h
  have hL : 1 ≤ lam * e ^ 2 := Nat.mul_le_mul hlam (Nat.one_le_pow _ _ he)
  have hq' : q = 2 * (lam * c * e) := by rw [hq]; ring
  have hq2 : 2 ≤ q := by
    have : 1 ≤ lam * c * e := Nat.mul_le_mul (Nat.mul_le_mul hlam hc) he
    omega
  have hq4 : 4 * p ≤ q ^ 2 := by
    have : q ^ 2 = 4 * p * (lam * e ^ 2) := by rw [hq, hp]; ring
    rw [this]
    exact Nat.le_mul_of_pos_right _ hL
  have hxge : p ^ p + q ^ q + 1 ≤ x := by rw [hx, w_one_eq_pow, w_one_eq_pow]; omega
  have hqq : q ^ 2 ≤ q ^ q := Nat.pow_le_pow_right (by omega) hq2
  have hq2' : 4 ≤ q ^ 2 := by nlinarith
  have h4p : 4 * p + 2 ≤ x := by
    rcases (show p = 1 ∨ p = 2 ∨ 3 ≤ p by omega) with h | h | h
    · subst h; simp at hxge; omega
    · subst h
      have hq3 : 3 ≤ q := by
        by_contra hq3
        have : q = 2 := by omega
        subst this; omega
      have : q ^ 3 ≤ q ^ q := Nat.pow_le_pow_right (by omega) hq3
      have : 27 ≤ q ^ 3 := by
        calc 27 = 3 ^ 3 := by norm_num
          _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
      norm_num at hxge
      omega
    · have h1 : p ^ 3 ≤ p ^ p := Nat.pow_le_pow_right (by omega) h
      have h2 : 9 * p ≤ p ^ 3 := by
        have : p ^ 3 = p * p * p := by ring
        rw [this]; nlinarith
      omega
  have h2q : 2 * q < x := by nlinarith [Nat.one_le_pow p p hp1]
  have h3q : 3 * q < b := by
    rcases (show q = 2 ∨ 3 ≤ q by omega) with h | h
    · subst h; norm_num at hxge; omega
    · have : 3 * q ≤ q ^ 2 := by nlinarith
      omega
  refine ⟨hq2, h4p, h2q, h3q, ?_, ?_⟩
  · -- otherwise `x^x < (p + 1) b^2 ≤ 4 (p + 1) x^(4p) < x^(4p+2)`
    by_contra hb
    have hA : (2 * p) ^ (2 * p) ≤ x ^ (2 * p) := Nat.pow_le_pow_left (by omega) _
    have hB : x ≤ x ^ (2 * p) := Nat.le_self_pow (by omega) x
    have hb2 : b ≤ 2 * x ^ (2 * p) := by omega
    have hb4 : b ^ 2 ≤ 4 * x ^ (4 * p) := by
      calc b ^ 2 ≤ (2 * x ^ (2 * p)) ^ 2 := Nat.pow_le_pow_left hb2 2
        _ = 4 * x ^ (4 * p) := by rw [mul_pow, ← pow_mul]; ring_nf
    have hC : x ^ (4 * p) * x ^ 2 ≤ x ^ x := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have hD : x ^ (4 * p) * x ^ 2 < x ^ (4 * p) * (4 * (p + 1)) := by
      calc x ^ (4 * p) * x ^ 2 ≤ x ^ x := hC
        _ < (p + 1) * b ^ 2 := hWlt
        _ ≤ (p + 1) * (4 * x ^ (4 * p)) := Nat.mul_le_mul_left _ hb4
        _ = x ^ (4 * p) * (4 * (p + 1)) := by ring
    have := Nat.lt_of_mul_lt_mul_left hD
    nlinarith
  · have h1 := two_mul_pow_self_le (show 1 ≤ x - 1 by omega) (show x - 1 < x by omega)
    have h2 : 2 * x * (3 * (x - 1) ^ (x - 1)) < 2 * x * b ^ 2 := by
      calc 2 * x * (3 * (x - 1) ^ (x - 1)) = 3 * (2 * x * (x - 1) ^ (x - 1)) := by ring
        _ ≤ 3 * x ^ x := Nat.mul_le_mul_left _ h1
        _ < 3 * ((p + 1) * b ^ 2) := by omega
        _ = (3 * p + 3) * b ^ 2 := by ring
        _ ≤ 2 * x * b ^ 2 := Nat.mul_le_mul_right _ (by omega)
    exact Nat.lt_of_mul_lt_mul_left h2

/-- **Proposition 25.17** (section 25.3.3). Under `0^0 = 1`, let `(p, q, x)` be a member in
base `b` (a solution with `R = 0`). Every other 3-digit solution of base `b` is either
`(p, x, r)` with
`(E1) g(r) = (x - q) b - w(p) - lam e^2`, where `g(r) = w(r) - r` and `w(p) + lam e^2 = x - w(q)`,
or `(p, q', x)` with `q' ≠ q` and `(E2) h_b(q') = h_b(q)`, where `h_b(d) = d b - w(d)`. -/
theorem prop25_17 {b p q x u v y : ℕ} (hs : IsSolution b 1 [p, q, x])
    (hR : 4 * p * x = 4 * p * (w 1 p + w 1 q) + q ^ 2) (hs' : IsSolution b 1 [u, v, y]) :
    [u, v, y] = [p, q, x] ∨
      (u = p ∧ v = x ∧ G y = ((x : ℤ) - q) * b - (x - w 1 q)) ∨
      (u = p ∧ y = x ∧ v ≠ q ∧ (v : ℤ) * b - w 1 v = q * b - w 1 q) := by
  obtain ⟨lam, c, e, -, -, hp, hq, hx, hY⟩ := theorem25_7_i hs hR
  obtain ⟨-, h4p, h2q, h3q, hbig, h3D⟩ := member_facts hs hp hq hx hY
  obtain ⟨hW, hpW, hWlt⟩ := member_bounds hs hp hq hx hY
  have he := member_e_pos hs hp hq hx hY
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have hxb := hs.lt_base x (by simp)
  have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.2 (hs'.head_ne_zero (by simp))
  have hvb := hs'.lt_base v (by simp)
  have hyb := hs'.lt_base y (by simp)
  -- the largest digit `M` is `x` (Lemma 25.13)
  have hdig : u ≤ x ∧ v ≤ x ∧ y ≤ x ∧ (u = x ∨ v = x ∨ y = x) := by
    set M := max u (max v y) with hMdef
    have hMmem : M ∈ [u, v, y] := by
      have : M = u ∨ M = v ∨ M = y := by omega
      rcases this with h | h | h <;> simp [h]
    have hmax : ∀ d ∈ [u, v, y], d ≤ M := by
      intro d hd; simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega
    obtain ⟨h1, h2⟩ := lemma25_13 le_rfl hs' hMmem hmax
    have hMx : M = x := by
      rcases lt_trichotomy M x with hlt | heq | hgt
      · have := w_le_of_le (m := 1) le_rfl (show M ≤ x - 1 by omega)
        rw [w_one_eq_pow (x - 1)] at this
        omega
      · exact heq
      · have h3 := two_mul_pow_self_le (show 1 ≤ x by omega) hgt
        rw [w_one_eq_pow] at h2
        have h4 : 2 * M * b ^ 2 ≤ 2 * M * x ^ x :=
          Nat.mul_le_mul_left _ (le_trans (Nat.le_mul_of_pos_left _ (by omega)) hpW)
        have h5 : 2 * M * b ^ 2 < (M + 1) * b ^ 2 := by omega
        have := Nat.lt_of_mul_lt_mul_right h5
        omega
    omega
  obtain ⟨hux, hvx, hyx, hxin⟩ := hdig
  -- the weights of the digits, as integers
  have wD : ∀ d, d ≤ x → d ≠ x → (w 1 d : ℤ) ≤ ((x - 1) ^ (x - 1) : ℕ) := fun d h1 h2 => by
    have := w_le_of_le (m := 1) le_rfl (show d ≤ x - 1 by omega)
    rw [w_one_eq_pow (x - 1)] at this
    exact_mod_cast this
  have w0 : ∀ d, (0 : ℤ) ≤ w 1 d := fun d => by positivity
  have heq := hs'.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [show (1 : ℕ) + 1 = 2 from rfl] at heq
  have hw2p : w 1 (2 * p) = (2 * p) ^ (2 * p) := w_one_eq_pow _
  have hwx : w 1 x = x ^ x := w_one_eq_pow _
  generalize hD : (x - 1) ^ (x - 1) = D at wD h3D
  generalize hWd : x ^ x = W at hW hpW hWlt hwx
  generalize hLd : lam * e ^ 2 = L at hW hx
  have hL1 : 1 ≤ L := by rw [← hLd]; exact Nat.mul_le_mul (Nat.pos_of_ne_zero (by
    rintro rfl; simp at hp; omega)) (Nat.one_le_pow _ _ he)
  -- everything in `ℤ`
  have heq' : u * b ^ 2 + v * b + y = w 1 u + w 1 v + w 1 y := by omega
  have E : (u : ℤ) * b ^ 2 + v * b + y = w 1 u + w 1 v + w 1 y := by exact_mod_cast heq'
  have EW : (W : ℤ) = p * b ^ 2 + q * b + L := by exact_mod_cast hW
  have EWlt : (W : ℤ) < (p + 1) * b ^ 2 := by exact_mod_cast hWlt
  have EX : (x : ℤ) = w 1 p + w 1 q + L := by exact_mod_cast hx
  have ED : 3 * (D : ℤ) < b ^ 2 := by exact_mod_cast h3D
  have Ewx : (w 1 x : ℤ) = W := by exact_mod_cast hwx
  have Ebig : (w 1 (2 * p) : ℤ) + x < b := by rw [hw2p]; exact_mod_cast hbig
  have Exb : (x : ℤ) + 1 ≤ b := by exact_mod_cast hxb
  have Eb0 : (0 : ℤ) ≤ b := by positivity
  have Ebb : (x + 1 : ℤ) * b ≤ b * b := mul_le_mul_of_nonneg_right Exb Eb0
  have E4p : (4 : ℤ) * p + 2 ≤ x := by exact_mod_cast h4p
  have E2q : (2 : ℤ) * q < x := by exact_mod_cast h2q
  have E3q : (3 : ℤ) * q * b < b * b :=
    mul_lt_mul_of_pos_right (by exact_mod_cast h3q) (by omega)
  have Eqb : (0 : ℤ) ≤ q * b := by positivity
  have E7b : (7 : ℤ) * b ≤ b * b := mul_le_mul_of_nonneg_right (by omega) Eb0
  have EL : (1 : ℤ) ≤ L := by exact_mod_cast hL1
  have Ewp := w0 p
  have Ewq := w0 q
  have Ewu := w0 u
  have Ewv := w0 v
  have Ewy := w0 y
  rcases eq_or_ne u x with hux' | hux'
  · -- a leading `x` weighs too little: `x b^2 > 3 w(x)`
    exfalso
    rw [hux'] at E
    have h1 : (3 * (p : ℤ) + 3) * b ^ 2 ≤ x * b ^ 2 :=
      mul_le_mul_of_nonneg_right (by omega) (by positivity)
    have hv : (w 1 v : ℤ) ≤ W := by
      rw [← Ewx]; exact_mod_cast w_le_of_le (m := 1) le_rfl hvx
    have hy : (w 1 y : ℤ) ≤ W := by
      rw [← Ewx]; exact_mod_cast w_le_of_le (m := 1) le_rfl hyx
    have : (0 : ℤ) ≤ v * b := by positivity
    linarith
  have hu := wD u hux hux'
  rcases eq_or_ne v x with hvx' | hvx'
  · rw [hvx'] at E
    rcases eq_or_ne y x with hyx' | hyx'
    · -- `(u, x, x)`
      exfalso
      rw [hyx', Ewx] at E
      rcases lt_trichotomy u (2 * p) with h | h | h
      · have h1 : (1 : ℤ) * b ^ 2 ≤ (2 * p - u) * b ^ 2 :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        linarith
      · subst h
        have h1 : (1 : ℤ) * b ≤ (x - 2 * q) * b := mul_le_mul_of_nonneg_right (by omega) Eb0
        push_cast at E
        linarith
      · have h1 : (1 : ℤ) * b ^ 2 ≤ (u - 2 * p) * b ^ 2 :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        have h2 : (0 : ℤ) ≤ (x - 2 * q) * b := mul_nonneg (by omega) Eb0
        linarith
    · -- `(u, x, y)`: the leading digit is `p`, and (E1)
      have hy := wD y hyx hyx'
      rw [Ewx] at E
      rcases lt_trichotomy u p with h | h | h
      · exfalso
        have h1 : (1 : ℤ) * b ^ 2 ≤ (p - u) * b ^ 2 :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        have : (y : ℤ) + 1 ≤ b := by exact_mod_cast hyb
        linarith
      · subst h
        right; left
        refine ⟨rfl, hvx', ?_⟩
        rw [← w_one_sub]
        linarith
      · exfalso
        have h1 : (1 : ℤ) * b ^ 2 ≤ (u - p) * b ^ 2 :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        have h2 : (0 : ℤ) ≤ (x - q) * b := mul_nonneg (by omega) Eb0
        linarith
  · have hv := wD v hvx hvx'
    rcases eq_or_ne y x with hyx' | hyx'
    · -- `(u, v, x)`: the leading digit is `p`, and (E2)
      rw [hyx', Ewx] at E
      rcases lt_trichotomy u p with h | h | h
      · exfalso
        have h1 : (1 : ℤ) * b ^ 2 ≤ (p - u) * b ^ 2 :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        have h2 : (v : ℤ) * b ≤ (b - 1) * b := mul_le_mul_of_nonneg_right (by omega) Eb0
        linarith
      · subst h
        rcases eq_or_ne v q with hvq | hvq
        · left; rw [hvq, hyx']
        · right; right
          refine ⟨rfl, hyx', hvq, ?_⟩
          linarith
      · exfalso
        have h1 : (1 : ℤ) * b ^ 2 ≤ (u - p) * b ^ 2 :=
          mul_le_mul_of_nonneg_right (by omega) (by positivity)
        have h2 : (0 : ℤ) ≤ v * b := by positivity
        linarith
    · exfalso
      omega

/-- **Proposition 25.17**, the count (section 25.3.3). Under `0^0 = 1`, a base with a 3-digit
member has at most 3 three-digit solutions: `g` is injective, so (E1) has at most one
solution, and `h_b` takes each value at most twice, so (E2) has at most one besides `q`. -/
theorem prop25_17_card {b p q x : ℕ} (hs : IsSolution b 1 [p, q, x])
    (hR : 4 * p * x = 4 * p * (w 1 p + w 1 q) + q ^ 2) : (solStrings b 1 3).card ≤ 3 := by
  classical
  have hb : 1 ≤ b := by have := hs.lt_base x (by simp); omega
  set S := solStrings b 1 3
  let S2 := S.filter fun s => ∃ y, s = [p, x, y] ∧ G y = ((x : ℤ) - q) * b - (x - w 1 q)
  let S3 := S.filter fun s =>
    ∃ v, s = [p, v, x] ∧ v ≠ q ∧ (v : ℤ) * b - w 1 v = q * b - w 1 q
  have hsub : S ⊆ {[p, q, x]} ∪ S2 ∪ S3 := by
    intro s hsS
    obtain ⟨hlen, hsol⟩ := (mem_solStrings hb).1 hsS
    obtain ⟨u, v, y, rfl⟩ := List.length_eq_three.1 hlen
    rcases prop25_17 hs hR hsol with h | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, hvq, h⟩
    · simp [h]
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨hsS, y, rfl, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hsS, v, rfl, hvq, h⟩)
  have h2 : S2.card ≤ 1 := by
    refine Finset.card_le_one.2 fun s hs t ht => ?_
    obtain ⟨-, y, rfl, hy⟩ := Finset.mem_filter.1 hs
    obtain ⟨-, y', rfl, hy'⟩ := Finset.mem_filter.1 ht
    rw [G_injective (hy.trans hy'.symm)]
  have h3 : S3.card ≤ 1 := by
    refine Finset.card_le_one.2 fun s hs t ht => ?_
    obtain ⟨-, v, rfl, hvq, hv⟩ := Finset.mem_filter.1 hs
    obtain ⟨-, v', rfl, hvq', hv'⟩ := Finset.mem_filter.1 ht
    by_contra hne
    have hvv : v ≠ v' := fun h => hne (by rw [h])
    -- `a ↦ a^a - a b` takes the value at `q` at most twice
    have := card_le_two_of_convex (fun a => (a : ℤ) ^ a - a * b)
      (fun a => by simpa using pow_self_sub_convex (b : ℤ) a) ((q : ℤ) ^ q - q * b) {q, v, v'}
      (by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [w_one_eq_pow, w_one_eq_pow] at hv hv'
        push_cast at hv hv'
        rcases ha with rfl | rfl | rfl <;> linarith)
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hvq, Ne.symm hvq']),
      Finset.card_pair hvv] at this
    omega
  calc S.card ≤ ({[p, q, x]} ∪ S2 ∪ S3).card := Finset.card_le_card hsub
    _ ≤ ({[p, q, x]} ∪ S2).card + S3.card := Finset.card_union_le _ _
    _ ≤ ({[p, q, x]} : Finset (List ℕ)).card + S2.card + S3.card := by
        have := Finset.card_union_le ({[p, q, x]} : Finset (List ℕ)) S2; omega
    _ ≤ 3 := by rw [Finset.card_singleton]; omega

end Munchausen
