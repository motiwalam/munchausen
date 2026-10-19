import Munchausen.ShortEquations

/-!
# Three-digit strings with one large digit (Theorem 25.7, Proposition 22.8)

Completing the square turns a 3-digit solution `(p, q, r)` in base `b` into
`(2 p b + q)^2 = N + R` with `N = 4 l x^x`, where `x` is the large digit and `l` the leading
digit. When `N` is a perfect square and `R ≠ 0`, the two squares are too close.
-/

namespace Munchausen

/-- Two squares `U^2 = V^2 + R` with `U ≥ 1` and `R ≠ 0` satisfy `V^2 < R^2`
(proof of Theorem 25.7 (ii)). -/
lemma sq_lt_sq_of_sq_eq {U V R : ℤ} (hU : 1 ≤ U) (hV : 0 ≤ V) (h : U ^ 2 = V ^ 2 + R)
    (hR : R ≠ 0) : V ^ 2 < R ^ 2 := by
  rcases lt_trichotomy U V with hlt | heq | hgt
  · -- `-R = (V - U)(V + U) ≥ V + U > V`
    have : V + U ≤ -R := by nlinarith
    nlinarith
  · subst heq; exact absurd (by linarith) hR
  · have : U + V ≤ R := by nlinarith
    nlinarith

/-- The value of a 3-digit string, times `4 p`, as a completed square. -/
lemma complete_square {b p q r F : ℕ} (h : p * b ^ 2 + q * b + r = F) :
    ((2 * p * b + q : ℕ) : ℤ) ^ 2 = 4 * p * ((F : ℤ) - r) + q ^ 2 := by
  have : ((p * b ^ 2 + q * b + r : ℕ) : ℤ) = F := by rw [h]
  push_cast at this ⊢
  nlinarith

/-- A digit at most `B` weighs at most `B^B` (for `m ≤ 1`, `B ≥ 1`). -/
lemma w_le_pow {m u B : ℕ} (hm : m ≤ 1) (hB : 1 ≤ B) (hu : u ≤ B) : w m u ≤ B ^ B := by
  calc w m u ≤ w m B := w_le_of_le hm hu
    _ = B ^ B := w_of_ne_zero m (by omega)

/-- `5 B^B ≤ (2B + 4)^B` for `B ≥ 1`. -/
lemma five_mul_pow_le (B : ℕ) (hB : 1 ≤ B) : 5 * B ^ B ≤ (2 * B + 4) ^ B := by
  rcases Nat.lt_or_ge B 3 with h | h
  · interval_cases B <;> norm_num
  · have h1 : (2 * B) ^ B ≤ (2 * B + 4) ^ B := Nat.pow_le_pow_left (by omega) _
    have h2 : 8 ≤ 2 ^ B := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) h
    rw [mul_pow] at h1
    nlinarith [Nat.one_le_pow B B (by omega)]

/-- For `x ≥ 2B + 4`, `x^x ≥ 25 x^4 (B^B)^2`. -/
lemma pow_self_ge {x B : ℕ} (hB : 1 ≤ B) (hx : 2 * B + 4 ≤ x) :
    25 * x ^ 4 * (B ^ B) ^ 2 ≤ x ^ x := by
  have h1 : x ^ (4 + 2 * B) ≤ x ^ x := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 5 * B ^ B ≤ x ^ B :=
    (five_mul_pow_le B hB).trans (Nat.pow_le_pow_left hx B)
  have e : x ^ (4 + 2 * B) = x ^ 4 * (x ^ B) ^ 2 := by ring
  rw [e] at h1
  have h3 : (5 * B ^ B) ^ 2 ≤ (x ^ B) ^ 2 := Nat.pow_le_pow_left h2 2
  calc 25 * x ^ 4 * (B ^ B) ^ 2 = x ^ 4 * (5 * B ^ B) ^ 2 := by ring
    _ ≤ x ^ 4 * (x ^ B) ^ 2 := Nat.mul_le_mul_left _ h3
    _ ≤ x ^ x := h1

/-- `w(d) ≥ d` as integers, for every digit. -/
lemma le_w_int (m d : ℕ) : (d : ℤ) ≤ (w m d : ℤ) := by exact_mod_cast le_w' m d

/-- If `-C ≤ R ≤ A` with `A, C ≥ 0` and `4 (A + C) ≤ T`, then `16 R^2 ≤ T^2`. -/
lemma sq_le_of_bounds {R A C T : ℤ} (hA : 0 ≤ A) (hC : 0 ≤ C) (h1 : -C ≤ R) (h2 : R ≤ A)
    (hT : 4 * (A + C) ≤ T) : 16 * R ^ 2 ≤ T ^ 2 := by
  have h3 : |4 * R| ≤ T := by
    rw [abs_le]; constructor <;> linarith
  have := sq_le_sq' (abs_le.1 h3).1 (abs_le.1 h3).2
  nlinarith

/-- The size of `R` when the large digit is last (proof of Theorem 25.7 (ii)). -/
lemma bound_last {p q x B W wp wq : ℤ} (hp1 : 1 ≤ p) (hpB : p ≤ B) (hq0 : 0 ≤ q) (hqB : q ≤ B)
    (hxB : 2 * B + 4 ≤ x) (hwp0 : 0 ≤ wp) (hwq0 : 0 ≤ wq) (hwp : wp ≤ W) (hwq : wq ≤ W)
    (hW1 : 1 ≤ W) :
    16 * (4 * p * (wp + wq - x) + q ^ 2) ^ 2 ≤ (25 * x ^ 2 * W) ^ 2 := by
  have hB : 0 ≤ B := by linarith
  have hW : 0 ≤ W := by linarith
  have hx1 : 1 ≤ x := by linarith
  have k1 : p * (wp + wq) ≤ B * (2 * W) := mul_le_mul hpB (by linarith) (by linarith) hB
  have k2 : q ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hq0 hqB 2
  have k3 : 2 * B * W ≤ x * W := mul_le_mul_of_nonneg_right (by linarith) hW
  have k4 : (2 * B) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have k5 : p * x ≤ B * x := mul_le_mul_of_nonneg_right hpB (by linarith)
  have k6 : 2 * B * x ≤ x * x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have k7 : x * W ≤ x ^ 2 * W := by
    have : x ≤ x ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hW
  have k8 : x ^ 2 ≤ x ^ 2 * W := le_mul_of_one_le_right (by positivity) (by linarith)
  have m1 : 0 ≤ p * (wp + wq) := mul_nonneg (by linarith) (by linarith)
  have m2 : 0 ≤ p * x := mul_nonneg (by linarith) (by linarith)
  have m3 : 0 ≤ q ^ 2 := sq_nonneg q
  apply sq_le_of_bounds (A := 4 * p * (wp + wq) + q ^ 2) (C := 4 * p * x)
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- **Theorem 25.7 (ii)**, large digit last (section 25.1.4). Let `(p, q, x)` have
`p, q ≤ B` and `x ≥ 2B + 4`. If `N = 4 p x^x` is a perfect square and
`R = 4 p (w(p) + w(q) - x) + q^2 ≠ 0`, then the string is not a solution in any base. -/
theorem theorem25_7_ii_last {b m p q x B V : ℕ} (hm : m ≤ 1) (hB : 1 ≤ B) (hp : p ≤ B)
    (hq : q ≤ B) (hx : 2 * B + 4 ≤ x) (hV : 4 * p * x ^ x = V ^ 2)
    (hR : 4 * (p : ℤ) * ((w m p : ℤ) + w m q - x) + q ^ 2 ≠ 0) :
    ¬ IsSolution b m [p, q, x] := by
  intro hs
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero m (show x ≠ 0 by omega)] at heq
  have hsq := complete_square (b := b) (p := p) (q := q) (r := x)
    (F := w m p + (w m q + x ^ x)) (by rw [← heq]; ring)
  set W := B ^ B
  have hwp : (w m p : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hp
  have hwq : (w m q : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hq
  have hW1 : (1 : ℤ) ≤ W := by exact_mod_cast Nat.one_le_pow B B (by omega)
  have hbig : 25 * (x : ℤ) ^ 4 * (W : ℤ) ^ 2 ≤ (x : ℤ) ^ x := by exact_mod_cast pow_self_ge hB hx
  set R : ℤ := 4 * (p : ℤ) * ((w m p : ℤ) + w m q - x) + q ^ 2 with hRdef
  have hUV : ((2 * p * b + q : ℕ) : ℤ) ^ 2 = (V : ℤ) ^ 2 + R := by
    rw [hsq, hRdef, ← (by exact_mod_cast hV : (4 * p * x ^ x : ℤ) = (V : ℤ) ^ 2)]
    push_cast; ring
  have hU1 : (1 : ℤ) ≤ ((2 * p * b + q : ℕ) : ℤ) := by
    have : 1 ≤ 2 * p * b + q := by
      have := hs.lt_base p (by simp); nlinarith
    exact_mod_cast this
  have hlt := sq_lt_sq_of_sq_eq hU1 (by positivity) hUV hR
  -- but `R` is small
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp1
  have hb2 := bound_last (p := p) (q := q) (x := x) (B := B) (W := W) (wp := w m p)
    (wq := w m q) hpZ (by exact_mod_cast hp) (by positivity) (by exact_mod_cast hq)
    (by exact_mod_cast hx) (by positivity) (by positivity) hwp hwq hW1
  have hV2 : 4 * (x : ℤ) ^ x ≤ (V : ℤ) ^ 2 := by
    rw [← (by exact_mod_cast hV : (4 * p * x ^ x : ℤ) = (V : ℤ) ^ 2)]
    have : (0 : ℤ) ≤ (x : ℤ) ^ x := by positivity
    nlinarith
  have hx4 : (0 : ℤ) < (x : ℤ) ^ 4 * (W : ℤ) ^ 2 := by
    have : (0 : ℤ) < x := by exact_mod_cast (show 0 < x by omega)
    positivity
  have e : (25 * (x : ℤ) ^ 2 * W) ^ 2 = 625 * ((x : ℤ) ^ 4 * (W : ℤ) ^ 2) := by ring
  rw [e] at hb2
  rw [← hRdef] at hb2
  nlinarith

/-- **Theorem 25.7 (ii)**, large digit in the middle (section 25.1.4). Let `(p, x, r)` have
`p, r ≤ B` and `x ≥ 2B + 4`. If `N = 4 p x^x` is a perfect square, the string is not a
solution in any base. Here `R = 4 p (w(p) + w(r) - r) + x^2 > 0`. -/
theorem theorem25_7_ii_middle {b m p r x B V : ℕ} (hm : m ≤ 1) (hB : 1 ≤ B) (hp : p ≤ B)
    (hr : r ≤ B) (hx : 2 * B + 4 ≤ x) (hV : 4 * p * x ^ x = V ^ 2) :
    ¬ IsSolution b m [p, x, r] := by
  intro hs
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero m (show x ≠ 0 by omega)] at heq
  have hsq := complete_square (b := b) (p := p) (q := x) (r := r)
    (F := w m p + (x ^ x + w m r)) (by rw [← heq]; ring)
  set W := B ^ B
  have hwp : (w m p : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hp
  have hwr : (w m r : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hr
  have hW1 : (1 : ℤ) ≤ W := by exact_mod_cast Nat.one_le_pow B B (by omega)
  have hbig : 25 * (x : ℤ) ^ 4 * (W : ℤ) ^ 2 ≤ (x : ℤ) ^ x := by exact_mod_cast pow_self_ge hB hx
  set R : ℤ := 4 * (p : ℤ) * ((w m p : ℤ) + w m r - r) + x ^ 2 with hRdef
  have hVZ : (4 * p * x ^ x : ℤ) = (V : ℤ) ^ 2 := by exact_mod_cast hV
  have hUV : ((2 * p * b + x : ℕ) : ℤ) ^ 2 = (V : ℤ) ^ 2 + R := by
    rw [hsq, hRdef, ← hVZ]; push_cast; ring
  have hU1 : (1 : ℤ) ≤ ((2 * p * b + x : ℕ) : ℤ) := by exact_mod_cast (show 1 ≤ 2 * p * b + x by omega)
  have hpZ : (1 : ℤ) ≤ p := by exact_mod_cast hp1
  have hpB : (p : ℤ) ≤ B := by exact_mod_cast hp
  have hxB : 2 * (B : ℤ) + 4 ≤ x := by exact_mod_cast hx
  have hrw : (r : ℤ) ≤ w m r := le_w_int m r
  have hwp1 : (1 : ℤ) ≤ w m p := by exact_mod_cast one_le_w (m := m) (show p ≠ 0 by omega)
  have hR0 : 0 < R := by
    have : (0 : ℤ) < (p : ℤ) * ((w m p : ℤ) + w m r - r) := mul_pos (by linarith) (by linarith)
    have : (0 : ℤ) ≤ (x : ℤ) ^ 2 := sq_nonneg _
    simp only [hRdef]; linarith
  have hlt := sq_lt_sq_of_sq_eq hU1 (by positivity) hUV hR0.ne'
  -- `R ≤ 5 x^2 W`
  have hRle : R ≤ 5 * (x : ℤ) ^ 2 * W := by
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have k1 : (p : ℤ) * ((w m p : ℤ) + w m r - r) ≤ B * (2 * W) :=
      mul_le_mul hpB (by linarith) (by linarith) (by linarith)
    have k3 : 2 * (B : ℤ) * W ≤ x * W := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have k7 : (x : ℤ) * W ≤ x ^ 2 * W := by
      have : (x : ℤ) ≤ x ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have k8 : (x : ℤ) ^ 2 ≤ x ^ 2 * W := le_mul_of_one_le_right (by positivity) hW1
    simp only [hRdef]; linarith
  have hR2 : R ^ 2 ≤ 25 * ((x : ℤ) ^ 4 * (W : ℤ) ^ 2) := by
    have := pow_le_pow_left₀ hR0.le hRle 2
    have e : (5 * (x : ℤ) ^ 2 * W) ^ 2 = 25 * ((x : ℤ) ^ 4 * (W : ℤ) ^ 2) := by ring
    linarith
  have hx0 : (0 : ℤ) < (x : ℤ) ^ x := by
    have : (0 : ℤ) < x := by exact_mod_cast (show 0 < x by omega)
    positivity
  have : (x : ℤ) ^ x ≤ (V : ℤ) ^ 2 := by
    rw [← hVZ]; nlinarith
  nlinarith

/-- **Theorem 25.7 (ii)**, large digit in front (section 25.1.4), under `0^0 = 1`. Let
`(x, q, r)` have `q, r ≤ B` and `x ≥ 2B + 4`. If `N = 4 x x^x` is a perfect square, the string
is not a solution in any base. Here `R = 4 x (w(q) + w(r) - r) + q^2 > 0`. (Under `0^0 = 0`
the strings `(x, 0, 0)` and `(x, 0, 1)` have `R = 0`; they are the self-paying families.) -/
theorem theorem25_7_ii_leading {b q r x B V : ℕ} (hB : 1 ≤ B) (hq : q ≤ B)
    (hr : r ≤ B) (hx : 2 * B + 4 ≤ x) (hV : 4 * x * x ^ x = V ^ 2) :
    ¬ IsSolution b 1 [x, q, r] := by
  intro hs
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero 1 (show x ≠ 0 by omega)] at heq
  have hsq := complete_square (b := b) (p := x) (q := q) (r := r)
    (F := x ^ x + (w 1 q + w 1 r)) (by rw [← heq]; ring)
  set W := B ^ B
  have hwq : (w 1 q : ℤ) ≤ W := by exact_mod_cast w_le_pow le_rfl hB hq
  have hwr : (w 1 r : ℤ) ≤ W := by exact_mod_cast w_le_pow le_rfl hB hr
  have hW1 : (1 : ℤ) ≤ W := by exact_mod_cast Nat.one_le_pow B B (by omega)
  have hbig : 25 * (x : ℤ) ^ 4 * (W : ℤ) ^ 2 ≤ (x : ℤ) ^ x := by exact_mod_cast pow_self_ge hB hx
  set R : ℤ := 4 * (x : ℤ) * ((w 1 q : ℤ) + w 1 r - r) + q ^ 2 with hRdef
  have hVZ : (4 * x * x ^ x : ℤ) = (V : ℤ) ^ 2 := by exact_mod_cast hV
  have hUV : ((2 * x * b + q : ℕ) : ℤ) ^ 2 = (V : ℤ) ^ 2 + R := by
    rw [hsq, hRdef, ← hVZ]; push_cast; ring
  have hb1 : 1 ≤ b := by have := hs.lt_base x (by simp); omega
  have hU1 : (1 : ℤ) ≤ ((2 * x * b + q : ℕ) : ℤ) := by
    have : 1 ≤ 2 * x * b + q := by nlinarith
    exact_mod_cast this
  have hxZ : (1 : ℤ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hxB : 2 * (B : ℤ) + 4 ≤ x := by exact_mod_cast hx
  have hqB : (q : ℤ) ≤ B := by exact_mod_cast hq
  have hrw : (r : ℤ) ≤ w 1 r := le_w_int 1 r
  have hwq1 : (1 : ℤ) ≤ w 1 q := by
    rw [w_one_eq_pow]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · simp
    · exact_mod_cast Nat.one_le_pow _ _ hq0
  have hR0 : 0 < R := by
    have : (0 : ℤ) < (x : ℤ) * ((w 1 q : ℤ) + w 1 r - r) := mul_pos (by linarith) (by linarith)
    have : (0 : ℤ) ≤ (q : ℤ) ^ 2 := sq_nonneg _
    simp only [hRdef]; linarith
  have hlt := sq_lt_sq_of_sq_eq hU1 (by positivity) hUV hR0.ne'
  -- `R ≤ 9 x^2 W`
  have hRle : R ≤ 9 * (x : ℤ) ^ 2 * W := by
    have hr0 : (0 : ℤ) ≤ r := by positivity
    have hq0 : (0 : ℤ) ≤ q := by positivity
    have k1 : (x : ℤ) * ((w 1 q : ℤ) + w 1 r - r) ≤ x * (2 * W) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have k2 : (q : ℤ) ^ 2 ≤ (x : ℤ) ^ 2 := pow_le_pow_left₀ hq0 (by linarith) 2
    have k7 : (x : ℤ) * W ≤ x ^ 2 * W := by
      have : (x : ℤ) ≤ x ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have k8 : (x : ℤ) ^ 2 ≤ x ^ 2 * W := le_mul_of_one_le_right (by positivity) hW1
    simp only [hRdef]; linarith
  have hR2 : R ^ 2 ≤ 81 * ((x : ℤ) ^ 4 * (W : ℤ) ^ 2) := by
    have := pow_le_pow_left₀ hR0.le hRle 2
    have e : (9 * (x : ℤ) ^ 2 * W) ^ 2 = 81 * ((x : ℤ) ^ 4 * (W : ℤ) ^ 2) := by ring
    linarith
  have hx0 : (0 : ℤ) < (x : ℤ) ^ x := by positivity
  have h4 : 4 * (x : ℤ) ^ x ≤ (V : ℤ) ^ 2 := by rw [← hVZ]; nlinarith
  nlinarith

/-! ### Theorem 8.3: a large leading digit in the square class -/

/-- `(Y + 1)^(n+1) ≥ Y^(n+1) + (n+1) Y^n` (the first two binomial terms). -/
lemma pow_succ_ge (Y n : ℕ) : Y ^ (n + 1) + (n + 1) * Y ^ n ≤ (Y + 1) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (Y + 1) ^ (n + 2) = (Y + 1) ^ (n + 1) * (Y + 1) := pow_succ _ _
    rw [h]
    have h2 : Y ^ (n + 1 + 1) + (n + 1 + 1) * Y ^ (n + 1) ≤
        (Y ^ (n + 1) + (n + 1) * Y ^ n) * (Y + 1) := by
      have : (Y ^ (n + 1) + (n + 1) * Y ^ n) * (Y + 1) =
          Y ^ (n + 1 + 1) + (n + 1 + 1) * Y ^ (n + 1) + (n + 1) * Y ^ n := by ring
      omega
    exact h2.trans (Nat.mul_le_mul_right _ ih)

/-- A string of digits at most `B` has `b P_t(b) ≤ 2 B b^|t|` for `b ≥ 2`. -/
lemma P_mul_le {b B : ℕ} (hb : 2 ≤ b) {t : List ℕ} (ht : ∀ d ∈ t, d ≤ B) :
    P b t * b ≤ 2 * B * b ^ t.length := by
  induction t with
  | nil => simp
  | cons d t ih =>
    rw [P_cons, Nat.cast_id, List.length_cons]
    have hd := ht d (by simp)
    have ih' := ih (fun e he => ht e (by simp [he]))
    have h1 : d * b ^ t.length * b ≤ B * b ^ (t.length + 1) := by
      rw [pow_succ, ← mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hd)
    have h2 : 2 * B * b ^ t.length ≤ B * b ^ (t.length + 1) := by
      rw [pow_succ]; nlinarith [Nat.zero_le (B * b ^ t.length)]
    nlinarith

/-- **Theorem 8.3** (section 8.2), with its explicit bound as hypotheses. Let `k ≥ 2`, let `t`
be `k - 1` digits at most `B` with weight sum `C`, and let `x ≥ 1` with
`x^(x-1) = Z^(k-1)`. Suppose `C < x (k-1) Z^(k-2)`, `2B < x (k-1)` and `C < Z` (all true for
`x` above a bound that depends on `B` and `k`). If `(x, t)` is a solution in base `b`, then
`b = Z`, and `t = (0, ..., 0, e)` with `e = (k-2) w(0) + w(e)`. -/
theorem theorem8_3 {b m k x Z B : ℕ} {t : List ℕ} (hk : 2 ≤ k) (hlen : t.length = k - 1)
    (htB : ∀ d ∈ t, d ≤ B) (hx : 1 ≤ x) (hZ : x ^ (x - 1) = Z ^ (k - 1))
    (h1 : Fs m t < x * (k - 1) * Z ^ (k - 2)) (h2 : 2 * B < x * (k - 1)) (h3 : Fs m t < Z)
    (hs : IsSolution b m (x :: t)) :
    b = Z ∧ ∃ e, t = List.replicate (k - 2) 0 ++ [e] ∧ e = (k - 2) * m + w m e := by
  have hb : 2 ≤ b := by have := hs.lt_base x (by simp); omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp only [show j + 2 - 1 = j + 1 by omega, show j + 2 - 2 = j by omega] at hlen hZ h1 h2 ⊢
  set C := Fs m t with hC
  set Q := P b t with hQ
  have heq := hs.eq
  rw [P_cons, Fs_cons, w_of_ne_zero m (by omega), hlen, Nat.cast_id] at heq
  have hxx : x ^ x = x * Z ^ (j + 1) := by
    rw [← hZ, ← pow_succ']; congr 1; omega
  rw [hxx] at heq
  -- `heq : x b^(j+1) + Q = x Z^(j+1) + C`
  have hQb : Q * b ≤ 2 * B * b ^ (j + 1) := by rw [← hlen]; exact P_mul_le hb htB
  have hQ' : Q ≤ 2 * B * b ^ j := by
    rw [pow_succ, ← mul_assoc] at hQb
    exact Nat.le_of_mul_le_mul_right hQb (by omega)
  have hbZ : b = Z := by
    rcases Nat.lt_trichotomy b Z with hlt | heq' | hgt
    · exfalso
      have hp := pow_succ_ge b j
      have hZb : (b + 1) ^ (j + 1) ≤ Z ^ (j + 1) := Nat.pow_le_pow_left hlt _
      have hbj : 1 ≤ b ^ j := Nat.one_le_pow _ _ (by omega)
      have k1 : x * (b ^ (j + 1) + (j + 1) * b ^ j) ≤ x * Z ^ (j + 1) :=
        Nat.mul_le_mul_left _ (hp.trans hZb)
      have k2 : 2 * B * b ^ j < x * (j + 1) * b ^ j := Nat.mul_lt_mul_of_pos_right h2 hbj
      nlinarith
    · exact heq'
    · exfalso
      have hp := pow_succ_ge Z j
      have hbZ' : (Z + 1) ^ (j + 1) ≤ b ^ (j + 1) := Nat.pow_le_pow_left hgt _
      have k1 : x * (Z ^ (j + 1) + (j + 1) * Z ^ j) ≤ x * b ^ (j + 1) :=
        Nat.mul_le_mul_left _ (hp.trans hbZ')
      nlinarith
  subst hbZ
  have hQC : Q = C := by omega
  refine ⟨rfl, ?_⟩
  -- the digits of `t` above the last one are 0
  obtain ⟨t', e, rfl⟩ : ∃ t' e, t = t' ++ [e] := by
    rcases List.eq_nil_or_concat t with h | ⟨t', e, h⟩
    · subst h; simp at hlen
    · exact ⟨t', e, by rw [h, List.concat_eq_append]⟩
  simp only [List.length_append, List.length_singleton] at hlen
  have hQe : Q = e + b * P b t' := by rw [hQ, P_append_singleton, Nat.cast_id]
  have hP0 : P b t' = 0 := by
    by_contra hne
    have : b ≤ b * P b t' := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    omega
  have hz : ∀ d ∈ t', d = 0 := by
    intro d hd
    have := Nat.digits_zero_of_eq_zero (b := b) (by omega) (L := t'.reverse) hP0 d
      (List.mem_reverse.2 hd)
    exact this
  have ht' : t' = List.replicate j 0 := by
    rw [List.eq_replicate_iff]; exact ⟨by omega, hz⟩
  refine ⟨e, by rw [ht'], ?_⟩
  have hCe : C = j * m + w m e := by
    rw [hC, ht', Fs_append, Fs_replicate, Fs_singleton, w_zero]
  have hPe : P b (List.replicate j 0) = 0 := P_replicate_zero _ _
  rw [ht', hPe, mul_zero, add_zero] at hQe
  omega

/-- **Theorem 8.3** under `0^0 = 1`: with the bound of `theorem8_3`, a solution `(x, t)` needs
`k = 2` and `t = (1)`, the string `(x, 1)` in base `x^(x-1)`. -/
theorem theorem8_3_one {b k x Z B : ℕ} {t : List ℕ} (hk : 2 ≤ k) (hlen : t.length = k - 1)
    (htB : ∀ d ∈ t, d ≤ B) (hx : 1 ≤ x) (hZ : x ^ (x - 1) = Z ^ (k - 1))
    (h1 : Fs 1 t < x * (k - 1) * Z ^ (k - 2)) (h2 : 2 * B < x * (k - 1)) (h3 : Fs 1 t < Z)
    (hs : IsSolution b 1 (x :: t)) : k = 2 ∧ t = [1] ∧ b = Z := by
  obtain ⟨hb, e, rfl, he⟩ := theorem8_3 hk hlen htB hx hZ h1 h2 h3 hs
  have hwe : e ≤ w 1 e := le_w' 1 e
  have hk2 : k = 2 := by omega
  subst hk2
  have he1 : e = 1 := by
    rcases Nat.lt_trichotomy e 1 with h | h | h
    · interval_cases e; simp at he
    · exact h
    · rw [w_of_ne_zero 1 (by omega)] at he
      have : e ^ 1 < e ^ e := Nat.pow_lt_pow_right (by omega) h
      simp at this; omega
  exact ⟨rfl, by rw [he1]; rfl, hb⟩

end Munchausen
