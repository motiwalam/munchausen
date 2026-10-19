import Munchausen.Applications

/-!
# Pruning rules and Pell families: the elementary parts of chapters 31 and 32

* Chapter 31: the residue rule of the exact search (Theorem 31.1), from Proposition 1.5; the
  ends of the interval of a node (Lemma 31.4); the two interval tests that contain
  Proposition 1.6 and section 1.7 (Proposition 31.5).
* Chapter 32: the reduction of `(p, q, x)` and `(p, x, q)` with `x` even and `p = n f^2` to
  `U^2 - n V^2 = R` with `V = 2 f x^(x/2)` (section 32.1.1), `R ≠ 0` when `n` is not a square,
  the 2-adic size of `V` (Step 2 of Theorem 32.2), and the soundness of the sieve of
  Theorem 32.3: the discriminant `D` of a solution is a square modulo every integer.
-/

namespace Munchausen

/-! ### Chapter 31: the residue rule -/

/-- The weight sum splits as the shifted weights plus the digit sum:
`F(s) = ∑ g(x) + ∑ x`. -/
lemma Fs_eq_sum_g_add_sum (m : ℕ) (s : List ℕ) : Fs m s = (s.map (g m)).sum + s.sum := by
  induction s with
  | nil => simp
  | cons d t ih =>
    rw [Fs_cons, List.map_cons, List.sum_cons, List.sum_cons, ih, g]
    have := le_w' m d
    omega

/-- Proposition 1.5 in the form of section 31.2.1: the shifted weights `r_m(x) = w(x) - x` of a
solution sum to `0` modulo `b - 1`. -/
theorem IsSolution.sum_g_modEq_zero {b m : ℕ} {s : List ℕ} (hb : 1 ≤ b) (h : IsSolution b m s) :
    (s.map (g m)).sum ≡ 0 [MOD b - 1] := by
  have := h.Fs_modEq_sum hb
  rw [Fs_eq_sum_g_add_sum] at this
  exact Nat.ModEq.add_right_cancel' s.sum (by simpa using this)

/-- **Theorem 31.1** (section 31.2.1). A node has decided and forced digits `known` and one
free slot, which holds a digit below `k`. If no `y < k` completes the residue,
`R_m + r_m(y) ≡ 0 (mod b - 1)`, then no completion (in any order) is a solution under
`0^0 = m`. -/
theorem theorem31_1 {b m k : ℕ} (hb : 1 ≤ b) (known : List ℕ)
    (hrule : ∀ y < k, ¬ (known.map (g m)).sum + g m y ≡ 0 [MOD b - 1])
    {y : ℕ} (hy : y < k) {s : List ℕ} (hs : s.Perm (y :: known)) : ¬ IsSolution b m s := by
  intro h
  have := h.sum_g_modEq_zero hb
  rw [(hs.map (g m)).sum_eq, List.map_cons, List.sum_cons, add_comm] at this
  exact hrule y hy this

lemma Fs_le_of_le {m m' : ℕ} (hmm : m ≤ m') (s : List ℕ) : Fs m s ≤ Fs m' s := by
  induction s with
  | nil => simp
  | cons d t ih =>
    rw [Fs_cons, Fs_cons]
    have : w m d ≤ w m' d := by
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simpa using hmm
      · rw [w_of_ne_zero m hd.ne', w_of_ne_zero m' hd.ne']
    omega

/-- **Lemma 31.4** (section 31.3.3). Let a node have known digits `known` and free slots `ys`,
each below `k ≥ 2`. Under `0^0 = m ≤ 1` every completion has its sum in the interval
`[lo, hi]` with `lo = t = F_0(known)` and
`hi = t + z + rf W(k-1) = F_1(known) + rf (k-1)^(k-1)`. -/
theorem lemma31_4 {m k : ℕ} (hm : m ≤ 1) (hk : 2 ≤ k) (known ys : List ℕ)
    (hys : ∀ y ∈ ys, y < k) :
    Fs 0 known ≤ Fs m (known ++ ys) ∧
      Fs m (known ++ ys) ≤ Fs 1 known + ys.length * (k - 1) ^ (k - 1) := by
  rw [Fs_append]
  refine ⟨(Fs_le_of_le (Nat.zero_le m) known).trans (Nat.le_add_right _ _), ?_⟩
  have h1 := Fs_le_of_le hm known
  have h2 : Fs m ys ≤ ys.length * (k - 1) ^ (k - 1) := by
    induction ys with
    | nil => simp
    | cons y t ih =>
      rw [Fs_cons, List.length_cons]
      have hy : w m y ≤ (k - 1) ^ (k - 1) := by
        rw [← w_of_ne_zero m (show k - 1 ≠ 0 by omega)]
        exact w_le_of_le hm (by have := hys y (by simp); omega)
      have := ih (fun z hz => hys z (by simp [hz]))
      nlinarith
  omega

/-- **Lemma 31.4**: both ends are attained. The completion with every free slot 0 under
`0^0 = 0` has sum `lo`, and the completion with every free slot `k - 1` under `0^0 = 1` has sum
`hi`. So the interval is the exact hull of the sums of the completions. -/
theorem lemma31_4_attained {k : ℕ} (hk : 2 ≤ k) (known : List ℕ) (rf : ℕ) :
    Fs 0 (known ++ List.replicate rf 0) = Fs 0 known ∧
      Fs 1 (known ++ List.replicate rf (k - 1)) = Fs 1 known + rf * (k - 1) ^ (k - 1) := by
  simp only [Fs_append, Fs_replicate, w_zero, mul_zero, add_zero, true_and]
  rw [w_of_ne_zero 1 (by omega)]

/-- **Proposition 31.5** (section 31.4.1), length `d = b`, `b ≥ 7`. A child of the root with
`e ≤ 2` copies of `b - 1` has `hi = e (b-1)^(b-1) + (b-e) (b-2)^(b-2) < b^(b-1)`, so it fails
the interval test. This is the inequality of Proposition 1.6. -/
theorem prop31_5_hi {b e : ℕ} (hb : 7 ≤ b) (he : e ≤ 2) :
    e * (b - 1) ^ (b - 1) + (b - e) * (b - 2) ^ (b - 2) < b ^ (b - 1) := by
  have := prop1_6_ineq hb
  have h1 : e * (b - 1) ^ (b - 1) ≤ 2 * (b - 1) ^ (b - 1) := Nat.mul_le_mul_right _ he
  have h2 : (b - e) * (b - 2) ^ (b - 2) ≤ b * (b - 2) ^ (b - 2) :=
    Nat.mul_le_mul_right _ (Nat.sub_le b e)
  omega

/-- **Proposition 31.5**, length `d = b - 1`. A child with `e ≥ 3` copies of `b - 1` has
`lo ≥ e (b-1)^(b-1) > b^(b-1)`, so it fails the interval test (section 1.7). -/
theorem prop31_5_lo {b e : ℕ} (hb : 2 ≤ b) (he : 3 ≤ e) :
    b ^ (b - 1) < e * (b - 1) ^ (b - 1) :=
  (pow_lt_three_mul b hb).trans_le (Nat.mul_le_mul_right _ he)

/-! ### Chapter 32: Pell equations for `(p, q, x)` and `(p, x, q)` -/

/-- For even `x`, `x^x = (x^(x/2))^2`. -/
lemma pow_self_eq_sq {x : ℕ} (hx : Even x) : x ^ x = (x ^ (x / 2)) ^ 2 := by
  rw [← pow_mul]; congr 1; obtain ⟨k, rfl⟩ := hx; omega

/-- **Section 32.1.1**, large digit last. If `(p, q, x)` is a solution in base `b`, `x ≥ 2` is
even and `p = n f^2`, then `U^2 - n V^2 = R` with `U = 2 p b + q`, `V = 2 f x^(x/2)` and
`R = q^2 + 4 p (w(p) + w(q) - x)`. -/
theorem pell_last {b m p q x n f : ℕ} (hs : IsSolution b m [p, q, x]) (hx : x ≠ 0)
    (hxe : Even x) (hp : p = n * f ^ 2) :
    ((2 * p * b + q : ℕ) : ℤ) ^ 2 - n * ((2 * f * x ^ (x / 2) : ℕ) : ℤ) ^ 2 =
      q ^ 2 + 4 * p * ((w m p : ℤ) + w m q - x) := by
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero m hx, pow_self_eq_sq hxe] at heq
  have hsq := complete_square (b := b) (p := p) (q := q) (r := x)
    (F := w m p + (w m q + (x ^ (x / 2)) ^ 2)) (by rw [← heq]; ring)
  rw [hsq, hp]; push_cast; ring

/-- **Section 32.1.1**, large digit in the middle. If `(p, x, q)` is a solution, `x ≥ 2` is even
and `p = n f^2`, then `U^2 - n V^2 = R` with `U = 2 p b + x`, `V = 2 f x^(x/2)` and
`R = x^2 + 4 p (w(p) + w(q) - q)`. -/
theorem pell_middle {b m p q x n f : ℕ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hxe : Even x) (hp : p = n * f ^ 2) :
    ((2 * p * b + x : ℕ) : ℤ) ^ 2 - n * ((2 * f * x ^ (x / 2) : ℕ) : ℤ) ^ 2 =
      x ^ 2 + 4 * p * ((w m p : ℤ) + w m q - q) := by
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero m hx, pow_self_eq_sq hxe] at heq
  have hsq := complete_square (b := b) (p := p) (q := x) (r := q)
    (F := w m p + ((x ^ (x / 2)) ^ 2 + w m q)) (by rw [← heq]; ring)
  rw [hsq, hp]; push_cast; ring

/-- `U^2 - n V^2 ≠ 0` when `n` is not a perfect square and `V ≠ 0`. -/
lemma sq_sub_mul_sq_ne_zero {n U V : ℕ} (hn : ¬ IsSquare n) (hV : V ≠ 0) :
    (U : ℤ) ^ 2 - n * V ^ 2 ≠ 0 := by
  intro h
  have : n * V ^ 2 = U ^ 2 := by
    have : (n : ℤ) * V ^ 2 = U ^ 2 := by linarith
    exact_mod_cast this
  obtain ⟨d, hd, -⟩ := isSquare_of_mul_sq hV this
  exact hn ⟨d, by rw [hd, sq]⟩

/-- **Section 32.1.1**: `R ≠ 0`. If `p = n f^2` with `n` not a square (for example squarefree
and `n > 1`), and `(p, q, x)` with `x ≥ 2` even is a solution, then
`q^2 + 4 p (w(p) + w(q) - x) ≠ 0`, since `R = 0` would make `n` a square. -/
theorem pell_last_R_ne_zero {b m p q x n f : ℕ} (hs : IsSolution b m [p, q, x]) (hx : x ≠ 0)
    (hxe : Even x) (hp : p = n * f ^ 2) (hn : ¬ IsSquare n) :
    (q : ℤ) ^ 2 + 4 * p * ((w m p : ℤ) + w m q - x) ≠ 0 := by
  have hp1 : p ≠ 0 := hs.head_ne_zero (by simp)
  have hf : f ≠ 0 := by rintro rfl; simp [hp] at hp1
  rw [← pell_last hs hx hxe hp]
  exact sq_sub_mul_sq_ne_zero hn (by positivity)

/-- `R ≠ 0` for the middle position. -/
theorem pell_middle_R_ne_zero {b m p q x n f : ℕ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hxe : Even x) (hp : p = n * f ^ 2) (hn : ¬ IsSquare n) :
    (x : ℤ) ^ 2 + 4 * p * ((w m p : ℤ) + w m q - q) ≠ 0 := by
  have hp1 : p ≠ 0 := hs.head_ne_zero (by simp)
  have hf : f ≠ 0 := by rintro rfl; simp [hp] at hp1
  rw [← pell_middle hs hx hxe hp]
  exact sq_sub_mul_sq_ne_zero hn (by positivity)

/-- Step 2 of **Theorem 32.2**: for even `x`, `2^(x/2 + 1)` divides `V = 2 f x^(x/2)`, so
`2^(x/2 + 2)` divides `β' - β = 2 V √n`. -/
theorem two_pow_dvd_V {x : ℕ} (hxe : Even x) (f : ℕ) : 2 ^ (x / 2 + 1) ∣ 2 * f * x ^ (x / 2) := by
  obtain ⟨y, hy⟩ := even_iff_two_dvd.1 hxe
  rw [hy, Nat.mul_div_cancel_left y (by norm_num), mul_pow]
  exact Dvd.intro (f * y ^ y) (by ring)

/-- The discriminant `D = q^2 + 4 p (w(p) + w(q) + x^x - x)` of `(p, q, x)` (section 32.1.4). -/
def discLast (m p q x : ℕ) : ℤ := (q : ℤ) ^ 2 + 4 * p * ((w m p : ℤ) + w m q + x ^ x - x)

/-- The discriminant `D = x^2 + 4 p (w(p) + x^x + w(q) - q)` of `(p, x, q)` (section 32.1.4). -/
def discMid (m p q x : ℕ) : ℤ := (x : ℤ) ^ 2 + 4 * p * ((w m p : ℤ) + x ^ x + w m q - q)

/-- **Section 32.1.4**, the test of the sieve. For `x ≥ 1`, `(p, q, x)` is a solution in base
`b` exactly when its digits are valid and `D = (2 p b + q)^2`. -/
theorem isSolution_last_iff_disc {b m p q x : ℕ} (hx : x ≠ 0) :
    IsSolution b m [p, q, x] ↔ (1 ≤ p ∧ p < b ∧ q < b ∧ x < b) ∧
      discLast m p q x = ((2 * p * b + q : ℕ) : ℤ) ^ 2 := by
  constructor
  · intro hs
    have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
    refine ⟨⟨hp, hs.lt_base p (by simp), hs.lt_base q (by simp), hs.lt_base x (by simp)⟩, ?_⟩
    have heq := hs.eq
    simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
      add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
    rw [w_of_ne_zero m hx] at heq
    have heqN : p * b ^ 2 + q * b + x = w m p + (w m q + x ^ x) := by rw [← heq]; ring
    have heqZ : (p : ℤ) * b ^ 2 + q * b + x = w m p + (w m q + x ^ x) := by exact_mod_cast heqN
    rw [discLast]; push_cast; linear_combination (-4 * (p : ℤ)) * heqZ
  · rintro ⟨⟨hp, hpb, hqb, hxb⟩, hD⟩
    refine ⟨?_, fun _ => by simp; omega, ?_⟩
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> assumption
    · simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
        add_zero, zero_add, pow_zero, pow_one, mul_one]
      rw [w_of_ne_zero m hx]
      rw [discLast] at hD; push_cast at hD
      have hpZ : (0 : ℤ) < 4 * p := by have : (1 : ℤ) ≤ p := by exact_mod_cast hp
                                       linarith
      have : (4 * p : ℤ) * (p * b ^ 2 + q * b + x) = 4 * p * (w m p + (w m q + x ^ x)) := by
        linear_combination (-1 : ℤ) * hD
      have hN : p * b ^ 2 + q * b + x = w m p + (w m q + x ^ x) := by
        exact_mod_cast mul_left_cancel₀ hpZ.ne' this
      rw [← hN]; ring

/-- **Section 32.1.4**, the soundness of the sieve, large digit last: if `(p, q, x)` with
`x ≥ 1` is a solution in some base, its discriminant `D` is a square modulo every `l`. So an
`x` whose `D` is a non-square modulo some prime is excluded. -/
theorem sieve_last {b m p q x : ℕ} (hx : x ≠ 0) (hs : IsSolution b m [p, q, x]) (l : ℕ) :
    IsSquare ((discLast m p q x : ℤ) : ZMod l) := by
  rw [((isSolution_last_iff_disc hx).1 hs).2]
  exact ⟨((2 * p * b + q : ℕ) : ZMod l), by push_cast; ring⟩

/-- **Section 32.1.4**, the test of the sieve for the middle position: for `x ≥ 1`, `(p, x, q)`
is a solution exactly when its digits are valid and `D = (2 p b + x)^2`. -/
theorem isSolution_mid_iff_disc {b m p q x : ℕ} (hx : x ≠ 0) :
    IsSolution b m [p, x, q] ↔ (1 ≤ p ∧ p < b ∧ q < b ∧ x < b) ∧
      discMid m p q x = ((2 * p * b + x : ℕ) : ℤ) ^ 2 := by
  constructor
  · intro hs
    have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
    refine ⟨⟨hp, hs.lt_base p (by simp), hs.lt_base q (by simp), hs.lt_base x (by simp)⟩, ?_⟩
    have heq := hs.eq
    simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
      add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
    rw [w_of_ne_zero m hx] at heq
    have heqN : p * b ^ 2 + x * b + q = w m p + (x ^ x + w m q) := by rw [← heq]; ring
    have heqZ : (p : ℤ) * b ^ 2 + x * b + q = w m p + (x ^ x + w m q) := by exact_mod_cast heqN
    rw [discMid]; push_cast; linear_combination (-4 * (p : ℤ)) * heqZ
  · rintro ⟨⟨hp, hpb, hqb, hxb⟩, hD⟩
    refine ⟨?_, fun _ => by simp; omega, ?_⟩
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> assumption
    · simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
        add_zero, zero_add, pow_zero, pow_one, mul_one]
      rw [w_of_ne_zero m hx]
      rw [discMid] at hD; push_cast at hD
      have hpZ : (0 : ℤ) < 4 * p := by have : (1 : ℤ) ≤ p := by exact_mod_cast hp
                                       linarith
      have : (4 * p : ℤ) * (p * b ^ 2 + x * b + q) = 4 * p * (w m p + (x ^ x + w m q)) := by
        linear_combination (-1 : ℤ) * hD
      have hN : p * b ^ 2 + x * b + q = w m p + (x ^ x + w m q) := by
        exact_mod_cast mul_left_cancel₀ hpZ.ne' this
      rw [← hN]; ring

/-- **Section 32.1.4**, the soundness of the sieve for the middle position. -/
theorem sieve_mid {b m p q x : ℕ} (hx : x ≠ 0) (hs : IsSolution b m [p, x, q]) (l : ℕ) :
    IsSquare ((discMid m p q x : ℤ) : ZMod l) := by
  rw [((isSolution_mid_iff_disc hx).1 hs).2]
  exact ⟨((2 * p * b + x : ℕ) : ZMod l), by push_cast; ring⟩

end Munchausen
