import Munchausen.SearchRules

/-!
# Three digits when the field changes: the elementary parts of chapter 36

* Section 36.1: for `(p, q, x)` with the large digit `x` last, the equation
  `U^2 + D = 4 p x^x` with `U = 2 p b + q` and `D = 4 p (x - W) - q^2`; Lemma 36.1 in elementary
  form: (a) every prime `l` of `x` has `v_l(D)` even and `-D / l^(v_l(D))` a nonzero square modulo
  `l` (that is, `l` splits in `Q(sqrt(-D))`), the rounding step of (b), and the step of (c)
  (`gcd(x, D) = 1` makes `U` prime to `x`).
* Lemma 36.2: the bound `‖L(1, χ)‖ ≤ log N + 2` for every nontrivial Dirichlet character, with
  the partial sums of norm at most `N / 2` and summation by parts. The class number formula is
  cited.
* Lehmer numbers, Lemma 36.4 (a primitive divisor `P` of `L_n`, `n` odd, has `P ≡ ±1 (mod 2n)`),
  and the theorems of Bilu, Hanrot and Voutier (Lemma 36.3) as hypotheses (`BHVTheorem`,
  `VoutierTheorem`): with them every Lehmer number `L_n`, `n ≥ 7` odd, `|α β| > 9`, has a prime
  factor `P ≥ 2n - 1` (Step 5 of Theorem 36.5).
* The arithmetic steps of Theorem 36.5, Corollary 36.7 (`gcd(x, D) = gcd(x, K0)`), the exact
  computation of Corollary 36.6 for `p = 1` and `x ≤ 7619`, the upper bound of Step 4 of
  Theorem 36.9, the local condition of Proposition 36.11 and the reduction of Proposition 36.12.
-/

namespace Munchausen

open Finset

/-! ### Section 36.1: the equation in the field of `R` -/

/-- The constant `D = 4 p (x - W) - q^2` of section 36.1.2, with `W = w(p) + w(q)`. For a
solution `(p, q, x)` it is `-R`, and it is positive once `x > W + q^2 / (4 p)`. -/
def fieldD (m p q x : ℕ) : ℤ := 4 * p * ((x : ℤ) - (w m p + w m q)) - q ^ 2

/-- `D = 4 p x - K0` with `K0 = q^2 + 4 p W` (proof of Corollary 36.7). -/
lemma fieldD_eq (m p q x : ℕ) :
    fieldD m p q x = 4 * p * x - ((q : ℤ) ^ 2 + 4 * p * (w m p + w m q)) := by
  rw [fieldD]; ring

/-- `D > 0` exactly when `4 p x > 4 p W + q^2`, that is `x > W + q^2 / (4 p)`. -/
lemma fieldD_pos_iff (m p q x : ℕ) :
    0 < fieldD m p q x ↔ 4 * p * (w m p + w m q) + q ^ 2 < 4 * p * x := by
  rw [fieldD]
  constructor
  · intro h; zify; linarith
  · intro h; zify at h; linarith

/-- **Section 36.1.2**, the equation. If `(p, q, x)` with `x ≥ 1` is a solution in base `b`,
then `U^2 + D = 4 p x^x` with `U = 2 p b + q`. So `μ = (U + sqrt(-D)) / 2` has norm `p x^x`. -/
theorem field_last {b m p q x : ℕ} (hs : IsSolution b m [p, q, x]) (hx : x ≠ 0) :
    ((2 * p * b + q : ℕ) : ℤ) ^ 2 + fieldD m p q x = 4 * p * x ^ x := by
  have h := ((isSolution_last_iff_disc hx).1 hs).2
  rw [discLast] at h
  rw [← h, fieldD]; ring

/-- **Section 36.1.2**: `(p, q, x)` with `x ≥ 1` is a solution in base `b` exactly when its
digits are valid and `U^2 + D = 4 p x^x`. -/
theorem isSolution_last_iff_field {b m p q x : ℕ} (hx : x ≠ 0) :
    IsSolution b m [p, q, x] ↔ (1 ≤ p ∧ p < b ∧ q < b ∧ x < b) ∧
      ((2 * p * b + q : ℕ) : ℤ) ^ 2 + fieldD m p q x = 4 * p * x ^ x := by
  rw [isSolution_last_iff_disc hx, discLast, fieldD]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩ <;> linear_combination -h

/-- **Section 36.1.2**: `μ = (U + sqrt(-D)) / 2` is an algebraic integer, since `U` and `D` have
the parity of `q` and `D ≡ -q^2 (mod 4)`. In integer terms: `U ≡ D (mod 2)` and
`U^2 + D ≡ 0 (mod 4)`. -/
theorem field_mu_integral (b m p q x : ℕ) :
    (2 : ℤ) ∣ (2 * p * b + q : ℕ) - fieldD m p q x ∧
      (4 : ℤ) ∣ ((2 * p * b + q : ℕ) : ℤ) ^ 2 + fieldD m p q x := by
  constructor
  · obtain ⟨r, hr⟩ := Int.even_mul_succ_self (q : ℤ)
    refine ⟨p * b - 2 * p * ((x : ℤ) - (w m p + w m q)) + r, ?_⟩
    rw [fieldD]; push_cast
    linear_combination hr
  · exact ⟨p ^ 2 * b ^ 2 + p * b * q + p * ((x : ℤ) - (w m p + w m q)),
      by rw [fieldD]; push_cast; ring⟩

/-- The valuation argument of **Lemma 36.1** (a). Let `l` be prime, `U, D ≥ 1`, `l^x ∣ U^2 + D`
and `D < l^x`. Then `D = l^(2k) u` with `l ∤ u` and `-u` a square modulo `l`. -/
lemma split_of_pow_dvd_sq_add {l x U D : ℕ} (hl : l.Prime) (hU : U ≠ 0) (hD : D ≠ 0)
    (hdvd : l ^ x ∣ U ^ 2 + D) (hDx : D < l ^ x) :
    ∃ k u : ℕ, D = l ^ (2 * k) * u ∧ ¬ l ∣ u ∧ ∃ y : ℕ, l ∣ y ^ 2 + u := by
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hD l hl.ne_one
  obtain ⟨j, U', hU', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hU l hl.ne_one
  have hl0 : 0 < l := hl.pos
  have hvx : v < x := by
    have : l ^ v ≤ l ^ v * u :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hu))
    exact (Nat.pow_lt_pow_iff_right hl.one_lt).1 (lt_of_le_of_lt this hDx)
  -- cancel `l^a` from `l^(a+1) ∣ l^a * Y`
  have cancel : ∀ a Y : ℕ, a + 1 ≤ x → l ^ a * Y = (l ^ j * U') ^ 2 + l ^ v * u → l ∣ Y := by
    intro a Y ha hY
    have h1 : l ^ a * l ∣ l ^ a * Y := by
      rw [← pow_succ, hY]; exact (pow_dvd_pow l ha).trans hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hl0 a) h1
  rcases lt_trichotomy (2 * j) v with h | h | h
  · exfalso
    have hY : l ^ (2 * j) * (U' ^ 2 + l ^ (v - 2 * j) * u) = (l ^ j * U') ^ 2 + l ^ v * u := by
      rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]; ring
    have := cancel _ _ (by omega) hY
    have h2 : l ∣ l ^ (v - 2 * j) * u := dvd_mul_of_dvd_left (dvd_pow_self l (by omega)) _
    have : l ∣ U' ^ 2 := (Nat.dvd_add_right h2).1 (by rwa [add_comm] at this)
    exact hU' (hl.dvd_of_dvd_pow this)
  · refine ⟨j, u, by rw [h], hu, U', ?_⟩
    have hY : l ^ v * (U' ^ 2 + u) = (l ^ j * U') ^ 2 + l ^ v * u := by rw [← h]; ring
    exact cancel _ _ (by omega) hY
  · exfalso
    have hY : l ^ v * (l ^ (2 * j - v) * U' ^ 2 + u) = (l ^ j * U') ^ 2 + l ^ v * u := by
      rw [mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h.le]; ring
    have := cancel _ _ (by omega) hY
    have h2 : l ∣ l ^ (2 * j - v) * U' ^ 2 := dvd_mul_of_dvd_left (dvd_pow_self l (by omega)) _
    exact hu ((Nat.dvd_add_right h2).1 this)

/-- **Lemma 36.1** (a), in elementary form. Let `(p, q, x)` be a solution with `D > 0` and
`D < 2^x` (the library assumes `x > 2 log2(p D)`, which gives this). Then every prime `l` of `x`
has `D = l^(2k) u` with `l ∤ u` and `-u` a nonzero square modulo `l`. For odd `l` this says that
`l` splits in `Q(sqrt(-D))`. -/
theorem lemma36_1_a {b m p q x l : ℕ} (hs : IsSolution b m [p, q, x]) (hx : x ≠ 0)
    (hl : l.Prime) (hlx : l ∣ x) (hD : 0 < fieldD m p q x) (hDx : fieldD m p q x < 2 ^ x) :
    ∃ (k : ℕ) (u : ℤ), fieldD m p q x = l ^ (2 * k) * u ∧ ¬ (l : ℤ) ∣ u ∧
      IsSquare ((-u : ℤ) : ZMod l) := by
  have heq := field_last hs hx
  obtain ⟨Dn, hDn⟩ : ∃ Dn : ℕ, fieldD m p q x = Dn := ⟨(fieldD m p q x).toNat, by omega⟩
  rw [hDn] at heq hD hDx
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have hb : p < b := hs.lt_base p (by simp)
  have hU : 2 * p * b + q ≠ 0 := by
    have : 0 < 2 * p * b := Nat.mul_pos (Nat.mul_pos two_pos hp) (by omega)
    omega
  have heqN : (2 * p * b + q) ^ 2 + Dn = 4 * p * x ^ x := by exact_mod_cast heq
  have hdvd : l ^ x ∣ (2 * p * b + q) ^ 2 + Dn := by
    rw [heqN]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hlx x) _
  have hDx' : Dn < l ^ x := by
    have : (Dn : ℤ) < 2 ^ x := hDx
    have h2 : 2 ^ x ≤ l ^ x := Nat.pow_le_pow_left hl.two_le x
    zify at h2 ⊢; linarith
  obtain ⟨k, u, hDu, hu, y, hy⟩ :=
    split_of_pow_dvd_sq_add hl hU (by omega) hdvd hDx'
  refine ⟨k, u, by rw [hDn, hDu]; push_cast; ring, by exact_mod_cast hu, ⟨(y : ZMod l), ?_⟩⟩
  have : ((y ^ 2 + u : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hy
  push_cast at this ⊢
  linear_combination -this

/-- The rounding step of **Lemma 36.1** (b). At a prime `l ∣ x` that splits into `L, L'`, let
`a ≤ a'` be the valuations of `μ` at the two primes, with `a + a' = e + x k`
(`e = v_l(p)`, `k = v_l(x) ≥ 1`) and `2 a ≤ d` (`d = v_l(D)`), and `2 (e + d) < x`. Then `a`
rounds to `0` and `a'` to `x k`, and the two remainders `a` and `a' - x k` have absolute values
summing to at most `max(e, d) ≤ e + d`.

The library's proof says "at most `v_l(p) + v_l(D)/2`". That is not right when `l ∣ gcd(U, D)`:
for `e = 0` and `a = d / 2 ≥ 1` the remainders are `a` and `-a`, with sum `d`. The bound
`s(J) ≤ log(p D)` of (b) still holds with `e + d` per prime. -/
theorem lemma36_1_round {a a' e k x d : ℕ} (hsum : a + a' = e + x * k) (hmin : 2 * a ≤ d)
    (hx : 2 * (e + d) < x) :
    2 * a < x ∧ 2 * |(a' : ℤ) - x * k| < x ∧ (a : ℤ) + |(a' : ℤ) - x * k| ≤ max e d := by
  have h : (a' : ℤ) - x * k = e - a := by zify at hsum; linarith
  rw [h]
  refine ⟨by omega, ?_, ?_⟩
  · rcases abs_cases ((e : ℤ) - a) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega
  · rcases abs_cases ((e : ℤ) - a) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · have : (e : ℤ) ≤ max e d := by exact_mod_cast le_max_left e d
      linarith
    · have : (d : ℤ) ≤ max e d := by exact_mod_cast le_max_right e d
      omega

/-- The example behind the correction in `lemma36_1_round`: with `e = 0`, `k = 1`, `d = 2` and
`a = 1`, `a' = x - 1`, the remainders sum to `2 > e + d / 2 = 1`. -/
example (x : ℕ) (hx : 2 ≤ x) : (1 : ℤ) + |((x - 1 : ℕ) : ℤ) - x * 1| = 2 := by
  rw [Nat.cast_sub (by omega)]; simp

/-- The step of **Lemma 36.1** (c): if `gcd(x, D) = 1`, then no prime of `x` divides `U`, so
the primes above `x` divide only one of `μ`, `μ'`, and the `x`-part of `(μ)` is `A^x` with
`N(A) = x`. -/
theorem lemma36_1_c {b m p q x : ℕ} (hs : IsSolution b m [p, q, x]) (hx : x ≠ 0)
    (hcop : IsCoprime (x : ℤ) (fieldD m p q x)) : IsCoprime (x : ℤ) ((2 * p * b + q : ℕ) : ℤ) := by
  have heq := field_last hs hx
  rw [Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
  by_contra hne
  obtain ⟨l, hl, hldvd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : (l : ℤ) ∣ x := (Int.natCast_dvd_natCast.2 hldvd).trans (Int.gcd_dvd_left _ _)
  have h2 : (l : ℤ) ∣ ((2 * p * b + q : ℕ) : ℤ) :=
    (Int.natCast_dvd_natCast.2 hldvd).trans (Int.gcd_dvd_right _ _)
  have h3 : (l : ℤ) ∣ fieldD m p q x := by
    have : fieldD m p q x = 4 * p * x ^ x - ((2 * p * b + q : ℕ) : ℤ) ^ 2 := by linarith
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right (dvd_pow h1 hx) _) (dvd_pow h2 two_ne_zero)
  have := Int.dvd_gcd h1 h3
  rw [hcop] at this
  exact hl.one_lt.ne' (Nat.dvd_one.1 this)

/-! ### Lemma 36.2: the value `L(1, χ)` -/

/-- Summation by parts, the tail estimate in the proof of **Lemma 36.2**: if the partial sums
`S(k) = a(0) + ... + a(k)` have norm at most `B` for `k ≥ N`, and the weights `c` are nonnegative
and decrease from `N + 1` on, then `‖∑_{N < k ≤ M} a(k) c(k)‖ ≤ 2 B c(N + 1)`. -/
theorem norm_sum_Ioc_mul_le {a : ℕ → ℂ} {c : ℕ → ℝ} {N M : ℕ} {B : ℝ} (hNM : N ≤ M)
    (hc : ∀ k, N < k → c (k + 1) ≤ c k) (hc0 : ∀ k, 0 ≤ c k)
    (hS : ∀ k, N ≤ k → ‖∑ i ∈ range (k + 1), a i‖ ≤ B) :
    ‖∑ k ∈ Ioc N M, a k * c k‖ ≤ 2 * B * c (N + 1) := by
  set S : ℕ → ℂ := fun k => ∑ i ∈ range (k + 1), a i with hSdef
  have inv : ∀ M, N ≤ M →
      ‖∑ k ∈ Ioc N M, a k * c k - S M * c (M + 1)‖ ≤ B * (2 * c (N + 1) - c (M + 1)) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      simp only [Ioc_self, sum_empty, zero_sub, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hc0 _)]
      have := hS N le_rfl
      nlinarith [hc0 (N + 1)]
    | succ M hM ih =>
      rw [sum_Ioc_succ_top hM]
      have ha : a (M + 1) = S (M + 1) - S M := by
        simp only [hSdef, sum_range_succ]; ring
      have e : ∑ k ∈ Ioc N M, a k * c k + a (M + 1) * c (M + 1) - S (M + 1) * c (M + 1 + 1) =
          (∑ k ∈ Ioc N M, a k * c k - S M * c (M + 1)) +
            S (M + 1) * ((c (M + 1) - c (M + 2) : ℝ) : ℂ) := by
        rw [ha]; push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.2 (hc (M + 1) (by omega)))]
      have := hS (M + 1) (by omega)
      have h2 : 0 ≤ c (M + 1) - c (M + 2) := sub_nonneg.2 (hc (M + 1) (by omega))
      calc _ ≤ B * (2 * c (N + 1) - c (M + 1)) + B * (c (M + 1) - c (M + 2)) := by
            gcongr
        _ = _ := by ring
  have h1 := inv M hNM
  have h2 : ‖S M * c (M + 1)‖ ≤ B * c (M + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 _)]
    exact mul_le_mul_of_nonneg_right (hS M hNM) (hc0 _)
  calc ‖∑ k ∈ Ioc N M, a k * c k‖
      = ‖(∑ k ∈ Ioc N M, a k * c k - S M * c (M + 1)) + S M * c (M + 1)‖ := by ring_nf
    _ ≤ B * (2 * c (N + 1) - c (M + 1)) + B * c (M + 1) :=
        (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * B * c (N + 1) := by ring

/-- A sequence of period `N` sums to the same value over any `N` consecutive terms. -/
lemma sum_range_shift_of_periodic {a : ℕ → ℂ} {N : ℕ} (hper : Function.Periodic a N) (j : ℕ) :
    ∑ k ∈ range N, a (j + k) = ∑ k ∈ range N, a k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have h1 := sum_range_succ (fun k => a (j + k)) N
    have h2 := sum_range_succ' (fun k => a (j + k)) N
    have h3 : a (j + N) = a (j + 0) := by rw [add_zero]; exact hper j
    have : ∑ k ∈ range N, a (j + 1 + k) = ∑ k ∈ range N, a (j + (k + 1)) := by
      refine sum_congr rfl fun k _ => by rw [add_assoc, add_comm 1 k]
    rw [this]
    linear_combination h2.symm.trans h1 + h3

/-- The partial sums in the proof of **Lemma 36.2**: a sequence of period `N` with values of norm
at most 1 and sum 0 over a period (a nontrivial character modulo `N`) has all partial sums of
norm at most `N / 2`. A partial sum is minus the sum over the rest of the period, and one of the
two pieces has at most `N / 2` terms. -/
theorem norm_sum_range_le_half {a : ℕ → ℂ} {N : ℕ} (hN : 0 < N) (hper : Function.Periodic a N)
    (hsum : ∑ k ∈ range N, a k = 0) (ha : ∀ k, ‖a k‖ ≤ 1) (t : ℕ) :
    ‖∑ k ∈ range t, a k‖ ≤ N / 2 := by
  have hred : ∀ q r, ∑ k ∈ range (N * q + r), a k = ∑ k ∈ range r, a k := by
    intro q r
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show N * (q + 1) + r = (N * q + r) + N by ring, sum_range_add, ih,
        sum_range_shift_of_periodic hper, hsum, add_zero]
  rw [← Nat.div_add_mod t N, hred]
  set r := t % N
  have hr : r < N := Nat.mod_lt t hN
  have hsplit := sum_range_add_sum_Ico a hr.le
  rw [hsum] at hsplit
  have h1 : ‖∑ k ∈ range r, a k‖ ≤ r := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ range r, ‖a k‖ ≤ ∑ _k ∈ range r, (1 : ℝ) := sum_le_sum fun k _ => ha k
      _ = r := by simp
  have h2 : ‖∑ k ∈ range r, a k‖ ≤ (N : ℝ) - r := by
    rw [show ∑ k ∈ range r, a k = -∑ k ∈ Ico r N, a k by linear_combination hsplit, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Ico r N, ‖a k‖ ≤ ∑ _k ∈ Ico r N, (1 : ℝ) := sum_le_sum fun k _ => ha k
      _ = (N : ℝ) - r := by simp [Nat.cast_sub hr.le]
  linarith

/-- **Lemma 36.2**, the partial sums of the `L`-series. For a nontrivial Dirichlet character `χ`
modulo `N` and real `σ ≥ 1`, every partial sum of `∑ χ(n) / n^σ` has norm at most `log N + 2`:
the terms up to `N` give at most `1 + log N`, and summation by parts with partial sums of norm at
most `N / 2` bounds the rest by `N / (N + 1) < 1`. -/
theorem lemma36_2_partial {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ : ℝ}
    (hσ : 1 ≤ σ) (M : ℕ) :
    ‖∑ n ∈ range M, LSeries.term (fun n => χ n) σ n‖ ≤ Real.log N + 2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set a : ℕ → ℂ := fun n => χ n with ha_def
  set c : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ σ with hc_def
  have hterm : ∀ n, 0 < n → LSeries.term (fun n => χ n) σ n = a n * c n := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn.ne', hc_def, ha_def]
    simp only
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast; ring
  have hc0 : ∀ n, 0 ≤ c n := fun n => by simp only [hc_def]; positivity
  have hcle : ∀ n, 0 < n → c n ≤ 1 / (n : ℝ) := by
    intro n hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [hc_def]
    gcongr
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le h1 hσ
  have hanti : ∀ k, 0 < k → c (k + 1) ≤ c k := by
    intro k hk
    simp only [hc_def]
    have : (0 : ℝ) < k := by exact_mod_cast hk
    gcongr
    · linarith
  have hnorm : ∀ n, 0 < n → ‖LSeries.term (fun n => χ n) σ n‖ ≤ 1 / (n : ℝ) := by
    intro n hn
    rw [hterm n hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc0 n)]
    have := DirichletCharacter.norm_le_one χ (n : ZMod N)
    calc ‖a n‖ * c n ≤ 1 * (1 / (n : ℝ)) :=
          mul_le_mul this (hcle n hn) (hc0 n) zero_le_one
      _ = 1 / (n : ℝ) := one_mul _
  -- the head: the terms up to `N`
  have head : ∑ n ∈ range (N + 1), ‖LSeries.term (fun n => χ n) σ n‖ ≤ 1 + Real.log N := by
    rw [sum_range_succ', LSeries.term_zero, norm_zero, add_zero]
    refine le_trans ?_ (harmonic_le_one_add_log N)
    rw [harmonic, Rat.cast_sum]
    refine sum_le_sum fun n _ => ?_
    have := hnorm (n + 1) (Nat.succ_pos n)
    push_cast at this ⊢
    simpa using this
  rcases le_or_gt M (N + 1) with hM | hM
  · refine (norm_sum_le _ _).trans (le_trans ?_ (head.trans (by linarith)))
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hM) fun _ _ _ => norm_nonneg _
  -- the tail, by summation by parts
  obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
  have hper : Function.Periodic a N := fun n => by
    simp only [ha_def]; push_cast; rw [ZMod.natCast_self, add_zero]
  have hsum : ∑ k ∈ range N, a k = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    refine sum_bij (fun k _ => (k : ZMod N)) (by simp) (fun i hi j hj h => ?_)
      (fun x _ => ⟨x.val, by simp [ZMod.val_lt], by simp⟩) (fun _ _ => rfl)
    have := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hi),
      Nat.mod_eq_of_lt (mem_range.1 hj)] at this
    exact this
  have hS : ∀ k, N ≤ k → ‖∑ i ∈ range (k + 1), a i‖ ≤ (N : ℝ) / 2 := fun k _ =>
    norm_sum_range_le_half hN hper hsum (fun n => DirichletCharacter.norm_le_one χ _) _
  have htail := norm_sum_Ioc_mul_le (a := a) (c := c) (N := N) (M := K) (B := (N : ℝ) / 2)
    (by omega) (fun k hk => hanti k (by omega)) hc0 hS
  rw [← sum_range_add_sum_Ico _ (show N + 1 ≤ K + 1 by omega), Finset.Ico_add_one_add_one_eq_Ioc]
  have he : ∑ k ∈ Ioc N K, LSeries.term (fun n => χ n) σ k = ∑ k ∈ Ioc N K, a k * c k :=
    sum_congr rfl fun k hk => hterm k (by have := (mem_Ioc.1 hk).1; omega)
  rw [he]
  have hcN : c (N + 1) ≤ 1 / ((N + 1 : ℕ) : ℝ) := hcle (N + 1) (Nat.succ_pos N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 2 * ((N : ℝ) / 2) * c (N + 1) ≤ 1 := by
    have : 2 * ((N : ℝ) / 2) * (1 / ((N + 1 : ℕ) : ℝ)) ≤ 1 := by
      push_cast; rw [mul_one_div, div_le_one (by positivity)]; linarith
    exact le_trans (by gcongr) this
  calc _ ≤ ‖∑ n ∈ range (N + 1), LSeries.term (fun n => χ n) σ n‖ + ‖∑ k ∈ Ioc N K, a k * c k‖ :=
        norm_add_le _ _
    _ ≤ (1 + Real.log N) + 1 := add_le_add ((norm_sum_le _ _).trans head) (htail.trans h1)
    _ = Real.log N + 2 := by ring

/-- **Lemma 36.2**, the value at 1: for a nontrivial Dirichlet character `χ` modulo `N`,
`‖L(1, χ)‖ ≤ log N + 2`. The value `L(1, χ)` is Mathlib's analytic continuation; it is the limit
of `L(σ, χ)` as `σ → 1+`, where the series converges and `lemma36_2_partial` bounds it. -/
theorem lemma36_2 {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ Real.log N + 2 := by
  have hbound : ∀ σ : ℝ, 1 < σ → ‖χ.LFunction σ‖ ≤ Real.log N + 2 := by
    intro σ hσ
    have hre : 1 < (σ : ℂ).re := by simpa using hσ
    rw [DirichletCharacter.LFunction_eq_LSeries χ hre]
    have hs := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hre).LSeriesHasSum
    have ht := (HasSum.tendsto_sum_nat hs).norm
    exact le_of_tendsto' ht fun M => lemma36_2_partial χ hχ hσ.le M
  have hcont : ContinuousAt χ.LFunction 1 :=
    (DirichletCharacter.differentiableAt_LFunction χ 1 (Or.inr hχ)).continuousAt
  have hlim : Filter.Tendsto (fun σ : ℝ => χ.LFunction σ) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (χ.LFunction 1)) := by
    have h1 : Filter.Tendsto (fun σ : ℝ => (σ : ℂ)) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
      have := (Complex.continuous_ofReal.tendsto 1).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using this
    exact hcont.tendsto.comp h1
  exact le_of_tendsto hlim.norm (eventually_nhdsWithin_of_forall fun σ hσ => hbound σ hσ)

/-! ### Lehmer numbers and Lemma 36.4 -/

/-- The Lehmer numbers of the pair with parameters `R = (α + β)^2` and `Q = α β`:
`L_n = (α^n - β^n) / (α - β)` for odd `n` and `(α^n - β^n) / (α^2 - β^2)` for even `n`, given by
their recurrence. -/
def lehmer (R Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => (if Even n then 1 else R) * lehmer R Q (n + 1) - Q * lehmer R Q n

@[simp] lemma lehmer_zero (R Q : ℤ) : lehmer R Q 0 = 0 := rfl
@[simp] lemma lehmer_one (R Q : ℤ) : lehmer R Q 1 = 1 := rfl

lemma lehmer_add_two (R Q : ℤ) (n : ℕ) :
    lehmer R Q (n + 2) = (if Even n then 1 else R) * lehmer R Q (n + 1) - Q * lehmer R Q n :=
  rfl

/-- The Lehmer numbers in a commutative ring that holds `α` and `β`: if `(α + β)^2 = R` and
`α β = Q`, then `α^n - β^n = (α - β) L_n` for odd `n` and `(α - β) (α + β) L_n` for even `n`. -/
theorem pow_sub_pow_eq_lehmer {A : Type*} [CommRing A] {R Q : ℤ} {α β : A}
    (hR : (α + β) ^ 2 = R) (hQ : α * β = Q) (n : ℕ) :
    α ^ n - β ^ n = (α - β) * (if Even n then α + β else 1) * lehmer R Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp
    | 1, _ => simp
    | n + 2, ih =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have hrec : α ^ (n + 2) - β ^ (n + 2) =
          (α + β) * (α ^ (n + 1) - β ^ (n + 1)) - α * β * (α ^ n - β ^ n) := by ring
      rw [hrec, h1, h0, lehmer_add_two]
      rcases Nat.even_or_odd n with hn | hn
      · have hn1 : ¬ Even (n + 1) := by rw [Nat.not_even_iff_odd]; exact hn.add_one
        have hn2 : Even (n + 2) := hn.add (by decide)
        simp only [hn, hn1, hn2, ite_true, ite_false]
        push_cast
        rw [hQ]; ring
      · have hn0 : ¬ Even n := Nat.not_even_iff_odd.2 hn
        have hn1 : Even (n + 1) := hn.add_one
        have hn2 : ¬ Even (n + 2) := by
          rw [Nat.not_even_iff_odd]; exact hn.add_even (by decide)
        simp only [hn0, hn1, hn2, ite_true, ite_false]
        push_cast
        rw [← hR, hQ]; ring

/-- **Lemma 36.4** (section 36.2.1). Let `L_n` be the Lehmer numbers of the parameters
`R = (α + β)^2`, `Q = α β`, let `n ≥ 5` be odd and `P` a primitive divisor of `L_n`: a prime
that divides `L_n` but not `(α^2 - β^2)^2 = R (R - 4 Q)` and no `L_d` with `1 ≤ d < n`. Then `P`
is odd and `P ≡ ±1 (mod 2n)`, so `P ≥ 2n - 1`.

The library states this for `n ≥ 7` and a Lehmer pair. The proof uses only that `P` does not
divide `R (R - 4 Q)`: it works in an algebraic closure of `ZMod P`, where `z = α / β` has order
`n` and `z + 1/z = (R - 2Q)/Q` is fixed by Frobenius, so `z^P = z` or `z^P = 1/z`. -/
theorem lemma36_4 {R Q : ℤ} {n P : ℕ} (hP : P.Prime) (hn : Odd n) (hn5 : 5 ≤ n)
    (hdvd : (P : ℤ) ∣ lehmer R Q n) (hRQ : ¬ (P : ℤ) ∣ R * (R - 4 * Q))
    (hprim : ∀ d, 0 < d → d < n → ¬ (P : ℤ) ∣ lehmer R Q d) :
    Odd P ∧ ((P : ℤ) ≡ 1 [ZMOD 2 * n] ∨ (P : ℤ) ≡ -1 [ZMOD 2 * n]) ∧ 2 * n - 1 ≤ P := by
  have := Fact.mk hP
  set F := AlgebraicClosure (ZMod P)
  have hcast : ∀ a : ℤ, (a : F) = 0 ↔ (P : ℤ) ∣ a := CharP.intCast_eq_zero_iff F P
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((R : ℤ) : F) (n := 2) (by norm_num)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    (Polynomial.X ^ 2 - Polynomial.C s * Polynomial.X + Polynomial.C ((Q : ℤ) : F))
    (by
      have : (Polynomial.X ^ 2 - Polynomial.C s * Polynomial.X +
          Polynomial.C ((Q : ℤ) : F)).degree = 2 := by compute_degree!
      rw [this]; norm_num)
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at hα
  set β := s - α with hβ
  have hsum : α + β = s := by rw [hβ]; ring
  have hprod : α * β = ((Q : ℤ) : F) := by rw [hβ]; linear_combination -hα
  have hR : (α + β) ^ 2 = ((R : ℤ) : F) := by rw [hsum, hs]
  have key := pow_sub_pow_eq_lehmer hR hprod
  have hR0 : ((R : ℤ) : F) ≠ 0 := fun h => hRQ (dvd_mul_of_dvd_left ((hcast R).1 h) _)
  have hRQ0 : ((R - 4 * Q : ℤ) : F) ≠ 0 := fun h => hRQ (dvd_mul_of_dvd_right ((hcast _).1 h) _)
  have hs0 : α + β ≠ 0 := by
    intro h; apply hR0; rw [← hR, h]; ring
  have hsub0 : α - β ≠ 0 := by
    intro h; apply hRQ0
    have : (α - β) ^ 2 = ((R - 4 * Q : ℤ) : F) := by
      push_cast; rw [← hR, ← hprod]; ring
    rw [← this, h]; ring
  -- `L_d = 0` in `F` exactly when `α^d = β^d`, for `d ≥ 1`
  have hL : ∀ d, ((lehmer R Q d : ℤ) : F) = 0 ↔ α ^ d = β ^ d := by
    intro d
    rw [← sub_eq_zero (a := α ^ d), key d]
    split_ifs <;> simp [hsub0, hs0]
  have hLn : α ^ n = β ^ n := (hL n).1 ((hcast _).2 hdvd)
  have hβ0 : β ≠ 0 := by
    intro h0
    have : α ^ n = 0 := by rw [hLn, h0, zero_pow (by omega)]
    have hα0 : α = 0 := pow_eq_zero_iff (by omega) |>.1 this
    exact hs0 (by rw [hα0, h0]; ring)
  have hα0 : α ≠ 0 := by
    intro h0
    have : β ^ n = 0 := by rw [← hLn, h0, zero_pow (by omega)]
    have hb0 : β = 0 := pow_eq_zero_iff (by omega) |>.1 this
    exact hs0 (by rw [h0, hb0]; ring)
  set z := α / β with hz
  have hzpow : ∀ d, z ^ d = 1 ↔ α ^ d = β ^ d := by
    intro d
    rw [hz, div_pow, div_eq_one_iff_eq (pow_ne_zero _ hβ0)]
  have horder : orderOf z = n := by
    rw [orderOf_eq_iff (by omega)]
    refine ⟨(hzpow n).2 hLn, fun d hd hd0 h =>
      hprim d hd0 hd ((hcast _).1 ((hL d).2 ((hzpow d).1 h)))⟩
  have hz0 : z ≠ 0 := div_ne_zero hα0 hβ0
  -- `z + 1/z` lies in the prime field, so Frobenius fixes it
  have hc : z + z⁻¹ = ((R - 2 * Q : ℤ) : F) / ((Q : ℤ) : F) := by
    have hQ0 : ((Q : ℤ) : F) ≠ 0 := by rw [← hprod]; exact mul_ne_zero hα0 hβ0
    have e : (α / β + β / α) * (α * β) = α ^ 2 + β ^ 2 := by
      rw [div_add_div _ _ hβ0 hα0, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hβ0 hα0)]; ring
    rw [eq_div_iff hQ0, ← hprod, hz, inv_div, e]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    rw [← hR, ← hprod]; ring
  have hfrob : (z + z⁻¹) ^ P = z + z⁻¹ := by
    rw [hc, div_pow]
    have h1 : ∀ a : ℤ, ((a : ℤ) : F) ^ P = a := fun a => by
      have := frobenius_def (R := F) P (a : F)
      rw [← this]; exact map_intCast _ a
    rw [h1, h1]
  rw [add_pow_char, inv_pow] at hfrob
  have hzP0 : z ^ P ≠ 0 := pow_ne_zero _ hz0
  have hquad : (z ^ P - z) * (z ^ P - z⁻¹) = 0 := by
    have : (z ^ P - z) * (z ^ P - z⁻¹) = z ^ P * ((z ^ P + (z ^ P)⁻¹) - (z + z⁻¹)) := by
      linear_combination mul_inv_cancel₀ hz0 - mul_inv_cancel₀ hzP0
    rw [this, hfrob, sub_self, mul_zero]
  have hdiv : n ∣ P - 1 ∨ n ∣ P + 1 := by
    have hP1 : 1 ≤ P := hP.one_lt.le
    rcases mul_eq_zero.1 hquad with h | h
    · left
      rw [← horder]
      apply orderOf_dvd_of_pow_eq_one
      have : z ^ P = z ^ (P - 1) * z := by rw [← pow_succ, Nat.sub_add_cancel hP1]
      rw [sub_eq_zero, this] at h
      exact (mul_eq_right₀ hz0).1 h
    · right
      rw [← horder]
      apply orderOf_dvd_of_pow_eq_one
      rw [sub_eq_zero] at h
      rw [pow_succ, h, inv_mul_cancel₀ hz0]
  -- the arithmetic
  have hPodd : Odd P := by
    rcases hP.eq_two_or_odd' with h2 | h
    · subst h2
      rcases hdiv with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact h
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn
  have hP1 : 1 ≤ P := hP.one_lt.le
  have hP2 := hP.two_le
  obtain ⟨k, hk⟩ := hPodd
  refine ⟨⟨k, hk⟩, ?_⟩
  rcases hdiv with h | h
  · have h2n : 2 * n ∣ P - 1 := hcop.mul_dvd_of_dvd_of_dvd ⟨k, by omega⟩ h
    have hZ : ((2 * n : ℕ) : ℤ) ∣ ((P - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h2n
    push_cast [Nat.cast_sub hP1] at hZ
    have hle := Nat.le_of_dvd (by omega) h2n
    exact ⟨Or.inl (Int.modEq_iff_dvd.2 hZ).symm, by omega⟩
  · have h2n : 2 * n ∣ P + 1 := hcop.mul_dvd_of_dvd_of_dvd ⟨k + 1, by omega⟩ h
    have hZ : ((2 * n : ℕ) : ℤ) ∣ ((P + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h2n
    push_cast at hZ
    have hle := Nat.le_of_dvd (by omega) h2n
    refine ⟨Or.inr (Int.modEq_iff_dvd.2 ?_).symm, by omega⟩
    simpa using hZ

/-- For odd `n` the Lehmer number is `L_n = (α^n - β^n) / (α - β)`, for complex `α ≠ β` with
`(α + β)^2 = R` and `α β = Q`. -/
theorem lehmer_eq_div {R Q : ℤ} {α β : ℂ} (hR : (α + β) ^ 2 = R) (hQ : α * β = Q) (hαβ : α ≠ β)
    {n : ℕ} (hn : Odd n) : (lehmer R Q n : ℂ) = (α ^ n - β ^ n) / (α - β) := by
  rw [pow_sub_pow_eq_lehmer hR hQ n]
  simp only [Nat.not_even_iff_odd.2 hn, ite_false, mul_one]
  rw [mul_div_cancel_left₀ _ (sub_ne_zero.2 hαβ)]

/-- A Lehmer pair, given by its parameters (section 36.2.1): `R = (α + β)^2` and `Q = α β` are
nonzero coprime integers, and `α / β` is not a root of unity. The last condition is stated for
every complex `α, β` with these parameters; they are determined up to a common sign and order,
which does not change it. -/
def IsLehmerPair (R Q : ℤ) : Prop :=
  R ≠ 0 ∧ Q ≠ 0 ∧ IsCoprime R Q ∧
    ∀ α β : ℂ, (α + β) ^ 2 = R → α * β = Q → ∀ k : ℕ, 0 < k → (α / β) ^ k ≠ 1

/-- A primitive divisor of `L_n` (section 36.2.1): a prime that divides `L_n` but not
`(α^2 - β^2)^2 L_1 ⋯ L_(n-1)`, where `(α^2 - β^2)^2 = R (R - 4 Q)`. -/
def IsPrimitiveDivisor (R Q : ℤ) (n P : ℕ) : Prop :=
  P.Prime ∧ (P : ℤ) ∣ lehmer R Q n ∧
    ¬ (P : ℤ) ∣ R * (R - 4 * Q) * ∏ d ∈ Ico 1 n, lehmer R Q d

/-- The theorem of Bilu, Hanrot and Voutier (**Lemma 36.3** (a), cited): for every Lehmer pair
and every `n > 30`, `L_n` has a primitive divisor. It is used only as a hypothesis. -/
def BHVTheorem : Prop :=
  ∀ R Q : ℤ, IsLehmerPair R Q → ∀ n : ℕ, 30 < n → ∃ P, IsPrimitiveDivisor R Q n P

/-- The table of **Lemma 36.3** (b): for odd `7 ≤ n ≤ 29`, the pairs `(a, b) = (R, R - 4 Q)`
of the Lehmer pairs without a primitive divisor of `L_n`, up to equivalence. -/
def voutierTable : ℕ → List (ℤ × ℤ)
  | 7 => [(1, -7), (1, -19), (3, -5), (5, -7), (13, -3), (14, -22)]
  | 9 => [(5, -3), (7, -1), (7, -5)]
  | 13 => [(1, -7)]
  | 15 => [(7, -1), (10, -2)]
  | _ => []

/-- Voutier's theorem (**Lemma 36.3** (b), cited): for odd `7 ≤ n ≤ 29`, a Lehmer pair without
a primitive divisor of `L_n` is equivalent to one of `voutierTable n`. Equivalent pairs have
`α_1 / α_2 = β_1 / β_2 ∈ {±1, ±i}`; the factor `±i` changes `(R, Q)` to `(-R, -Q)`. It is used
only as a hypothesis. -/
def VoutierTheorem : Prop :=
  ∀ R Q : ℤ, IsLehmerPair R Q → ∀ n : ℕ, Odd n → 7 ≤ n → n ≤ 29 →
    (∀ P, ¬ IsPrimitiveDivisor R Q n P) →
      (R, R - 4 * Q) ∈ voutierTable n ∨ (-R, -(R - 4 * Q)) ∈ voutierTable n

/-- **Lemma 36.3** (b): every pair of the table has `|α β| = |a - b| / 4 ≤ 9`. -/
lemma voutierTable_abs_le : ∀ n < 30, ∀ ab ∈ voutierTable n, |ab.1 - ab.2| ≤ 36 := by
  decide

/-- A primitive divisor satisfies the hypotheses of `lemma36_4`. -/
lemma IsPrimitiveDivisor.not_dvd {R Q : ℤ} {n P : ℕ} (h : IsPrimitiveDivisor R Q n P) :
    ¬ (P : ℤ) ∣ R * (R - 4 * Q) ∧ ∀ d, 0 < d → d < n → ¬ (P : ℤ) ∣ lehmer R Q d := by
  obtain ⟨hP, -, hnd⟩ := h
  refine ⟨fun h => hnd (dvd_mul_of_dvd_left h _), fun d hd0 hdn h => hnd ?_⟩
  exact dvd_mul_of_dvd_right (h.trans (Finset.dvd_prod_of_mem _ (mem_Ico.2 ⟨hd0, hdn⟩))) _

/-- Step 5 of **Theorem 36.5**, from the cited theorems. Assume Lemma 36.3 (`BHVTheorem`,
`VoutierTheorem`). For a Lehmer pair with `|α β| > 9` and odd `n ≥ 7`, `L_n` has a primitive
divisor `P`, and by Lemma 36.4 `P ≡ ±1 (mod 2n)` and `P ≥ 2n - 1`. -/
theorem exists_large_primitive_divisor (hB : BHVTheorem) (hV : VoutierTheorem) {R Q : ℤ}
    (hL : IsLehmerPair R Q) (hQ : 9 < |Q|) {n : ℕ} (hn : Odd n) (hn7 : 7 ≤ n) :
    ∃ P, IsPrimitiveDivisor R Q n P ∧
      ((P : ℤ) ≡ 1 [ZMOD 2 * n] ∨ (P : ℤ) ≡ -1 [ZMOD 2 * n]) ∧ 2 * n - 1 ≤ P := by
  have hex : ∃ P, IsPrimitiveDivisor R Q n P := by
    rcases lt_or_ge 30 n with h | h
    · exact hB R Q hL n h
    · by_contra hne
      push Not at hne
      have hn29 : n ≤ 29 := by
        rcases hn with ⟨k, rfl⟩; omega
      have hmem := hV R Q hL n hn hn7 hn29 hne
      have hab := voutierTable_abs_le n (by omega)
      rcases hmem with hm | hm
      · have := hab _ hm
        simp only at this
        rw [show R - (R - 4 * Q) = 4 * Q by ring, abs_mul] at this
        norm_num at this; omega
      · have := hab _ hm
        simp only at this
        rw [show -R - -(R - 4 * Q) = -(4 * Q) by ring, abs_neg, abs_mul] at this
        norm_num at this; omega
  obtain ⟨P, hP⟩ := hex
  obtain ⟨h1, h2⟩ := hP.not_dvd
  obtain ⟨-, hmod, hle⟩ := lemma36_4 hP.1 hn (by omega) hP.2.1 h1 h2
  exact ⟨P, hP, hmod, hle⟩

/-! ### Theorem 36.5 and Corollaries 36.6, 36.7: the elementary steps -/

/-- `D < 4 p x`: in `D = 4 p x - K0` the constant `K0 = q^2 + 4 p W` is positive. -/
lemma fieldD_lt {m p q x : ℕ} (hp : 1 ≤ p) : fieldD m p q x < 4 * p * x := by
  rw [fieldD_eq]
  have : (1 : ℤ) ≤ w m p := by
    rw [w_of_ne_zero m (by omega)]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have : (0 : ℤ) ≤ w m q := by positivity
  nlinarith

/-- Step 3 of **Theorem 36.5**: `U^2 > 3 D` for `x ≥ 3`. So the argument `θ` of `μ`, with
`tan θ = sqrt(D) / U`, is below `π / 6`, and `α / β` is not a root of unity. -/
theorem theorem36_5_step3 {b m p q x : ℕ} (hs : IsSolution b m [p, q, x]) (hx : 3 ≤ x) :
    3 * fieldD m p q x < ((2 * p * b + q : ℕ) : ℤ) ^ 2 := by
  have heq := field_last hs (by omega)
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have hlt := fieldD_lt (m := m) (q := q) (x := x) hp
  have hxx : 4 * x ≤ x ^ x := by
    have h3 : x ^ 3 ≤ x ^ x := Nat.pow_le_pow_right (by omega) hx
    have : 4 * x ≤ x ^ 3 := by
      rw [pow_succ, pow_two]
      exact Nat.mul_le_mul_right x (by nlinarith)
    omega
  have hxx' : (4 * x : ℤ) ≤ (x : ℤ) ^ x := by exact_mod_cast hxx
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- Steps 5 and 6 of **Theorem 36.5**, the final inequalities. Let `x = t n` with `n` odd,
`t ≤ h` (the order of the class of `A` is at most the class number `h`), and
`h ≤ 2 sqrt(D0) L` with `L = (log 4D + 2) / π` (Lemma 36.2 with `|Δ_K| ≤ 4 D0`), `D0 ≤ D`.
If `n ≥ 7`, assume `(2n - 1)^2 D0 ≤ D` (a primitive divisor `P ≥ 2n - 1` of `L_n` divides `f`,
`D = f^2 D0`). Then `x ≤ 10 sqrt(D) L`. -/
theorem theorem36_5_final {x t n : ℕ} {h D D0 L : ℝ} (hx : x = t * n) (hn : Odd n)
    (hth : (t : ℝ) ≤ h) (hh : h ≤ 2 * Real.sqrt D0 * L) (hL : 0 ≤ L)
    (hD0D : D0 ≤ D) (hP : 7 ≤ n → (2 * n - 1 : ℝ) ^ 2 * D0 ≤ D) :
    (x : ℝ) ≤ 10 * Real.sqrt D * L := by
  have hs0 : Real.sqrt D0 ≤ Real.sqrt D := Real.sqrt_le_sqrt hD0D
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  rw [hx]; push_cast
  rcases le_or_gt n 5 with h5 | h7
  · have hn5 : (n : ℝ) ≤ 5 := by exact_mod_cast h5
    calc (t : ℝ) * n ≤ t * 5 := by gcongr
      _ ≤ 2 * Real.sqrt D0 * L * 5 := by nlinarith
      _ ≤ 2 * Real.sqrt D * L * 5 := by gcongr
      _ = 10 * Real.sqrt D * L := by ring
  · have h7' : 7 ≤ n := by rcases hn with ⟨k, rfl⟩; omega
    have hn7 : (7 : ℝ) ≤ n := by exact_mod_cast h7'
    have hsq : (2 * n - 1 : ℝ) * Real.sqrt D0 ≤ Real.sqrt D := by
      have h1 : (0 : ℝ) ≤ 2 * n - 1 := by linarith
      calc (2 * n - 1 : ℝ) * Real.sqrt D0 = Real.sqrt ((2 * n - 1) ^ 2 * D0) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1]
        _ ≤ Real.sqrt D := Real.sqrt_le_sqrt (hP h7')
    have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
    have hsD0 : 0 ≤ Real.sqrt D0 := Real.sqrt_nonneg _
    calc (t : ℝ) * n ≤ 2 * Real.sqrt D0 * L * n := by
          have : (t : ℝ) ≤ 2 * Real.sqrt D0 * L := hth.trans hh
          exact mul_le_mul_of_nonneg_right this (by linarith)
      _ = L * (2 * n * Real.sqrt D0) := by ring
      _ ≤ L * (2 * Real.sqrt D) := by
          apply mul_le_mul_of_nonneg_left _ hL
          nlinarith
      _ ≤ 10 * Real.sqrt D * L := by nlinarith

/-- **Corollary 36.7**, first step: `D = 4 p x - K0` with `K0 = q^2 + 4 p W`, so `x` prime to
`K0` makes `x` prime to `D`. -/
theorem corollary36_7_coprime {m p q x : ℕ}
    (h : IsCoprime (x : ℤ) ((q : ℤ) ^ 2 + 4 * p * (w m p + w m q))) :
    IsCoprime (x : ℤ) (fieldD m p q x) := by
  rw [fieldD_eq, sub_eq_add_neg, add_comm]
  have := h.neg_right.add_mul_left_right (4 * p)
  convert this using 1; ring

/-- **Corollary 36.6**, first step: for `p = 1`, `D = 4 x - K0` with `K0 = q^2 + 4 + 4 w(q)`,
so `gcd(x, K0) = 1` gives `gcd(x, D) = 1`. -/
theorem corollary36_6_coprime {m q x : ℕ}
    (h : IsCoprime (x : ℤ) ((q : ℤ) ^ 2 + 4 + 4 * w m q)) :
    IsCoprime (x : ℤ) (fieldD m 1 q x) := by
  apply corollary36_7_coprime
  convert h using 1; simp; ring

/-- `x^x` modulo a prime `l`, by Fermat: `0` if `l ∣ x`, else `(x mod l)^(x mod (l - 1))`. -/
def powRes (l x : ℕ) : ℕ := if x % l = 0 then 0 else (x % l) ^ (x % (l - 1))

lemma natCast_pow_self_eq_powRes {l x : ℕ} (hl : l.Prime) (hx : x ≠ 0) :
    ((x ^ x : ℕ) : ZMod l) = (powRes l x : ZMod l) := by
  have := Fact.mk hl
  rw [powRes]
  split_ifs with h
  · have h0 : (x : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_of_mod_eq_zero h)
    push_cast; rw [h0, zero_pow hx]
  · have h0 : (x : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun hd => h (Nat.mod_eq_zero_of_dvd hd)
    have h1 := ZMod.pow_card_sub_one_eq_one h0
    push_cast
    rw [ZMod.natCast_mod]
    rw [show (x : ZMod l) ^ x = (x : ZMod l) ^ ((l - 1) * (x / (l - 1)) + x % (l - 1)) by
      rw [Nat.div_add_mod], pow_add, pow_mul, h1, one_pow, one_mul]

/-- The discriminant `q^2 + 4 (1 + w(q) + x^x - x)` of `(1, q, x)` modulo `l`, by `powRes`. -/
def resDisc (l m q x : ℕ) : ℕ := (q ^ 2 + 4 * (1 + w m q + powRes l x + (l - x % l))) % l

lemma natCast_resDisc {l m q x : ℕ} (hl : l.Prime) (hx : x ≠ 0) :
    ((resDisc l m q x : ℕ) : ZMod l) = ((discLast m 1 q x : ℤ) : ZMod l) := by
  have hlt : x % l ≤ l := (Nat.mod_lt x hl.pos).le
  have hp := natCast_pow_self_eq_powRes hl hx
  push_cast at hp
  rw [resDisc, ZMod.natCast_mod, discLast]
  push_cast [Nat.cast_sub hlt]
  rw [← hp]
  rw [ZMod.natCast_self, ZMod.natCast_mod, w_one]
  ring

/-- `nonres l r` is Euler's test: `r^((l - 1) / 2) ≡ -1 (mod l)`, so `r` is not a square
modulo the odd prime `l`. -/
def nonres (l r : ℕ) : Bool := r ^ (l / 2) % l == l - 1

lemma not_isSquare_of_nonres {l r : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (h : nonres l r = true) :
    ¬ IsSquare (r : ZMod l) := by
  have := Fact.mk hl
  have h2 : Fact (2 < l) := ⟨by have := hl.two_le; omega⟩
  rw [nonres, beq_iff_eq] at h
  have hpow : (r : ZMod l) ^ (l / 2) = -1 := by
    have : ((r ^ (l / 2) % l : ℕ) : ZMod l) = ((l - 1 : ℕ) : ZMod l) := by rw [h]
    rw [ZMod.natCast_mod, Nat.cast_sub hl.one_le, ZMod.natCast_self] at this
    push_cast at this; rw [this]; ring
  have hr0 : (r : ZMod l) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := hl.two_le; omega)] at hpow
    exact one_ne_zero (neg_eq_zero.1 hpow.symm)
  rw [ZMod.euler_criterion l hr0, hpow]
  exact ZMod.neg_one_ne_one

/-- The primes of the certificate of `corollary36_6_computation`. -/
def certPrimes : List ℕ :=
  [61, 251, 347, 317, 257, 349, 191, 137, 227, 331, 47, 3]

lemma certPrimes_prime : ∀ l ∈ certPrimes, l.Prime := by
  simp only [certPrimes, List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

/-- The test of `corollary36_6_computation` for one string `(1, q, x)`: `D ≤ 0`, or the string is
`(1, 0, 3)` under `0^0 = 0`, or the discriminant is a non-square modulo a prime of
`certPrimes`. -/
def cor36_6Ok (m q x : ℕ) : Bool :=
  !(decide (4 * (1 + w m q) + q ^ 2 < 4 * x)) || (m == 0 && q == 0 && x == 3) ||
    certPrimes.any fun l => nonres l (resDisc l m q x)

/-- The run of `corollary36_6_computation` for one convention and one `q`: every odd
`x ≤ 7619`. -/
def cor36_6Range (m q : ℕ) : Bool := (List.range 3810).all fun i => cor36_6Ok m q (2 * i + 1)

/-! The kernel checks the run in fourteen parts, which Lean checks in parallel. -/

theorem cor36_6_check_0_0 : cor36_6Range 0 0 = true := by decide +kernel
theorem cor36_6_check_0_1 : cor36_6Range 0 1 = true := by decide +kernel
theorem cor36_6_check_0_2 : cor36_6Range 0 2 = true := by decide +kernel
theorem cor36_6_check_0_3 : cor36_6Range 0 3 = true := by decide +kernel
theorem cor36_6_check_0_4 : cor36_6Range 0 4 = true := by decide +kernel
theorem cor36_6_check_0_5 : cor36_6Range 0 5 = true := by decide +kernel
theorem cor36_6_check_0_6 : cor36_6Range 0 6 = true := by decide +kernel
theorem cor36_6_check_1_0 : cor36_6Range 1 0 = true := by decide +kernel
theorem cor36_6_check_1_1 : cor36_6Range 1 1 = true := by decide +kernel
theorem cor36_6_check_1_2 : cor36_6Range 1 2 = true := by decide +kernel
theorem cor36_6_check_1_3 : cor36_6Range 1 3 = true := by decide +kernel
theorem cor36_6_check_1_4 : cor36_6Range 1 4 = true := by decide +kernel
theorem cor36_6_check_1_5 : cor36_6Range 1 5 = true := by decide +kernel
theorem cor36_6_check_1_6 : cor36_6Range 1 6 = true := by decide +kernel

lemma cor36_6Range_eq_true {m q : ℕ} (hm : m ≤ 1) (hq : q ≤ 6) : cor36_6Range m q = true := by
  interval_cases m <;> interval_cases q
  exacts [cor36_6_check_0_0, cor36_6_check_0_1, cor36_6_check_0_2, cor36_6_check_0_3,
    cor36_6_check_0_4, cor36_6_check_0_5, cor36_6_check_0_6, cor36_6_check_1_0,
    cor36_6_check_1_1, cor36_6_check_1_2, cor36_6_check_1_3, cor36_6_check_1_4,
    cor36_6_check_1_5, cor36_6_check_1_6]

/-- **Corollary 36.6**, the exact computation for `p = 1` (section 36.7). Under either convention
let `x ≤ 7619` be odd with `x > 1 + w(q) + q^2 / 4` (that is `D > 0`). If `(1, q, x)` is a
solution in base `b`, then it is `(1, 0, 3)` in base 5 under `0^0 = 0`. With Theorem 36.5, which
gives `x ≤ 7618` when `gcd(x, q^2 + 4 + 4 w(q)) = 1` and `x ≥ 11`, this is Corollary 36.6 for
`p = 1`. The kernel tests every odd `x` up to 7619 for `q ≤ 6`; for `q ≥ 7`, `D > 0` needs
`x > 7^7`. -/
theorem corollary36_6_computation {b m q x : ℕ} (hm : m ≤ 1) (hx : Odd x) (hx7619 : x ≤ 7619)
    (hD : 4 * (1 + w m q) + q ^ 2 < 4 * x) (hs : IsSolution b m [1, q, x]) :
    m = 0 ∧ q = 0 ∧ x = 3 ∧ b = 5 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hq : q ≤ 6 := by
    by_contra hq
    have h1 : 7 ^ 7 ≤ w m q := by
      rw [w_of_ne_zero m (by omega)]
      exact (Nat.pow_le_pow_left (by omega) 7).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  obtain ⟨i, rfl⟩ := hx
  have hcheck := cor36_6Range_eq_true hm hq
  simp only [cor36_6Range, List.all_eq_true, List.mem_range] at hcheck
  have hok := hcheck i (by omega)
  rw [cor36_6Ok] at hok
  simp only [hD, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, List.any_eq_true] at hok
  rcases hok with ⟨⟨rfl, rfl⟩, h3⟩ | ⟨l, hl, hnr⟩
  · refine ⟨rfl, rfl, h3, ?_⟩
    have := ((isSolution_last_iff_disc hx0).1 hs).2
    rw [h3, discLast] at this
    norm_num [w] at this
    nlinarith
  · exfalso
    have hlp := certPrimes_prime l hl
    apply not_isSquare_of_nonres hlp (by rintro rfl; simp [certPrimes] at hl) hnr
    rw [natCast_resDisc hlp hx0]
    exact sieve_last hx0 hs l

/-! ### Theorem 36.9: the upper bound of Step 4 -/

/-- Step 4 of **Theorem 36.9**, the upper bound. For a solution with `x ≥ 3`,
`4 D x^x < 8 x U^2`. Since `D < 4 p x`, this is `(2 tan θ)^2 = 4 D / U^2 < 8 x / x^x`, that is
`|Λ0| = 2 θ ≤ 2 tan θ < sqrt(8 x) x^(-x/2)`. -/
theorem theorem36_9_upper {b m p q x : ℕ} (hs : IsSolution b m [p, q, x]) (hx : 3 ≤ x) :
    4 * fieldD m p q x * x ^ x < 8 * x * ((2 * p * b + q : ℕ) : ℤ) ^ 2 := by
  have heq := field_last hs (by omega)
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
  have hlt := fieldD_lt (m := m) (q := q) (x := x) hp
  have hxx : 2 * x ≤ x ^ x := by
    have h3 : x ^ 2 ≤ x ^ x := Nat.pow_le_pow_right (by omega) (by omega)
    have : 2 * x ≤ x ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right x (by omega)
    omega
  have hxx' : (2 * x : ℤ) ≤ (x : ℤ) ^ x := by exact_mod_cast hxx
  have hp' : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hx' : (3 : ℤ) ≤ x := by exact_mod_cast hx
  have hU : ((2 * p * b + q : ℕ) : ℤ) ^ 2 = 4 * p * x ^ x - fieldD m p q x := by linarith
  rw [hU]
  have hX : (0 : ℤ) < (x : ℤ) ^ x := by positivity
  nlinarith [mul_lt_mul_of_pos_right hlt hX, mul_le_mul_of_nonneg_left hxx'
    (show (0 : ℤ) ≤ 16 * p * x by positivity)]

/-! ### Section 36.4: the middle and leading positions -/

/-- **Proposition 36.11** (section 36.4.1), the local condition. Let `(p, x, q)` with `x ≥ 1`
be a solution and `A = w(p) + w(q) - q`. Every prime `l` that divides `x` and not `2 p A` has
`(p A / l) = 1`, since `U^2 = 4 p x^x + x^2 + 4 p A ≡ 4 p A (mod l)`. The density statement
is not formalized. -/
theorem prop36_11 {b m p q x l : ℕ} [Fact l.Prime] (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hlx : l ∣ x)
    (hl2 : ¬ (l : ℤ) ∣ 2 * p * ((w m p : ℤ) + w m q - q)) :
    legendreSym l (p * ((w m p : ℤ) + w m q - q)) = 1 := by
  set A : ℤ := (w m p : ℤ) + w m q - q with hA
  have hD := ((isSolution_mid_iff_disc hx).1 hs).2
  rw [discMid] at hD
  have hx0 : (x : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hlx
  have hcast : ((2 * p * b + x : ℕ) : ZMod l) ^ 2 = 4 * ((p * A : ℤ) : ZMod l) := by
    have := congrArg (fun z : ℤ => (z : ZMod l)) hD
    push_cast at this ⊢
    rw [← this, hx0, zero_pow hx, hA]; push_cast; ring
  have h2 : (2 : ZMod l) ≠ 0 := by
    intro h
    have : (l : ℤ) ∣ 2 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
    exact hl2 (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left this _) _)
  have hpA : ((p * A : ℤ) : ZMod l) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact hl2 (by rw [mul_assoc]; exact dvd_mul_of_dvd_right h _)
  rw [legendreSym.eq_one_iff l hpA]
  refine ⟨((2 * p * b + x : ℕ) : ZMod l) / 2, ?_⟩
  rw [div_mul_div_comm, ← sq, hcast]
  field_simp
  ring

/-- **Proposition 36.12** (section 36.4.2), the reduction. If `(x, q, r)` is a solution with `x`
even and `x = n f^2`, then `U^2 - n V^2 = R` with `U = 2 x b + q`, `V = 2 f x^(x/2)` and
`R = q^2 + 4 x (w(q) + w(r) - r)`; and `2^(x/2 + 1)` divides `V` (`two_pow_dvd_V`). The
inequality of Theorem 32.2 (Baker) is not formalized. -/
theorem pell_lead {b m x q r n f : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0)
    (hxe : Even x) (hxn : x = n * f ^ 2) :
    ((2 * x * b + q : ℕ) : ℤ) ^ 2 - n * ((2 * f * x ^ (x / 2) : ℕ) : ℤ) ^ 2 =
      q ^ 2 + 4 * x * ((w m q : ℤ) + w m r - r) := by
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero m hx] at heq
  have hsq := complete_square (b := b) (p := x) (q := q) (r := r)
    (F := x ^ x + (w m q + w m r)) (by rw [← heq]; ring)
  rw [hsq]
  have hpow : ((x ^ (x / 2) : ℕ) : ℤ) ^ 2 = (x : ℤ) ^ x := by
    exact_mod_cast (pow_self_eq_sq hxe).symm
  have hxZ : (x : ℤ) = n * f ^ 2 := by exact_mod_cast hxn
  push_cast at hpow ⊢
  have : (n : ℤ) * (2 * f * (x : ℤ) ^ (x / 2)) ^ 2 = 4 * x * x ^ x := by
    rw [mul_pow, hpow]; linear_combination (-4 * (x : ℤ) ^ x) * hxZ
  rw [this]; ring

end Munchausen
