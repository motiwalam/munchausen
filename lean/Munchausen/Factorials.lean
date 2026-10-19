import Munchausen.OtherSystems

/-!
# Factorials against `x^x` (chapter 33)

A solution for a weight `wt` is a string whose value in base `b` is the sum of the weights of
its digits. The factorion weight is `x!`, with `w(0) = m`.

* Proposition 33.9: `(1, x)` is a factorion in base `x! - x + 1`, so there are infinitely many
  2-digit factorions; Conjecture 33.11 (finitely many for each length `k ≥ 3`) as a `Prop`;
* the completed square of a 3-digit string, `U^2 = M + K` (the table of chapter 33);
* Lemma 33.1 in finite form: if `U^2 = M + K` and `l` divides `M` more often than `K`, then
  `K` is an `l`-adic square (even valuation, square unit part modulo `l`, or modulo 8 for
  `l = 2`); and the obstruction of Lemma 33.2 for `M = c x!`;
* Theorem 33.4 (b) and (d): the middle position has `x < 2 p A`; `A = 0` only for
  `w(0) = 0`, `q = 0`, `r ≤ 2`, and then `4 x x!` is not a square for `x ≥ 4`;
* Theorem 33.12: a sufficient condition for identity families of length `j + 1`, for any
  weight;
* Proposition 33.13: `x! = lam y^j` forces every prime of `(x/2, x]` into `lam`;
* Proposition 33.21: the bound `r^v ≤ t T + 1` on the self-paying digits of a construction;
* the abc conjecture as a hypothesis `ABC`, and the abc step of Theorem 33.16:
  `U^2 = N + R`, `R ≠ 0` gives `N ≤ K (rad(N) U |R|)^(1 + ε)`.
-/

namespace Munchausen

/-- A solution for an arbitrary weight `wt` (chapter 33): digits below `b`, a nonzero
leading digit, and value equal to the sum of the weights of the digits. -/
structure IsWSolution (wt : ℕ → ℕ) (b : ℕ) (s : List ℕ) : Prop where
  lt_base : ∀ d ∈ s, d < b
  head_ne_zero : ∀ h : s ≠ [], s.head h ≠ 0
  eq : P b s = (s.map wt).sum

/-- The factorion weight (chapter 33): `x!` for `x ≥ 1` and `m` for `x = 0`. -/
def fw (m x : ℕ) : ℕ := if x = 0 then m else x.factorial

@[simp] lemma fw_zero (m : ℕ) : fw m 0 = m := by simp [fw]

lemma fw_of_ne_zero (m : ℕ) {x : ℕ} (hx : x ≠ 0) : fw m x = x.factorial := by simp [fw, hx]

/-- Munchausen strings are the solutions for the weight `w m`. -/
lemma isSolution_iff_isWSolution (b m : ℕ) (s : List ℕ) :
    IsSolution b m s ↔ IsWSolution (w m) b s :=
  ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

lemma P_triple {R : Type*} [CommSemiring R] (b : R) (a c d : ℕ) :
    P b [a, c, d] = a * b ^ 2 + c * b + d := by
  simp [P, Nat.ofDigits]; ring

/-! ### Proposition 33.9 -/

lemma two_mul_le_factorial {x : ℕ} (hx : 3 ≤ x) : 2 * x ≤ x.factorial := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [Nat.factorial_succ]
  have : 2 ≤ y.factorial := le_trans (by omega) (Nat.self_le_factorial y)
  nlinarith

/-- **Proposition 33.9** (section 33.2.1). For every `x ≥ 3`, `(1, x)` is a factorion in base
`x! - x + 1`, under either convention. -/
theorem prop33_9 (m : ℕ) {x : ℕ} (hx : 3 ≤ x) :
    IsWSolution (fw m) (x.factorial - x + 1) [1, x] := by
  have h2 := two_mul_le_factorial hx
  refine ⟨fun d hd => ?_, fun _ => by simp, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> omega
  · rw [P_pair]
    simp only [Nat.cast_id, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      fw_of_ne_zero m one_ne_zero, fw_of_ne_zero m (show x ≠ 0 by omega), Nat.factorial_one]
    omega

/-- Proposition 33.9: there are infinitely many 2-digit factorions. -/
theorem infinite_two_digit_factorions (m : ℕ) :
    {s : List ℕ | s.length = 2 ∧ ∃ b, IsWSolution (fw m) b s}.Infinite := by
  have hinj : Function.Injective fun n : ℕ => [1, n + 3] := by
    intro a b h; simpa using h
  refine Set.infinite_of_injective_forall_mem hinj fun n => ⟨rfl, _, prop33_9 m (by omega)⟩

/-- **Conjecture 33.11** (section 33.2.3). For each `k ≥ 3` there are finitely many `k`-digit
factorions, under either convention. -/
def Conjecture33_11 (m : ℕ) : Prop :=
  ∀ k, 3 ≤ k → {s : List ℕ | s.length = k ∧ ∃ b, IsWSolution (fw m) b s}.Finite

/-! ### The completed square of a 3-digit string -/

/-- The completed square (chapter 33, notation): `(d2, d1, d0)` has value `N` in base `b`
exactly when `(2 d2 b + d1)^2 = 4 d2 (N - d0) + d1^2`, for `d2 ≠ 0`. -/
theorem three_digit_iff_sq {b d2 d1 d0 N : ℤ} (hd2 : d2 ≠ 0) :
    d2 * b ^ 2 + d1 * b + d0 = N ↔ (2 * d2 * b + d1) ^ 2 = 4 * d2 * (N - d0) + d1 ^ 2 := by
  constructor
  · intro h; rw [← h]; ring
  · intro h
    have : 4 * d2 * (d2 * b ^ 2 + d1 * b + d0 - N) = 0 := by linear_combination h
    have := (mul_eq_zero.1 this).resolve_left (by positivity)
    linear_combination this

/-- The table of chapter 33 for factorions with the large digit `x` last, `(p, q, x)`:
`U^2 = 4 p x! + K` with `U = 2 p b + q` and `K = q^2 + 4 p (w(p) + w(q) - x)`. -/
theorem factorion_last_iff {m b p q x : ℕ} (hp : p ≠ 0) :
    P b [p, q, x] = ([p, q, x].map (fw m)).sum ↔
      ((2 * p * b + q : ℕ) : ℤ) ^ 2 = 4 * p * (fw m x : ℤ) +
        ((q : ℤ) ^ 2 + 4 * p * ((fw m p : ℤ) + fw m q - x)) := by
  have h := three_digit_iff_sq (b := (b : ℤ)) (d1 := (q : ℤ)) (d0 := (x : ℤ))
    (N := ((fw m p + fw m q + fw m x : ℕ) : ℤ)) (d2 := (p : ℤ)) (by exact_mod_cast hp)
  rw [P_triple]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.cast_id]
  rw [← Nat.cast_inj (R := ℤ)]
  push_cast at h ⊢
  rw [show ((fw m p : ℤ) + (fw m q + (fw m x + 0))) = fw m p + fw m q + fw m x by ring, h]
  constructor <;> intro h' <;> linear_combination h'

/-! ### Lemma 33.1 and the obstruction of Lemma 33.2 -/

/-- Comparing `p`-adic valuations: `p^a x = p^b y` with `p ∤ x`, `p ∤ y` forces `a = b`. -/
lemma pow_mul_eq_pow_mul_iff {p : ℤ} (hp : Prime p) {a b : ℕ} {x y : ℤ} (hx : ¬ p ∣ x)
    (hy : ¬ p ∣ y) (h : p ^ a * x = p ^ b * y) : a = b := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso; apply hx
    obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
    have : p ^ a * (x - p ^ (k + 1) * y) = 0 := by rw [pow_add] at h; linear_combination h
    have := (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hp0)
    exact ⟨p ^ k * y, by linear_combination this⟩
  · exact hab
  · exfalso; apply hy
    obtain ⟨k, rfl⟩ : ∃ k, a = b + (k + 1) := ⟨a - b - 1, by omega⟩
    have : p ^ b * (y - p ^ (k + 1) * x) = 0 := by rw [pow_add] at h; linear_combination -h
    have := (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hp0)
    exact ⟨p ^ k * x, by linear_combination this⟩

/-- The valuation of a square: `U^2 = l^v Y` with `l ∤ Y` forces `v` even and `Y` a square of
an integer prime to `l`. -/
lemma sq_eq_pow_mul {l : ℕ} (hl : l.Prime) {U Y : ℤ} {v : ℕ} (hY : ¬ (l : ℤ) ∣ Y)
    (h : U ^ 2 = (l : ℤ) ^ v * Y) : ∃ u : ℤ, ¬ (l : ℤ) ∣ u ∧ v = 2 * (v / 2) ∧ u ^ 2 = Y := by
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have hU : U ≠ 0 := by
    rintro rfl
    have : (l : ℤ) ^ v * Y = 0 := by rw [← h]; ring
    rcases mul_eq_zero.1 this with h0 | h0
    · exact pow_ne_zero _ (by exact_mod_cast hl.ne_zero) h0
    · exact hY (h0 ▸ dvd_zero _)
  obtain ⟨a, u, hu, hUu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hU) l
    hl.one_lt.ne'
  have hU2 : U ^ 2 = ((l : ℤ) ^ (2 * a)) * (u : ℤ) ^ 2 := by
    rw [← Int.natAbs_sq U, hUu]; push_cast; ring
  have hu2 : ¬ (l : ℤ) ∣ (u : ℤ) ^ 2 := fun hd =>
    hu (by exact_mod_cast hlZ.dvd_of_dvd_pow hd)
  have hva : 2 * a = v := pow_mul_eq_pow_mul_iff hlZ hu2 hY (hU2.symm.trans h)
  refine ⟨u, fun hd => hu (by exact_mod_cast hd), by omega, ?_⟩
  rw [← hva] at h
  have : (l : ℤ) ^ (2 * a) * ((u : ℤ) ^ 2 - Y) = 0 := by linear_combination -hU2 + h
  linear_combination (mul_eq_zero.1 this).resolve_left
    (pow_ne_zero _ (by exact_mod_cast hl.ne_zero))

/-- **Lemma 33.1** (section 33.1.1), for an odd or even prime `l`, in finite form. Let
`U^2 = M + K` with `K = l^v k`, `l ∤ k`, and `l^(v+1) ∣ M`. Then `K` is an `l`-adic square:
`v` is even and `k` is a square modulo `l`. -/
theorem lemma33_1 {l : ℕ} (hl : l.Prime) {U M K k : ℤ} {v : ℕ} (hK : K = (l : ℤ) ^ v * k)
    (hk : ¬ (l : ℤ) ∣ k) (hM : (l : ℤ) ^ (v + 1) ∣ M) (h : U ^ 2 = M + K) :
    Even v ∧ ∃ r : ℤ, (l : ℤ) ∣ r ^ 2 - k := by
  obtain ⟨M', rfl⟩ := hM
  have hY : ¬ (l : ℤ) ∣ l * M' + k := fun hd => hk (by
    have := dvd_sub hd (dvd_mul_right (l : ℤ) M'); simpa using this)
  obtain ⟨u, -, hv, hu⟩ := sq_eq_pow_mul hl hY (by rw [h, hK]; ring)
  exact ⟨⟨v / 2, by omega⟩, u, ⟨M', by linear_combination hu⟩⟩

/-- **Lemma 33.1** for `l = 2`: if `U^2 = M + K` with `K = 2^v k`, `k` odd and `2^(v+3) ∣ M`,
then `v` is even and `k ≡ 1 (mod 8)`. -/
theorem lemma33_1_two {U M K k : ℤ} {v : ℕ} (hK : K = 2 ^ v * k) (hk : ¬ (2 : ℤ) ∣ k)
    (hM : (2 : ℤ) ^ (v + 3) ∣ M) (h : U ^ 2 = M + K) : Even v ∧ (8 : ℤ) ∣ k - 1 := by
  obtain ⟨M', rfl⟩ := hM
  have hY : ¬ ((2 : ℕ) : ℤ) ∣ 8 * M' + k := by push_cast; omega
  obtain ⟨u, hu2, hv, hu⟩ := sq_eq_pow_mul Nat.prime_two hY (by
    push_cast; rw [h, hK]; ring)
  refine ⟨⟨v / 2, by omega⟩, ?_⟩
  obtain ⟨s, rfl⟩ : Odd u := Int.not_even_iff_odd.1 (by
    rintro ⟨t, rfl⟩; exact hu2 ⟨t, by push_cast; ring⟩)
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self s
  exact ⟨-M' + t, by linear_combination -hu + 4 * ht⟩

/-- `l^(x / l)` divides `x!` for a prime `l`. -/
lemma pow_div_dvd_factorial {l : ℕ} (hl : l.Prime) (x : ℕ) : l ^ (x / l) ∣ x.factorial := by
  rcases Nat.lt_or_ge x l with hxl | hxl
  · simp [Nat.div_eq_of_lt hxl]
  have hlog : Nat.log l x < Nat.log l x + 1 := Nat.lt_succ_self _
  rw [hl.pow_dvd_factorial_iff hlog]
  have h1 : 1 ≤ Nat.log l x := Nat.le_log_of_pow_le hl.one_lt (by simpa using hxl)
  calc x / l = x / l ^ 1 := by rw [pow_one]
    _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log l x + 1), x / l ^ i :=
      Finset.single_le_sum (f := fun i => x / l ^ i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩)

/-- **Lemma 33.2** (section 33.1.1), the obstruction. Let `K = l^v k` with `l` prime, `l ∤ k`,
and suppose `K` is not an `l`-adic square: `v` odd or `k` not a square modulo `l`. If
`l^(v+1) ∣ x!` (for example `v + 1 ≤ x / l`), then `U^2 = c x! + K` has no solution. With
`v = 0` this is part (a), `l ≤ x`; part (c) is the case `v + 1 ≤ x / l`. -/
theorem lemma33_2 {l : ℕ} (hl : l.Prime) {c K k : ℤ} {v x : ℕ} (hK : K = (l : ℤ) ^ v * k)
    (hk : ¬ (l : ℤ) ∣ k) (hnsq : ¬ Even v ∨ ∀ r : ℤ, ¬ (l : ℤ) ∣ r ^ 2 - k)
    (hx : l ^ (v + 1) ∣ x.factorial) (U : ℤ) : U ^ 2 ≠ c * x.factorial + K := by
  intro h
  have hM : (l : ℤ) ^ (v + 1) ∣ c * x.factorial :=
    dvd_mul_of_dvd_right (by exact_mod_cast hx) c
  obtain ⟨hv, r, hr⟩ := lemma33_1 hl hK hk hM h
  rcases hnsq with h1 | h1
  · exact h1 hv
  · exact h1 r hr

/-! ### Theorem 33.4 (b) and (d) -/

/-- **Theorem 33.4 (b)** (section 33.1.3). In the middle position `K = x^2 + 4 p A` with `p, A ≥ 1`
is a square only for `x < 2 p A`. -/
theorem theorem33_4_b {x p A t : ℕ} (hp : 1 ≤ p) (hA : 1 ≤ A) (h : x ^ 2 + 4 * p * A = t ^ 2) :
    x < 2 * p * A := by
  have hpA : 1 ≤ p * A := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hxt : x < t := by
    by_contra hc
    have : t ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith
  nlinarith

/-- **Theorem 33.4 (d)** (section 33.1.3), the case `A = 0`. For the factorion weight,
`A = w(q) + w(r) - r` vanishes exactly when `w(0) = 0`, `q = 0` and `r ≤ 2`. -/
theorem theorem33_4_d_A {m q r : ℕ} : fw m q + fw m r = r ↔ m = 0 ∧ q = 0 ∧ r ≤ 2 := by
  have hr : ∀ r, 3 ≤ r → r < r.factorial := fun r hr => by
    have := two_mul_le_factorial hr; omega
  constructor
  · intro h
    have hq : fw m q = 0 := by
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp only [fw_zero, add_eq_zero] at h; exact h.1
      · rw [fw_of_ne_zero m hr0.ne'] at h
        have := Nat.self_le_factorial r; omega
    have hq0 : q = 0 := by
      by_contra hq0; rw [fw_of_ne_zero m hq0] at hq; exact Nat.factorial_ne_zero q hq
    subst hq0
    simp only [fw_zero] at hq; subst hq
    refine ⟨rfl, rfl, ?_⟩
    by_contra hr3
    rw [fw_zero, zero_add, fw_of_ne_zero 0 (by omega)] at h
    have := hr r (by omega); omega
  · rintro ⟨rfl, rfl, hr2⟩
    interval_cases r <;> simp [fw]

/-- **Theorem 33.4 (d)** (section 33.1.3). For `x ≥ 4`, `4 x x!` is not a perfect square: a
prime `l` with `x / 2 < l < x` divides it exactly once (Bertrand). -/
theorem theorem33_4_d {x : ℕ} (hx : 4 ≤ x) (U : ℕ) : U ^ 2 ≠ 4 * x * x.factorial := by
  obtain ⟨l, hl, hl1, hl2⟩ := Nat.exists_prime_lt_and_le_two_mul (x / 2) (by omega)
  have hlx : l < x := by
    rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : l ≠ x := by
        rintro rfl
        have := hl.eq_one_or_self_of_dvd 2 ⟨k, by omega⟩
        omega
      omega
    · omega
  have hl3 : 3 ≤ l := by omega
  intro h
  have hlU : l ∣ U := hl.dvd_of_dvd_pow (n := 2) (h ▸ dvd_mul_of_dvd_right
    (Nat.dvd_factorial hl.pos hlx.le) _)
  have hl2U : l ^ 2 ∣ 4 * x * x.factorial := h ▸ pow_dvd_pow_of_dvd hlU 2
  have hcop : Nat.Coprime (l ^ 2) (4 * x) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd hl]
    intro hd
    rcases (Nat.Prime.dvd_mul hl).1 hd with hd | hd
    · have := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1
        (hl.dvd_of_dvd_pow (n := 2) (by simpa using hd))
      omega
    · obtain ⟨k, hk⟩ := hd
      have : x < 2 * l := by omega
      rcases k with _ | _ | k
      · omega
      · omega
      · nlinarith
  exact not_sq_dvd_factorial hl hlx.le (by omega) (hcop.dvd_of_dvd_mul_left hl2U)

/-! ### Theorem 33.12: identity families for any weight -/

/-- The digits `t_i = M^(j-i) C(j, i) (M u)^i` are at most `(M u)^j` once `u ≥ j`. -/
lemma binomDigits_le {j M u d : ℕ} (hju : j ≤ u) (hd : d ∈ binomDigits j M (M * u)) :
    d ≤ (M * u) ^ j := by
  simp only [binomDigits, List.mem_map, List.mem_range] at hd
  obtain ⟨i, hi, rfl⟩ := hd
  have h1 : j.choose i ≤ u ^ (j - i) := by
    rw [← Nat.choose_symm hi.le]
    exact (Nat.choose_le_pow j (j - i)).trans (Nat.pow_le_pow_left hju _)
  calc M ^ (j - i) * j.choose i * (M * u) ^ i ≤ M ^ (j - i) * u ^ (j - i) * (M * u) ^ i :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ = (M * u) ^ j := by
        rw [← mul_pow, ← pow_add, Nat.sub_add_cancel hi.le]

/-- **Theorem 33.12** (section 33.3.1), one member. Let `j ≥ 2`, `M ≥ 1`, `u ≥ j`, let the
digits be `t_i = M^(j-i) C(j, i) (M u)^i` (`binomDigits j M (M u)`), and
`x = (M u)^j + sum w(t_i)`. Suppose `w(x) = y^j` with `M ∣ y` (S1) and `y > M (x + v)` whenever
`v^j ≤ x` (S3). Then `(t_0, ..., t_(j-1), x)` is a solution in base `b = (y - M u) / M`, under
any value of `w(0)`. -/
theorem theorem33_12_member (wt : ℕ → ℕ) {j M u x y : ℕ} (hj : 2 ≤ j) (hM : 1 ≤ M)
    (hju : j ≤ u)
    (hx : x = (M * u) ^ j + ((binomDigits j M (M * u)).map wt).sum)
    (hS1 : wt x = y ^ j) (hMy : M ∣ y) (hS3 : ∀ v, v ^ j ≤ x → M * (x + v) < y) :
    IsWSolution wt ((y - M * u) / M) (binomDigits j M (M * u) ++ [x]) := by
  set t := binomDigits j M (M * u) with ht
  have hu : 1 ≤ u := by omega
  have hMu : 1 ≤ M * u := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hpos : ∀ d ∈ t, 1 ≤ d := fun d hd => binomDigits_pos hM hMu hd
  have hMuj : (M * u) ^ j ≤ x := by rw [hx]; omega
  have hy := hS3 (M * u) hMuj
  obtain ⟨y', rfl⟩ := hMy
  have hb : (M * y' - M * u) / M = y' - u := by
    rw [← Nat.mul_sub, Nat.mul_div_cancel_left _ (by omega)]
  rw [hb]
  have hxb : x < y' - u := by
    have : M * (x + M * u) < M * y' := hy
    have h1 : x + M * u < y' := Nat.lt_of_mul_lt_mul_left this
    have : u ≤ M * u := Nat.le_mul_of_pos_left u (by omega)
    omega
  refine ⟨fun d hd => ?_, fun h => ?_, ?_⟩
  · rcases List.mem_append.1 hd with hd | hd
    · have := binomDigits_le hju hd; omega
    · simp at hd; omega
  · rw [List.head_append_of_ne_nil (by simp [ht, binomDigits]; omega)]
    have := hpos _ (List.head_mem (by simp [ht, binomDigits]; omega))
    omega
  · have key := mul_P_binomDigits ((y' - u : ℕ) : ℤ) j M (M * u)
    have hyb : (M : ℤ) * ((y' - u : ℕ) : ℤ) + ((M * u : ℕ) : ℤ) = ((M * y' : ℕ) : ℤ) := by
      push_cast [show u ≤ y' by omega]; ring
    rw [hyb] at key
    rw [← Nat.cast_inj (R := ℤ)]
    rw [P_append_singleton, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have hxz : ((x : ℕ) : ℤ) = ((M * u : ℕ) : ℤ) ^ j + ((t.map wt).sum : ℤ) := by
      rw [hx]; push_cast; ring
    have hS1' : ((wt x : ℕ) : ℤ) = ((M * y' : ℕ) : ℤ) ^ j := by rw [hS1]; push_cast; ring
    push_cast at key hxz hS1' ⊢
    rw [← ht] at key
    linear_combination key + hxz - hS1'

/-- **Theorem 33.12** (section 33.3.1). Let `j ≥ 2` and `M ≥ 1`, and suppose that
`M ∣ w(d)` whenever `M ∣ d ≥ 1` (S2), and that every `x ≥ X0` with `M ∣ x` has `w(x) = y^j`
with `M ∣ y` (S1) and `y > M (x + v)` whenever `v^j ≤ x` (S3). Then there are infinitely many
solutions of length `j + 1`. -/
theorem theorem33_12 (wt : ℕ → ℕ) {j M X0 : ℕ} (hj : 2 ≤ j) (hM : 1 ≤ M)
    (hS2 : ∀ d, 1 ≤ d → M ∣ d → M ∣ wt d)
    (hS : ∀ x, X0 ≤ x → M ∣ x → ∃ y, wt x = y ^ j ∧ M ∣ y ∧ ∀ v, v ^ j ≤ x → M * (x + v) < y) :
    {s : List ℕ | s.length = j + 1 ∧ ∃ b, IsWSolution wt b s}.Infinite := by
  set xx : ℕ → ℕ := fun u => (M * u) ^ j + ((binomDigits j M (M * u)).map wt).sum with hxx
  set f : ℕ → List ℕ := fun n => binomDigits j M (M * (n + X0 + j)) ++ [xx (n + X0 + j)]
  have hinj : Function.Injective f := by
    intro a a' h
    have h1 : (f a)[1]? = (f a')[1]? := by rw [h]
    simp only [f] at h1
    rw [List.getElem?_append_left (by rw [length_binomDigits]; omega),
      List.getElem?_append_left (by rw [length_binomDigits]; omega),
      binomDigits_getElem_one hj, binomDigits_getElem_one hj] at h1
    simp only [Option.some.injEq] at h1
    have hpos : 0 < M ^ (j - 1) * j * M := by positivity
    have : M ^ (j - 1) * j * M * (a + X0 + j) = M ^ (j - 1) * j * M * (a' + X0 + j) := by
      simpa only [mul_assoc] using h1
    have := Nat.eq_of_mul_eq_mul_left hpos this
    omega
  refine Set.infinite_of_injective_forall_mem hinj fun n => ?_
  set u := n + X0 + j with hu
  have hMu : 1 ≤ M * u := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hxX : X0 ≤ xx u := by
    have : u ≤ (M * u) ^ j :=
      (Nat.le_mul_of_pos_left u (by omega)).trans (Nat.le_self_pow (by omega) _)
    simp only [hxx]; omega
  have hMx : M ∣ xx u := by
    simp only [hxx]
    refine dvd_add (dvd_pow (dvd_mul_right M u) (by omega)) (List.dvd_sum fun d hd => ?_)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hd
    refine hS2 t (binomDigits_pos hM hMu ht) ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ht
    have hi' : i < j := List.mem_range.1 hi
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self M (by omega)) _) _
  obtain ⟨y, hy1, hy2, hy3⟩ := hS (xx u) hxX hMx
  refine ⟨by simp [f, length_binomDigits], _,
    theorem33_12_member wt hj hM (by omega) rfl hy1 hy2 hy3⟩

/-! ### Proposition 33.13: factorials are not powers -/

/-- **Proposition 33.13** (section 33.3.2). If `d x! = n y^j` with `j ≥ 2` and `l` is a prime
with `x / 2 < l ≤ x`, then `l` divides `n` or `d`: every prime of `(x/2, x]` lies in the
numerator or the denominator of `lam = n / d` in `x! = lam y^j`. -/
theorem prop33_13 {x j n d y l : ℕ} (hj : 2 ≤ j) (hl : l.Prime) (hl1 : x < 2 * l) (hl2 : l ≤ x)
    (h : d * x.factorial = n * y ^ j) : l ∣ n ∨ l ∣ d := by
  by_contra hnd
  push Not at hnd
  obtain ⟨hn, hd⟩ := hnd
  have hlx : l ∣ d * x.factorial := dvd_mul_of_dvd_right (Nat.dvd_factorial hl.pos hl2) d
  rw [h] at hlx
  have hly : l ∣ y := hl.dvd_of_dvd_pow ((hl.dvd_mul.1 hlx).resolve_left hn)
  have hl2y : l ^ 2 ∣ n * y ^ j :=
    dvd_mul_of_dvd_right ((pow_dvd_pow_of_dvd hly 2).trans (pow_dvd_pow y hj)) n
  rw [← h] at hl2y
  have hcop : Nat.Coprime (l ^ 2) d := Nat.Coprime.pow_left 2 ((hl.coprime_iff_not_dvd).2 hd)
  exact not_sq_dvd_factorial hl hl2 hl1 (hcop.dvd_of_dvd_mul_left hl2y)

/-- Proposition 33.13, the bound: if `x! = lam y^j` with `lam` a positive integer, `j ≥ 2` and
`x ≥ 2`, then `x < 2 lam`. -/
theorem prop33_13_lt {x j lam y : ℕ} (hj : 2 ≤ j) (hx : 2 ≤ x) (hlam : 1 ≤ lam)
    (h : x.factorial = lam * y ^ j) : x < 2 * lam := by
  obtain ⟨l, hl, hl1, hl2⟩ := Nat.exists_prime_lt_and_le_two_mul (x / 2) (by omega)
  rcases prop33_13 (x := x) (n := lam) (y := y) (d := 1) hj hl (by omega) (by omega)
    (by simpa using h) with h1 | h1
  · have := Nat.le_of_dvd (by omega) h1; omega
  · exact absurd (Nat.le_of_dvd one_pos h1) (by have := hl.two_le; omega)

/-- Proposition 33.13, the consequence for identities: a last digit `x ≥ t0!` with `t0 ≥ 3`
never has `x! = lam y^j` with `lam ∣ t0`. -/
theorem prop33_13_identity {t0 x j lam y : ℕ} (ht0 : 3 ≤ t0) (hx : t0.factorial ≤ x)
    (hj : 2 ≤ j) (hlam : lam ∣ t0) : x.factorial ≠ lam * y ^ j := by
  intro h
  have hlam1 : 1 ≤ lam := Nat.pos_of_dvd_of_pos hlam (by omega)
  have h1 := prop33_13_lt hj (by have := two_mul_le_factorial ht0; omega) hlam1 h
  have h2 := Nat.le_of_dvd (by omega) hlam
  have h3 := two_mul_le_factorial ht0
  omega

/-! ### Proposition 33.21 -/

/-- **Proposition 33.21** (section 33.5.1), the arithmetic. A self-paying digit `r^v` of base
`r^t` sits at position `P = v (r^v - 1) / t`; if `P ≤ T`, then `r^v ≤ t T + 1`. The digits of a
set `S` of self-paying digits have distinct exponents in `[1, v_top]`, so `|S| ≤ v_top`. -/
theorem prop33_21 {r t v P T : ℕ} (hv : 1 ≤ v) (hr : 1 ≤ r) (hP : t * P = v * (r ^ v - 1))
    (hPT : P ≤ T) : r ^ v ≤ t * T + 1 := by
  have h1 : 1 ≤ r ^ v := Nat.one_le_pow _ _ hr
  have h2 : r ^ v - 1 ≤ v * (r ^ v - 1) := Nat.le_mul_of_pos_left _ hv
  have h3 : t * P ≤ t * T := Nat.mul_le_mul_left t hPT
  omega

theorem prop33_21_card {S : Finset ℕ} {vtop : ℕ} (hS : S ⊆ Finset.Icc 1 vtop) :
    S.card ≤ vtop := by
  simpa using Finset.card_le_card hS

/-! ### The abc conjecture as a hypothesis (sections 33.1.5 and 33.4) -/

/-- The radical of `n`, the product of its prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The abc conjecture in the form of section 33.4.1: for every `ε > 0` there is `K` with
`c ≤ K rad(a b c)^(1 + ε)` for coprime positive `a + b = c`. It is used only as a hypothesis. -/
def ABC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

lemma one_le_rad (n : ℕ) : 1 ≤ rad n :=
  Finset.one_le_prod fun _ hp => (Nat.prime_of_mem_primeFactors hp).one_le

lemma rad_le_self {n : ℕ} (hn : n ≠ 0) : rad n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

lemma rad_le_of_dvd {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) : rad a ≤ rad b :=
  Finset.prod_le_prod_of_subset_of_one_le (Nat.primeFactors_mono h hb)
    fun _ hp _ => (Nat.prime_of_mem_primeFactors hp).one_le

lemma rad_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : rad (a * b) ≤ rad a * rad b := by
  unfold rad
  rw [Nat.primeFactors_mul ha hb, ← Finset.prod_union_inter]
  exact Nat.le_mul_of_pos_right _ (Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_inter.1 hp).1).pos)

lemma rad_pow {n k : ℕ} (hk : k ≠ 0) : rad (n ^ k) = rad n := by
  unfold rad; rw [Nat.primeFactors_pow n hk]

/-- The abc step for a non-coprime sum: if `A + B = C` with `A, B > 0` and `g = gcd(A, B)`,
abc applies to `A/g + B/g = C/g`, and `rad` of the product is at most
`rad(A/g) rad(B/g) rad(C/g)`. -/
lemma abc_div_gcd {ε K : ℝ}
    (hK : ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)) (hε : 0 < ε)
    {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hABC : A + B = C) :
    ((C / Nat.gcd A B : ℕ) : ℝ) ≤ K * ((rad (A / Nat.gcd A B) * rad (B / Nat.gcd A B) *
      rad (C / Nat.gcd A B) : ℕ) : ℝ) ^ (1 + ε) := by
  set g := Nat.gcd A B with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  have hgA : g ∣ A := Nat.gcd_dvd_left A B
  have hgB : g ∣ B := Nat.gcd_dvd_right A B
  have ha : 0 < A / g := Nat.div_pos (Nat.le_of_dvd hA hgA) hg0
  have hb : 0 < B / g := Nat.div_pos (Nat.le_of_dvd hB hgB) hg0
  have hc : A / g + B / g = C / g := by rw [← hABC, Nat.add_div_of_dvd_right hgA]
  have h := hK _ _ _ ha hb hc (Nat.coprime_div_gcd_div_gcd hg0)
  refine h.trans ?_
  have hK0 : 0 ≤ K := by
    by_contra hK0
    push Not at hK0
    have : K * (rad (A / g * (B / g) * (C / g)) : ℝ) ^ (1 + ε) < 0 :=
      mul_neg_of_neg_of_pos hK0 (Real.rpow_pos_of_pos (by exact_mod_cast one_le_rad _) _)
    have : (0 : ℝ) ≤ ((C / g : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  apply mul_le_mul_of_nonneg_left _ hK0
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by linarith)
  have hcpos : 0 < C / g := by omega
  have h1 := rad_mul_le (a := A / g * (B / g)) (b := C / g) (by positivity) hcpos.ne'
  have h2 := rad_mul_le (a := A / g) (b := B / g) ha.ne' hb.ne'
  have h3 : rad (A / g * (B / g)) * rad (C / g) ≤ rad (A / g) * rad (B / g) * rad (C / g) :=
    Nat.mul_le_mul_right _ h2
  exact_mod_cast h1.trans h3

lemma div_rpow_le {x g ε : ℝ} (hx : 0 ≤ x) (hg : 1 ≤ g) (hε : 0 ≤ ε) :
    (x / g) ^ (1 + ε) ≤ x ^ (1 + ε) / g := by
  have hg0 : 0 < g := by linarith
  rw [Real.div_rpow hx hg0.le]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) hg0
  calc g = g ^ (1 : ℝ) := (Real.rpow_one g).symm
    _ ≤ g ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hg (by linarith)

lemma abc_finish {K ε : ℝ} (hε : 0 < ε) {N g : ℕ} {X Y : ℝ} (hg : 0 < g) (hgN : g ∣ N)
    (hN : 0 < N) (h : ((N / g : ℕ) : ℝ) ≤ K * X ^ (1 + ε)) (hX0 : 0 ≤ X) (hXY : X ≤ Y / g) :
    (N : ℝ) ≤ K * Y ^ (1 + ε) := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hNg : ((N / g : ℕ) : ℝ) = (N : ℝ) / g := Nat.cast_div hgN (by positivity)
  rw [hNg] at h
  have hNpos : (0 : ℝ) < N / g := by positivity
  have hK : 0 < K := by
    by_contra hK; push Not at hK
    have : K * X ^ (1 + ε) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hK (Real.rpow_nonneg hX0 _)
    linarith
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ Y / g := hX0.trans hXY
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => by linarith [h.2]
  have h1 : X ^ (1 + ε) ≤ (Y / g) ^ (1 + ε) := Real.rpow_le_rpow hX0 hXY (by linarith)
  have h2 := div_rpow_le hY0 hg' hε.le
  have h3 : (N : ℝ) / g ≤ K * Y ^ (1 + ε) / g := by
    calc (N : ℝ) / g ≤ K * X ^ (1 + ε) := h
      _ ≤ K * (Y ^ (1 + ε) / g) := mul_le_mul_of_nonneg_left (h1.trans h2) hK.le
      _ = K * Y ^ (1 + ε) / g := by ring
  have hg0 : (0 : ℝ) < g := by positivity
  rwa [div_le_div_iff_of_pos_right hg0] at h3

/-- **Theorem 33.16** (section 33.4.1), the abc step. Assume abc. For every `ε > 0` there is `K`
such that `U^2 = N + R` with `N, U > 0`, `R ≠ 0` implies `N ≤ K (rad(N) U |R|)^(1 + ε)`. In
the 3-digit equation `U^2 = N + R` of Theorem 25.7 (and of the factorions, section 33.1.5) this
is the inequality that bounds the large digit when `R ≠ 0`. -/
theorem theorem33_16_abc (habc : ABC) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ (N U : ℕ) (R : ℤ), 0 < N → 0 < U → R ≠ 0 → (U : ℤ) ^ 2 = N + R →
      (N : ℝ) ≤ K * ((rad N : ℝ) * U * |R|) ^ (1 + ε) := by
  obtain ⟨K, hK⟩ := habc ε hε
  refine ⟨K, fun N U R hN hU hR h => ?_⟩
  set r := R.natAbs with hr
  have hr0 : 0 < r := Int.natAbs_pos.2 hR
  have hRr : |R| = (r : ℝ) := by rw [hr, Nat.cast_natAbs, Int.cast_abs]
  rw [hRr]
  have hU2 : U ^ 2 ≠ 0 := by positivity
  have hradU : rad (U ^ 2) ≤ U := (rad_pow (by norm_num)).le.trans (rad_le_self hU.ne')
  have hcU : ((U ^ 2 : ℕ) : ℤ) = (U : ℤ) ^ 2 := by push_cast; ring
  rcases lt_or_gt_of_ne hR with hneg | hpos
  · -- `U^2 + r = N`
    have hsum : U ^ 2 + r = N := by omega
    set g := Nat.gcd (U ^ 2) r
    have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hr0
    have hgN : g ∣ N := hsum ▸ dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    have hgr : g ∣ r := Nat.gcd_dvd_right _ _
    have h1 := abc_div_gcd hK hε (by positivity) hr0 hsum
    refine abc_finish hε hg hgN hN h1 (Nat.cast_nonneg _) ?_
    have b1 : rad (U ^ 2 / g) ≤ U :=
      (rad_le_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)) hU2).trans hradU
    have b2 : rad (r / g) ≤ r / g := rad_le_self (Nat.div_pos (Nat.le_of_dvd hr0 hgr) hg).ne'
    have b3 : rad (N / g) ≤ rad N := rad_le_of_dvd (Nat.div_dvd_of_dvd hgN) hN.ne'
    have hb : rad (U ^ 2 / g) * rad (r / g) * rad (N / g) ≤ U * (r / g) * rad N :=
      Nat.mul_le_mul (Nat.mul_le_mul b1 b2) b3
    have hrg : ((r / g : ℕ) : ℝ) = (r : ℝ) / g := Nat.cast_div hgr (by positivity)
    calc ((rad (U ^ 2 / g) * rad (r / g) * rad (N / g) : ℕ) : ℝ)
        ≤ ((U * (r / g) * rad N : ℕ) : ℝ) := by exact_mod_cast hb
      _ = (rad N : ℝ) * U * r / g := by push_cast [hrg]; ring
  · -- `N + r = U^2`
    have hsum : N + r = U ^ 2 := by omega
    set g := Nat.gcd N r
    have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hr0
    have hgN : g ∣ N := Nat.gcd_dvd_left _ _
    have hgr : g ∣ r := Nat.gcd_dvd_right _ _
    have h1 := abc_div_gcd hK hε hN hr0 hsum
    have hle : ((N / g : ℕ) : ℝ) ≤ ((U ^ 2 / g : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_le_div_right (by omega)
    refine abc_finish hε hg hgN hN (hle.trans h1) (Nat.cast_nonneg _) ?_
    have hgU : g ∣ U ^ 2 := hsum ▸ dvd_add hgN hgr
    have b1 : rad (U ^ 2 / g) ≤ U :=
      (rad_le_of_dvd (Nat.div_dvd_of_dvd hgU) hU2).trans hradU
    have b2 : rad (r / g) ≤ r / g := rad_le_self (Nat.div_pos (Nat.le_of_dvd hr0 hgr) hg).ne'
    have b3 : rad (N / g) ≤ rad N := rad_le_of_dvd (Nat.div_dvd_of_dvd hgN) hN.ne'
    have hb : rad (N / g) * rad (r / g) * rad (U ^ 2 / g) ≤ rad N * (r / g) * U :=
      Nat.mul_le_mul (Nat.mul_le_mul b3 b2) b1
    have hrg : ((r / g : ℕ) : ℝ) = (r : ℝ) / g := Nat.cast_div hgr (by positivity)
    calc ((rad (N / g) * rad (r / g) * rad (U ^ 2 / g) : ℕ) : ℝ)
        ≤ ((rad N * (r / g) * U : ℕ) : ℝ) := by exact_mod_cast hb
      _ = (rad N : ℝ) * U * r / g := by push_cast [hrg]; ring

/-- **Theorem 33.16** (section 33.4.1), the first inequality. Assume abc and `0 < ε ≤ 1`. If
`U^2 = N + R` with `N, U > 0` and `0 < |R| ≤ N`, then `U^2 ≤ 2 N` and
`N^((1 - ε)/2) ≤ 2 K (rad(N) |R|)^(1 + ε)`; taking logarithms gives the displayed inequality
`(1 - ε)/2 log N ≤ log K + (1 + ε) log(rad(N) |R|) + log 2`. -/
theorem theorem33_16 (habc : ABC) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, ∀ (N U : ℕ) (R : ℤ), 0 < N → 0 < U → R ≠ 0 → |R| ≤ N →
      (U : ℤ) ^ 2 = N + R → (N : ℝ) ^ ((1 - ε) / 2) ≤ 2 * K * ((rad N : ℝ) * |R|) ^ (1 + ε) := by
  obtain ⟨K, hK⟩ := theorem33_16_abc habc hε
  refine ⟨K, fun N U R hN hU hR hRN h => ?_⟩
  have main := hK N U R hN hU hR h
  push_cast at main ⊢
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU0 : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hrad0 : (0 : ℝ) ≤ (rad N : ℝ) * |(R : ℝ)| := by positivity
  have hRN' : |(R : ℝ)| ≤ N := by exact_mod_cast hRN
  have hU2 : (U : ℝ) ^ 2 ≤ 2 * N := by
    have : ((U : ℤ) : ℝ) ^ 2 = (N : ℝ) + R := by exact_mod_cast h
    push_cast at this
    have := le_abs_self (R : ℝ)
    linarith
  have hUr : (U : ℝ) ^ (1 + ε) ≤ 2 * (N : ℝ) ^ ((1 + ε) / 2) := by
    have e1 : (U : ℝ) ^ (1 + ε) = ((U : ℝ) ^ (2 : ℝ)) ^ ((1 + ε) / 2) := by
      rw [← Real.rpow_mul hU0]; ring_nf
    have e2 : ((U : ℝ) ^ (2 : ℝ)) = (U : ℝ) ^ 2 := Real.rpow_two _
    rw [e1, e2]
    calc ((U : ℝ) ^ 2) ^ ((1 + ε) / 2) ≤ (2 * (N : ℝ)) ^ ((1 + ε) / 2) :=
          Real.rpow_le_rpow (by positivity) hU2 (by linarith)
      _ = (2 : ℝ) ^ ((1 + ε) / 2) * (N : ℝ) ^ ((1 + ε) / 2) :=
          Real.mul_rpow (by norm_num) hN0.le
      _ ≤ 2 * (N : ℝ) ^ ((1 + ε) / 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
          calc (2 : ℝ) ^ ((1 + ε) / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
  have hsplit : ((rad N : ℝ) * U * |(R : ℝ)|) ^ (1 + ε) =
      ((rad N : ℝ) * |(R : ℝ)|) ^ (1 + ε) * (U : ℝ) ^ (1 + ε) := by
    rw [← Real.mul_rpow hrad0 hU0]; ring_nf
  rw [hsplit] at main
  have hA0 : 0 ≤ ((rad N : ℝ) * |(R : ℝ)|) ^ (1 + ε) := Real.rpow_nonneg hrad0 _
  have hK0 : 0 < K := by
    by_contra hK0; push Not at hK0
    have : K * (((rad N : ℝ) * |(R : ℝ)|) ^ (1 + ε) * (U : ℝ) ^ (1 + ε)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK0 (mul_nonneg hA0 (Real.rpow_nonneg hU0 _))
    linarith
  have hNp : (0 : ℝ) < (N : ℝ) ^ ((1 + ε) / 2) := Real.rpow_pos_of_pos hN0 _
  have h2 : (N : ℝ) ≤ 2 * K * ((rad N : ℝ) * |(R : ℝ)|) ^ (1 + ε) * (N : ℝ) ^ ((1 + ε) / 2) := by
    calc (N : ℝ) ≤ K * (((rad N : ℝ) * |(R : ℝ)|) ^ (1 + ε) * (U : ℝ) ^ (1 + ε)) := main
      _ ≤ K * (((rad N : ℝ) * |(R : ℝ)|) ^ (1 + ε) * (2 * (N : ℝ) ^ ((1 + ε) / 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUr hA0) hK0.le
      _ = _ := by ring
  have e3 : (N : ℝ) ^ ((1 - ε) / 2) = (N : ℝ) / (N : ℝ) ^ ((1 + ε) / 2) := by
    rw [show (1 - ε) / 2 = 1 - (1 + ε) / 2 by ring, Real.rpow_sub hN0, Real.rpow_one]
  rw [e3, div_le_iff₀ hNp]
  exact h2

end Munchausen
