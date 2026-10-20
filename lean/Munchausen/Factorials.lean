import Munchausen.OtherSystems
import Munchausen.ThreeDigitBases

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
  `U^2 = N + R`, `R ≠ 0` gives `N ≤ K (rad(N) U |R|)^(1 + ε)`; with `rad(4 l x^x) ≤ 2 l x`
  and `|R| ≤ 9 x^2 B^B` (Theorem 25.7) this bounds the large digit of a 3-digit solution by
  `x ≤ (2 + δ) B + C_δ`, in every position, and gives Corollary 33.17 (with the self-paying
  exceptions `(x, 0, 0)`, `(x, 0, 1)` under `0^0 = 0`);
* Theorem 15.10 under abc: finitely many 2-digit solutions in perfect-power bases with one
  weight much smaller than the other.
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

/-! ### Theorem 33.16 to the end, and Corollary 33.17 -/

lemma rad_four : rad 4 = 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, rad_pow (by norm_num), rad, Nat.prime_two.primeFactors]
  simp

/-- `rad(4 l x^x) ≤ 2 l x` (proof of Theorem 33.16). -/
lemma rad_four_mul_pow_self_le {l x : ℕ} (hl : 1 ≤ l) (hx : 1 ≤ x) :
    rad (4 * l * x ^ x) ≤ 2 * l * x := by
  have h4l : 4 * l ≠ 0 := by omega
  have hxx : x ^ x ≠ 0 := by positivity
  calc rad (4 * l * x ^ x) ≤ rad (4 * l) * rad (x ^ x) := rad_mul_le h4l hxx
    _ ≤ (rad 4 * rad l) * rad (x ^ x) :=
        Nat.mul_le_mul_right _ (rad_mul_le (by norm_num) (by omega))
    _ ≤ (2 * l) * x := by
        rw [rad_four, rad_pow (by omega)]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 (rad_le_self (by omega)))
          (rad_le_self (by omega))

/-- **Theorem 33.16** (section 33.4.1), the bound on `x`. Assume abc. For every `δ > 0` there is
`C` such that `U^2 = 4 l x^x + R` with `1 ≤ l ≤ x`, `1 ≤ B`, `x ≥ 2B + 4`, `U > 0`, `R ≠ 0` and
`|R| ≤ 9 x^2 B^B` (the setting of Theorem 25.7) implies `x ≤ (2 + δ) B + C`. The proof takes
`ε = δ/(4 + δ)` in `theorem33_16`, so that `2 (1 + ε)/(1 - ε) = 2 + δ`, and uses
`rad(N) ≤ 2 l x` and `log B ≤ log x`. -/
theorem theorem33_16_bound (habc : ABC) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ (l x B U : ℕ) (R : ℤ), 1 ≤ l → l ≤ x → 1 ≤ B → 2 * B + 4 ≤ x → 0 < U →
      R ≠ 0 → |R| ≤ 9 * x ^ 2 * B ^ B → (U : ℤ) ^ 2 = 4 * l * x ^ x + R →
      (x : ℝ) ≤ (2 + δ) * B + C := by
  set ε := δ / (4 + δ) with hεdef
  have h4δ : 0 < 4 + δ := by linarith
  have hε : 0 < ε := div_pos hδ h4δ
  have hε1 : ε < 1 := (div_lt_one h4δ).2 (by linarith)
  obtain ⟨K, hK⟩ := theorem33_16 habc hε hε1.le
  set A := |Real.log (2 * K)| + (1 + ε) * (Real.log 18 + 4) with hA
  refine ⟨2 * A / (1 - ε), fun l x B U R hl hlx hB hx hU hR hRb heq => ?_⟩
  set N := 4 * l * x ^ x with hN
  have hx3 : 3 ≤ x := by omega
  have hxpos : 0 < x := by omega
  have hNpos : 0 < N := by positivity
  -- `|R| ≤ N`
  have hbig := pow_self_ge hB hx
  have hRN : |R| ≤ (N : ℤ) := by
    refine hRb.trans ?_
    have h1 : 9 * x ^ 2 * B ^ B ≤ N := by
      have : 1 ≤ B ^ B := Nat.one_le_pow _ _ (by omega)
      have : x ^ 2 ≤ x ^ 4 := Nat.pow_le_pow_right hxpos (by norm_num)
      have : 9 * x ^ 2 * B ^ B ≤ 25 * x ^ 4 * (B ^ B) ^ 2 := by
        calc 9 * x ^ 2 * B ^ B ≤ 25 * x ^ 4 * (B ^ B * B ^ B) := by
              apply Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) this)
              exact Nat.le_mul_of_pos_left _ (by omega)
          _ = 25 * x ^ 4 * (B ^ B) ^ 2 := by ring
      have : x ^ x ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact_mod_cast h1
  have main := hK N U R hNpos hU hR hRN (by rw [heq, hN]; push_cast; ring)
  -- the real inequality
  have hxr : (3 : ℝ) ≤ x := by exact_mod_cast hx3
  have hx0 : (0 : ℝ) < x := by linarith
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBx : (B : ℝ) ≤ x := by exact_mod_cast (show B ≤ x by omega)
  have hRpos : (0 : ℝ) < |(R : ℝ)| := abs_pos.2 (by exact_mod_cast hR)
  have hrad1 : (1 : ℝ) ≤ rad N := by exact_mod_cast one_le_rad N
  have hP0 : 0 < ((rad N : ℝ) * |(R : ℝ)|) := by positivity
  have hLHS : 0 < (N : ℝ) ^ ((1 - ε) / 2) := Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have hK2 : 0 < 2 * K := by
    by_contra h
    push Not at h
    have : 2 * K * ((rad N : ℝ) * |(R : ℝ)|) ^ (1 + ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (Real.rpow_nonneg hP0.le _)
    push_cast at main
    linarith
  -- `rad(N) |R| ≤ 18 x^4 B^B`
  have hradN : (rad N : ℝ) ≤ 2 * x * x := by
    have h1 := rad_four_mul_pow_self_le hl hxpos
    have h2 : 2 * l * x ≤ 2 * x * x := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hlx)
    exact_mod_cast h1.trans h2
  have hRr : |(R : ℝ)| ≤ 9 * x ^ 2 * (B : ℝ) ^ B := by
    have : ((|R| : ℤ) : ℝ) ≤ ((9 * x ^ 2 * B ^ B : ℕ) : ℝ) := by exact_mod_cast hRb
    push_cast at this
    exact this
  have hprod : (rad N : ℝ) * |(R : ℝ)| ≤ 18 * (x : ℝ) ^ 4 * (B : ℝ) ^ B := by
    calc (rad N : ℝ) * |(R : ℝ)| ≤ (2 * x * x) * (9 * x ^ 2 * (B : ℝ) ^ B) :=
          mul_le_mul hradN hRr (abs_nonneg _) (by positivity)
      _ = 18 * (x : ℝ) ^ 4 * (B : ℝ) ^ B := by ring
  -- logarithms
  have hNx : (x : ℝ) ^ x ≤ N := by
    have : x ^ x ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ (by omega)
    exact_mod_cast this
  have hlog := Real.log_le_log hLHS (by push_cast at main; exact main)
  rw [Real.log_rpow (by exact_mod_cast hNpos), Real.log_mul hK2.ne'
    (Real.rpow_pos_of_pos hP0 _).ne', Real.log_rpow hP0] at hlog
  have hl1 : (x : ℝ) * Real.log x ≤ Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hNx
  have hl2 : Real.log ((rad N : ℝ) * |(R : ℝ)|) ≤
      Real.log 18 + 4 * Real.log x + B * Real.log x := by
    have := Real.log_le_log hP0 hprod
    rw [Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero 4 hx0.ne'))
        (pow_ne_zero B (by linarith : (0 : ℝ) < B).ne'),
      Real.log_mul (by norm_num) (pow_ne_zero 4 hx0.ne'), Real.log_pow, Real.log_pow,
      Nat.cast_ofNat] at this
    have hlogB : Real.log B ≤ Real.log x := Real.log_le_log (by linarith) hBx
    have : (B : ℝ) * Real.log B ≤ B * Real.log x :=
      mul_le_mul_of_nonneg_left hlogB (by linarith)
    linarith
  set L := Real.log x with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog18 : 0 ≤ Real.log 18 := Real.log_nonneg (by norm_num)
  have hε0 : 0 ≤ 1 + ε := by linarith
  -- `(1 - ε)/2 x L ≤ log(2K) + (1 + ε)(log 18 + 4 L + B L)`
  have key : (1 - ε) / 2 * (x * L) ≤
      Real.log (2 * K) + (1 + ε) * (Real.log 18 + 4 * L + B * L) := by
    have h1 : (1 - ε) / 2 * (x * L) ≤ (1 - ε) / 2 * Real.log N :=
      mul_le_mul_of_nonneg_left hl1 (by linarith)
    have h2 : (1 + ε) * Real.log ((rad N : ℝ) * |(R : ℝ)|) ≤
        (1 + ε) * (Real.log 18 + 4 * L + B * L) := mul_le_mul_of_nonneg_left hl2 hε0
    linarith
  -- divide by `L ≥ 1`
  have key2 : (1 - ε) / 2 * x * L ≤ (A + (1 + ε) * B) * L := by
    have h1 : Real.log (2 * K) ≤ |Real.log (2 * K)| * L := by
      have := le_abs_self (Real.log (2 * K))
      nlinarith [abs_nonneg (Real.log (2 * K))]
    have h2 : (1 + ε) * Real.log 18 ≤ (1 + ε) * Real.log 18 * L := by
      have : 0 ≤ (1 + ε) * Real.log 18 := mul_nonneg hε0 hlog18
      nlinarith
    rw [hA]
    nlinarith
  have key3 : (1 - ε) / 2 * x ≤ A + (1 + ε) * B :=
    le_of_mul_le_mul_right key2 (by linarith)
  have h1ε : 0 < 1 - ε := by linarith
  have hratio : 2 * (1 + ε) / (1 - ε) = 2 + δ := by
    rw [hεdef, div_eq_iff (by rw [← hεdef]; exact h1ε.ne')]
    field_simp
    ring
  have : (x : ℝ) ≤ (2 * (1 + ε) * B + 2 * A) / (1 - ε) := by
    rw [le_div_iff₀ h1ε]
    linarith
  rwa [add_div, mul_div_right_comm, hratio] at this

/-- `|R| ≤ 9 x^2 W` from `16 R^2 ≤ (25 x^2 W)^2` with `W ≥ 0`. -/
lemma abs_le_of_sixteen_sq_le {R x W : ℤ} (hW : 0 ≤ W) (h : 16 * R ^ 2 ≤ (25 * x ^ 2 * W) ^ 2) :
    |R| ≤ 9 * x ^ 2 * W := by
  by_contra hc
  push Not at hc
  have h1 : (9 * x ^ 2 * W) ^ 2 < |R| ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
  rw [sq_abs] at h1
  nlinarith

/-- **Theorem 33.16** for 3-digit solutions (section 33.4.1). Assume abc. For every `δ > 0` there
is `C` such that every 3-digit solution, under either convention, with two digits at most
`B ≥ 1` and a third digit `x ≥ 2B + 4` in any position and with `R ≠ 0` (`R` of Theorem 25.7)
has `x ≤ (2 + δ) B + C`. In the middle `R > 0` always. -/
theorem theorem33_16_solution (habc : ABC) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ b m B x : ℕ, m ≤ 1 → 1 ≤ B → 2 * B + 4 ≤ x →
      (∀ p q, IsSolution b m [p, q, x] → p ≤ B → q ≤ B →
        4 * (p : ℤ) * ((w m p : ℤ) + w m q - x) + q ^ 2 ≠ 0 → (x : ℝ) ≤ (2 + δ) * B + C) ∧
      (∀ p r, IsSolution b m [p, x, r] → p ≤ B → r ≤ B → (x : ℝ) ≤ (2 + δ) * B + C) ∧
      (∀ q r, IsSolution b m [x, q, r] → q ≤ B → r ≤ B →
        4 * (x : ℤ) * ((w m q : ℤ) + w m r - r) + q ^ 2 ≠ 0 → (x : ℝ) ≤ (2 + δ) * B + C) := by
  obtain ⟨C, hC⟩ := theorem33_16_bound habc hδ
  refine ⟨C, fun b m B x hm hB hx => ?_⟩
  set W := B ^ B
  have hW1 : (1 : ℤ) ≤ W := by exact_mod_cast Nat.one_le_pow B B (by omega)
  have hxB : 2 * (B : ℤ) + 4 ≤ x := by exact_mod_cast hx
  have hx1 : (1 : ℤ) ≤ x := by linarith
  have hX : (x : ℤ) ≤ (x : ℤ) ^ 2 := by nlinarith
  have hX2 : (x : ℤ) ^ 2 ≤ (x : ℤ) ^ 2 * W := le_mul_of_one_le_right (by positivity) hW1
  have hXW : (x : ℤ) * W ≤ (x : ℤ) ^ 2 * W := mul_le_mul_of_nonneg_right hX (by linarith)
  have hWc : ((B : ℤ) ^ B) = (W : ℤ) := by simp [W]
  refine ⟨?_, ?_, ?_⟩
  · intro p q hs hp hq hR
    have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
    have heq := hs.eq
    simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
      add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
    rw [w_of_ne_zero m (show x ≠ 0 by omega)] at heq
    have hsq := complete_square (b := b) (p := p) (q := q) (r := x)
      (F := w m p + (w m q + x ^ x)) (by rw [← heq]; ring)
    have hb : 1 ≤ b := by have := hs.lt_base p (by simp); omega
    have hwp : (w m p : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hp
    have hwq : (w m q : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hq
    have h16 := bound_last (p := p) (q := q) (x := x) (B := B) (W := W) (wp := w m p)
      (wq := w m q) (by exact_mod_cast hp1) (by exact_mod_cast hp) (by positivity)
      (by exact_mod_cast hq) hxB (by positivity) (by positivity) hwp hwq hW1
    refine hC p x B (2 * p * b + q) _ hp1 (by omega) hB hx (by positivity) hR ?_ ?_
    · have := abs_le_of_sixteen_sq_le (by positivity) h16
      rw [hWc]; linarith
    · rw [hsq]; push_cast; ring
  · intro p r hs hp hr
    have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 (hs.head_ne_zero (by simp))
    have heq := hs.eq
    simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
      add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
    rw [w_of_ne_zero m (show x ≠ 0 by omega)] at heq
    have hsq := complete_square (b := b) (p := p) (q := x) (r := r)
      (F := w m p + (x ^ x + w m r)) (by rw [← heq]; ring)
    have hwp : (w m p : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hp
    have hwr : (w m r : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hr
    have hR0 := R_pos_middle m (p := p) (r := r) (x := x) hp1
    refine hC p x B (2 * p * b + x) _ hp1 (by omega) hB hx (by omega) hR0.ne' ?_ ?_
    · rw [abs_of_pos hR0]
      have hpB : (p : ℤ) ≤ B := by exact_mod_cast hp
      have hr0 : (0 : ℤ) ≤ r := by positivity
      have k1 : (p : ℤ) * ((w m p : ℤ) + w m r - r) ≤ B * (2 * W) :=
        mul_le_mul hpB (by linarith) (by linarith [le_w_int m r, hwp, hr0,
          (by exact_mod_cast Nat.zero_le _ : (0 : ℤ) ≤ w m p)]) (by linarith)
      have k3 : 2 * (B : ℤ) * W ≤ x * W := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      rw [hWc]
      linarith
    · rw [hsq]; push_cast; ring
  · intro q r hs hq hr hR
    have heq := hs.eq
    simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
      add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
    rw [w_of_ne_zero m (show x ≠ 0 by omega)] at heq
    have hsq := complete_square (b := b) (p := x) (q := q) (r := r)
      (F := x ^ x + (w m q + w m r)) (by rw [← heq]; ring)
    have hb : 1 ≤ b := by have := hs.lt_base x (by simp); omega
    have hwq : (w m q : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hq
    have hwr : (w m r : ℤ) ≤ W := by exact_mod_cast w_le_pow hm hB hr
    refine hC x x B (2 * x * b + q) _ (by omega) le_rfl hB hx
      (lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) hb)
        (Nat.le_add_right _ _)) hR ?_ ?_
    · have hrw := le_w_int m r
      have hq0 : (0 : ℤ) ≤ q := by positivity
      have hwq0 : (0 : ℤ) ≤ w m q := by positivity
      have hqB : (q : ℤ) ≤ B := by exact_mod_cast hq
      have hR0 : 0 ≤ 4 * (x : ℤ) * ((w m q : ℤ) + w m r - r) + q ^ 2 := by
        have : 0 ≤ (x : ℤ) * ((w m q : ℤ) + w m r - r) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      rw [abs_of_nonneg hR0]
      have k1 : (x : ℤ) * ((w m q : ℤ) + w m r - r) ≤ x * (2 * W) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have k2 : (q : ℤ) ^ 2 ≤ (x : ℤ) ^ 2 := pow_le_pow_left₀ hq0 (by linarith) 2
      rw [hWc]
      linarith
    · rw [hsq]; push_cast; ring

/-- The self-paying family `(x, 0, 0)` (Proposition 2.3): under `0^0 = 0`, for odd `x ≥ 5` it is
a solution in base `x^((x-1)/2)`, with the large digit in front and `R = 0`. So Corollary 33.17
needs these strings as exceptions under `0^0 = 0` (problem 9 of `STATUS.md`). -/
theorem isSolution_x_0_0 {x : ℕ} (hx : Odd x) (hx5 : 5 ≤ x) :
    IsSolution (x ^ ((x - 1) / 2)) 0 [x, 0, 0] := by
  obtain ⟨k, rfl⟩ := hx
  have hlt : 2 * k + 1 < (2 * k + 1) ^ ((2 * k + 1 - 1) / 2) :=
    calc 2 * k + 1 < (2 * k + 1) ^ 2 := by nlinarith
      _ ≤ (2 * k + 1) ^ ((2 * k + 1 - 1) / 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsp : SelfPaying ((2 * k + 1) ^ ((2 * k + 1 - 1) / 2)) (2 * k + 1) [0, 0].length := by
    refine ⟨by omega, by simp, hlt, ?_⟩
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
    rw [← pow_mul, show (2 * k + 1 - 1) / 2 * 2 = 2 * k by omega, ← pow_succ']
  rw [isSolution_selfPaying_cons_iff hsp (fun d hd => by simp at hd; omega)]
  simp

/-- **Corollary 33.17** (section 33.4.1), corrected. Assume abc. For every `ε > 0` there is
`B_ε` such that every 3-digit solution, under either convention, whose largest digit `x`
exceeds `(2 + ε) max(B_ε, B)`, where the two other digits are at most `B`, is a member of case
(i) of Theorem 25.7 when `x` is last; `x` is never in the middle; and when `x` leads, the
convention is `0^0 = 0` and the string is `(x, 0, 0)` or `(x, 0, 1)`, a self-paying family
(`isSolution_x_0_0`). The library omits this last exception (problem 9 of `STATUS.md`). -/
theorem corollary33_17 (habc : ABC) {ε : ℝ} (hε : 0 < ε) :
    ∃ Bε : ℕ, ∀ b m B x : ℕ, m ≤ 1 → (2 + ε) * (max Bε B : ℕ) < (x : ℝ) →
      (∀ p q, IsSolution b m [p, q, x] → p ≤ B → q ≤ B →
        ∃ lam c e, Squarefree lam ∧ 1 ≤ c ∧ p = lam * c ^ 2 ∧ q = 2 * lam * c * e ∧
          x = w m p + w m q + lam * e ^ 2 ∧ x ^ x = lam * (c * b + e) ^ 2) ∧
      (∀ p r, IsSolution b m [p, x, r] → p ≤ B → r ≤ B → False) ∧
      (∀ q r, IsSolution b m [x, q, r] → q ≤ B → r ≤ B → m = 0 ∧ q = 0 ∧ r ≤ 1) := by
  obtain ⟨C, hC⟩ := theorem33_16_solution habc (half_pos hε)
  set Bε := ⌈(4 + 2 * |C|) / ε⌉₊ + 1
  refine ⟨Bε, fun b m B x hm hx => ?_⟩
  set B1 := max B 1
  have hB1 : 1 ≤ B1 := le_max_right _ _
  have hBB1 : B ≤ B1 := le_max_left _ _
  have hM : max Bε B = max Bε B1 := by
    simp only [B1, Bε]
    rw [max_comm B 1, ← max_assoc, max_eq_left (by omega : 1 ≤ ⌈(4 + 2 * |C|) / ε⌉₊ + 1)]
  rw [hM] at hx
  set M := max Bε B1
  have hMB : (B1 : ℝ) ≤ M := by exact_mod_cast le_max_right Bε B1
  have hMε : (Bε : ℝ) ≤ M := by exact_mod_cast le_max_left Bε B1
  have hεB : 4 + 2 * |C| ≤ ε * Bε := by
    have h1 := Nat.le_ceil ((4 + 2 * |C|) / ε)
    have h2 : (⌈(4 + 2 * |C|) / ε⌉₊ : ℝ) ≤ Bε := by simp only [Bε]; push_cast; linarith
    rw [div_le_iff₀ hε] at h1
    nlinarith
  have hx4 : 2 * B1 + 4 ≤ x := by
    have : (2 * B1 + 4 : ℝ) < x := by nlinarith [abs_nonneg C]
    exact_mod_cast this.le
  have hbig : (2 + ε / 2) * B1 + C < (x : ℝ) := by
    have : ε / 2 * Bε ≤ ε / 2 * M := mul_le_mul_of_nonneg_left hMε (by linarith)
    nlinarith [le_abs_self C, abs_nonneg C]
  obtain ⟨hlast, hmid, hlead⟩ := hC b m B1 x hm hB1 hx4
  refine ⟨fun p q hs hp hq => ?_, fun p r hs hp hr => ?_, fun q r hs hq hr => ?_⟩
  · by_cases hR : 4 * (p : ℤ) * ((w m p : ℤ) + w m q - x) + q ^ 2 = 0
    · refine theorem25_7_i hs ?_
      have : (4 * p * x : ℤ) = 4 * p * (w m p + w m q) + q ^ 2 := by linear_combination -hR
      exact_mod_cast this
    · exact absurd (hlast p q hs (hp.trans hBB1) (hq.trans hBB1) hR) (not_le.2 hbig)
  · exact absurd (hmid p r hs (hp.trans hBB1) (hr.trans hBB1)) (not_le.2 hbig)
  · by_cases hR : 4 * (x : ℤ) * ((w m q : ℤ) + w m r - r) + q ^ 2 = 0
    · have hrw := le_w_int m r
      have hq0 : (0 : ℤ) ≤ w m q := by positivity
      have hx0 : (0 : ℤ) < x := by exact_mod_cast (show 0 < x by omega)
      have h1 : 0 ≤ (x : ℤ) * ((w m q : ℤ) + w m r - r) := mul_nonneg hx0.le (by linarith)
      have hqq : (q : ℤ) ^ 2 = 0 := by nlinarith [sq_nonneg (q : ℤ)]
      have hq : q = 0 := by exact_mod_cast pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hqq
      subst hq
      have h2 : (x : ℤ) * ((w m 0 : ℤ) + w m r - r) = 0 := by nlinarith
      have h3 : (w m 0 : ℤ) + w m r - r = 0 := (mul_eq_zero.1 h2).resolve_left hx0.ne'
      rw [w_zero] at h3
      have hm0 : (m : ℤ) = 0 := by linarith [hrw, (by positivity : (0 : ℤ) ≤ m)]
      have hm0' : m = 0 := by exact_mod_cast hm0
      refine ⟨hm0', rfl, ?_⟩
      by_contra hr1
      push Not at hr1
      have : r < w m r := by
        rw [w_of_ne_zero m (by omega)]
        calc r < r ^ 2 := by nlinarith
          _ ≤ r ^ r := Nat.pow_le_pow_right (by omega) hr1
      have : (r : ℤ) < w m r := by exact_mod_cast this
      linarith
    · exact absurd (hlead q r hs (hq.trans hBB1) (hr.trans hBB1) hR) (not_le.2 hbig)

/-! ### Theorem 15.10 under abc -/

/-- The analytic step of Theorem 15.10: if `x^x ≤ K (2 x · x^(x γ))^(2+ε) (2 x^(2 + x/2))^(1+ε)`
with `(2 + ε) γ + (1 + ε)/2 < 1`, then `x` is bounded. -/
lemma bounded_of_rpow_le {K ε γ : ℝ} (hε : 0 ≤ ε)
    (hη : 0 < 1 - (2 + ε) * γ - (1 + ε) / 2) :
    ∃ X0 : ℕ, ∀ x : ℕ, 1 ≤ x → (x : ℝ) ^ x ≤
      K * (2 * x * (x : ℝ) ^ ((x : ℝ) * γ)) ^ (2 + ε) *
        (2 * (x : ℝ) ^ (2 + (x : ℝ) / 2)) ^ (1 + ε) →
      x ≤ X0 := by
  set η := 1 - (2 + ε) * γ - (1 + ε) / 2 with hηdef
  set C := |Real.log K| + (3 + 2 * ε) * Real.log 2 + (4 + 3 * ε) with hC
  refine ⟨max 3 ⌈C / η⌉₊, fun x hx h => ?_⟩
  by_contra hlt
  push Not at hlt
  have hx3 : 3 < x := lt_of_le_of_lt (le_max_left _ _) hlt
  have hxC : C / η < x := lt_of_lt_of_le (Nat.lt_of_ceil_lt (lt_of_le_of_lt (le_max_right _ _)
    hlt)) le_rfl
  have hxr : (3 : ℝ) < x := by exact_mod_cast hx3
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hA : 0 < 2 * (x : ℝ) * (x : ℝ) ^ ((x : ℝ) * γ) := by positivity
  have hB : 0 < 2 * (x : ℝ) ^ (2 + (x : ℝ) / 2) := by positivity
  have hP1 : 0 < (2 * (x : ℝ) * (x : ℝ) ^ ((x : ℝ) * γ)) ^ (2 + ε) := Real.rpow_pos_of_pos hA _
  have hP2 : 0 < (2 * (x : ℝ) ^ (2 + (x : ℝ) / 2)) ^ (1 + ε) := Real.rpow_pos_of_pos hB _
  have hLHS : 0 < (x : ℝ) ^ x := by positivity
  have hK : 0 < K := by
    by_contra hK
    push Not at hK
    have : K * (2 * x * (x : ℝ) ^ ((x : ℝ) * γ)) ^ (2 + ε) *
        (2 * (x : ℝ) ^ (2 + (x : ℝ) / 2)) ^ (1 + ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hK hP1.le) hP2.le
    linarith
  have hl := Real.log_le_log hLHS h
  rw [Real.log_mul (by positivity) hP2.ne', Real.log_mul hK.ne' hP1.ne', Real.log_rpow hA,
    Real.log_rpow hB, Real.log_mul (by positivity) (by positivity), Real.log_mul h2.ne' hx0.ne',
    Real.log_rpow hx0, Real.log_mul h2.ne' (by positivity), Real.log_rpow hx0,
    Real.log_pow] at hl
  -- `η x log x ≤ C log x`
  set L := Real.log x
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have key : η * x * L ≤ C * L := by
    have h1 : Real.log K ≤ |Real.log K| * L := by
      have := le_abs_self (Real.log K)
      nlinarith [abs_nonneg (Real.log K)]
    have h2' : (3 + 2 * ε) * Real.log 2 ≤ (3 + 2 * ε) * Real.log 2 * L := by
      have : 0 ≤ (3 + 2 * ε) * Real.log 2 := by positivity
      nlinarith
    rw [hηdef, hC]
    nlinarith
  have hL0 : 0 < L := by linarith
  have : η * x ≤ C := le_of_mul_le_mul_right (by linarith) hL0
  rw [div_lt_iff₀ hη] at hxC
  linarith

/-- abc for a sum that need not be coprime: `C ≤ gcd(A, B) K (rad A rad B rad C)^(1+ε)`. -/
lemma abc_le_gcd_mul {ε K : ℝ}
    (hK : ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)) (hε : 0 < ε)
    {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) (hABC : A + B = C) :
    (C : ℝ) ≤ Nat.gcd A B * (K * ((rad A * rad B * rad C : ℕ) : ℝ) ^ (1 + ε)) := by
  set g := Nat.gcd A B with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  have hgA : g ∣ A := Nat.gcd_dvd_left A B
  have hgB : g ∣ B := Nat.gcd_dvd_right A B
  have hgC : g ∣ C := hABC ▸ dvd_add hgA hgB
  have h := abc_div_gcd hK hε hA hB hABC
  rw [← hg] at h
  have hC0 : 0 < C := by omega
  have hrad : rad (A / g) * rad (B / g) * rad (C / g) ≤ rad A * rad B * rad C :=
    Nat.mul_le_mul (Nat.mul_le_mul (rad_le_of_dvd (Nat.div_dvd_of_dvd hgA) hA.ne')
      (rad_le_of_dvd (Nat.div_dvd_of_dvd hgB) hB.ne'))
      (rad_le_of_dvd (Nat.div_dvd_of_dvd hgC) hC0.ne')
  have hCg : ((C / g : ℕ) : ℝ) = (C : ℝ) / g := Nat.cast_div hgC (by positivity)
  rw [hCg] at h
  have hpos : (0 : ℝ) < (C : ℝ) / g := by positivity
  have hK0 : 0 < K := by
    by_contra hK0
    push Not at hK0
    have : K * ((rad (A / g) * rad (B / g) * rad (C / g) : ℕ) : ℝ) ^ (1 + ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    linarith
  have h2 : ((rad (A / g) * rad (B / g) * rad (C / g) : ℕ) : ℝ) ^ (1 + ε) ≤
      ((rad A * rad B * rad C : ℕ) : ℝ) ^ (1 + ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hrad) (by linarith)
  have h3 : (C : ℝ) / g ≤ K * ((rad A * rad B * rad C : ℕ) : ℝ) ^ (1 + ε) :=
    h.trans (mul_le_mul_of_nonneg_left h2 hK0.le)
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg0
  rw [div_le_iff₀ hg'] at h3
  linarith

/-- The inequality behind each case of Theorem 15.10: from `X ≤ D K (W D)^(1+ε)` with
`1 ≤ D ≤ 2 x x^(x γ)` and `W ≤ 2 x^(2 + x/2)` follows the hypothesis of
`bounded_of_rpow_le`. -/
lemma abc_case_le {K ε γ X D W x : ℝ} (hε : 0 ≤ ε) (hX : 0 < X) (hD1 : 1 ≤ D)
    (hD : D ≤ 2 * x * x ^ (x * γ)) (hW0 : 0 ≤ W) (hW : W ≤ 2 * x ^ (2 + x / 2))
    (h : X ≤ D * (K * (W * D) ^ (1 + ε))) :
    X ≤ K * (2 * x * x ^ (x * γ)) ^ (2 + ε) * (2 * x ^ (2 + x / 2)) ^ (1 + ε) := by
  have hD0 : 0 < D := by linarith
  have hK : 0 < K := by
    by_contra hK
    push Not at hK
    have : D * (K * (W * D) ^ (1 + ε)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hD0.le
        (mul_nonpos_of_nonpos_of_nonneg hK (Real.rpow_nonneg (by positivity) _))
    linarith
  have e2 : D ^ (2 + ε) = D * D ^ (1 + ε) := by
    rw [show (2 : ℝ) + ε = 1 + (1 + ε) by ring, Real.rpow_add hD0, Real.rpow_one]
  have e1 : D * (K * (W * D) ^ (1 + ε)) = K * D ^ (2 + ε) * W ^ (1 + ε) := by
    rw [Real.mul_rpow hW0 hD0.le, e2]
    ring
  rw [e1] at h
  refine h.trans ?_
  apply mul_le_mul _ (Real.rpow_le_rpow hW0 hW (by linarith)) (Real.rpow_nonneg hW0 _)
    (mul_nonneg hK.le (Real.rpow_nonneg (by linarith) _))
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hD0.le hD (by linarith)) hK.le

lemma sqrt_bound {r x : ℕ} (h : r ^ 2 ≤ 2 * x ^ x) : (r : ℝ) ≤ 2 * (x : ℝ) ^ ((x : ℝ) / 2) := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hsq : ((x : ℝ) ^ ((x : ℝ) / 2)) ^ 2 = (x : ℝ) ^ x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have h1 : (r : ℝ) ^ 2 ≤ (2 * (x : ℝ) ^ ((x : ℝ) / 2)) ^ 2 := by
    rw [mul_pow, hsq]
    have : ((r ^ 2 : ℕ) : ℝ) ≤ ((2 * x ^ x : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    have : (0 : ℝ) ≤ (x : ℝ) ^ x := by positivity
    linarith
  have h2 : (0 : ℝ) ≤ 2 * (x : ℝ) ^ ((x : ℝ) / 2) := by positivity
  nlinarith [sq_nonneg ((r : ℝ) - 2 * (x : ℝ) ^ ((x : ℝ) / 2)), Nat.cast_nonneg (α := ℝ) r]

lemma W_bound {u v r x : ℕ} (hu : u ≤ x) (hv : v ≤ x) (hr : r ^ 2 ≤ 2 * x ^ x) :
    ((u * r * v : ℕ) : ℝ) ≤ 2 * (x : ℝ) ^ (2 + (x : ℝ) / 2) := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  rw [Real.rpow_add' hx0 (by positivity), Real.rpow_two]
  have h1 := sqrt_bound hr
  have hu' : (u : ℝ) ≤ x := by exact_mod_cast hu
  have hv' : (v : ℝ) ≤ x := by exact_mod_cast hv
  push_cast
  have : (u : ℝ) * r ≤ x * (2 * (x : ℝ) ^ ((x : ℝ) / 2)) :=
    mul_le_mul hu' h1 (Nat.cast_nonneg r) hx0
  calc (u : ℝ) * r * v ≤ x * (2 * (x : ℝ) ^ ((x : ℝ) / 2)) * x :=
        mul_le_mul this hv' (Nat.cast_nonneg v) (by positivity)
    _ = 2 * (x ^ 2 * (x : ℝ) ^ ((x : ℝ) / 2)) := by ring

lemma D_bound {N x : ℕ} (hx : 1 ≤ x) {γ : ℝ} (hγ : 0 ≤ γ)
    (h : (N : ℝ) ≤ ((x ^ x : ℕ) : ℝ) ^ γ ∨ N ≤ x) :
    (N : ℝ) ≤ 2 * x * (x : ℝ) ^ ((x : ℝ) * γ) := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h1 : (1 : ℝ) ≤ (x : ℝ) ^ ((x : ℝ) * γ) := Real.one_le_rpow hx1 (by positivity)
  have e : ((x ^ x : ℕ) : ℝ) ^ γ = (x : ℝ) ^ ((x : ℝ) * γ) := by
    rw [Real.rpow_mul hx0]; push_cast; rw [Real.rpow_natCast]
  rcases h with h | h
  · rw [e] at h
    nlinarith
  · have : (N : ℝ) ≤ x := by exact_mod_cast h
    nlinarith

/-- One case of Theorem 15.10: abc for `A + B = C` with `x^x ≤ C`, `rad(A B C) ≤ u r v B`, and
the size bounds, gives the hypothesis of `bounded_of_rpow_le` at `x`. -/
lemma abc_case_nat {ε K γ : ℝ}
    (hK : ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)) (hε : 0 < ε) (hγ : 0 ≤ γ)
    {A B C x u v r : ℕ} (hA : 0 < A) (hB : 0 < B) (hABC : A + B = C) (hx : 1 ≤ x)
    (hX : x ^ x ≤ C) (hrad : rad A * rad B * rad C ≤ u * r * v * B) (hu : u ≤ x) (hv : v ≤ x)
    (hr : r ^ 2 ≤ 2 * x ^ x) (hBx : (B : ℝ) ≤ ((x ^ x : ℕ) : ℝ) ^ γ ∨ B ≤ x) :
    (x : ℝ) ^ x ≤
      K * (2 * x * (x : ℝ) ^ ((x : ℝ) * γ)) ^ (2 + ε) *
        (2 * (x : ℝ) ^ (2 + (x : ℝ) / 2)) ^ (1 + ε) := by
  have h := abc_le_gcd_mul hK hε hA hB hABC
  have hg : Nat.gcd A B ≤ B := Nat.gcd_le_right _ hB
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hK0 : 0 < K := by
    by_contra hK0
    push Not at hK0
    have : (Nat.gcd A B : ℝ) * (K * ((rad A * rad B * rad C : ℕ) : ℝ) ^ (1 + ε)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
        (mul_nonpos_of_nonpos_of_nonneg hK0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    linarith
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have h2 : (C : ℝ) ≤ B * (K * (((u * r * v : ℕ) : ℝ) * B) ^ (1 + ε)) := by
    refine h.trans (mul_le_mul (by exact_mod_cast hg) (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hrad) (by linarith)) hK0.le)
      (mul_nonneg hK0.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by linarith))
  have hX' : (x : ℝ) ^ x ≤ C := by exact_mod_cast hX
  exact abc_case_le hε.le (by positivity) hB1 (D_bound hx hγ hBx) (Nat.cast_nonneg _)
    (W_bound hu hv hr) (hX'.trans h2)

lemma pow_self_lt_pow_self {a c : ℕ} (ha : 1 ≤ a) (h : a ^ a < c ^ c) : a < c := by
  by_contra hac
  push Not at hac
  have := (Nat.pow_le_pow_left hac c).trans (Nat.pow_le_pow_right (by omega) hac)
  omega

/-- **Theorem 15.10** (section 15.3), assuming abc. Fix `δ > 0`. Only finitely many 2-digit
solutions `(a, c)` under `0^0 = 0` with `c ≥ 2`, `c ≠ a^a` and a perfect-power base `r^t`,
`t ≥ 2`, satisfy `min(a^a, c^c) ≤ max(a^a, c^c)^(1/4 - δ)`. -/
theorem theorem15_10 (habc : ABC) {δ : ℝ} (hδ : 0 < δ) :
    {p : ℕ × ℕ | 2 ≤ p.2 ∧ p.2 ≠ p.1 ^ p.1 ∧ ∃ r t : ℕ, 2 ≤ t ∧ IsSolution (r ^ t) 0 [p.1, p.2] ∧
      (min (p.1 ^ p.1) (p.2 ^ p.2) : ℕ) ≤
        ((max (p.1 ^ p.1) (p.2 ^ p.2) : ℕ) : ℝ) ^ ((1 : ℝ) / 4 - δ)}.Finite := by
  set δ₀ := min δ (1 / 4) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδ (by norm_num)
  have hδ₀le : δ₀ ≤ 1 / 4 := min_le_right _ _
  have hδ₀δ : δ₀ ≤ δ := min_le_left _ _
  set γ : ℝ := 1 / 4 - δ₀ with hγdef
  have hγ : 0 ≤ γ := by linarith
  have hη : 0 < 1 - (2 + δ₀) * γ - (1 + δ₀) / 2 := by rw [hγdef]; nlinarith
  obtain ⟨K, hK⟩ := habc δ₀ hδ₀pos
  obtain ⟨X0, hX0⟩ := bounded_of_rpow_le (K := K) hδ₀pos.le hη
  refine (Set.Finite.subset (Finset.range (X0 + 1) ×ˢ Finset.range (X0 + 1)).finite_toSet ?_)
  rintro ⟨a, c⟩ ⟨hc2, hca, r, t, ht, hsol, hmin⟩
  dsimp only at hc2 hca hsol hmin
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  obtain ⟨hlt, hhead, heq⟩ := hsol
  have ha : a ≠ 0 := hhead (by simp)
  have hab : a < r ^ t := hlt a (by simp)
  have hcb : c < r ^ t := hlt c (by simp)
  have hr2 : 2 ≤ r := by
    by_contra h
    have : r ^ t ≤ 1 := pow_le_one₀ (Nat.zero_le _) (by omega)
    omega
  have hrb : r ^ 2 ≤ r ^ t := Nat.pow_le_pow_right (by omega) ht
  have heq' : a * r ^ t + c = a ^ a + c ^ c := by
    have := heq
    simp only [P_pair, Fs_pair, w_of_ne_zero 0 ha, w_of_ne_zero 0 (show c ≠ 0 by omega),
      Nat.cast_id] at this
    exact this
  have hγ' : (1 : ℝ) / 4 - δ ≤ γ := by linarith
  -- `min ≤ max^γ`
  have hmin' : ((min (a ^ a) (c ^ c) : ℕ) : ℝ) ≤ ((max (a ^ a) (c ^ c) : ℕ) : ℝ) ^ γ := by
    refine hmin.trans (Real.rpow_le_rpow_of_exponent_le ?_ hγ')
    have : 1 ≤ max (a ^ a) (c ^ c) := le_trans (Nat.one_le_pow _ _ (by omega)) (le_max_right _ _)
    exact_mod_cast this
  have hcc : c < c ^ c := by
    calc c < c ^ 2 := by nlinarith
      _ ≤ c ^ c := Nat.pow_le_pow_right (by omega) hc2
  rcases lt_trichotomy (a ^ a) (c ^ c) with hlt' | heq'' | hgt
  · -- `a^a < c^c`: the bound is on `c`
    have hac : a < c := pow_self_lt_pow_self (by omega) hlt'
    rw [min_eq_left hlt'.le, max_eq_right hlt'.le] at hmin'
    have hrc : r ^ 2 ≤ 2 * c ^ c := by
      have : a * r ^ t ≤ 2 * c ^ c := by omega
      have : r ^ t ≤ a * r ^ t := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hradC : rad (a * r ^ t) ≤ a * r :=
      (rad_mul_le ha (by positivity)).trans (Nat.mul_le_mul (rad_le_self ha)
        ((rad_pow (by omega)).le.trans (rad_le_self (by omega))))
    have hradc : rad (c ^ c) ≤ c := (rad_pow (by omega)).le.trans (rad_le_self (by omega))
    have hcX : c ≤ X0 := by
      rcases lt_or_gt_of_ne hca with h1 | h1
      · -- `c < a^a`: `c^c + (a^a - c) = a r^t`
        refine hX0 c (by omega) (abc_case_nat hK hδ₀pos hγ (A := c ^ c) (B := a ^ a - c)
          (C := a * r ^ t) (u := a) (v := c) (r := r) (by positivity) (by omega) (by omega)
          (by omega) (by omega) ?_ hac.le le_rfl hrc (Or.inl ?_))
        · calc rad (c ^ c) * rad (a ^ a - c) * rad (a * r ^ t)
              ≤ c * (a ^ a - c) * (a * r) :=
                Nat.mul_le_mul (Nat.mul_le_mul hradc (rad_le_self (by omega))) hradC
            _ = a * r * c * (a ^ a - c) := by ring
        · have : ((a ^ a - c : ℕ) : ℝ) ≤ ((a ^ a : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
          exact this.trans hmin'
      · -- `a^a < c`: `a r^t + (c - a^a) = c^c`
        refine hX0 c (by omega) (abc_case_nat hK hδ₀pos hγ (A := a * r ^ t) (B := c - a ^ a)
          (C := c ^ c) (u := a) (v := c) (r := r) (by positivity) (by omega) (by omega)
          (by omega) le_rfl ?_ hac.le le_rfl hrc (Or.inr (by omega)))
        calc rad (a * r ^ t) * rad (c - a ^ a) * rad (c ^ c)
            ≤ a * r * (c - a ^ a) * c :=
              Nat.mul_le_mul (Nat.mul_le_mul hradC (rad_le_self (by omega))) hradc
          _ = a * r * c * (c - a ^ a) := by ring
    exact ⟨by omega, by omega⟩
  · -- `a^a = c^c` contradicts the hypothesis
    exfalso
    rw [heq'', min_self, max_self] at hmin'
    have h1 : (1 : ℝ) < ((c ^ c : ℕ) : ℝ) := by exact_mod_cast (show 1 < c ^ c by omega)
    have : ((c ^ c : ℕ) : ℝ) ^ γ < ((c ^ c : ℕ) : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt h1 (by linarith)
    rw [Real.rpow_one] at this
    linarith
  · -- `c^c < a^a`: the bound is on `a`
    have hca' : c < a := pow_self_lt_pow_self (by omega) hgt
    rw [min_eq_right hgt.le, max_eq_left hgt.le] at hmin'
    have hra : r ^ 2 ≤ 2 * a ^ a := by
      have : a * r ^ t ≤ 2 * a ^ a := by omega
      have : r ^ t ≤ a * r ^ t := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hradC : rad (a * r ^ t) ≤ a * r :=
      (rad_mul_le ha (by positivity)).trans (Nat.mul_le_mul (rad_le_self ha)
        ((rad_pow (by omega)).le.trans (rad_le_self (by omega))))
    have hrada : rad (a ^ a) ≤ a := (rad_pow ha).le.trans (rad_le_self ha)
    have haX : a ≤ X0 := by
      refine hX0 a (by omega) (abc_case_nat hK hδ₀pos hγ (A := a ^ a) (B := c ^ c - c)
        (C := a * r ^ t) (u := a) (v := a) (r := r) (by positivity) (by omega) (by omega)
        (by omega) (by omega) ?_ le_rfl le_rfl hra (Or.inl ?_))
      · calc rad (a ^ a) * rad (c ^ c - c) * rad (a * r ^ t)
            ≤ a * (c ^ c - c) * (a * r) :=
              Nat.mul_le_mul (Nat.mul_le_mul hrada (rad_le_self (by omega))) hradC
          _ = a * r * a * (c ^ c - c) := by ring
      · have : ((c ^ c - c : ℕ) : ℝ) ≤ ((c ^ c : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
        exact this.trans hmin'
    exact ⟨by omega, by omega⟩

end Munchausen
