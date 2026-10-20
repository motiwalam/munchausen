import Munchausen.FieldFamily

/-!
# The middle and leading positions: the elementary parts of chapter 38

* Section 38.1: the equations `b (p b + x) = x^x + A` (middle) and `b (x b + q) = x^x + A`
  (leading), their completed squares, and `A ≥ 1`.
* Section 38.2.1: the ring `Z[θ]` with `θ^2 = k^2 + x θ` (`θ = (x + sqrt R)/2`,
  `R = x^2 + 4 k^2`), the norms `N(θ + k) = k x`, `N(θ - k) = -k x`, `N(μ) = p x^x`, and
  Lemma 38.1 in elementary form: the splitting conditions of (a), the coprimality of `θ, θ'`,
  of `θ + k, θ' + k` and of `μ, μ'`, and (d) for a prime power `x`: `x^x` divides
  `μ (θ + k)^x` or `μ (θ' + k)^x`.
* Theorem 38.2: the bounds of Step 3 (`2k (1 - k^2/x^2) ≤ x log z ≤ 2k`), the trace of Steps 2
  and 3, the inequality of Step 4 (`x^2 (g- - e Λ0) ≤ 2 e k^3`), and the positivity of `g-`
  from Hermite's theorem, stated as the hypothesis `HermiteTheorem`.
* Corollary 38.3 (a) in full: `(1, x, 1)` and `(1, x, 0)` (`0^0 = 0`) with `x` an odd prime
  power are solutions only for `x = 3` (base 4) and `x = 7` (base 904). This is Theorem 38.2
  for `k = 1` with the unit built in `Z[θ]`, and needs no cited theorem.
* Section 38.4: the ring `Z[θ]` of the leading position (`θ^2 = x A + q θ`, `N(θ) = -x A`,
  `N(μ) = x^(x+1)`), Lemma 38.5 for `x` prime to `q` (`(-A)^(x+1) μ = ν0 θ^(x+1)` with
  `N(ν0) = (-A)^(x+1)`), Theorem 38.7 when `R = 4x + 1` is a square, the odd `x` of
  Corollary 38.8, and the case `q = 0` of Corollary 38.9.
* Section 38.6, the exact test for `x ≤ 6000`, replayed by the kernel as a sieve: the odd `x`
  of `(1, x, 1)`, `(1, x, 0)`, `(1, x, 3)`, `(3, x, 1)`, `(3, x, 0)` and the even `x` of
  `(x, 1, 1)`, `(x, 1, 0)`.

The ideal-theoretic statements (the factorizations of Lemma 38.1 (b) to (d) and Lemma 38.5 in
`O_K`, Lemma 38.4 in the biquadratic field), Theorem 38.2 for `k > 1` (Step 1 needs the ideals),
the computed gaps of Table 38.2.3.1, Theorem 38.6 (Matveev) and Theorem 38.7 for `R` not a
square (Laurent) are not formalized.
-/

namespace Munchausen

open QuadraticAlgebra

/-! ### Section 38.1: the equations -/

/-- `A = w(p) + w(q) - q` of the middle string `(p, x, q)`. -/
def midA (m p q : ℕ) : ℤ := (w m p : ℤ) + w m q - q

/-- `A = w(q) + w(r) - r` of the leading string `(x, q, r)`. -/
def leadA (m q r : ℕ) : ℤ := (w m q : ℤ) + w m r - r

/-- **Section 38.1**, the middle equation: if `(p, x, q)` with `x ≥ 1` is a solution in base `b`,
then `b (p b + x) = x^x + A`. -/
theorem mid_eq {b m p q x : ℕ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0) :
    (b : ℤ) * (p * b + x) = (x : ℤ) ^ x + midA m p q := by
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero m hx] at heq
  have heqZ : ((p * b ^ 2 + x * b + q : ℕ) : ℤ) = ((w m p + (x ^ x + w m q) : ℕ) : ℤ) := by
    rw [← heq]; push_cast; ring
  push_cast at heqZ
  rw [midA]; linear_combination heqZ

/-- **Section 38.1**, the leading equation: if `(x, q, r)` with `x ≥ 1` is a solution in base
`b`, then `b (x b + q) = x^x + A`. -/
theorem lead_eq {b m q r x : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0) :
    (b : ℤ) * (x * b + q) = (x : ℤ) ^ x + leadA m q r := by
  have heq := hs.eq
  simp only [P_cons, P_nil, List.length_cons, List.length_nil, Nat.cast_id, Fs_cons, Fs_nil,
    add_zero, zero_add, pow_zero, pow_one, mul_one] at heq
  rw [w_of_ne_zero m hx] at heq
  have heqZ : ((x * b ^ 2 + q * b + r : ℕ) : ℤ) = ((x ^ x + (w m q + w m r) : ℕ) : ℤ) := by
    rw [← heq]; push_cast; ring
  push_cast at heqZ
  rw [leadA]; linear_combination heqZ

/-- **Section 38.1**, the completed square of the middle position: `U^2 = 4 p x^x + R` with
`U = 2 p b + x` and `R = x^2 + 4 p A`. -/
theorem mid_sq {b m p q x : ℕ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0) :
    ((2 * p * b + x : ℕ) : ℤ) ^ 2 = 4 * p * (x : ℤ) ^ x + ((x : ℤ) ^ 2 + 4 * p * midA m p q) := by
  have := mid_eq hs hx
  push_cast; linear_combination 4 * (p : ℤ) * this

/-- **Section 38.1**, the completed square of the leading position: `U^2 = 4 x^(x+1) + R` with
`U = 2 x b + q` and `R = q^2 + 4 x A`. -/
theorem lead_sq {b m q r x : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0) :
    ((2 * x * b + q : ℕ) : ℤ) ^ 2 =
      4 * (x : ℤ) ^ (x + 1) + ((q : ℤ) ^ 2 + 4 * x * leadA m q r) := by
  have := lead_eq hs hx
  push_cast; linear_combination 4 * (x : ℤ) * this

/-- **Section 38.1**: in the middle position `A ≥ 1`. -/
lemma one_le_midA {m p q : ℕ} (hp : p ≠ 0) : 1 ≤ midA m p q := by
  have h1 : (1 : ℤ) ≤ w m p := by exact_mod_cast one_le_w hp
  have h2 := le_w_int m q
  rw [midA]; linarith

/-- **Section 38.1**: in the leading position `A ≥ 1`, except for the strings `(x, 0, 0)` and
`(x, 0, 1)` under `0^0 = 0`, where `A = 0`. -/
lemma one_le_leadA {m q r : ℕ} (h : ¬ (m = 0 ∧ q = 0 ∧ r ≤ 1)) : 1 ≤ leadA m q r := by
  rw [leadA]
  have hr := le_w_int m r
  by_cases hq : q = 0
  · subst hq
    by_cases hm : m = 0
    · subst hm
      have hr2 : 2 ≤ r := by omega
      have : (r : ℤ) + 1 ≤ w 0 r := by
        rw [w_of_ne_zero 0 (by omega)]
        have : r + 1 ≤ r ^ r := by
          calc r + 1 ≤ r ^ 2 := by nlinarith
            _ ≤ r ^ r := Nat.pow_le_pow_right (by omega) hr2
        exact_mod_cast this
      simp; linarith
    · simp only [w_zero]
      have : (1 : ℤ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
      linarith
  · have : (1 : ℤ) ≤ w m q := by exact_mod_cast one_le_w hq
    linarith

/-- The leading strings `(x, 0, 0)` and `(x, 0, 1)` under `0^0 = 0` have `A = 0`. -/
lemma leadA_eq_zero {r : ℕ} (hr : r ≤ 1) : leadA 0 0 r = 0 := by
  interval_cases r <;> simp [leadA]

/-! ### Section 38.2.1: the ring `Z[θ]` of the middle position -/

/-- The ring `Z[θ]` of section 38.2.1, `θ^2 = k^2 + x θ`: in `Q(sqrt R)`, `R = x^2 + 4 k^2`,
`θ = (x + sqrt R)/2`. The conjugation `'` is `star`, with `θ' = x - θ`. -/
abbrev MidRing (k x : ℤ) := QuadraticAlgebra ℤ (k ^ 2) x

lemma star_omega {a b : ℤ} :
    star (ω : QuadraticAlgebra ℤ a b) = (b : QuadraticAlgebra ℤ a b) - ω := by
  ext <;> simp

lemma norm_omega_add {a b : ℤ} (r : ℤ) :
    QuadraticAlgebra.norm ((ω : QuadraticAlgebra ℤ a b) + (r : QuadraticAlgebra ℤ a b)) =
      r ^ 2 + b * r - a := by
  rw [norm_def]; simp; ring

lemma norm_omega_sub {a b : ℤ} (r : ℤ) :
    QuadraticAlgebra.norm ((ω : QuadraticAlgebra ℤ a b) - (r : QuadraticAlgebra ℤ a b)) =
      r ^ 2 - b * r - a := by
  rw [norm_def]; simp; ring

lemma norm_omega' {a b : ℤ} : QuadraticAlgebra.norm (ω : QuadraticAlgebra ℤ a b) = -a := by
  rw [norm_def]; simp

/-- **Section 38.2.1**: `θ θ' = -k^2`, `N(θ + k) = k x`, `N(θ - k) = -k x`. -/
theorem mid_norms (k x : ℤ) :
    QuadraticAlgebra.norm (ω : MidRing k x) = -k ^ 2 ∧
      QuadraticAlgebra.norm ((ω : MidRing k x) + (k : MidRing k x)) = k * x ∧
      QuadraticAlgebra.norm ((ω : MidRing k x) - (k : MidRing k x)) = -(k * x) := by
  refine ⟨norm_omega', ?_, ?_⟩
  · rw [norm_omega_add]; ring
  · rw [norm_omega_sub]; ring

/-- `δ = 2 θ - x = θ - θ'` is `sqrt R`: `δ^2 = R = x^2 + 4 k^2`. -/
lemma mid_delta_sq (k x : ℤ) :
    (2 * (ω : MidRing k x) - (x : MidRing k x)) ^ 2 = ((x ^ 2 + 4 * k ^ 2 : ℤ) : MidRing k x) := by
  ext <;> simp [pow_two] <;> ring

/-- **Section 38.2.1**: if `(p, x, q)` is a solution with `p A = k^2`, then
`μ = (U + sqrt R)/2 = p b + θ` has norm `p x^x`. -/
theorem mid_norm_mu {b m p q x : ℕ} {k : ℤ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hk : p * midA m p q = k ^ 2) :
    QuadraticAlgebra.norm ((ω : MidRing k x) + ((p * b : ℤ) : MidRing k x)) = p * (x : ℤ) ^ x := by
  rw [norm_omega_add, ← hk]
  linear_combination (p : ℤ) * mid_eq hs hx

/-- If `a - b = δ` with `δ^2 = R`, `a b = N` (both integers), and `R` is prime to `N`, then `a`
and `b` are coprime. -/
lemma isCoprime_of_sub_mul {A : Type*} [CommRing A] {a b δ : A} {R N : ℤ}
    (hδ : a - b = δ) (hR : δ ^ 2 = R) (hN : a * b = N) (h : IsCoprime R N) : IsCoprime a b := by
  obtain ⟨u, v, huv⟩ := h
  refine ⟨u * δ + v * b, -(u * δ), ?_⟩
  have : ((u * R + v * N : ℤ) : A) = 1 := by rw [huv]; simp
  push_cast at this
  rw [← this, ← hR, ← hN, ← hδ]; ring

lemma star_omega_add_omega {a b : ℤ} :
    star (ω : QuadraticAlgebra ℤ a b) + ω = (b : QuadraticAlgebra ℤ a b) := by
  rw [star_omega]; ring

lemma omega_mul_star_omega {a b : ℤ} :
    (ω : QuadraticAlgebra ℤ a b) * star ω = ((-a : ℤ) : QuadraticAlgebra ℤ a b) := by
  ext <;> simp

/-- **Lemma 38.1** (b), the elementary step: if `x` is prime to `k`, `θ` and `θ'` are coprime,
since `θ + θ' = x` and `θ θ' = -k^2`. So a prime above `l ∣ k` divides at most one of them. -/
theorem lemma38_1_b {k x : ℤ} (h : IsCoprime x k) : IsCoprime (ω : MidRing k x) (star ω) := by
  obtain ⟨u, v, huv⟩ := h.pow_right (n := 2)
  refine ⟨(u : MidRing k x) - (v : MidRing k x) * star ω, (u : MidRing k x), ?_⟩
  have h1 := star_omega_add_omega (a := k ^ 2) (b := x)
  have h2 := omega_mul_star_omega (a := k ^ 2) (b := x)
  have : ((u * x + v * k ^ 2 : ℤ) : MidRing k x) = 1 := by rw [huv]; simp
  push_cast at this h2
  linear_combination (u : MidRing k x) * h1 - (v : MidRing k x) * h2 + this

/-- **Lemma 38.1** (c), the elementary step: if `R = x^2 + 4 k^2` is prime to `k x`, then
`θ + k` and `θ' + k` are coprime (they differ by `sqrt R`, and their product is `k x`). -/
theorem lemma38_1_c {k x : ℤ} (h : IsCoprime (x ^ 2 + 4 * k ^ 2) (k * x)) :
    IsCoprime ((ω : MidRing k x) + (k : MidRing k x)) (star ω + (k : MidRing k x)) := by
  refine isCoprime_of_sub_mul (δ := 2 * ω - (x : MidRing k x)) ?_ (mid_delta_sq k x) ?_ h
  · rw [star_omega]; ring
  · have h2 := omega_mul_star_omega (a := k ^ 2) (b := x)
    rw [star_omega] at h2 ⊢
    push_cast at h2 ⊢
    linear_combination h2

/-- **Lemma 38.1** (a), the coprimality behind it: for `x` odd and prime to `k`, `R = x^2 + 4 k^2`
is prime to `k` and to `x`. -/
theorem lemma38_1_coprime {k x : ℤ} (hx : Odd x) (h : IsCoprime x k) :
    IsCoprime (x ^ 2 + 4 * k ^ 2) k ∧ IsCoprime (x ^ 2 + 4 * k ^ 2) x := by
  constructor
  · have : IsCoprime (x ^ 2) k := h.pow_left
    have := this.add_mul_left_left (4 * k)
    convert this using 1; ring
  · have h2 : IsCoprime (2 : ℤ) x := by
      obtain ⟨c, rfl⟩ := hx
      exact ⟨-c, 1, by ring⟩
    have : IsCoprime (4 * k ^ 2) x := by
      have h4 : IsCoprime (4 : ℤ) x := by
        have := h2.pow_left (m := 2); norm_num at this; exact this
      exact h4.mul_left (h.symm.pow_left)
    have := this.add_mul_left_left x
    convert this using 1; ring

/-- **Lemma 38.1** (a), the residues of `R = x^2 + 4 k^2`: modulo a prime `l ∣ k` it is `x^2`,
and modulo a prime `l ∣ x` it is `(2 k)^2`. Both are nonzero squares when `l` is odd and does
not divide the other number, so `l` splits in `K`. -/
theorem lemma38_1_a {k x : ℤ} {l : ℕ} :
    ((l : ℤ) ∣ k → ((x ^ 2 + 4 * k ^ 2 : ℤ) : ZMod l) = (x : ZMod l) ^ 2) ∧
      ((l : ℤ) ∣ x → ((x ^ 2 + 4 * k ^ 2 : ℤ) : ZMod l) = (2 * k : ZMod l) ^ 2) := by
  constructor
  · intro h
    have : (k : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
    push_cast; rw [this]; ring
  · intro h
    have : (x : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
    push_cast; rw [this]; ring

/-- **Lemma 38.1** (a), for `l = 2 ∣ k`: `R ≡ x^2 ≡ 1 (mod 8)` when `x` is odd, so 2 splits. -/
theorem lemma38_1_a_two {k x : ℤ} (hk : 2 ∣ k) (hx : Odd x) : (x ^ 2 + 4 * k ^ 2) % 8 = 1 := by
  obtain ⟨c, rfl⟩ := hk
  obtain ⟨d, rfl⟩ := hx
  have : (2 * d + 1) ^ 2 + 4 * (2 * c) ^ 2 = 8 * (2 * c ^ 2 + d * (d + 1) / 2) + 1 := by
    have h2 : 2 ∣ d * (d + 1) := even_iff_two_dvd.1 (Int.even_mul_succ_self d)
    have := Int.ediv_mul_cancel h2
    nlinarith [this]
  rw [this]; omega

/-- Evaluation of `Z[ω]`, `ω^2 = a + b ω`, modulo `M` at an integer `r` with
`r^2 ≡ a + b r (mod M)`. When `R = b^2 + 4a` is prime to `M`, the two roots `r` and `b - r`
give `Z[ω] / (M) ≅ (Z/M)^2`; this replaces the primes above the divisors of `M`. -/
def evalMod {a b : ℤ} (M : ℕ) (r : ℤ) (h : (M : ℤ) ∣ r ^ 2 - b * r - a) :
    QuadraticAlgebra ℤ a b →ₐ[ℤ] ZMod M :=
  QuadraticAlgebra.lift ⟨(r : ZMod M), by
    have : ((r ^ 2 - b * r - a : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
    push_cast at this
    simp only [zsmul_eq_mul, mul_one]; linear_combination this⟩

lemma evalMod_apply {a b : ℤ} {M : ℕ} {r : ℤ} (h : (M : ℤ) ∣ r ^ 2 - b * r - a)
    (z : QuadraticAlgebra ℤ a b) : evalMod M r h z = ((z.re + z.im * r : ℤ) : ZMod M) := by
  simp [evalMod, zsmul_eq_mul]

lemma evalMod_omega {a b : ℤ} {M : ℕ} {r : ℤ} (h : (M : ℤ) ∣ r ^ 2 - b * r - a) :
    evalMod M r h (ω : QuadraticAlgebra ℤ a b) = r := by
  simp [evalMod_apply]

/-- If `z` vanishes at two roots `r, s` modulo `M` with `r - s` prime to `M`, then `M ∣ z` in
`Z[ω]`. -/
lemma dvd_of_evalMod {a b : ℤ} {M : ℕ} {r s : ℤ} (hr : (M : ℤ) ∣ r ^ 2 - b * r - a)
    (hs : (M : ℤ) ∣ s ^ 2 - b * s - a) (hrs : IsCoprime (r - s) M) {z : QuadraticAlgebra ℤ a b}
    (h1 : evalMod M r hr z = 0) (h2 : evalMod M s hs z = 0) :
    ((M : ℤ) : QuadraticAlgebra ℤ a b) ∣ z := by
  rw [evalMod_apply, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
  have him : (M : ℤ) ∣ z.im := by
    have : (M : ℤ) ∣ z.im * (r - s) := by
      have := dvd_sub h1 h2; convert this using 1; ring
    exact hrs.symm.dvd_of_dvd_mul_right this
  have hre : (M : ℤ) ∣ z.re := by
    have := dvd_sub h1 (dvd_mul_of_dvd_left him r); simpa using this
  obtain ⟨c1, hc1⟩ := hre
  obtain ⟨c2, hc2⟩ := him
  exact ⟨⟨c1, c2⟩, by ext <;> simp [hc1, hc2]⟩

/-- **Lemma 38.1** (d), in elementary form. Let `(p, x, q)` be a solution with `p A = k^2`, `x` a
prime power `l^c` prime to `R = x^2 + 4 k^2` (true for `x` odd and prime to `k`), and
`μ = p b + θ`. Then `x^x` divides `μ (θ + k)^x` or `μ (θ' + k)^x` in `Z[θ]`: the ideal `B` of
norm `x` in `(μ)` is `P'` or `P`, where `(θ + k) = K_k P`. The proof evaluates at the two roots
`r = -p b` and `s = x + p b` of `T^2 - x T - k^2` modulo `x^x`: `μ` vanishes at `r`, and
`(r + k)(s + k) = x (k - p x^(x-1))` with `s - r = U` prime to `l`, so `x` divides `r + k` or
`s + k`. -/
theorem lemma38_1_d {b m p q x l c : ℕ} {k : ℤ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hk : p * midA m p q = k ^ 2) (hl : l.Prime) (hxl : x = l ^ c)
    (hR : IsCoprime ((x : ℤ) ^ 2 + 4 * k ^ 2) (x : ℤ)) :
    (((x ^ x : ℕ) : ℤ) : MidRing k x) ∣
        ((ω : MidRing k x) + ((p * b : ℤ) : MidRing k x)) *
          ((ω : MidRing k x) + (k : MidRing k x)) ^ x ∨
      (((x ^ x : ℕ) : ℤ) : MidRing k x) ∣
        ((ω : MidRing k x) + ((p * b : ℤ) : MidRing k x)) * (star ω + (k : MidRing k x)) ^ x := by
  have heq := mid_eq hs hx
  set U : ℤ := 2 * p * b + x with hU
  have hUsq : U ^ 2 = ((x : ℤ) ^ 2 + 4 * k ^ 2) + x * (4 * p * x ^ (x - 1)) := by
    have : (x : ℤ) ^ x = x * x ^ (x - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hU, ← hk]; linear_combination (4 * (p : ℤ)) * heq + 4 * (p : ℤ) * this
  have hUx : IsCoprime U x := by
    have : IsCoprime (U ^ 2) x := by rw [hUsq]; exact hR.add_mul_left_left _
    exact (IsCoprime.pow_left_iff (by norm_num)).1 this
  set r : ℤ := -(p * b) with hr
  set s : ℤ := x + p * b with hs'
  have hroot : r ^ 2 - x * r - k ^ 2 = p * (x : ℤ) ^ x := by
    rw [hr, ← hk]; linear_combination (p : ℤ) * heq
  have hroot' : s ^ 2 - x * s - k ^ 2 = p * (x : ℤ) ^ x := by
    rw [hs', ← hk]; linear_combination (p : ℤ) * heq
  have hM : ((x ^ x : ℕ) : ℤ) = (x : ℤ) ^ x := by push_cast; rfl
  have hdr : ((x ^ x : ℕ) : ℤ) ∣ r ^ 2 - x * r - k ^ 2 := by
    rw [hroot, hM]; exact dvd_mul_left _ _
  have hds : ((x ^ x : ℕ) : ℤ) ∣ s ^ 2 - x * s - k ^ 2 := by
    rw [hroot', hM]; exact dvd_mul_left _ _
  have hrs : IsCoprime (r - s) ((x ^ x : ℕ) : ℤ) := by
    rw [hM, show r - s = -U by rw [hr, hs', hU]; ring]
    exact (hUx.pow_right).neg_left
  -- `x` divides `r + k` or `s + k`
  have hprod : (r + k) * (s + k) = x * (k - p * x ^ (x - 1)) := by
    have : (x : ℤ) ^ x = x * x ^ (x - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hr, hs']; linear_combination (-(p : ℤ)) * heq - hk - (p : ℤ) * this
  have hdiv : (x : ℤ) ∣ r + k ∨ (x : ℤ) ∣ s + k := by
    rcases Nat.eq_zero_or_pos c with hc | hc
    · left; rw [hxl, hc]; simp
    have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    have hlx : (l : ℤ) ∣ x := by rw [hxl]; push_cast; exact dvd_pow_self _ hc.ne'
    have hxlZ : (x : ℤ) = (l : ℤ) ^ c := by rw [hxl]; push_cast; rfl
    by_cases h1 : (l : ℤ) ∣ r + k
    · left
      have h2 : ¬ (l : ℤ) ∣ s + k := by
        intro h2
        have : (l : ℤ) ∣ U := by
          have := dvd_sub h2 h1; convert this using 1; rw [hr, hs', hU]; ring
        have hu := hUx.of_isCoprime_of_dvd_right hlx
        exact hlZ.not_isUnit (hu.isUnit_of_dvd' this (dvd_refl _))
      have hc' : IsCoprime ((l : ℤ) ^ c) (s + k) := ((hlZ.coprime_iff_not_dvd).2 h2).pow_left
      rw [hxlZ] at hprod ⊢
      exact hc'.dvd_of_dvd_mul_right ⟨_, hprod⟩
    · right
      have hc' : IsCoprime ((l : ℤ) ^ c) (r + k) := ((hlZ.coprime_iff_not_dvd).2 h1).pow_left
      rw [hxlZ] at hprod ⊢
      exact hc'.dvd_of_dvd_mul_left ⟨_, hprod⟩
  have hzero : ∀ t : ℤ, (x : ℤ) ∣ t → ((t ^ x : ℤ) : ZMod (x ^ x)) = 0 := by
    intro t ht
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hM]
    exact pow_dvd_pow_of_dvd ht x
  have hμr : evalMod (x ^ x) r hdr ((ω : MidRing k x) + ((p * b : ℤ) : MidRing k x)) = 0 := by
    rw [map_add, evalMod_omega, map_intCast, hr]; push_cast; ring
  rcases hdiv with h | h
  · right
    refine dvd_of_evalMod hdr hds hrs (by rw [map_mul, hμr, zero_mul]) ?_
    have e1 : evalMod (x ^ x) s hds (star ω + (k : MidRing k x)) =
        ((r : ℤ) : ZMod (x ^ x)) + ((k : ℤ) : ZMod (x ^ x)) := by
      rw [star_omega]; simp only [map_add, map_sub, map_intCast, evalMod_omega]
      rw [hs', hr]; push_cast; ring
    rw [map_mul, map_pow, e1]
    have := hzero _ h; push_cast at this; rw [this, mul_zero]
  · left
    refine dvd_of_evalMod hdr hds hrs (by rw [map_mul, hμr, zero_mul]) ?_
    have e1 : evalMod (x ^ x) s hds ((ω : MidRing k x) + (k : MidRing k x)) =
        ((s : ℤ) : ZMod (x ^ x)) + ((k : ℤ) : ZMod (x ^ x)) := by
      simp only [map_add, map_intCast, evalMod_omega]
    rw [map_mul, map_pow, e1]
    have := hzero _ h; push_cast at this; rw [this, mul_zero]

/-- **Lemma 38.1** (d), the coprimality of `μ` and `μ'`: they differ by `sqrt R`, and
`μ μ' = p x^x`; so they are coprime when `R` is prime to `p x`. -/
theorem lemma38_1_d_coprime {b m p q x : ℕ} {k : ℤ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hk : p * midA m p q = k ^ 2) (hR : IsCoprime ((x : ℤ) ^ 2 + 4 * k ^ 2) ((p : ℤ) * x)) :
    IsCoprime ((ω : MidRing k x) + ((p * b : ℤ) : MidRing k x))
      (star ((ω : MidRing k x) + ((p * b : ℤ) : MidRing k x))) := by
  refine isCoprime_of_sub_mul (δ := 2 * ω - (x : MidRing k x)) ?_ (mid_delta_sq k x)
    (N := p * (x : ℤ) ^ x) ?_ ?_
  · rw [star_add, star_omega]; simp; ring
  · rw [← algebraMap_norm_eq_mul_star, mid_norm_mu hs hx hk]; simp
  · exact (hR.of_isCoprime_of_dvd_right (dvd_mul_right _ _)).mul_right
      (hR.of_isCoprime_of_dvd_right (dvd_mul_left _ _)).pow_right

/-! ### The real embeddings -/

/-- The real root `(b + sqrt(b^2 + 4 a))/2` of `T^2 - b T - a`. -/
noncomputable def rootR (a b : ℤ) : ℝ := (b + Real.sqrt (b ^ 2 + 4 * a)) / 2

/-- The other root `(b - sqrt(b^2 + 4 a))/2`. -/
noncomputable def rootR' (a b : ℤ) : ℝ := (b - Real.sqrt (b ^ 2 + 4 * a)) / 2

lemma rootR_add (a b : ℤ) : rootR a b + rootR' a b = b := by
  rw [rootR, rootR']; ring

lemma rootR_mul {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) : rootR a b * rootR' a b = -a := by
  rw [rootR, rootR']
  have := Real.sq_sqrt h
  linear_combination (-1 / 4 : ℝ) * this

lemma rootR_sq {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) :
    rootR a b * rootR a b = a + b * rootR a b := by
  have h1 := rootR_add a b
  have h2 := rootR_mul h
  linear_combination (rootR a b) * h1 - h2

lemma rootR'_sq {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) :
    rootR' a b * rootR' a b = a + b * rootR' a b := by
  have h1 := rootR_add a b
  have h2 := rootR_mul h
  linear_combination (rootR' a b) * h1 - h2

/-- The real embedding `ω ↦ (b + sqrt(b^2 + 4a))/2` of `Z[ω]`. -/
noncomputable def embR (a b : ℤ) (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) :
    QuadraticAlgebra ℤ a b →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨rootR a b, by simp only [zsmul_eq_mul, mul_one]; exact rootR_sq h⟩

/-- The conjugate embedding `ω ↦ (b - sqrt(b^2 + 4a))/2`. -/
noncomputable def embR' (a b : ℤ) (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) :
    QuadraticAlgebra ℤ a b →ₐ[ℤ] ℝ :=
  QuadraticAlgebra.lift ⟨rootR' a b, by simp only [zsmul_eq_mul, mul_one]; exact rootR'_sq h⟩

lemma embR_apply {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) (z : QuadraticAlgebra ℤ a b) :
    embR a b h z = z.re + z.im * rootR a b := by
  simp [embR, zsmul_eq_mul]

lemma embR'_apply {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) (z : QuadraticAlgebra ℤ a b) :
    embR' a b h z = z.re + z.im * rootR' a b := by
  simp [embR', zsmul_eq_mul]

lemma embR'_star {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) (z : QuadraticAlgebra ℤ a b) :
    embR' a b h (star z) = embR a b h z := by
  rw [embR'_apply, embR_apply]
  have := rootR_add a b
  simp only [re_star, im_star]; push_cast
  linear_combination (-(z.im : ℝ)) * this

lemma embR_mul_embR' {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) (z : QuadraticAlgebra ℤ a b) :
    embR a b h z * embR' a b h z = ((QuadraticAlgebra.norm z : ℤ) : ℝ) := by
  rw [embR_apply, embR'_apply, norm_def]
  have h1 := rootR_add a b
  have h2 := rootR_mul h
  push_cast
  linear_combination (z.re * z.im : ℝ) * h1 + (z.im : ℝ) ^ 2 * h2

lemma embR_add_embR' {a b : ℤ} (h : (0 : ℝ) ≤ b ^ 2 + 4 * a) (z : QuadraticAlgebra ℤ a b) :
    embR a b h z + embR' a b h z = ((QuadraticAlgebra.trace z : ℤ) : ℝ) := by
  rw [embR_apply, embR'_apply, trace_def]
  have h1 := rootR_add a b
  push_cast
  linear_combination (z.im : ℝ) * h1

/-! ### Theorem 38.2: the real steps -/

/-- The series bounds `2 y ≤ log((1 + y)/(1 - y)) ≤ 2 y / (1 - y^2)` for `0 ≤ y < 1`
(`log z = 2 artanh y` in Step 3 of Theorem 38.2). -/
lemma log_one_add_div_one_sub_bounds {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1) :
    2 * y ≤ Real.log ((1 + y) / (1 - y)) ∧ Real.log ((1 + y) / (1 - y)) ≤ 2 * y / (1 - y ^ 2) := by
  have habs : |y| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  rw [← Real.log_div (by linarith) (by linarith)] at hs
  constructor
  · have := le_hasSum hs 0 (fun j _ => by positivity)
    simpa using this
  · have hy2 : y ^ 2 < 1 := by nlinarith
    have hg := (hasSum_geometric_of_lt_one (sq_nonneg y) hy2).mul_left (2 * y)
    have hle := hasSum_le (fun j => ?_) hs hg
    · rw [div_eq_mul_inv]; exact hle
    · rw [pow_succ, pow_mul]
      have hj : (1 : ℝ) / (2 * j + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith
      have : 0 ≤ (y ^ 2) ^ j * y := by positivity
      nlinarith

/-- **Theorem 38.2**, Step 3, the bounds on `x log z`. Let `x, k > 0`,
`θ = (x + sqrt(x^2 + 4 k^2))/2` and `z = (θ + k)/(θ - k)`. Then `θ > k`, `z > 1` and
`2k (1 - k^2/x^2) ≤ x log z ≤ 2k`. -/
theorem theorem38_2_step3 {x k : ℝ} (hx : 0 < x) (hk : 0 < k) :
    let θ := (x + Real.sqrt (x ^ 2 + 4 * k ^ 2)) / 2
    k < θ ∧ 2 * k * (1 - k ^ 2 / x ^ 2) ≤ x * Real.log ((θ + k) / (θ - k)) ∧
      x * Real.log ((θ + k) / (θ - k)) ≤ 2 * k := by
  intro θ
  set S := Real.sqrt (x ^ 2 + 4 * k ^ 2) with hS
  have hS2 : S ^ 2 = x ^ 2 + 4 * k ^ 2 := Real.sq_sqrt (by positivity)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSk : 2 * k < S := by nlinarith
  have hθk : k < θ := by simp only [θ]; linarith
  have hθ0 : 0 < θ := by linarith
  have hθsq : θ ^ 2 = x * θ + k ^ 2 := by simp only [θ]; nlinarith
  have hSup : S ≤ x + 2 * k ^ 2 / x := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (x + 2 * k ^ 2 / x) ^ 2 = x ^ 2 + 4 * k ^ 2 + (2 * k ^ 2 / x) ^ 2 := by
      field_simp; ring
    rw [this]; nlinarith [sq_nonneg (2 * k ^ 2 / x)]
  set y := k / θ with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one hθ0]; exact hθk
  have hz : (θ + k) / (θ - k) = (1 + y) / (1 - y) := by
    rw [hy]; field_simp
  obtain ⟨hlo, hhi⟩ := log_one_add_div_one_sub_bounds hy0 hy1
  rw [hz]
  have hy2 : 2 * y / (1 - y ^ 2) = 2 * k / x := by
    have h1y : 1 - y ^ 2 = x / θ := by
      rw [hy, div_pow]; field_simp; linarith [hθsq]
    rw [h1y, hy]; field_simp
  refine ⟨hθk, ?_, ?_⟩
  · have hθup : θ ≤ x + k ^ 2 / x := by
      simp only [θ]
      have : 2 * k ^ 2 / x = 2 * (k ^ 2 / x) := by ring
      linarith
    have h1 : 2 * k * x / (x + k ^ 2 / x) ≤ 2 * x * y := by
      rw [hy, div_le_iff₀ (by positivity)]
      rw [show 2 * x * (k / θ) * (x + k ^ 2 / x) = 2 * k * x * ((x + k ^ 2 / x) / θ) by
        field_simp]
      have : 1 ≤ (x + k ^ 2 / x) / θ := by rw [le_div_iff₀ hθ0]; linarith
      nlinarith [mul_pos (mul_pos two_pos hk) hx]
    have h2 : 2 * k * (1 - k ^ 2 / x ^ 2) ≤ 2 * k * x / (x + k ^ 2 / x) := by
      rw [le_div_iff₀ (by positivity)]
      have : 2 * k * (1 - k ^ 2 / x ^ 2) * (x + k ^ 2 / x) = 2 * k * x - 2 * k * k ^ 4 / x ^ 3 := by
        field_simp; ring
      rw [this]
      have : 0 ≤ 2 * k * k ^ 4 / x ^ 3 := by positivity
      linarith
    nlinarith
  · calc x * Real.log ((1 + y) / (1 - y)) ≤ x * (2 * y / (1 - y ^ 2)) :=
          mul_le_mul_of_nonneg_left hhi hx.le
      _ = 2 * k := by rw [hy2]; field_simp

/-- The function `f` of **Theorem 38.2**: `f(t) = 2 c sinh t` for odd `e`, `2 c cosh t` for even
`e` (with `c = k^a`). -/
noncomputable def gapF (c : ℝ) (e : ℕ) (t : ℝ) : ℝ :=
  if Even e then 2 * c * Real.cosh t else 2 * c * Real.sinh t

lemma gapF_strictMonoOn {c : ℝ} (hc : 0 < c) (e : ℕ) : StrictMonoOn (gapF c e) (Set.Ici 0) := by
  intro s hs t ht hst
  unfold gapF
  split_ifs
  · have := Real.cosh_strictMonoOn hs ht hst; nlinarith
  · have := Real.sinh_strictMono hst; nlinarith

/-- **Theorem 38.2**, Steps 2 and 3, the trace. Let `w > 0` with `w w' = (-1)^e`, and
`w = exp(-s τ)` with `s = ±1` and `τ ≥ 0`. Then `|c (w + w')| = f(τ)`. -/
theorem theorem38_2_trace {c w w' τ : ℝ} {e : ℕ} (hc : 0 ≤ c) (hτ : 0 ≤ τ)
    (hw : w = Real.exp τ ∨ w = Real.exp (-τ)) (hww : w * w' = (-1) ^ e) :
    |c * (w + w')| = gapF c e τ := by
  have hw0 : w ≠ 0 := by rcases hw with rfl | rfl <;> exact (Real.exp_pos _).ne'
  have hw' : w' = (-1) ^ e / w := by field_simp; linarith
  have hexp : Real.exp τ * Real.exp (-τ) = 1 := by rw [← Real.exp_add]; simp
  unfold gapF
  rcases Nat.even_or_odd e with he | he
  · simp only [he, ↓reduceIte]; rw [hw', he.neg_one_pow]
    have : c * (w + 1 / w) = 2 * c * Real.cosh τ := by
      rw [Real.cosh_eq]
      rcases hw with rfl | rfl
      · field_simp; linear_combination (-c) * hexp
      · field_simp; linear_combination (-c) * hexp
    rw [this, abs_of_nonneg (by have := Real.cosh_pos τ; positivity)]
  · simp only [Nat.not_even_iff_odd.2 he, ↓reduceIte]; rw [hw', he.neg_one_pow]
    have hsh : 0 ≤ Real.sinh τ := Real.sinh_nonneg_iff.2 hτ
    rcases hw with rfl | rfl
    · have : c * (Real.exp τ + -1 / Real.exp τ) = 2 * c * Real.sinh τ := by
        rw [Real.sinh_eq]; field_simp; linear_combination c * hexp
      rw [this, abs_of_nonneg (by positivity)]
    · have : c * (Real.exp (-τ) + -1 / Real.exp (-τ)) = -(2 * c * Real.sinh τ) := by
        rw [Real.sinh_eq]; field_simp; linear_combination c * hexp
      rw [this, abs_neg, abs_of_nonneg (by positivity)]

/-- **Theorem 38.2**, Step 4. Let `T` be an integer with `|T| = f(τ)`, where
`2ke - 2ek^3/x^2 - e Λ0 ≤ τ ≤ 2ke + e Λ0`, and let `N0` be an integer with
`f(2ke - g-) = N0` and `f(2ke + g+) = N0 + 1` (so `N0 = floor(f(2ke))` and `g-, g+` are the
gaps). If `e Λ0 < g+`, then `x^2 (g- - e Λ0) ≤ 2 e k^3`. Here `K = 2ke` and `δ = e Λ0`. -/
theorem theorem38_2_step4 {c x k K δ τ gm gp : ℝ} {e : ℕ} {T N0 : ℤ} (hc : 0 < c) (hx : 0 < x)
    (hT : |(T : ℝ)| = gapF c e τ) (hτ : 0 ≤ τ)
    (hlo : K - 2 * e * k ^ 3 / x ^ 2 - δ ≤ τ) (hhi : τ ≤ K + δ)
    (hgm0 : 0 ≤ K - gm) (hgm : gapF c e (K - gm) = N0) (hgp : gapF c e (K + gp) = N0 + 1)
    (hδ : δ < gp) :
    x ^ 2 * (gm - δ) ≤ 2 * e * k ^ 3 := by
  have hmono := gapF_strictMonoOn hc e
  have h1 : gapF c e τ < N0 + 1 := by
    rw [← hgp]
    exact hmono hτ (Set.mem_Ici.2 (by linarith)) (by linarith)
  have h2 : |T| ≤ N0 := by
    have : (|T| : ℝ) < N0 + 1 := by rw [hT]; exact h1
    exact_mod_cast Int.lt_add_one_iff.1 (by exact_mod_cast this)
  have h3 : τ ≤ K - gm := by
    by_contra hlt
    push Not at hlt
    have := hmono hgm0 hτ hlt
    rw [hgm, ← hT] at this
    have : (N0 : ℝ) < |T| := by exact_mod_cast this
    have : N0 < |T| := by exact_mod_cast this
    omega
  have : gm - δ ≤ 2 * e * k ^ 3 / x ^ 2 := by linarith
  rw [le_div_iff₀ (by positivity)] at this
  linarith

/-- Hermite's theorem (1873): `e` is transcendental. Cited in the positivity step of
**Theorem 38.2** (`f(2ke)` is not an integer); used only as a hypothesis. -/
def HermiteTheorem : Prop := Transcendental ℤ (Real.exp 1)

/-- **Theorem 38.2**, positivity: under Hermite's theorem, `f(n) = 2 c sinh n` or `2 c cosh n`
is not an integer for an integer `c ≥ 1` and `n ≥ 1`, since `E = e^n` would be a root of
`c E^2 - N E ∓ c`. -/
theorem theorem38_2_not_int (hH : HermiteTheorem) {c n : ℕ} (hc : 0 < c) (hn : 0 < n) (e : ℕ)
    (N : ℤ) : gapF c e n ≠ N := by
  intro hN
  have hT : Transcendental ℤ (Real.exp n) := by
    have := hH.pow hn; rwa [← Real.exp_nat_mul, mul_one] at this
  apply hT
  set E := Real.exp n with hE
  have hE0 : E ≠ 0 := (Real.exp_pos _).ne'
  have hEinv : Real.exp (-(n : ℝ)) = E⁻¹ := by rw [Real.exp_neg]
  set σ : ℤ := if Even e then 1 else -1 with hσ
  have hroot : (c : ℝ) * E ^ 2 - N * E + σ * c = 0 := by
    unfold gapF at hN
    split_ifs at hN with he
    · have : σ = 1 := by simp only [hσ, he, ↓reduceIte]
      rw [this, ← hN, Real.cosh_eq, hEinv]; field_simp; push_cast; ring
    · have : σ = -1 := by simp only [hσ, he, ↓reduceIte]
      rw [this, ← hN, Real.sinh_eq, hEinv]; field_simp; push_cast; ring
  refine ⟨Polynomial.C (c : ℤ) * Polynomial.X ^ 2 - Polynomial.C N * Polynomial.X +
    Polynomial.C (σ * c), ?_, ?_⟩
  · intro h0
    have := congrArg (fun p => Polynomial.coeff p 2) h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_zero] at this
    norm_num at this
    omega
  · simp only [map_add, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow,
      algebraMap_int_eq, Int.coe_castRingHom]
    push_cast
    linear_combination hroot

/-- **Theorem 38.2**, positivity of the gap: under Hermite's theorem, if
`f(2ke - g-) = floor(f(2ke))` with `g- ≥ 0`, then `g- > 0`. -/
theorem theorem38_2_gap_pos (hH : HermiteTheorem) {c n : ℕ} (hc : 0 < c) (hn : 0 < n) {e : ℕ}
    {gm : ℝ} {N0 : ℤ} (hgm0 : 0 ≤ gm) (hgm : gapF c e (n - gm) = N0) : 0 < gm := by
  rcases hgm0.lt_or_eq with h | h
  · exact h
  · exfalso; rw [← h, sub_zero] at hgm; exact theorem38_2_not_int hH hc hn e N0 hgm

/-! ### Corollary 38.3 (a): the family `b (b + x) = x^x + 1` -/

lemma exp_two_bounds : 7.389 < Real.exp 2 ∧ Real.exp 2 < 7.3891 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  constructor <;> nlinarith

/-- If `w > 0` and `w` or `1/w` lies in `[7.19, 7.4]`, then `w - 1/w` is not an integer: its
absolute value lies strictly between 7 and 8. -/
lemma sub_inv_ne_int {w : ℝ} (hw : 0 < w)
    (h : (7.19 ≤ w ∧ w ≤ 7.4) ∨ (7.19 ≤ w⁻¹ ∧ w⁻¹ ≤ 7.4)) (T : ℤ) : (T : ℝ) ≠ w - w⁻¹ := by
  intro hT
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hi : w⁻¹ ≤ 1 / 7.19 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h1
    have hi0 : 0 < w⁻¹ := inv_pos.2 hw
    have hlo : (7 : ℝ) < T := by rw [hT]; norm_num at hi ⊢; linarith
    have hhi : (T : ℝ) < 8 := by rw [hT]; linarith
    have : (7 : ℤ) < T := by exact_mod_cast hlo
    have : T < (8 : ℤ) := by exact_mod_cast hhi
    omega
  · have hw' : w ≤ 1 / 7.19 := by
      rw [← inv_inv w, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h1
    have hlo : (T : ℝ) < -7 := by rw [hT]; norm_num at hw' ⊢; linarith
    have hhi : (-8 : ℝ) < T := by rw [hT]; linarith
    have : T < (-7 : ℤ) := by exact_mod_cast hlo
    have : (-8 : ℤ) < T := by exact_mod_cast hhi
    omega

/-- Step 3 of **Theorem 38.2** for `k = 1` and `x ≥ 9`, numerically: with
`t = (x + sqrt(x^2 + 4))/2`, `z = (t + 1)/(t - 1)` has `7.2 ≤ z^x ≤ 7.3891` (between
`e^(2 - 2/81)` and `e^2`). -/
lemma k1_pow_bounds {x : ℕ} (hx : 9 ≤ x) :
    let t := ((x : ℝ) + Real.sqrt ((x : ℝ) ^ 2 + 4 * 1 ^ 2)) / 2
    1 < t ∧ 7.2 ≤ ((t + 1) / (t - 1)) ^ x ∧ ((t + 1) / (t - 1)) ^ x ≤ 7.3891 := by
  intro t
  have hx0 : (0 : ℝ) < x := by positivity
  have hx9 : (9 : ℝ) ≤ x := by exact_mod_cast hx
  obtain ⟨ht1', hlo, hhi⟩ := theorem38_2_step3 hx0 one_pos
  have ht1 : 1 < t := ht1'
  set z := (t + 1) / (t - 1) with hz
  have hz0 : 0 < z := div_pos (by linarith) (by linarith)
  refine ⟨ht1, ?_, ?_⟩
  · rw [← Real.exp_log hz0, ← Real.exp_nat_mul]
    have h1 : 2 - 2 / 81 ≤ (x : ℝ) * Real.log z := by
      have : 1 / (x : ℝ) ^ 2 ≤ 1 / 81 := by
        apply one_div_le_one_div_of_le (by norm_num); nlinarith
      have : 2 * 1 * (1 - 1 ^ 2 / (x : ℝ) ^ 2) = 2 - 2 * (1 / (x : ℝ) ^ 2) := by ring
      linarith
    calc (7.2 : ℝ) ≤ Real.exp 2 * (1 - 2 / 81) := by nlinarith [exp_two_bounds.1]
      _ ≤ Real.exp 2 * Real.exp (-(2 / 81)) := by
          gcongr; linarith [Real.add_one_le_exp (-(2 / 81 : ℝ))]
      _ = Real.exp (2 - 2 / 81) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (x * Real.log z) := Real.exp_le_exp.2 h1
  · rw [← Real.exp_log hz0, ← Real.exp_nat_mul]
    calc Real.exp (x * Real.log z) ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)
      _ ≤ 7.3891 := exp_two_bounds.2.le

/-- `x^x ≥ 1001000 (x + 1)^2` for `x ≥ 9`. -/
lemma pow_self_ge_k1 {x : ℕ} (hx : 9 ≤ x) : 1001000 * (x + 1) ^ 2 ≤ x ^ x := by
  have h7 : 9 ^ 7 ≤ x ^ 7 := Nat.pow_le_pow_left hx 7
  have h9 : x ^ 9 ≤ x ^ x := Nat.pow_le_pow_right (by omega) hx
  have : x ^ 9 = x ^ 7 * x ^ 2 := by ring
  nlinarith

/-- The odd `x ≤ 8` in `b (b + x) = x^x + 1` with `x < b`: only `x = 3` (`b = 4`) and `x = 7`
(`b = 904`); `x = 1` gives `b = 1`, and `b (b + 5) = 3126` has no root. -/
lemma mid11_small {b x : ℕ} (hxb : x < b) (hxo : Odd x) (hx8 : x ≤ 8)
    (heqN : b * (b + x) = x ^ x + 1) : (x = 3 ∧ b = 4) ∨ (x = 7 ∧ b = 904) := by
  obtain ⟨i, rfl⟩ := hxo
  have hi : i ≤ 3 := by omega
  interval_cases i
  · norm_num at heqN; nlinarith
  · norm_num at heqN
    left; refine ⟨rfl, ?_⟩
    rcases lt_trichotomy b 4 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  · norm_num at heqN
    exfalso
    rcases le_or_gt b 53 with h | h
    · nlinarith
    · nlinarith
  · norm_num at heqN
    right; refine ⟨rfl, ?_⟩
    rcases lt_trichotomy b 904 with h | h | h
    · nlinarith
    · exact h
    · nlinarith

/-- **Corollary 38.3** (a). Under either convention, `(1, x, 1)` and (under `0^0 = 0`)
`(1, x, 0)` with `x` an odd prime power are solutions only for `x = 3` (base 4) and `x = 7`
(base 904). This is Theorem 38.2 for `k = 1`, `e = 1`, `a = 0`, with the unit built in `Z[θ]`:
by `lemma38_1_d`, `μ (θ + 1)^x = x^x γ` or `μ (θ' + 1)^x = x^x γ`, with `N(γ) = 1`; then
`W = (-θ')^x γ^2` or `W = θ^x γ^2` has norm `-1`, and its real value is `z^x μ/μ'` or
`μ'/(z^x μ)` with `z = (θ + 1)/(θ - 1)`. Step 3 puts `z^x` between `e^(2 - 2/x^2)` and `e^2`,
and `μ/μ'` is within `10^-3` of 1, so the trace `W - 1/W` lies strictly between 7 and 8 in
absolute value for `x ≥ 9`. The cases `x ≤ 7` are checked directly. -/
theorem corollary38_3_a {b m q x l c : ℕ} (hq : q = 1 ∨ (q = 0 ∧ m = 0)) (hl : l.Prime)
    (hxl : x = l ^ c) (hxo : Odd x) (hs : IsSolution b m [1, x, q]) :
    (x = 3 ∧ b = 4) ∨ (x = 7 ∧ b = 904) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxo
  have hA : midA m 1 q = 1 := by rcases hq with rfl | ⟨rfl, rfl⟩ <;> simp [midA]
  have heq := mid_eq hs hx0
  rw [hA] at heq
  push_cast at heq
  have hxb : x < b := hs.lt_base x (by simp)
  have heqN : b * (b + x) = x ^ x + 1 := by
    have : ((b * (b + x) : ℕ) : ℤ) = ((x ^ x + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  by_cases hx8 : x ≤ 8
  · exact mid11_small hxb hxo hx8 heqN
  exfalso
  push Not at hx8
  have hx9 : 9 ≤ x := by obtain ⟨i, rfl⟩ := hxo; omega
  have hk : ((1 : ℕ) : ℤ) * midA m 1 q = (1 : ℤ) ^ 2 := by rw [hA]; norm_num
  have hxoZ : Odd (x : ℤ) := by obtain ⟨i, rfl⟩ := hxo; exact ⟨i, by push_cast; ring⟩
  have hR := (lemma38_1_coprime hxoZ (isCoprime_one_right (x := (x : ℤ)))).2
  have hd := lemma38_1_d hs hx0 hk hl hxl hR
  -- the two real embeddings
  have h0 : (0 : ℝ) ≤ ((x : ℤ) : ℝ) ^ 2 + 4 * (((1 : ℤ) ^ 2 : ℤ) : ℝ) := by positivity
  set φ := embR ((1 : ℤ) ^ 2) x h0 with hφ
  set φ' := embR' ((1 : ℤ) ^ 2) x h0 with hφ'
  set t := rootR ((1 : ℤ) ^ 2) x with ht
  set t' := rootR' ((1 : ℤ) ^ 2) x with ht'
  have htt : t + t' = x := by rw [ht, ht', rootR_add]; simp
  have htm : t * t' = -1 := by rw [ht, ht', rootR_mul h0]; norm_num
  have hφω : φ ω = t := by
    rw [hφ, embR_apply, re_omega, im_omega, Int.cast_zero, Int.cast_one, zero_add, one_mul]
  have hφ'ω : φ' ω = t' := by
    rw [hφ', embR'_apply, re_omega, im_omega, Int.cast_zero, Int.cast_one, zero_add, one_mul]
  have hφstar : ∀ z, φ (star z) = φ' z := fun z => by
    rw [hφ, hφ', ← embR'_star h0 (star z), star_star]
  have hφ'star : ∀ z, φ' (star z) = φ z := embR'_star h0
  have htdef : t = ((x : ℝ) + Real.sqrt ((x : ℝ) ^ 2 + 4 * 1 ^ 2)) / 2 := by
    rw [ht, rootR]; push_cast; ring_nf
  obtain ⟨ht1, hZlo, hZhi⟩ := k1_pow_bounds hx9
  rw [← htdef] at ht1 hZlo hZhi
  set Z := ((t + 1) / (t - 1)) ^ x with hZ
  -- `μ = b + θ` and its two real values
  set μ : MidRing 1 x := ω + ((((1 : ℕ) : ℤ) * b : ℤ) : MidRing 1 x) with hμ
  have hM : φ μ = b + t := by rw [hμ, map_add, hφω, map_intCast]; push_cast; ring
  have hM' : φ' μ = b + t' := by rw [hμ, map_add, hφ'ω, map_intCast]; push_cast; ring
  have hMM : φ μ * φ' μ = (x : ℝ) ^ x := by
    rw [hφ, hφ', embR_mul_embR', mid_norm_mu hs hx0 hk]; push_cast; ring
  set M := φ μ with hMdef
  set M' := φ' μ with hM'def
  set X : ℝ := (x : ℝ) ^ x with hX
  have hXpos : 0 < X := by positivity
  have hb10 : (10 : ℝ) ≤ b := by exact_mod_cast (show 10 ≤ b by omega)
  have ht'eq : t' = -1 / t := by field_simp; linarith
  have ht'1 : -1 < t' := by
    rw [ht'eq, lt_div_iff₀ (by linarith)]; linarith
  have ht'0 : t' < 0 := by rw [ht'eq]; exact div_neg_of_neg_of_pos (by norm_num) (by linarith)
  have hM'pos : 0 < M' := by rw [hM']; linarith
  have hMpos : 0 < M := by rw [hM]; linarith
  -- `M ≤ 1.001 M'`
  have hdiff : t - t' ≤ x + 1 := by
    have h1 : (t - t') ^ 2 = (x : ℝ) ^ 2 + 4 := by
      linear_combination (t + t' + x) * htt - 4 * htm
    have h2 : 0 < t - t' := by nlinarith
    have : (9 : ℝ) ≤ x := by exact_mod_cast hx9
    nlinarith
  have hXbig : 1001000 * ((x : ℝ) + 1) ^ 2 ≤ X := by
    rw [hX]; exact_mod_cast pow_self_ge_k1 hx9
  have hMle : M ≤ 1.001 * M' := by
    have hMd : M - M' ≤ x + 1 := by rw [hM, hM']; linarith
    have hx1 : (0 : ℝ) < x + 1 := by positivity
    have hbig : 1000 * ((x : ℝ) + 1) ≤ M' := by
      by_contra hlt
      push Not at hlt
      have : M * M' < 1001000 * ((x : ℝ) + 1) ^ 2 := by
        have hM1 : M < 1001 * ((x : ℝ) + 1) := by linarith
        calc M * M' < (1001 * ((x : ℝ) + 1)) * (1000 * ((x : ℝ) + 1)) :=
              mul_lt_mul'' hM1 hlt hMpos.le hM'pos.le
          _ = 1001000 * ((x : ℝ) + 1) ^ 2 := by ring
      linarith
    linarith
  have hMge : M' ≤ M := by rw [hM, hM']; linarith
  have hM'e : M' = X / M := by field_simp; linarith
  -- identities between `t`, `t'` and `x`
  have hpp : (t + 1) * (t' + 1) = x := by linear_combination htm + htt
  have hq1 : t * (t' + 1) = t - 1 := by linear_combination htm
  have htm1 : (-t') * t = 1 := by linear_combination -htm
  have hAB : (t + 1) ^ x * (t' + 1) ^ x = X := by rw [← mul_pow, hpp]
  have hCB : t ^ x * (t' + 1) ^ x = (t - 1) ^ x := by rw [← mul_pow, hq1]
  have hEC : (-t') ^ x * t ^ x = 1 := by rw [← mul_pow, htm1, one_pow]
  have hZdef : Z = (t + 1) ^ x / (t ^ x * (t' + 1) ^ x) := by rw [hZ, div_pow, hCB]
  have hxodd : (-1 : ℝ) ^ x = -1 := hxo.neg_one_pow
  have hA0 : 0 < (t + 1) ^ x := by positivity
  have hB0 : 0 < (t' + 1) ^ x := pow_pos (by linarith) _
  have hC0 : 0 < t ^ x := pow_pos (by linarith) _
  have hE0 : 0 < (-t') ^ x := pow_pos (by linarith) _
  -- the unit `W`, its trace, and the contradiction
  suffices key : ∃ W : MidRing 1 x, φ W * φ' W = -1 ∧ 0 < φ W ∧
      ((7.19 ≤ φ W ∧ φ W ≤ 7.4) ∨ (7.19 ≤ (φ W)⁻¹ ∧ (φ W)⁻¹ ≤ 7.4)) by
    obtain ⟨W, hWn, hWpos, hWb⟩ := key
    apply sub_inv_ne_int hWpos hWb (QuadraticAlgebra.trace W)
    rw [← embR_add_embR' h0, ← hφ, ← hφ']
    have : φ' W = -(φ W)⁻¹ := by field_simp; linarith
    rw [this]; ring
  have hgg : ∀ g g' P Q : ℝ, P * Q = X → X * g = P * (t + 1) ^ x →
      X * g' = Q * (t' + 1) ^ x → g * g' = 1 := by
    intro g g' P Q hPQ e1 e2
    have : X * X * (g * g') = X * X := by
      rw [show X * X * (g * g') = (X * g) * (X * g') by ring, e1, e2]
      rw [show P * (t + 1) ^ x * (Q * (t' + 1) ^ x) = (P * Q) * ((t + 1) ^ x * (t' + 1) ^ x)
        by ring, hPQ, hAB]
    have hXX : X * X ≠ 0 := by positivity
    exact (mul_eq_left₀ hXX).1 this
  have hEF : (-t') ^ x * (-t) ^ x = -1 := by
    rw [← mul_pow, show (-t') * (-t) = -1 by linear_combination htm, hxodd]
  have hCD : t ^ x * t' ^ x = -1 := by rw [← mul_pow, htm, hxodd]
  have hE : (-t') ^ x = (t ^ x)⁻¹ := eq_inv_of_mul_eq_one_left hEC
  have hXAB : X = (t + 1) ^ x * (t' + 1) ^ x := hAB.symm
  rcases hd with ⟨γ, hγ⟩ | ⟨γ, hγ⟩
  · -- `μ (θ + 1)^x = x^x γ`: `W = (-θ')^x γ^2`, of value `z^x μ / μ'`
    have e1 := congrArg φ hγ
    have e2 := congrArg φ' hγ
    simp only [map_mul, map_pow, map_add, map_intCast, hφω, hφ'ω] at e1 e2
    push_cast at e1 e2
    rw [← hX] at e1 e2
    have hg := hgg (φ γ) (φ' γ) M M' hMM e1.symm e2.symm
    have hgv : φ γ = M * (t + 1) ^ x / X := by field_simp; linarith
    refine ⟨(-star ω) ^ x * γ ^ 2, ?_, ?_, ?_⟩
    · simp only [map_mul, map_pow, map_neg, hφstar, hφ'star, hφω, hφ'ω]
      calc (-t') ^ x * φ γ ^ 2 * ((-t) ^ x * φ' γ ^ 2)
          = ((-t') ^ x * (-t) ^ x) * (φ γ * φ' γ) ^ 2 := by ring
        _ = -1 := by rw [hg, hEF]; ring
    · simp only [map_mul, map_pow, map_neg, hφstar, hφ'ω]
      rw [hgv]
      positivity
    · left
      have hval : φ ((-star ω) ^ x * γ ^ 2) = Z * (M / M') := by
        simp only [map_mul, map_pow, map_neg, hφstar, hφ'ω]
        rw [hgv, hZdef, hM'e, hE, hXAB]
        field_simp
      rw [hval]
      have hr1 : 1 ≤ M / M' := by rw [le_div_iff₀ hM'pos]; linarith
      have hr2 : M / M' ≤ 1.001 := by rw [div_le_iff₀ hM'pos]; linarith
      have h1 := mul_le_mul hZlo hr1 (by norm_num) (by linarith)
      have h2 := mul_le_mul hZhi hr2 (by linarith) (by norm_num)
      constructor <;> linarith
  · -- `μ (θ' + 1)^x = x^x γ`: `W = θ^x γ^2`, of value `μ' / (z^x μ)`
    have e1 := congrArg φ hγ
    have e2 := congrArg φ' hγ
    simp only [map_mul, map_pow, map_add, map_intCast, hφstar, hφ'star, hφω, hφ'ω] at e1 e2
    push_cast at e1 e2
    rw [← hX] at e1 e2
    have hg := hgg (φ' γ) (φ γ) M' M (by rw [mul_comm]; exact hMM) e2.symm e1.symm
    have hgv : φ γ = M * (t' + 1) ^ x / X := by field_simp; linarith
    refine ⟨ω ^ x * γ ^ 2, ?_, ?_, ?_⟩
    · simp only [map_mul, map_pow, hφω, hφ'ω]
      calc t ^ x * φ γ ^ 2 * (t' ^ x * φ' γ ^ 2) = (t ^ x * t' ^ x) * (φ' γ * φ γ) ^ 2 := by ring
        _ = -1 := by rw [hg, hCD]; ring
    · simp only [map_mul, map_pow, hφω]
      rw [hgv]
      positivity
    · right
      have hval : (φ (ω ^ x * γ ^ 2))⁻¹ = Z * (M' / M) := by
        simp only [map_mul, map_pow, hφω]
        rw [hgv, hZdef, hM'e, hXAB]
        field_simp
      rw [hval]
      have hr1 : M' / M ≤ 1 := by rw [div_le_one hMpos]; exact hMge
      have hr2 : 1 / 1.001 ≤ M' / M := by
        rw [div_le_div_iff₀ (by norm_num) hMpos]; linarith
      have h1 := mul_le_mul hZlo hr2 (by norm_num) (by linarith)
      have h2 := mul_le_mul hZhi hr1 (by linarith) (by norm_num)
      constructor <;> linarith

/-! ### Section 38.4: the leading position -/

/-- The ring `Z[θ]` of section 38.4.1, `θ^2 = x A + q θ`: in `Q(sqrt R)`, `R = q^2 + 4 x A`,
`θ = (q + sqrt R)/2`. -/
abbrev LeadRing (x A q : ℤ) := QuadraticAlgebra ℤ (x * A) q

/-- **Section 38.4.1**: `θ θ' = -x A`, `θ + θ' = q`, and for a solution `(x, q, r)`,
`μ = (U + sqrt R)/2 = x b + θ` has norm `x^(x+1)`. -/
theorem lead_norms {b m q r x : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0) :
    QuadraticAlgebra.norm (ω : LeadRing x (leadA m q r) q) = -(x * leadA m q r) ∧
      star (ω : LeadRing x (leadA m q r) q) + ω = (q : LeadRing x (leadA m q r) q) ∧
      QuadraticAlgebra.norm ((ω : LeadRing x (leadA m q r) q) +
        ((x * b : ℤ) : LeadRing x (leadA m q r) q)) = (x : ℤ) ^ (x + 1) := by
  refine ⟨norm_omega', star_omega_add_omega, ?_⟩
  rw [norm_omega_add]
  linear_combination (x : ℤ) * lead_eq hs hx

/-- **Lemma 38.5**, the divisibility, for `x` prime to `q`: `x^(x+1)` divides `μ θ'^(x+1)` in
`Z[θ]`. At the two roots `r = -x b` and `s = q + x b` of `T^2 - q T - x A` modulo
`x^(x+1)`, `μ` vanishes at `r` and `θ'` takes the value `r ≡ 0 (mod x)` at `s`; and
`s - r = U` is prime to `x`. So the part of `(μ)` above `x` and the part of `(θ)` above `x` lie
on the same primes. -/
theorem lemma38_5_dvd {b m q r x : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0)
    (hq : IsCoprime (q : ℤ) x) :
    (((x ^ (x + 1) : ℕ) : ℤ) : LeadRing x (leadA m q r) q) ∣
      ((ω : LeadRing x (leadA m q r) q) + ((x * b : ℤ) : LeadRing x (leadA m q r) q)) *
        (star ω) ^ (x + 1) := by
  have heq := lead_eq hs hx
  set A := leadA m q r with hA
  set U : ℤ := 2 * x * b + q with hU
  have hUx : IsCoprime U x := by
    have : U = q + x * (2 * b) := by rw [hU]; ring
    rw [this]; exact hq.add_mul_left_left _
  have hM : ((x ^ (x + 1) : ℕ) : ℤ) = (x : ℤ) ^ (x + 1) := by push_cast; rfl
  set ρ : ℤ := -(x * b) with hρ
  set σ : ℤ := q + x * b with hσ
  have hroot : ρ ^ 2 - q * ρ - x * A = (x : ℤ) ^ (x + 1) := by
    rw [hρ, pow_succ]; linear_combination (x : ℤ) * heq
  have hroot' : σ ^ 2 - q * σ - x * A = (x : ℤ) ^ (x + 1) := by
    rw [hσ, pow_succ]; linear_combination (x : ℤ) * heq
  have hdr : ((x ^ (x + 1) : ℕ) : ℤ) ∣ ρ ^ 2 - q * ρ - x * A := by rw [hroot, hM]
  have hds : ((x ^ (x + 1) : ℕ) : ℤ) ∣ σ ^ 2 - q * σ - x * A := by rw [hroot', hM]
  have hrs : IsCoprime (ρ - σ) ((x ^ (x + 1) : ℕ) : ℤ) := by
    rw [hM, show ρ - σ = -U by rw [hρ, hσ, hU]; ring]
    exact hUx.pow_right.neg_left
  refine dvd_of_evalMod hdr hds hrs ?_ ?_
  · rw [map_mul, map_add, evalMod_omega, map_intCast]
    have : ((ρ : ℤ) : ZMod (x ^ (x + 1))) + ((x * b : ℤ) : ZMod (x ^ (x + 1))) = 0 := by
      rw [hρ]; push_cast; ring
    rw [this, zero_mul]
  · rw [map_mul, map_pow, star_omega, map_sub, map_intCast, evalMod_omega]
    have : ((q : ℤ) : ZMod (x ^ (x + 1))) - (σ : ZMod (x ^ (x + 1))) =
        (((-(x * b) : ℤ)) : ZMod _) := by
      rw [hσ]; push_cast; ring
    rw [this, ← Int.cast_pow, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2, mul_zero]
    rw [hM]; exact pow_dvd_pow_of_dvd ⟨-(b : ℤ), by ring⟩ _

/-- If `n z = n w` in `Z[ω]` with `n ≠ 0` an integer, then `z = w`. -/
lemma intCast_mul_cancel {a b n : ℤ} (hn : n ≠ 0) {z w : QuadraticAlgebra ℤ a b}
    (h : (n : QuadraticAlgebra ℤ a b) * z = n * w) : z = w := by
  have h1 : n * z.re = n * w.re := by
    have := congrArg QuadraticAlgebra.re h
    simpa only [re_mul, re_intCast, im_intCast, mul_zero, zero_mul, add_zero,
      Int.cast_id] using this
  have h2 : n * z.im = n * w.im := by
    have := congrArg QuadraticAlgebra.im h
    simpa only [im_mul, re_intCast, im_intCast, mul_zero, zero_mul, add_zero,
      Int.cast_id] using this
  ext
  · exact mul_left_cancel₀ hn h1
  · exact mul_left_cancel₀ hn h2

/-- **Lemma 38.5**, for `x` prime to `q`: `ν = μ / θ^(x+1)` is an S-unit for the primes of
`A`. In integer form: `(-A)^(x+1) μ = ν0 θ^(x+1)` with `ν0` in `Z[θ]` of norm `(-A)^(x+1)`,
so `ν = ν0 / (-A)^(x+1)`. For `(x, 1, 1)`, `A = 1`, and `ν0 = ±ν` is a unit of norm `-1` when
`x` is even (section 38.4.3). -/
theorem lemma38_5 {b m q r x : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0)
    (hq : IsCoprime (q : ℤ) x) :
    ∃ ν0 : LeadRing x (leadA m q r) q,
      (((-leadA m q r) ^ (x + 1) : ℤ) : LeadRing x (leadA m q r) q) *
          ((ω : LeadRing x (leadA m q r) q) + ((x * b : ℤ) : LeadRing x (leadA m q r) q)) =
        ν0 * ω ^ (x + 1) ∧ QuadraticAlgebra.norm ν0 = (-leadA m q r) ^ (x + 1) := by
  set A := leadA m q r with hA
  obtain ⟨ν0, hν⟩ := lemma38_5_dvd hs hx hq
  set μ : LeadRing x A q := ω + ((x * b : ℤ) : LeadRing x A q) with hμ
  have hθθ : (ω : LeadRing x A q) * star ω = ((-(x * A) : ℤ) : LeadRing x A q) :=
    omega_mul_star_omega
  have hxn : ((x : ℤ) ^ (x + 1)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hx)
  have key : (((x : ℤ) ^ (x + 1) : ℤ) : LeadRing x A q) *
        ((((-A) ^ (x + 1) : ℤ) : LeadRing x A q) * μ) =
      (((x : ℤ) ^ (x + 1) : ℤ) : LeadRing x A q) * (ν0 * ω ^ (x + 1)) := by
    have : ((x ^ (x + 1) : ℕ) : ℤ) = (x : ℤ) ^ (x + 1) := by push_cast; rfl
    rw [this] at hν
    calc (((x : ℤ) ^ (x + 1) : ℤ) : LeadRing x A q) * ((((-A) ^ (x + 1) : ℤ) : LeadRing x A q) * μ)
        = μ * (ω * star ω) ^ (x + 1) := by rw [hθθ]; push_cast; ring
      _ = (μ * star ω ^ (x + 1)) * ω ^ (x + 1) := by ring
      _ = _ := by rw [hν]; ring
  refine ⟨ν0, intCast_mul_cancel hxn key, ?_⟩
  have hn := congrArg QuadraticAlgebra.norm hν
  rw [map_mul, map_pow, QuadraticAlgebra.norm_star, norm_omega', map_mul, norm_intCast] at hn
  have hnμ := (lead_norms hs hx).2.2
  rw [← hA, ← hμ] at hnμ
  rw [hnμ] at hn
  have hxx : ((x ^ (x + 1) : ℕ) : ℤ) = (x : ℤ) ^ (x + 1) := by push_cast; rfl
  rw [hxx, show (-((x : ℤ) * A)) = x * (-A) by ring, mul_pow] at hn
  push_cast at hn
  have hxn2 : ((x : ℤ) ^ (x + 1)) ^ 2 ≠ 0 := pow_ne_zero _ hxn
  apply mul_left_cancel₀ hxn2
  linear_combination -hn

/-- **Theorem 38.7**, the case `R = 4x + 1` a square. If `b (x b + 1) = x^x + 1` with `b ≥ 1`
and `4x + 1` a square, then `x = 0`. Here `4x + 1 = (2m + 1)^2`, `x = m (m + 1)`, and
`μ = x b + m + 1`, `μ' = x b - m` are integers with `μ μ' = x^(x+1)`; `μ ≡ 1 (mod m)` and
`μ' ≡ 1 (mod m + 1)` force `μ = (m + 1)^(x+1)` and `μ' = m^(x+1)` (Lemma 38.5 in
`Q × Q`), and then `μ - μ' = 2m + 1` is too small. -/
theorem theorem38_7_square {b x : ℕ} (hb : 1 ≤ b) (heq : b * (x * b + 1) = x ^ x + 1)
    (hsq : IsSquare (4 * x + 1)) : x = 0 := by
  obtain ⟨s, hs⟩ := hsq
  have hsodd : Odd s := by
    have : Odd (s * s) := by rw [← hs]; exact ⟨2 * x, by ring⟩
    exact (Nat.odd_mul.1 this).1
  obtain ⟨m, rfl⟩ := hsodd
  have hxm : x = m * (m + 1) := by
    have : 4 * x = 4 * (m * (m + 1)) := by nlinarith
    omega
  by_contra hx0
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [zero_mul] at hxm; exact absurd hxm hx0
    · exact h
  -- the two factors
  set P := x * b + m + 1 with hP
  set Q := x * b - m with hQ
  have hxb : m < x * b := by
    have : m < x := by rw [hxm]; nlinarith
    nlinarith
  have hPQ : P * Q = m ^ (x + 1) * (m + 1) ^ (x + 1) := by
    rw [← mul_pow, ← hxm]
    have h1 : (x : ℤ) * b ^ 2 + b - 1 = x ^ x := by
      have : ((b * (x * b + 1) : ℕ) : ℤ) = ((x ^ x + 1 : ℕ) : ℤ) := by rw [heq]
      push_cast at this; linarith
    have : ((P * Q : ℕ) : ℤ) = ((x ^ (x + 1) : ℕ) : ℤ) := by
      rw [hP, hQ]; push_cast [Nat.cast_sub hxb.le]
      have hxmZ : (x : ℤ) = m * (m + 1) := by exact_mod_cast hxm
      rw [pow_succ, ← h1]
      linear_combination hxmZ
    exact_mod_cast this
  have hPm : Nat.Coprime P (m ^ (x + 1)) := by
    apply Nat.Coprime.pow_right
    have : P = m * ((m + 1) * b + 1) + 1 := by rw [hP, hxm]; ring
    rw [this, Nat.coprime_mul_left_add_left]; exact Nat.coprime_one_left m
  have hQm : Nat.Coprime Q ((m + 1) ^ (x + 1)) := by
    apply Nat.Coprime.pow_right
    have : Q = (m + 1) * (m * b - 1) + 1 := by
      rw [hQ, hxm]
      have : 1 ≤ m * b := Nat.one_le_iff_ne_zero.2 (by positivity)
      zify [this, hxb.le, (show m ≤ m * (m + 1) * b by nlinarith)]
      ring
    rw [this, Nat.coprime_mul_left_add_left]; exact Nat.coprime_one_left _
  have hP1 : P ∣ (m + 1) ^ (x + 1) := hPm.dvd_of_dvd_mul_left ⟨Q, hPQ.symm⟩
  have hQ1 : Q ∣ m ^ (x + 1) := hQm.dvd_of_dvd_mul_right ⟨P, by rw [← hPQ, mul_comm]⟩
  have hPle := Nat.le_of_dvd (by positivity) hP1
  have hQle := Nat.le_of_dvd (by positivity) hQ1
  have hQ0 : 0 < Q := by omega
  have hPeq : P = (m + 1) ^ (x + 1) := by
    by_contra hne
    have hlt : P < (m + 1) ^ (x + 1) := lt_of_le_of_ne hPle hne
    have : P * Q < (m + 1) ^ (x + 1) * m ^ (x + 1) :=
      Nat.mul_lt_mul_of_lt_of_le hlt hQle (by positivity)
    rw [hPQ] at this; nlinarith
  have hQeq : Q = m ^ (x + 1) := by
    have h1 : (m + 1) ^ (x + 1) * Q = (m + 1) ^ (x + 1) * m ^ (x + 1) := by
      calc (m + 1) ^ (x + 1) * Q = P * Q := by rw [hPeq]
        _ = _ := by rw [hPQ]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  -- `(m + 1)^(x+1) - m^(x+1) > 2m + 1`
  have hdiff : P = Q + 2 * m + 1 := by rw [hP, hQ]; omega
  have hx2 : 2 ≤ x := by rw [hxm]; nlinarith
  obtain ⟨j, hj⟩ : ∃ j, x + 1 = j + 3 := ⟨x - 2, by omega⟩
  rw [hPeq, hQeq, hj] at hdiff
  have h1 : m ^ (j + 1) + 1 ≤ (m + 1) ^ (j + 1) := by
    have := Nat.pow_lt_pow_left (show m < m + 1 by omega) (show j + 1 ≠ 0 by omega)
    omega
  rw [show (m + 1) ^ (j + 3) = (m + 1) ^ 2 * (m + 1) ^ (j + 1) by ring,
    show m ^ (j + 3) = m ^ 2 * m ^ (j + 1) by ring] at hdiff
  generalize m ^ (j + 1) = Y at h1 hdiff
  generalize (m + 1) ^ (j + 1) = Z at h1 hdiff
  nlinarith

/-- **Corollary 38.8**, odd `x`. Under either convention, `(x, 1, 1)`, and `(x, 1, 0)` under
`0^0 = 0`, is never a solution with `x` odd: `U = 2 x b + 1` satisfies
`U^2 = 4 x^(x+1) + 4x + 1` with `x^(x+1)` a square `V^2`, so `2V < U` and
`4 V + 1 ≤ 4x + 1`, which forces `x = 1`, and then the base would be 1. -/
theorem corollary38_8_odd {b m q x : ℕ} (hq : q = 1 ∨ (q = 0 ∧ m = 0)) (hxo : Odd x)
    (hs : IsSolution b m [x, 1, q]) : False := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxo
  have hA : leadA m 1 q = 1 := by rcases hq with rfl | ⟨rfl, rfl⟩ <;> simp [leadA]
  have hsq := lead_sq hs hx0
  rw [hA] at hsq
  have hxb : x < b := hs.lt_base x (by simp)
  obtain ⟨i, rfl⟩ := hxo
  have hN : (2 * (2 * i + 1) * b + 1) ^ 2 =
      4 * ((2 * i + 1) ^ (i + 1)) ^ 2 + (4 * (2 * i + 1) + 1) := by
    have : ((2 * (2 * i + 1) * b + 1 : ℕ) : ℤ) ^ 2 =
        ((4 * ((2 * i + 1) ^ (i + 1)) ^ 2 + (4 * (2 * i + 1) + 1) : ℕ) : ℤ) := by
      rw [hsq]; push_cast; ring
    exact_mod_cast this
  generalize hV : (2 * i + 1) ^ (i + 1) = V at hN
  generalize hU : 2 * (2 * i + 1) * b + 1 = U at hN
  have hUV : 2 * V < U := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_left h 2
    nlinarith
  have h1 : (2 * V + 1) ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left hUV 2
  have hVle : V ≤ 2 * i + 1 := by nlinarith
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · -- `x = 1`: `b (b + 1) = 2` forces `b = 1`, not a base above the digit 1
    have := lead_eq hs hx0
    rw [hA] at this
    push_cast at this
    nlinarith
  · have : (2 * i + 1) ^ 2 ≤ V := by
      rw [← hV]; exact Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith

/-- **Corollary 38.9**, the case `q = 0` of the leading position: if `(x, 0, r)` is a solution,
then `x b^2 = x^x + A`, so `x` divides `A`; for `A ≠ 0` this bounds `x ≤ |A|`. `A = 0` only for
`(x, 0, 0)` and `(x, 0, 1)` under `0^0 = 0` (`leadA_eq_zero`, `one_le_leadA`). -/
theorem corollary38_9_q_zero {b m r x : ℕ} (hs : IsSolution b m [x, 0, r]) (hx : x ≠ 0) :
    (x : ℤ) ∣ leadA m 0 r := by
  have heq := lead_eq hs hx
  have : leadA m 0 r = x * (b ^ 2 - x ^ (x - 1)) := by
    have hxx : (x : ℤ) ^ x = x * x ^ (x - 1) := by rw [← pow_succ']; congr 1; omega
    push_cast at heq
    linear_combination -heq - hxx
  rw [this]; exact dvd_mul_right _ _

/-! ### The exact test of section 38.6 for `x ≤ 6000`

The library tests every odd `x ≤ 6000` in the middle families `(1, x, 1)`, `(1, x, 0)`,
`(1, x, 3)`, `(3, x, 1)`, `(3, x, 0)` and every even `x ≤ 6000` in `(x, 1, 1)`, `(x, 1, 0)` by
integer square roots. The kernel replays this as a sieve: for each `x` it finds a prime `l` of
`primes38` modulo which `D = U^2` is a non-residue (Euler's criterion), except at the solutions
`x = 1, 3, 7` of `(1, x, 1)`. -/

/-- `D = x^2 + 4 p x^x + 4 p A` of the middle position modulo `l`, by `powRes`. -/
def resMid (l p A x : ℕ) : ℕ := (x ^ 2 + 4 * p * powRes l x + 4 * p * A) % l

/-- `D = 4 x^(x+1) + q^2 + 4 x A` of the leading position modulo `l`. -/
def resLead (l q A x : ℕ) : ℕ := (4 * (powRes l x * x) + q ^ 2 + 4 * x * A) % l

lemma natCast_resMid {l p A x : ℕ} (hl : l.Prime) (hx : x ≠ 0) :
    ((resMid l p A x : ℕ) : ZMod l) =
      (((x : ℤ) ^ 2 + 4 * p * (x : ℤ) ^ x + 4 * p * A : ℤ) : ZMod l) := by
  have hp := natCast_pow_self_eq_powRes hl hx
  push_cast at hp
  rw [resMid, ZMod.natCast_mod]; push_cast; rw [← hp]

lemma natCast_resLead {l q A x : ℕ} (hl : l.Prime) (hx : x ≠ 0) :
    ((resLead l q A x : ℕ) : ZMod l) =
      ((4 * (x : ℤ) ^ (x + 1) + q ^ 2 + 4 * x * A : ℤ) : ZMod l) := by
  have hp := natCast_pow_self_eq_powRes hl hx
  push_cast at hp
  rw [resLead, ZMod.natCast_mod]; push_cast; rw [← hp]; ring

/-- The sieve for the middle position: for a solution `(p, x, q)` with `A = w(p) + w(q) - q`,
`D = U^2` is a square modulo every prime. -/
lemma isSquare_resMid {b m p q x A l : ℕ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hA : midA m p q = A) (hl : l.Prime) : IsSquare ((resMid l p A x : ℕ) : ZMod l) := by
  rw [natCast_resMid hl hx]
  have h := mid_sq hs hx
  rw [hA] at h
  have h' : (x : ℤ) ^ 2 + 4 * p * (x : ℤ) ^ x + 4 * p * A = ((2 * p * b + x : ℕ) : ℤ) ^ 2 := by
    rw [h]; ring
  exact ⟨(((2 * p * b + x : ℕ) : ℤ) : ZMod l), by rw [h']; push_cast; ring⟩

/-- The sieve for the leading position. -/
lemma isSquare_resLead {b m q r x A l : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0)
    (hA : leadA m q r = A) (hl : l.Prime) : IsSquare ((resLead l q A x : ℕ) : ZMod l) := by
  rw [natCast_resLead hl hx]
  have h := lead_sq hs hx
  rw [hA] at h
  have h' : 4 * (x : ℤ) ^ (x + 1) + q ^ 2 + 4 * x * A = ((2 * x * b + q : ℕ) : ℤ) ^ 2 := by
    rw [h]; ring
  exact ⟨(((2 * x * b + q : ℕ) : ℤ) : ZMod l), by rw [h']; push_cast; ring⟩

/-- The primes of the certificates of the exact test. -/
def primes38 : List ℕ :=
  [263, 383, 277, 199, 149, 233, 311, 89, 83, 19, 229, 13, 61, 113, 101, 5, 17, 269, 257, 251,
    271, 7, 389, 167, 359, 367, 307, 107, 173, 11]

lemma primes38_prime : ∀ l ∈ primes38, l.Prime ∧ l ≠ 2 := by
  simp only [primes38, List.mem_cons, List.not_mem_nil, or_false]
  rintro l (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl) <;> norm_num

/-- `D` of the middle family `(p, A)` is a non-residue modulo a prime of `primes38`. -/
def okMid (p A x : ℕ) : Bool := primes38.any fun l => nonres l (resMid l p A x)

/-- `D` of the leading family `(q, A)` is a non-residue modulo a prime of `primes38`. -/
def okLead (q A x : ℕ) : Bool := primes38.any fun l => nonres l (resLead l q A x)

lemma not_okMid {b m p q x A : ℕ} (hs : IsSolution b m [p, x, q]) (hx : x ≠ 0)
    (hA : midA m p q = A) : okMid p A x = false := by
  rw [okMid, List.any_eq_false]
  intro l hl hnr
  obtain ⟨hlp, hl2⟩ := primes38_prime l hl
  exact not_isSquare_of_nonres hlp hl2 hnr (isSquare_resMid hs hx hA hlp)

lemma not_okLead {b m q r x A : ℕ} (hs : IsSolution b m [x, q, r]) (hx : x ≠ 0)
    (hA : leadA m q r = A) : okLead q A x = false := by
  rw [okLead, List.any_eq_false]
  intro l hl hnr
  obtain ⟨hlp, hl2⟩ := primes38_prime l hl
  exact not_isSquare_of_nonres hlp hl2 hnr (isSquare_resLead hs hx hA hlp)

/-! The four runs, each checked by the kernel. -/

theorem check38_mid_1_1 : (List.range 3000).all (fun i =>
    2 * i + 1 == 1 || 2 * i + 1 == 3 || 2 * i + 1 == 7 || okMid 1 1 (2 * i + 1)) = true := by
  decide +kernel

theorem check38_mid_1_25 :
    (List.range 3000).all (fun i => okMid 1 25 (2 * i + 1)) = true := by
  decide +kernel

theorem check38_mid_3_27 :
    (List.range 3000).all (fun i => okMid 3 27 (2 * i + 1)) = true := by
  decide +kernel

theorem check38_lead_1_1 :
    (List.range 3000).all (fun i => okLead 1 1 (2 * i + 2)) = true := by
  decide +kernel

/-- **Section 38.6**, the exact test, `(1, x, 1)` and `(1, x, 0)` (`0^0 = 0`): for odd
`x ≤ 6000` (prime power or not) the only solutions are `x = 3` in base 4 and `x = 7` in base
904. -/
theorem exact38_mid_one {b m q x : ℕ} (hq : q = 1 ∨ (q = 0 ∧ m = 0)) (hxo : Odd x)
    (hx : x ≤ 6000) (hs : IsSolution b m [1, x, q]) : (x = 3 ∧ b = 4) ∨ (x = 7 ∧ b = 904) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxo
  have hA : midA m 1 q = ((1 : ℕ) : ℤ) := by rcases hq with rfl | ⟨rfl, rfl⟩ <;> simp [midA]
  have hxb : x < b := hs.lt_base x (by simp)
  have heq := mid_eq hs hx0
  rw [hA] at heq
  have heqN : b * (b + x) = x ^ x + 1 := by
    have : ((b * (b + x) : ℕ) : ℤ) = ((x ^ x + 1 : ℕ) : ℤ) := by push_cast at heq ⊢; linarith
    exact_mod_cast this
  have hok := not_okMid hs hx0 hA
  obtain ⟨i, rfl⟩ := hxo
  have hc := check38_mid_1_1
  simp only [List.all_eq_true, List.mem_range] at hc
  have := hc i (by omega)
  rw [hok] at this
  simp only [Bool.or_false, Bool.or_eq_true, beq_iff_eq] at this
  exact mid11_small hxb ⟨i, rfl⟩ (by omega) heqN

/-- **Section 38.6**, the exact test, `(1, x, 3)`: no solution with `x ≤ 6000` odd. -/
theorem exact38_mid_three {b m x : ℕ} (hxo : Odd x) (hx : x ≤ 6000)
    (hs : IsSolution b m [1, x, 3]) : False := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxo
  have hA : midA m 1 3 = ((25 : ℕ) : ℤ) := by simp [midA, w]
  have hok := not_okMid hs hx0 hA
  obtain ⟨i, rfl⟩ := hxo
  have hc := check38_mid_1_25
  simp only [List.all_eq_true, List.mem_range] at hc
  have := hc i (by omega)
  rw [hok] at this
  exact Bool.false_ne_true this

/-- **Section 38.6**, the exact test, `(3, x, 1)` and `(3, x, 0)` (`0^0 = 0`): no solution with
`x ≤ 6000` odd. -/
theorem exact38_mid_three_one {b m q x : ℕ} (hq : q = 1 ∨ (q = 0 ∧ m = 0)) (hxo : Odd x)
    (hx : x ≤ 6000) (hs : IsSolution b m [3, x, q]) : False := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxo
  have hA : midA m 3 q = ((27 : ℕ) : ℤ) := by rcases hq with rfl | ⟨rfl, rfl⟩ <;> simp [midA, w]
  have hok := not_okMid hs hx0 hA
  obtain ⟨i, rfl⟩ := hxo
  have hc := check38_mid_3_27
  simp only [List.all_eq_true, List.mem_range] at hc
  have := hc i (by omega)
  rw [hok] at this
  exact Bool.false_ne_true this

/-- **Section 38.6**, the exact test, and **Corollary 38.8** for `x ≤ 6000`: `(x, 1, 1)`, and
`(x, 1, 0)` under `0^0 = 0`, is not a solution for any `x ≤ 6000` (odd `x` by
`corollary38_8_odd`, even `x` by the kernel). -/
theorem exact38_lead {b m q x : ℕ} (hq : q = 1 ∨ (q = 0 ∧ m = 0)) (hx : x ≤ 6000)
    (hs : IsSolution b m [x, 1, q]) : False := by
  rcases Nat.even_or_odd x with he | ho
  · have hx0 : x ≠ 0 := by
      rintro rfl; exact absurd (hs.head_ne_zero (by simp)) (by simp)
    have hA : leadA m 1 q = ((1 : ℕ) : ℤ) := by
      rcases hq with rfl | ⟨rfl, rfl⟩ <;> simp [leadA]
    have hok := not_okLead hs hx0 hA
    obtain ⟨i, rfl⟩ := he
    have hc := check38_lead_1_1
    simp only [List.all_eq_true, List.mem_range] at hc
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have := hc j (by omega)
    rw [show 2 * j + 2 = j + 1 + (j + 1) by ring, hok] at this
    exact Bool.false_ne_true this
  · exact corollary38_8_odd hq ho hs

/-- **Theorem 38.7**, the case `R` a square, for the strings: `(x, 1, 1)`, and `(x, 1, 0)` under
`0^0 = 0`, is not a solution when `R = 4x + 1` is a square (that is, `x = m (m + 1)`). -/
theorem theorem38_7_square_solution {b m q x : ℕ} (hq : q = 1 ∨ (q = 0 ∧ m = 0))
    (hs : IsSolution b m [x, 1, q]) (hsq : IsSquare (4 * x + 1)) : False := by
  have hx0 : x ≠ 0 := by
    rintro rfl; exact absurd (hs.head_ne_zero (by simp)) (by simp)
  have hA : leadA m 1 q = 1 := by rcases hq with rfl | ⟨rfl, rfl⟩ <;> simp [leadA]
  have heq := lead_eq hs hx0
  rw [hA] at heq
  have hxb : x < b := hs.lt_base x (by simp)
  have heqN : b * (x * b + 1) = x ^ x + 1 := by
    have : ((b * (x * b + 1) : ℕ) : ℤ) = ((x ^ x + 1 : ℕ) : ℤ) := by push_cast at heq ⊢; linarith
    exact_mod_cast this
  exact hx0 (theorem38_7_square (by omega) heqN hsq)

/-- **Corollary 38.8**, what is formalized: a solution `(x, 1, 1)`, or `(x, 1, 0)` under
`0^0 = 0`, needs `x` even, `R = 4x + 1` not a square, and `x > 6000`. The library closes the
rest with Laurent's bound `x ≤ 4.27 * 10^11` (Theorem 38.7) and the sieve of section 38.5,
which are not formalized. -/
theorem corollary38_8_partial {b m q x : ℕ} (hq : q = 1 ∨ (q = 0 ∧ m = 0))
    (hs : IsSolution b m [x, 1, q]) : Even x ∧ ¬ IsSquare (4 * x + 1) ∧ 6000 < x := by
  refine ⟨?_, fun h => theorem38_7_square_solution hq hs h, ?_⟩
  · rcases Nat.even_or_odd x with he | ho
    · exact he
    · exact (corollary38_8_odd hq ho hs).elim
  · by_contra h
    exact exact38_lead hq (by omega) hs

end Munchausen
