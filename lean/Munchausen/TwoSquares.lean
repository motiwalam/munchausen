import Munchausen.Applications

/-!
# Two-digit narcissistic numbers: the count of Theorem 30.12

Base `b` has exactly `τ(b^2 + 1) - 2` two-digit narcissistic numbers. By `isNarc2_iff` they
are the representations `b^2 + 1 = A^2 + B^2` with `B ≥ 3` odd. This file counts the
representations with Gaussian integers, in place of the formula `r_2(N) = 4 ∑ χ(d)`:

* `r(m) r(n) = 4 r(mn)` for coprime `m, n`, where `r(n)` is the number of `z ∈ Z[i]` of norm
  `n`: the factor of norm `m` of `z` is `gcd(z, m)` up to one of the 4 units;
* `r(p^k) = 4 (k + 1)` for a prime `p ≡ 1 (mod 4)`, `p = π π̄`: a `z` of norm `p^k` is
  `π z'` or a unit times `π̄^k`;
* so `r(n) = 4 τ(n)` for odd `n` whose primes are `≡ 1 (mod 4)`, and `r(2 n) = r(n)`;
* every odd prime factor of `b^2 + 1` is `≡ 1 (mod 4)`, and half of the representations with
  `B` odd have `B > 0`.
-/

open Zsqrtd

namespace Munchausen

/-- The representations `n = a^2 + b^2` as pairs `(a, b)` of integers. -/
def repZ (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    fun p => p.1 ^ 2 + p.2 ^ 2 = n

lemma mem_repZ {n : ℕ} {p : ℤ × ℤ} : p ∈ repZ n ↔ p.1 ^ 2 + p.2 ^ 2 = n := by
  constructor
  · intro h; exact (Finset.mem_filter.1 h).2
  · intro h
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_Icc.2 ?_, Finset.mem_Icc.2 ?_⟩, h⟩
    · have h1 := Int.le_self_sq p.1
      have h2 := Int.le_self_sq (-p.1)
      have h3 := sq_nonneg p.2
      rw [neg_sq] at h2
      constructor <;> linarith
    · have h1 := Int.le_self_sq p.2
      have h2 := Int.le_self_sq (-p.2)
      have h3 := sq_nonneg p.1
      rw [neg_sq] at h2
      constructor <;> linarith

/-- The Gaussian integer `a + b i`. -/
def toG (p : ℤ × ℤ) : GaussianInt := ⟨p.1, p.2⟩

lemma toG_injective : Function.Injective toG := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [toG, Zsqrtd.mk.injEq] at h
  rw [h.1, h.2]

lemma norm_toG (p : ℤ × ℤ) : (toG p).norm = p.1 ^ 2 + p.2 ^ 2 := by
  simp [toG, Zsqrtd.norm_def]; ring

lemma norm_eq_sq_add_sq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  simp [Zsqrtd.norm_def]; ring

/-- The Gaussian integers of norm `n`. -/
def repG (n : ℕ) : Finset GaussianInt := (repZ n).image toG

lemma mem_repG {n : ℕ} {z : GaussianInt} : z ∈ repG n ↔ z.norm = n := by
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
    rw [norm_toG]; exact mem_repZ.1 hp
  · intro h
    refine Finset.mem_image.2 ⟨(z.re, z.im), mem_repZ.2 ?_, rfl⟩
    rw [← h, norm_eq_sq_add_sq]

lemma card_repG (n : ℕ) : (repG n).card = (repZ n).card :=
  Finset.card_image_of_injective _ toG_injective

lemma card_repZ_one : (repZ 1).card = 4 := by decide

lemma card_repZ_two : (repZ 2).card = 4 := by decide

lemma mul_star_of_norm {z : GaussianInt} {n : ℕ} (h : z.norm = n) :
    z * star z = (n : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_mul_conj, h]; push_cast; rfl

lemma norm_dvd_of_dvd {x z : GaussianInt} (h : x ∣ z) : x.norm ∣ z.norm := by
  obtain ⟨k, rfl⟩ := h
  rw [Zsqrtd.norm_mul]; exact dvd_mul_right _ _

lemma norm_nonneg' (z : GaussianInt) : 0 ≤ z.norm := by
  rw [norm_eq_sq_add_sq]; positivity

/-- The factor of norm `m` (proof of the multiplicativity): if `N(z) = m n` with `m, n`
coprime, then `g = gcd(z, m)` has norm `m`. -/
lemma norm_gcd_eq {z : GaussianInt} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hz : z.norm = (m * n : ℕ)) : (EuclideanDomain.gcd z (m : GaussianInt)).norm = m := by
  set g := EuclideanDomain.gcd z (m : GaussianInt) with hg
  have hgz : g ∣ z := EuclideanDomain.gcd_dvd_left _ _
  have hgm : g ∣ (m : GaussianInt) := EuclideanDomain.gcd_dvd_right _ _
  -- `N(g) ∣ m`
  have h1 : g.norm ∣ (m : ℤ) * n := by
    have := norm_dvd_of_dvd hgz; rw [hz] at this; exact_mod_cast this
  have h2 : g.norm ∣ (m : ℤ) * m := by
    have := norm_dvd_of_dvd hgm
    have hm : (m : GaussianInt).norm = (m : ℤ) * m := by
      rw [show (m : GaussianInt) = ((m : ℤ) : GaussianInt) by push_cast; rfl, Zsqrtd.norm_intCast]
    rw [hm] at this; exact this
  obtain ⟨a, c, hac⟩ := (Nat.isCoprime_iff_coprime.2 hmn)
  have hdvd1 : g.norm ∣ (m : ℤ) := by
    have : (m : ℤ) = (m : ℤ) * m * a + (m : ℤ) * n * c := by linear_combination (-(m : ℤ)) * hac
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)
  -- `m ∣ N(g)` by Bezout
  have hdvd2 : (m : ℤ) ∣ g.norm := by
    rw [← Zsqrtd.intCast_dvd_intCast (d := -1), Zsqrtd.norm_eq_mul_conj]
    have hb := EuclideanDomain.gcd_eq_gcd_ab z (m : GaussianInt)
    rw [← hg] at hb
    set α := EuclideanDomain.gcdA z (m : GaussianInt)
    set β := EuclideanDomain.gcdB z (m : GaussianInt)
    have hzz : z * star z = ((m : ℤ) : GaussianInt) * n := by
      rw [mul_star_of_norm hz]; push_cast; ring
    have hsm : star (m : GaussianInt) = m := star_natCast m
    refine ⟨n * α * star α + z * α * star β + β * star z * star α + m * β * star β, ?_⟩
    rw [hb, star_add, star_mul, star_mul, hsm]
    push_cast at hzz ⊢
    linear_combination α * star α * hzz
  have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
  exact Int.dvd_antisymm (norm_nonneg' g) hm0 hdvd1 hdvd2

lemma norm_ne_zero_of {z : GaussianInt} {m : ℕ} (hm : 1 ≤ m) (h : z.norm = m) : z ≠ 0 := by
  rintro rfl; simp at h; omega

/-- **Multiplicativity** (proof of Theorem 30.12): `r(m) r(n) = 4 r(m n)` for coprime
`m, n ≥ 1`. Each `z` of norm `m n` is `x y` with `N(x) = m`, `N(y) = n` in exactly 4 ways:
`x` is `gcd(z, m)` times a unit. -/
theorem card_repG_mul {m n : ℕ} (hm : 1 ≤ m) (hmn : Nat.Coprime m n) :
    (repG m).card * (repG n).card = 4 * (repG (m * n)).card := by
  rw [← Finset.card_product]
  have hmaps : ∀ q ∈ repG m ×ˢ repG n, q.1 * q.2 ∈ repG (m * n) := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
    rw [mem_repG] at h1 h2 ⊢
    rw [Zsqrtd.norm_mul, h1, h2]; push_cast; ring
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_const_nat (m := 4), mul_comm]
  intro z hz
  rw [mem_repG] at hz
  set g := EuclideanDomain.gcd z (m : GaussianInt) with hgdef
  have hg : g.norm = m := norm_gcd_eq hmn hz
  have hg0 : g ≠ 0 := norm_ne_zero_of hm hg
  obtain ⟨z', hz'⟩ : g ∣ z := EuclideanDomain.gcd_dvd_left _ _
  have hz'n : z'.norm = n := by
    have := congrArg Zsqrtd.norm hz'
    rw [Zsqrtd.norm_mul, hg, hz] at this
    have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast at this
    exact (mul_left_cancel₀ hm0 this).symm
  have hfib : (repG m ×ˢ repG n).filter (fun q => q.1 * q.2 = z) =
      (repG 1).image (fun u => (u * g, star u * z')) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, mem_repG, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      have hx0 : x ≠ 0 := norm_ne_zero_of hm hx
      have hxm : x ∣ (m : GaussianInt) := ⟨star x, (mul_star_of_norm hx).symm⟩
      have hxz : x ∣ z := ⟨y, hxy.symm⟩
      obtain ⟨q', hq'⟩ : x ∣ g := EuclideanDomain.dvd_gcd hxz hxm
      have hq'n : q'.norm = 1 := by
        have := congrArg Zsqrtd.norm hq'
        rw [Zsqrtd.norm_mul, hg, hx] at this
        have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
        exact (mul_right_eq_self₀.1 this.symm).resolve_right hm0
      have hqq : q' * star q' = 1 := by rw [mul_star_of_norm (n := 1) (by rw [hq'n]; rfl)]; simp
      refine ⟨star q', by rw [Zsqrtd.norm_conj, hq'n]; rfl, ?_, ?_⟩
      · rw [hq']; linear_combination x * hqq
      · rw [star_star]
        have : x * (y - q' * z') = 0 := by rw [mul_sub, hxy, hz', hq']; ring
        exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hx0)).symm
    · rintro ⟨u, hu, rfl, rfl⟩
      have huu : u * star u = 1 := by rw [mul_star_of_norm hu]; simp
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [Zsqrtd.norm_mul, hu, hg]; simp
      · rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hu, hz'n]; simp
      · rw [hz']; linear_combination g * z' * huu
  rw [hfib, Finset.card_image_of_injective, card_repG, card_repZ_one]
  intro u u' h
  simp only [Prod.mk.injEq] at h
  exact mul_right_cancel₀ hg0 h.1

lemma norm_pow' (z : GaussianInt) (n : ℕ) : (z ^ n).norm = z.norm ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

/-- A Gaussian integer of prime norm is prime. -/
lemma prime_of_norm_prime {π : GaussianInt} {p : ℕ} (hp : p.Prime) (h : π.norm = p) : Prime π := by
  apply _root_.irreducible_iff_prime.1
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) π).2 hu
    rw [h] at this
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  · have hN := congrArg Zsqrtd.norm hab
    rw [Zsqrtd.norm_mul, h] at hN
    have ha := norm_nonneg' a
    have hb := norm_nonneg' b
    have hdvd : a.norm.natAbs ∣ p := ⟨b.norm.natAbs, by
      have : ((a.norm.natAbs * b.norm.natAbs : ℕ) : ℤ) = (p : ℤ) := by
        push_cast; rw [abs_of_nonneg ha, abs_of_nonneg hb]; exact hN.symm
      exact_mod_cast this.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · left
      apply (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) a).1
      have : (a.norm.natAbs : ℤ) = 1 := by exact_mod_cast h1
      rwa [Int.natAbs_of_nonneg ha] at this
    · right
      apply (Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0) b).1
      have h2 : (a.norm.natAbs : ℤ) = p := by exact_mod_cast h1
      rw [Int.natAbs_of_nonneg ha] at h2
      rw [h2] at hN
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact (mul_right_eq_self₀.1 hN.symm).resolve_right hp0

/-- For an odd prime `p = N(π)`, `π` does not divide its conjugate. -/
lemma not_dvd_star {π : GaussianInt} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : π.norm = p) :
    ¬ π ∣ star π := by
  intro hd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have h4 : ¬ (p : ℤ) ∣ 4 := by
    intro h4
    have hd4 : p ∣ 4 := by exact_mod_cast h4
    have hp4 : p ≤ 4 := Nat.le_of_dvd (by norm_num) hd4
    have hp2' := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · norm_num at hd4
    · norm_num at hp
  have hsum : π + star π = ⟨2 * π.re, 0⟩ := by ext <;> simp; ring
  have hdiff : π - star π = ⟨0, 2 * π.im⟩ := by ext <;> simp; ring
  have d1 : (p : ℤ) ∣ 4 * π.re ^ 2 := by
    have := norm_dvd_of_dvd (dvd_add (dvd_refl π) hd)
    rw [hsum, h, norm_eq_sq_add_sq] at this
    simpa [mul_pow] using this
  have d2 : (p : ℤ) ∣ 4 * π.im ^ 2 := by
    have := norm_dvd_of_dvd (dvd_sub (dvd_refl π) hd)
    rw [hdiff, h, norm_eq_sq_add_sq] at this
    simpa [mul_pow] using this
  have hre : (p : ℤ) ∣ π.re := hpZ.dvd_of_dvd_pow ((hpZ.dvd_or_dvd d1).resolve_left h4)
  have him : (p : ℤ) ∣ π.im := hpZ.dvd_of_dvd_pow ((hpZ.dvd_or_dvd d2).resolve_left h4)
  obtain ⟨a, ha⟩ := hre
  obtain ⟨c, hc⟩ := him
  have hN := h
  rw [norm_eq_sq_add_sq, ha, hc] at hN
  have : (p : ℤ) * (p * (a ^ 2 + c ^ 2)) = p * 1 := by linear_combination hN
  have h1 : (p : ℤ) * (a ^ 2 + c ^ 2) = 1 :=
    mul_left_cancel₀ (by exact_mod_cast hp.ne_zero) this
  have : (p : ℤ) ∣ 1 := ⟨_, h1.symm⟩
  exact hpZ.not_dvd_one this

/-- **The prime powers** (proof of Theorem 30.12): `r(p^k) = 4 (k + 1)` for a prime
`p ≡ 1 (mod 4)`. With `p = π π̄`, an element of norm `p^(k+1)` is `π z'` or a unit times
`π̄^(k+1)`. -/
theorem card_repG_prime_pow {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (k : ℕ) :
    (repG (p ^ k)).card = 4 * (k + 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  set π : GaussianInt := ⟨a, b⟩
  have hπN : π.norm = p := by rw [norm_eq_sq_add_sq]; push_cast [← hab]; rfl
  have hπ : Prime π := prime_of_norm_prime hp hπN
  have hst : ¬ π ∣ star π := not_dvd_star hp (by omega) hπN
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hsπN : (star π).norm = p := by rw [Zsqrtd.norm_conj, hπN]
  have hpπ : (p : GaussianInt) = π * star π := (mul_star_of_norm hπN).symm
  -- an element of norm `p^j` not divisible by `π` is a unit times `π̄^j`
  have key : ∀ j (z : GaussianInt), z.norm = (p ^ j : ℕ) → ¬ π ∣ z →
      ∃ u : GaussianInt, u.norm = 1 ∧ z = u * star π ^ j := by
    intro j
    induction j with
    | zero => intro z hz _; exact ⟨z, by simpa using hz, by simp⟩
    | succ j ih =>
      intro z hz hπz
      have h1 : π ∣ z * star z := by
        rw [mul_star_of_norm hz, pow_succ', Nat.cast_mul, hpπ, mul_assoc]
        exact dvd_mul_right _ _
      obtain ⟨c, hc⟩ := (hπ.dvd_or_dvd h1).resolve_left hπz
      have hzc : z = star π * star c := by
        have := congrArg star hc
        rw [star_star, star_mul] at this
        rw [this, mul_comm]
      have hcN : (star c).norm = (p ^ j : ℕ) := by
        have := congrArg Zsqrtd.norm hzc
        rw [Zsqrtd.norm_mul, hsπN, hz] at this
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        push_cast at this ⊢
        rw [pow_succ'] at this
        exact (mul_left_cancel₀ hp0 this).symm
      have hπc : ¬ π ∣ star c := fun hd => hπz (hzc ▸ dvd_mul_of_dvd_right hd _)
      obtain ⟨u, hu, hcu⟩ := ih (star c) hcN hπc
      exact ⟨u, hu, by rw [hzc, hcu]; ring⟩
  induction k with
  | zero => rw [pow_zero, card_repG, card_repZ_one]
  | succ k ih =>
    rw [← Finset.card_filter_add_card_filter_not (s := repG (p ^ (k + 1))) (fun z => π ∣ z)]
    have hA : (repG (p ^ (k + 1))).filter (fun z => π ∣ z) = (repG (p ^ k)).image (π * ·) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_image, mem_repG]
      constructor
      · rintro ⟨hz, z', rfl⟩
        refine ⟨z', ?_, rfl⟩
        rw [Zsqrtd.norm_mul, hπN] at hz
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        push_cast at hz ⊢
        rw [pow_succ'] at hz
        exact mul_left_cancel₀ hp0 hz
      · rintro ⟨z', hz', rfl⟩
        refine ⟨?_, dvd_mul_right _ _⟩
        rw [Zsqrtd.norm_mul, hπN, hz']; push_cast; ring
    have hB : (repG (p ^ (k + 1))).filter (fun z => ¬ π ∣ z) =
        (repG 1).image (· * star π ^ (k + 1)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_image, mem_repG]
      constructor
      · rintro ⟨hz, hπz⟩
        obtain ⟨u, hu, rfl⟩ := key (k + 1) z hz hπz
        exact ⟨u, by rw [hu]; rfl, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨?_, fun hd => hst ?_⟩
        · rw [Zsqrtd.norm_mul, norm_pow', hsπN, hu]; push_cast; ring
        · have huu : star u * u = 1 := by rw [mul_comm, mul_star_of_norm hu]; simp
          have : π ∣ star π ^ (k + 1) := by
            have := dvd_mul_of_dvd_right hd (star u)
            rwa [← mul_assoc, huu, one_mul] at this
          exact hπ.dvd_of_dvd_pow this
    rw [hA, hB, Finset.card_image_of_injective _ (mul_right_injective₀ hπ0), ih,
      Finset.card_image_of_injective _ (mul_left_injective₀ (pow_ne_zero _ (star_ne_zero.2 hπ0))),
      card_repG, card_repZ_one]
    ring

/-- `r(n) = 4 τ(n)` for odd `n` whose prime factors are all `≡ 1 (mod 4)`. -/
theorem card_repG_odd : ∀ n : ℕ, 1 ≤ n → Odd n → (∀ q, q.Prime → q ∣ n → q % 4 = 1) →
    (repG n).card = 4 * n.divisors.card := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ _ h4
    rw [card_repG_prime_pow hp (h4 p hp (dvd_pow_self p hk.ne')), Nat.divisors_prime_pow hp,
      Finset.card_map, Finset.card_range]
  | zero => intro h; omega
  | one => intro _ _ _; simp [card_repG, card_repZ_one]
  | coprime a b ha hb hab iha ihb =>
    intro _ hodd h4
    have hoa : Odd a := (Nat.odd_mul.1 hodd).1
    have hob : Odd b := (Nat.odd_mul.1 hodd).2
    have h1 := card_repG_mul (by omega) hab
    rw [iha (by omega) hoa (fun q hq hqa => h4 q hq (dvd_mul_of_dvd_left hqa b)),
      ihb (by omega) hob (fun q hq hqb => h4 q hq (dvd_mul_of_dvd_right hqb a))] at h1
    rw [Nat.Coprime.card_divisors_mul hab]
    nlinarith

/-- `r(2 n) = r(n)` for odd `n`. -/
theorem card_repG_two_mul {n : ℕ} (hodd : Odd n) : (repG (2 * n)).card = (repG n).card := by
  have h := card_repG_mul (m := 2) (n := n) (by norm_num) (Nat.coprime_two_left.2 hodd)
  rw [card_repG 2, card_repZ_two] at h
  omega

/-- Every odd prime factor of `b^2 + 1` is `≡ 1 (mod 4)`: `-1` is a square modulo it. -/
lemma mod_four_of_dvd_sq_add_one {q b : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : q ∣ b ^ 2 + 1) :
    q % 4 = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hsq : IsSquare (-1 : ZMod q) := by
    refine ⟨(b : ZMod q), ?_⟩
    have : ((b ^ 2 + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    push_cast at this
    linear_combination -this
  have h3 := (ZMod.exists_sq_eq_neg_one_iff).1 hsq
  have hodd := hq.eq_one_or_self_of_dvd 2
  rcases Nat.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
  · exfalso
    rcases hodd ⟨k, by omega⟩ with h1 | h1 <;> omega
  · omega

lemma sq_emod_four (a : ℤ) : (Odd a → a ^ 2 % 4 = 1) ∧ (¬ Odd a → a ^ 2 % 4 = 0) := by
  rcases Int.even_or_odd' a with ⟨k, rfl | rfl⟩
  · refine ⟨fun h => absurd h (by simp [parity_simps]), fun _ => ?_⟩
    have : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
    omega
  · refine ⟨fun _ => ?_, fun h => absurd ⟨k, rfl⟩ h⟩
    have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
    omega

/-- The representations with `B` odd and positive. -/
def oddPos (n : ℕ) : Finset (ℤ × ℤ) := (repZ n).filter fun p => Odd p.2 ∧ 0 < p.2

/-- Half of the representations with `B` odd have `B > 0`. -/
lemma card_odd_eq_two_mul (n : ℕ) :
    ((repZ n).filter fun p => Odd p.2).card = 2 * (oddPos n).card := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (repZ n).filter fun p => Odd p.2) (fun p => 0 < p.2)
  have hneg : (((repZ n).filter fun p => Odd p.2).filter fun p => ¬ 0 < p.2).card =
      (((repZ n).filter fun p => Odd p.2).filter fun p => 0 < p.2).card := by
    refine Finset.card_nbij' (fun p => (p.1, -p.2)) (fun p => (p.1, -p.2)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, mem_repZ] at hp ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      refine ⟨⟨by rw [neg_sq]; exact h1, h2.neg⟩, ?_⟩
      obtain ⟨j, hj⟩ := h2
      omega
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, mem_repZ] at hp ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      exact ⟨⟨by rw [neg_sq]; exact h1, h2.neg⟩, by omega⟩
    · intro p _; simp
    · intro p _; simp
  have hfil : (((repZ n).filter fun p => Odd p.2).filter fun p => 0 < p.2) = oddPos n := by
    rw [oddPos, Finset.filter_filter]
  rw [hfil] at hsplit hneg
  omega

/-- The count behind Theorem 30.12: `b^2 + 1 = A^2 + B^2` has exactly `τ(b^2 + 1)` solutions
with `B` odd and positive. -/
theorem card_oddPos_sq_add_one (b : ℕ) : (oddPos (b ^ 2 + 1)).card = (b ^ 2 + 1).divisors.card := by
  set N := b ^ 2 + 1 with hN
  have hodd2 := card_odd_eq_two_mul N
  rcases Nat.even_or_odd b with hb | hb
  · -- `N` odd: exactly one of `A, B` is odd, and swapping them halves the count
    have hNodd : Odd N := by
      obtain ⟨k, rfl⟩ := hb; exact ⟨2 * k ^ 2, by rw [hN]; ring⟩
    have hprimes : ∀ q, q.Prime → q ∣ N → q % 4 = 1 := by
      intro q hq hqN
      refine mod_four_of_dvd_sq_add_one hq ?_ hqN
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 hqN)
    have hall := card_repG_odd N (by omega) hNodd hprimes
    rw [card_repG] at hall
    have hsplit := Finset.card_filter_add_card_filter_not (s := repZ N) (fun p => Odd p.2)
    have hswap : ((repZ N).filter fun p => ¬ Odd p.2).card =
        ((repZ N).filter fun p => Odd p.2).card := by
      refine Finset.card_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, mem_repZ] at hp ⊢
        obtain ⟨h1, h2⟩ := hp
        refine ⟨by linarith, ?_⟩
        have hNo : ((N : ℕ) : ℤ) % 2 = 1 := by
          obtain ⟨k, hk⟩ := hNodd; rw [hk]; push_cast; omega
        have e1 := sq_emod_four p.1
        have e2 := sq_emod_four p.2
        by_contra h3
        have := e1.2 h3; have := e2.2 h2
        omega
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, mem_repZ] at hp ⊢
        obtain ⟨h1, h2⟩ := hp
        refine ⟨by linarith, fun h3 => ?_⟩
        have hNo : ((N : ℕ) : ℤ) % 2 = 1 := by
          obtain ⟨k, hk⟩ := hNodd; rw [hk]; push_cast; omega
        have := (sq_emod_four p.2).1 h2
        have := (sq_emod_four p.1).1 h3
        omega
      · intro p _; simp
      · intro p _; simp
    omega
  · -- `N = 2 M` with `M` odd: `A` and `B` are both odd
    obtain ⟨k, rfl⟩ := hb
    set M := 2 * k ^ 2 + 2 * k + 1 with hM
    have hNM : N = 2 * M := by rw [hN, hM]; ring
    have hMo : Odd M := ⟨k ^ 2 + k, by rw [hM]; ring⟩
    have hprimes : ∀ q, q.Prime → q ∣ M → q % 4 = 1 := by
      intro q hq hqM
      refine mod_four_of_dvd_sq_add_one (b := 2 * k + 1) hq ?_ ?_
      · rintro rfl; exact (Nat.not_even_iff_odd.2 hMo) (even_iff_two_dvd.2 hqM)
      · rw [← hN, hNM]; exact dvd_mul_of_dvd_right hqM 2
    have hall := card_repG_odd M (by omega) hMo hprimes
    rw [← card_repG_two_mul hMo, ← hNM, card_repG] at hall
    have hallodd : (repZ N).filter (fun p => Odd p.2) = repZ N := by
      apply Finset.filter_true_of_mem
      intro p hp
      rw [mem_repZ] at hp
      have hN4 : ((N : ℕ) : ℤ) % 4 = 2 := by rw [hNM, hM]; push_cast; ring_nf; omega
      by_contra h2
      have e2 := (sq_emod_four p.2).2 h2
      rcases em (Odd p.1) with h1 | h1
      · have := (sq_emod_four p.1).1 h1; omega
      · have := (sq_emod_four p.1).2 h1; omega
    rw [hallodd] at hodd2
    have hτ : N.divisors.card = 2 * M.divisors.card := by
      rw [hNM, Nat.Coprime.card_divisors_mul (Nat.coprime_two_left.2 hMo),
        Nat.Prime.divisors Nat.prime_two, Finset.card_pair (by norm_num : (1 : ℕ) ≠ 2)]
    omega

/-- The 2-digit narcissistic numbers of base `b`, as pairs `(s1, s0)`. -/
def narcSet (b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range b ×ˢ Finset.range b).filter fun q => IsNarc2 b q.1 q.2

/-- **Theorem 30.12** (section 30.3.1). For every `b ≥ 2`, base `b` has exactly
`τ(b^2 + 1) - 2` two-digit narcissistic numbers. -/
theorem theorem30_12 {b : ℕ} (hb : 2 ≤ b) : (narcSet b).card = (b ^ 2 + 1).divisors.card - 2 := by
  set N := b ^ 2 + 1 with hN
  set φ : ℕ × ℕ → ℤ × ℤ := fun q => (2 * q.1 - b, 2 * q.2 - 1) with hφ
  have hφinj : Function.Injective φ := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    ext <;> simp only <;> omega
  have hNZ : ((N : ℕ) : ℤ) = (b : ℤ) ^ 2 + 1 := by rw [hN]; push_cast; ring
  -- the image of the narcissistic numbers: `B` odd, `B > 0`, `B ≠ 1`
  have himage : (narcSet b).image φ = (oddPos N).filter fun p => p.2 ≠ 1 := by
    ext ⟨A, B⟩
    simp only [Finset.mem_image, Finset.mem_filter, narcSet, oddPos, mem_repZ, Finset.mem_product,
      Finset.mem_range, Prod.exists, φ, Prod.mk.injEq]
    constructor
    · rintro ⟨s1, s0, ⟨⟨-, -⟩, hn⟩, rfl, rfl⟩
      obtain ⟨h0, hsq⟩ := (isNarc2_iff b s1 s0).1 hn
      refine ⟨⟨by rw [hNZ]; exact hsq, ⟨s0 - 1, by omega⟩, by omega⟩, by omega⟩
    · rintro ⟨⟨hsq, ⟨j, hj⟩, hB0⟩, hB1⟩
      rw [hNZ] at hsq
      have hj1 : 1 ≤ j := by omega
      -- `A ≡ b (mod 2)` and `|A| < b`
      have hAb : (A + b) % 2 = 0 := by
        have e1 := sq_emod_four A
        have e2 := sq_emod_four (b : ℤ)
        have e3 := (sq_emod_four B).1 ⟨j, hj⟩
        rcases em (Odd A) with h1 | h1 <;> rcases em (Odd (b : ℤ)) with h2 | h2
        · obtain ⟨u, hu⟩ := h1; obtain ⟨v, hv⟩ := h2; omega
        · have := e1.1 h1; have := e2.2 h2; omega
        · have := e1.2 h1; have := e2.1 h2; omega
        · rw [Int.not_odd_iff_even] at h1 h2
          obtain ⟨u, hu⟩ := h1; obtain ⟨v, hv⟩ := h2; omega
      have hb0 : (0 : ℤ) ≤ b := by positivity
      have hA2 : A ^ 2 < (b : ℤ) ^ 2 := by nlinarith
      have hA : |A| < b := abs_lt_of_sq_lt_sq hA2 hb0
      rw [abs_lt] at hA
      have hBb : B ≤ b := by nlinarith
      obtain ⟨k, hk⟩ : ∃ k, A + b = 2 * k := ⟨(A + b) / 2, by omega⟩
      refine ⟨k.toNat, (j + 1).toNat, ⟨⟨by omega, by omega⟩, ?_⟩, by omega, by omega⟩
      refine (isNarc2_iff b _ _).2 ⟨by omega, ?_⟩
      have e1 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      have e2 : (((j + 1).toNat : ℕ) : ℤ) = j + 1 := Int.toNat_of_nonneg (by omega)
      rw [e1, e2]
      have : 2 * k - b = A := by omega
      rw [this, show 2 * (j + 1) - 1 = B by omega]
      exact hsq
  have hcard1 : ((oddPos N).filter fun p => p.2 ≠ 1).card + 2 = (oddPos N).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := oddPos N) (fun p => p.2 ≠ 1)
    have hone : ((oddPos N).filter fun p => ¬ p.2 ≠ 1) = {((b : ℤ), 1), (-(b : ℤ), 1)} := by
      ext ⟨A, B⟩
      simp only [Finset.mem_filter, oddPos, mem_repZ, not_not, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hsq, -, -⟩, rfl⟩
        rw [hNZ] at hsq
        have : (A - b) * (A + b) = 0 := by linear_combination hsq
        rcases mul_eq_zero.1 this with h | h
        · left; exact ⟨by linarith, rfl⟩
        · right; exact ⟨by linarith, rfl⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨by rw [hNZ]; ring, ⟨0, by ring⟩, by norm_num⟩, rfl⟩
        · exact ⟨⟨by rw [hNZ]; ring, ⟨0, by ring⟩, by norm_num⟩, rfl⟩
    have hb2 : ((b : ℤ), (1 : ℤ)) ≠ (-(b : ℤ), 1) := by
      simp only [ne_eq, Prod.mk.injEq, and_true]; omega
    rw [hone, Finset.card_pair hb2] at hsplit
    exact hsplit
  have h := card_oddPos_sq_add_one b
  rw [← hN] at h
  rw [← Finset.card_image_of_injective _ hφinj, himage]
  omega

/-- **Corollary 30.13 (2)** (section 30.3.1). An even base `b ≥ 2` has a 2-digit narcissistic
number exactly when `b^2 + 1` is composite. -/
theorem corollary30_13_two_iff {b : ℕ} (hb : 2 ≤ b) (heven : Even b) :
    (∃ s1 s0, IsNarc2 b s1 s0) ↔ ¬ (b ^ 2 + 1).Prime := by
  constructor
  · rintro ⟨s1, s0, h⟩ hp
    exact corollary30_13_two heven hp h
  · intro hnp
    have hne1 : b ^ 2 + 1 ≠ 1 := by have : 0 < b ^ 2 := by positivity
                                    omega
    set d := (b ^ 2 + 1).minFac
    have hd1 : 1 < d := (Nat.minFac_prime hne1).one_lt
    have hd2 : d < b ^ 2 + 1 :=
      lt_of_le_of_ne (Nat.minFac_le (by omega)) fun h => hnp (h ▸ Nat.minFac_prime hne1)
    have hdN : d ∣ b ^ 2 + 1 := Nat.minFac_dvd _
    have h3 : 3 ≤ (b ^ 2 + 1).divisors.card := by
      have hsub : ({1, d, b ^ 2 + 1} : Finset ℕ) ⊆ (b ^ 2 + 1).divisors := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Nat.mem_divisors]
        rcases hx with rfl | rfl | rfl
        · exact ⟨one_dvd _, by omega⟩
        · exact ⟨hdN, by omega⟩
        · exact ⟨dvd_rfl, by omega⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)] at this
      exact this
    have hc := theorem30_12 hb
    have : 0 < (narcSet b).card := by omega
    obtain ⟨⟨s1, s0⟩, hq⟩ := Finset.card_pos.1 this
    exact ⟨s1, s0, (Finset.mem_filter.1 hq).2⟩

end Munchausen
