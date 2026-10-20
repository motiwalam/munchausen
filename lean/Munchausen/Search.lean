import Munchausen.Congruences

/-!
# Near-solutions and search (chapters 26 and 27)

* Lemma 26.1, the swap lemma: rearranging digits keeps `F` and moves the value by a multiple
  of `b - 1`; a transposition moves it by `(x - y)(b^j - b^i)` (also in base `-b`,
  Lemma 26.4);
* Corollary 26.2: when a transposition keeps the offset class modulo `2(b-1)`;
* Proposition 26.10: the image of `c ↦ S(c)` is the same under both conventions;
* Proposition 27.8 and Corollary 27.9: which digit values fix the bottom digits of `S`;
* Lemma 27.3 and Theorem 27.5 in the interval oracle: the fooling-set bound for certificates
  of emptiness, with the claim of its proof.
-/

namespace Munchausen

/-! ### Chapter 26: the swap lemma -/

/-- **Lemma 26.1** (section 26.1.2), the multiset part. Rearranging the digits does not change
the weight sum, and changes the value by a multiple of `b - 1`. -/
theorem swap_lemma_perm {b m : ℕ} (hb : 1 ≤ b) {s s' : List ℕ} (h : s.Perm s') :
    Fs m s' = Fs m s ∧ P b s' ≡ P b s [MOD b - 1] := by
  refine ⟨(h.map (w m)).sum_eq.symm, ?_⟩
  have h1 := P_modEq_sum hb s
  have h2 := P_modEq_sum hb s'
  rw [← h.sum_eq] at h2
  exact h2.trans h1.symm

/-- **Lemma 26.1** (section 26.1.2), the transposition, in any commutative ring (so also for
negative bases, Lemma 26.4). Exchanging the digit `y` at position `j` and the digit `x` at
position `i < j` changes the value by `(x - y)(r^j - r^i)`. -/
theorem swap_lemma {R : Type*} [CommRing R] (r : R) (A B C : List ℕ) (x y : ℕ) :
    P r (A ++ x :: (B ++ y :: C)) - P r (A ++ y :: (B ++ x :: C)) =
      ((x : R) - y) * (r ^ (B.length + 1 + C.length) - r ^ C.length) := by
  simp only [P_append, P_cons, List.length_cons, List.length_append]
  ring

/-- The last two digits (Lemma 26.1): exchanging them moves the value by `(x - y)(b - 1)`; in
base `-b` (Lemma 26.4) by `-(x - y)(b + 1)`. -/
theorem swap_last_two {R : Type*} [CommRing R] (r : R) (A : List ℕ) (x y : ℕ) :
    P r (A ++ [x, y]) - P r (A ++ [y, x]) = ((x : R) - y) * (r - 1) := by
  have := swap_lemma r A [] [] x y
  simpa using this

/-! ### Corollary 26.2: the class of the moved offset -/

/-- The repunit `R_s = 1 + b + ... + b^(s-1)` and `b^(i+s) - b^i = b^i (b - 1) R_s`
(Lemma 26.1). -/
lemma repunit_identity (b : ℤ) (i s : ℕ) :
    b ^ (i + s) - b ^ i = b ^ i * (b - 1) * ∑ k ∈ Finset.range s, b ^ k := by
  rw [mul_assoc, mul_comm (b - 1), geom_sum_mul, pow_add]; ring

/-- **Corollary 26.2** (section 26.1.2). A transposition that moves `D` by
`(x - y)(b^(i+s) - b^i)` keeps `D` in its class modulo `2(b-1)` exactly when
`(x - y) b^i R_s` is even. -/
theorem corollary26_2 {b : ℤ} (hb : 2 ≤ b) (x y : ℤ) (i s : ℕ) :
    2 * (b - 1) ∣ (x - y) * (b ^ (i + s) - b ^ i) ↔
      2 ∣ (x - y) * b ^ i * ∑ k ∈ Finset.range s, b ^ k := by
  rw [repunit_identity]
  have e : (x - y) * (b ^ i * (b - 1) * ∑ k ∈ Finset.range s, b ^ k) =
      ((x - y) * b ^ i * ∑ k ∈ Finset.range s, b ^ k) * (b - 1) := by ring
  rw [e]
  exact mul_dvd_mul_iff_right (by omega)

/-- In an odd base, `R_s ≡ s (mod 2)`. -/
lemma repunit_mod_two {b : ℤ} (hb : Odd b) (s : ℕ) :
    (∑ k ∈ Finset.range s, b ^ k) % 2 = (s : ℤ) % 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Int.add_emod, ih]
    have : b ^ s % 2 = 1 := Int.odd_iff.1 (hb.pow)
    rw [this]; push_cast; omega

/-- **Corollary 26.2**, odd bases: the class is kept exactly when `(x - y)(j - i)` is even. -/
theorem corollary26_2_odd {b : ℤ} (hb : 2 ≤ b) (hodd : Odd b) (x y : ℤ) (i s : ℕ) :
    2 * (b - 1) ∣ (x - y) * (b ^ (i + s) - b ^ i) ↔ 2 ∣ (x - y) * s := by
  rw [corollary26_2 hb, Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, Int.mul_emod,
    Int.mul_emod (x - y), repunit_mod_two hodd, Int.odd_iff.1 hodd.pow, mul_one,
    Int.emod_emod_of_dvd _ (dvd_refl 2), ← Int.mul_emod]

/-! ### Proposition 26.10: the image of `F` -/

/-- **Proposition 26.10 (2)** (section 26.7.1). Under `0^0 = 0` zeros weigh nothing; under
`0^0 = 1` the digits 0 and 1 weigh the same. -/
theorem prop26_10_two (s : List ℕ) :
    Fs 0 s = Fs 0 (s.filter (· ≠ 0)) ∧ Fs 1 s = Fs 0 (s.map fun d => if d = 0 then 1 else d) := by
  constructor
  · induction s with
    | nil => rfl
    | cons d t ih =>
      by_cases hd : d = 0
      · subst hd; simp [ih]
      · simp [List.filter_cons, hd, ih]
  · induction s with
    | nil => rfl
    | cons d t ih =>
      by_cases hd : d = 0
      · subst hd; simp [ih]
      · simp [hd, ih, w_of_ne_zero _ hd]

/-- The multisets of Proposition 15.1: 1 to `b` digits below `b`, with a nonzero digit. -/
def ImageSet (b m : ℕ) : Set ℕ :=
  {N | ∃ c : List ℕ, 1 ≤ c.length ∧ c.length ≤ b ∧ (∀ d ∈ c, d < b) ∧ (∃ d ∈ c, d ≠ 0) ∧
    N = Fs m c}

/-- **Proposition 26.10 (1)** (section 26.7.1). The image of `c ↦ S(c)` is the same under both
conventions. -/
theorem prop26_10_one {b : ℕ} (hb : 2 ≤ b) : ImageSet b 0 = ImageSet b 1 := by
  ext N
  constructor
  · rintro ⟨c, h1, h2, h3, ⟨d, hd, hd0⟩, rfl⟩
    -- drop the zeros: a zero-free multiset weighs the same under both conventions
    refine ⟨c.filter (· ≠ 0), ?_, ?_, ?_, ?_, ?_⟩
    · exact List.length_pos_of_mem (List.mem_filter.2 ⟨hd, by simpa using hd0⟩)
    · exact (List.length_filter_le _ _).trans h2
    · intro e he; exact h3 e (List.mem_of_mem_filter he)
    · exact ⟨d, List.mem_filter.2 ⟨hd, by simpa using hd0⟩, hd0⟩
    · rw [(prop26_10_two c).1, (prop26_10_two (c.filter (· ≠ 0))).2]
      congr 1
      have hfix : ∀ e ∈ c.filter (· ≠ 0), (if e = 0 then 1 else e) = e := by
        intro e he
        have := (List.mem_filter.1 he).2
        simp only [ne_eq, decide_eq_true_eq] at this
        simp [this]
      rw [List.map_congr_left hfix, List.map_id']
  · rintro ⟨c, h1, h2, h3, ⟨d, hd, hd0⟩, rfl⟩
    refine ⟨c.map fun d => if d = 0 then 1 else d, by simpa using h1, by simpa using h2, ?_, ?_,
      (prop26_10_two c).2⟩
    · intro e he
      obtain ⟨d', hd', rfl⟩ := List.mem_map.1 he
      have := h3 d' hd'
      split_ifs <;> omega
    · exact ⟨if d = 0 then 1 else d, List.mem_map.2 ⟨d, hd, rfl⟩, by split_ifs <;> omega⟩

/-! ### Chapter 27: bottom digits -/

/-- **Proposition 27.8** (section 27.4.1). For `b, v ≥ 1`, `b^L` divides `v^v` exactly when
`L v_p(b) ≤ v v_p(v)` for every prime `p`. -/
theorem prop27_8 {b v L : ℕ} (hb : 1 ≤ b) (hv : 1 ≤ v) :
    b ^ L ∣ v ^ v ↔ ∀ p, L * b.factorization p ≤ v * v.factorization p := by
  rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity), Nat.factorization_pow,
    Nat.factorization_pow, Finsupp.le_def]
  simp

/-- **Proposition 27.8**, the values prime to `b` (section 27.4.1). For `L ≥ 1` and `b ≥ 2`,
a value `v ≥ 1` prime to `b` never has `b^L ∣ w(v)`, in particular `v = 1`. (`v = 0` under
`0^0 = 1` weighs 1 and never has it either; see `corollary27_9`.) -/
theorem not_dvd_w_of_coprime {b v L m : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L) (hv : Nat.Coprime v b) :
    ¬ b ^ L ∣ w m v := by
  intro h
  rcases Nat.eq_zero_or_pos v with rfl | hv0
  · simp at hv; omega
  · rw [w_of_ne_zero m hv0.ne'] at h
    have hcop : Nat.Coprime (v ^ v) (b ^ L) := Nat.Coprime.pow _ _ hv
    have := Nat.Coprime.eq_one_of_dvd hcop.symm h
    have : b ≤ b ^ L := Nat.le_self_pow (by omega) b
    omega

/-- **Corollary 27.9** (section 27.4.1). In the top-down order the values below `k` are the
unrevealed ones. The bottom `L ≥ 1` digits of `S` are known only when every unrevealed value
`v` has `b^L ∣ w(v)`; this forces `k ≤ 1` (the value 1 is revealed), and under `0^0 = 1` even
`k = 0`. So a bottom check never applies before the leaves of a top-down tree. -/
theorem corollary27_9 {b L m k : ℕ} (hb : 2 ≤ b) (hL : 1 ≤ L)
    (h : ∀ v < k, b ^ L ∣ w m v) : k ≤ 1 ∧ (m = 1 → k = 0) := by
  constructor
  · by_contra hk
    exact not_dvd_w_of_coprime hb hL (Nat.coprime_one_left b) (h 1 (by omega))
  · intro hm
    by_contra hk
    have h0 := h 0 (by omega)
    rw [w_zero, hm] at h0
    have : b ^ L ≤ 1 := Nat.le_of_dvd one_pos h0
    have : b ≤ b ^ L := Nat.le_self_pow (by omega) b
    omega

/-! ### Theorem 27.5: certificates of emptiness, abstract form -/

/-- A cylinder `(R, c_R)` of count vectors over the digit values `Fin b` (section 27.3.1): the
vectors whose counts on `R` are the given ones. -/
structure Cylinder (b : ℕ) where
  /-- the revealed values -/
  R : Finset (Fin b)
  /-- their counts -/
  cR : Fin b → ℕ

/-- A count vector lies in a cylinder when it has the cylinder's counts on `R`. -/
def Cylinder.Mem {b : ℕ} (x : Cylinder b) (c : Fin b → ℕ) : Prop := ∀ v ∈ x.R, c v = x.cR v

/-- The fooling-set bound: if every set of a cover meets the elements of `G` only within one
class of `κ`, the cover has at least as many sets as `κ` takes values on `G`. -/
theorem card_image_le_of_fooling {X K ι : Type*} [DecidableEq K] (κ : X → K) (G : Finset X)
    (A : ι → Set X) (cover : Finset ι) (hcover : ∀ c ∈ G, ∃ i ∈ cover, c ∈ A i)
    (hfool : ∀ i ∈ cover, ∀ c ∈ G, ∀ c' ∈ G, c ∈ A i → c' ∈ A i → κ c = κ c') :
    (G.image κ).card ≤ cover.card := by
  classical
  rcases G.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · simp
  obtain ⟨i₀, -, -⟩ := hcover c₀ hc₀
  have : Nonempty X := ⟨c₀⟩
  have : Nonempty ι := ⟨i₀⟩
  -- a representative of each class, and a set of the cover that contains it
  have hrep : ∀ k ∈ G.image κ, ∃ c ∈ G, κ c = k := fun k hk => by simpa using hk
  choose! rep hrepG hrepκ using hrep
  have hset : ∀ k ∈ G.image κ, ∃ i ∈ cover, rep k ∈ A i := fun k hk =>
    hcover (rep k) (hrepG k hk)
  choose! sel hselC hselA using hset
  refine Finset.card_le_card_of_injOn sel (fun k hk => hselC k hk) ?_
  intro k hk k' hk' h
  have := hfool (sel k) (hselC k hk) (rep k) (hrepG k hk) (rep k') (hrepG k' hk')
    (hselA k hk) (h ▸ hselA k' hk')
  rw [← hrepκ k hk, ← hrepκ k' hk', this]

/-- **Theorem 27.5** (section 27.3.1), abstract form. Let `G` be a finite set of count vectors
and `θ` a threshold on them. Assume the claim of the proof: a cylinder of the certificate that
contains `c ∈ G` and another vector reveals every value `≥ θ(c)`. Then a certificate covering
`G` has at least `N_k` cylinders, where `N_k` counts the restrictions `c|V_k` to the values
`≥ k` of the `c ∈ G` with `θ(c) ≤ k`. -/
theorem theorem27_5 {b : ℕ} (k : ℕ) (G : Finset (Fin b → ℕ)) (θ : (Fin b → ℕ) → ℕ)
    (cert : Finset (Cylinder b)) (hcover : ∀ c ∈ G, ∃ x ∈ cert, x.Mem c)
    (hclaim : ∀ x ∈ cert, ∀ c ∈ G, ∀ c', x.Mem c → x.Mem c' → c' ≠ c →
      ∀ v : Fin b, θ c ≤ v → v ∈ x.R) :
    ((G.filter fun c => θ c ≤ k).image fun c (v : {v : Fin b // k ≤ (v : ℕ)}) => c v).card ≤
      cert.card := by
  classical
  apply card_image_le_of_fooling _ _ (fun x => {c | x.Mem c}) cert
  · intro c hc
    exact hcover c (Finset.mem_filter.1 hc).1
  · intro x hx c hc c' hc' hxc hxc'
    obtain ⟨hcG, hck⟩ := Finset.mem_filter.1 hc
    funext v
    by_cases hcc : c' = c
    · rw [hcc]
    have hv : (v : Fin b) ∈ x.R := hclaim x hx c hcG c' hxc hxc' hcc v (hck.trans v.2)
    simp only [Set.mem_ofPred_eq] at hxc hxc'
    rw [hxc v hv, hxc' v hv]

/-! ### Lemma 26.3: the fibre of a multiset -/

/-- **Lemma 26.3** (the fibre, section 26.1.2). A rearrangement `s` of the multiset `c` is a
near-solution at offset `D` exactly when its value is `S(c) + D`, where `S(c) = F(c)`
depends only on the multiset. -/
theorem lemma26_3 {b m D : ℕ} {c s : List ℕ} (h : s.Perm c) :
    P b s = Fs m s + D ↔ P b s = Fs m c + D := by
  rw [show Fs m s = Fs m c from (h.map (w m)).sum_eq]

/-- **Lemma 26.3**, uniqueness: each pair `(c, D)` gives at most one near-solution. Two
rearrangements of `c` with digits below `b` that are near-solutions at the same offset are
equal. -/
theorem lemma26_3_unique {b m D : ℕ} (hb : 2 ≤ b) {c s s' : List ℕ} (hs : s.Perm c)
    (hs' : s'.Perm c) (hdig : ∀ d ∈ c, d < b) (h1 : P b s = Fs m s + D)
    (h2 : P b s' = Fs m s' + D) : s = s' := by
  rw [lemma26_3 hs] at h1
  rw [lemma26_3 hs'] at h2
  have hval : Nat.ofDigits b s.reverse = Nat.ofDigits b s'.reverse := by
    rw [← P_eq_ofDigits, ← P_eq_ofDigits, h1, h2]
  have := Nat.ofDigits_inj_of_len_eq (by omega)
    (by rw [List.length_reverse, List.length_reverse, hs.length_eq, hs'.length_eq])
    (fun d hd => hdig d (hs.mem_iff.1 (List.mem_reverse.1 hd)))
    (fun d hd => hdig d (hs'.mem_iff.1 (List.mem_reverse.1 hd))) hval
  exact List.reverse_injective this

/-! ### Theorem 27.5 in the interval oracle -/

section Oracle

variable {b : ℕ}

/-- The digit `j` from the top of a `d`-digit number `n` (`j = 0` is the leading digit). -/
def topDigit (b d n j : ℕ) : ℕ := n / b ^ (d - 1 - j) % b

/-- How often the value `v` occurs among the top `l` digits of `n`. -/
def prefixCount (b d n l v : ℕ) : ℕ :=
  ((Finset.range l).filter fun j => topDigit b d n j = v).card

/-- How many of the top `l` digits of `n` have a value outside `R`. -/
def outsideCount (b d n l : ℕ) (R : Finset (Fin b)) : ℕ :=
  ((Finset.range l).filter fun j => ∀ v ∈ R, topDigit b d n j ≠ v).card

/-- The weight sum `S(c)` of a count vector. -/
def wsum (wt : Fin b → ℕ) (c : Fin b → ℕ) : ℕ := ∑ v, c v * wt v

namespace Cylinder

/-- The values outside `R`. -/
def U (x : Cylinder b) : Finset (Fin b) := Finset.univ.filter (· ∉ x.R)

/-- The number `rf` of free copies. -/
def rf (d : ℕ) (x : Cylinder b) : ℕ := d - ∑ v ∈ x.R, x.cR v

/-- The weight `t` of the revealed copies. -/
def t (wt : Fin b → ℕ) (x : Cylinder b) : ℕ := ∑ v ∈ x.R, x.cR v * wt v

/-- The least weight outside `R`. -/
def minU (wt : Fin b → ℕ) (x : Cylinder b) : ℕ := if h : x.U.Nonempty then x.U.inf' h wt else 0

/-- The largest weight outside `R`. -/
def maxU (wt : Fin b → ℕ) (x : Cylinder b) : ℕ := x.U.sup wt

/-- The lower end of the interval `I(x)`, clipped at `b^(d-1)`. -/
def lo (d : ℕ) (wt : Fin b → ℕ) (x : Cylinder b) : ℕ :=
  max (x.t wt + x.rf d * x.minU wt) (b ^ (d - 1))

/-- The upper end of the interval `I(x)`, clipped at `b^d - 1`. -/
def hi (d : ℕ) (wt : Fin b → ℕ) (x : Cylinder b) : ℕ :=
  min (x.t wt + x.rf d * x.maxU wt) (b ^ d - 1)

/-- The length of `P(x)`, the common leading digits of the ends of `I(x)`. -/
def pre (d : ℕ) (wt : Fin b → ℕ) (x : Cylinder b) : ℕ :=
  Nat.findGreatest (fun l => x.lo d wt / b ^ (d - l) = x.hi d wt / b ^ (d - l)) d

/-- The interval test of section 27.3.1 fails: `I(x)` is empty, or `P(x)` holds more than `c_v`
copies of some `v ∈ R`, or more than `rf` digits outside `R`. -/
def Fails (d : ℕ) (wt : Fin b → ℕ) (x : Cylinder b) : Prop :=
  x.hi d wt < x.lo d wt ∨ (∃ v ∈ x.R, x.cR v < prefixCount b d (x.lo d wt) (x.pre d wt) v) ∨
    x.rf d < outsideCount b d (x.lo d wt) (x.pre d wt) x.R

end Cylinder

/-- Two numbers with the same quotient by `D` differ by less than `D`. -/
lemma sub_lt_of_div_eq {m n D : ℕ} (hD : 0 < D) (hmn : m ≤ n) (h : m / D = n / D) :
    n - m < D := by
  have h1 := Nat.div_add_mod m D
  have h2 := Nat.div_add_mod n D
  have h3 := Nat.mod_lt n hD
  rw [h] at h1
  omega

/-- Equal leading digits at length `L` give equal leading digits at every shorter length. -/
lemma div_eq_of_div_eq {m n : ℕ} {B e e' : ℕ} (hee : e ≤ e') (h : m / B ^ e = n / B ^ e) :
    m / B ^ e' = n / B ^ e' := by
  obtain ⟨k, rfl⟩ : ∃ k, e' = e + k := ⟨e' - e, by omega⟩
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

/-- The interval test passes on every cylinder `x` containing a count vector `c` (with `d`
copies and `S(c)` of `d` digits) whose sum `S(c)` has top `pre(x)` digits holding each value
`v` at most `c_v` times. -/
lemma not_fails_of_prefix {d : ℕ} (hb : 2 ≤ b) (wt : Fin b → ℕ) (x : Cylinder b)
    (c : Fin b → ℕ) (hsum : ∑ v, c v = d) (hmem : x.Mem c)
    (hS1 : b ^ (d - 1) ≤ wsum wt c) (hS2 : wsum wt c < b ^ d)
    (hpre : ∀ v : Fin b, prefixCount b d (wsum wt c) (x.pre d wt) v ≤ c v) :
    ¬ x.Fails d wt := by
  classical
  set n := wsum wt c with hn
  have hb0 : 0 < b := by omega
  have hRsum : ∑ v ∈ x.R, x.cR v = ∑ v ∈ x.R, c v :=
    Finset.sum_congr rfl fun v hv => (hmem v hv).symm
  have hsplit : ∀ f : Fin b → ℕ, ∑ v, f v = ∑ v ∈ x.R, f v + ∑ v ∈ x.U, f v := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ x.R) f]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hUc : ∑ v ∈ x.U, c v = x.rf d := by
    have := hsplit c; rw [hsum] at this
    simp only [Cylinder.rf, hRsum]; omega
  have hnt : n = x.t wt + ∑ v ∈ x.U, c v * wt v := by
    rw [hn, wsum, hsplit (fun v => c v * wt v), Cylinder.t]
    congr 1
    exact Finset.sum_congr rfl fun v hv => by rw [hmem v hv]
  have hmin : x.rf d * x.minU wt ≤ ∑ v ∈ x.U, c v * wt v := by
    rw [← hUc, Finset.sum_mul]
    refine Finset.sum_le_sum fun v hv => Nat.mul_le_mul_left _ ?_
    have hUne : x.U.Nonempty := ⟨v, hv⟩
    simp only [Cylinder.minU, hUne, ↓reduceDIte]
    exact Finset.inf'_le _ hv
  have hmax : ∑ v ∈ x.U, c v * wt v ≤ x.rf d * x.maxU wt := by
    rw [← hUc, Finset.sum_mul]
    exact Finset.sum_le_sum fun v hv => Nat.mul_le_mul_left _ (Finset.le_sup (f := wt) hv)
  have hlo : x.lo d wt ≤ n := max_le (by omega) hS1
  have hhi : n ≤ x.hi d wt := le_min (by omega) (by omega)
  set L := x.pre d wt with hL
  have hLd : L ≤ d := Nat.findGreatest_le d
  have hLspec : x.lo d wt / b ^ (d - L) = x.hi d wt / b ^ (d - L) := by
    refine Nat.findGreatest_spec
      (P := fun l => x.lo d wt / b ^ (d - l) = x.hi d wt / b ^ (d - l)) (Nat.zero_le d) ?_
    simp only [Nat.sub_zero]
    have hhi2 : x.hi d wt ≤ b ^ d - 1 := min_le_right _ _
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by have := pow_pos hb0 d; omega)]
  have hnL : n / b ^ (d - L) = x.lo d wt / b ^ (d - L) := by
    have h1 := Nat.div_le_div_right (c := b ^ (d - L)) hlo
    have h2 := Nat.div_le_div_right (c := b ^ (d - L)) hhi
    omega
  have hdig : ∀ j < L, topDigit b d (x.lo d wt) j = topDigit b d n j := by
    intro j hj
    simp only [topDigit]
    rw [div_eq_of_div_eq (show d - L ≤ d - 1 - j by omega) hnL]
  have hpc : ∀ v : Fin b, prefixCount b d (x.lo d wt) L v ≤ c v := by
    intro v
    refine le_trans (le_of_eq ?_) (hpre v)
    simp only [prefixCount]
    congr 1
    refine Finset.filter_congr fun j hj => ?_
    rw [hdig j (Finset.mem_range.1 hj)]
  have hout : outsideCount b d (x.lo d wt) L x.R ≤ x.rf d := by
    rw [← hUc]
    set f : ℕ → Fin b := fun j => ⟨topDigit b d (x.lo d wt) j, Nat.mod_lt _ hb0⟩ with hf
    have hmaps : ∀ j ∈ (Finset.range L).filter
        (fun j => ∀ v ∈ x.R, topDigit b d (x.lo d wt) j ≠ v), f j ∈ x.U := by
      intro j hj
      obtain ⟨-, hj⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hR => hj _ hR rfl⟩
    rw [outsideCount, Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_le_sum fun v _ => le_trans ?_ (hpc v)
    simp only [prefixCount]
    refine Finset.card_le_card fun j hj => ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    obtain ⟨hj3, -⟩ := Finset.mem_filter.1 hj1
    refine Finset.mem_filter.2 ⟨hj3, ?_⟩
    rw [← hj2]
  intro hfail
  unfold Cylinder.Fails at hfail
  rw [← hL] at hfail
  rcases hfail with h | ⟨v, hvR, hv⟩ | h
  · omega
  · have := hpc v
    rw [hmem v hvR] at this
    omega
  · omega

/-- **Lemma 27.3** (section 27.3.1). A failing cylinder contains no solution: if the `d` digits
of `S(c)` have the counts `c`, every cylinder containing `c` passes the interval test. -/
theorem lemma27_3 {d : ℕ} (hb : 2 ≤ b) (wt : Fin b → ℕ) (x : Cylinder b) (c : Fin b → ℕ)
    (hsum : ∑ v, c v = d) (hmem : x.Mem c) (hS1 : b ^ (d - 1) ≤ wsum wt c)
    (hS2 : wsum wt c < b ^ d) (hsol : ∀ v : Fin b, prefixCount b d (wsum wt c) d v = c v) :
    ¬ x.Fails d wt := by
  refine not_fails_of_prefix hb wt x c hsum hmem hS1 hS2 fun v => ?_
  rw [← hsol v]
  simp only [prefixCount]
  refine Finset.card_le_card fun j hj => ?_
  obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj1)
    (Nat.findGreatest_le d)), hj2⟩

/-- **Theorem 27.5** (section 27.3.1), the claim of the proof, in the interval oracle. Let the
cylinder `x` contain the count vector `c` (with `d` copies, `S(c)` of `d` digits, not starting
with `1, 0` or `b-1, b-1`), let the top `lam ≥ 1` digits of `S(c)` hold each value `v` at
most `c_v` times, and let `w(u) - w(m) ≥ b^(d - lam - 1)` for all `m < u` with `u ≥ θ`. If `x`
is not a single vector and fails, every value outside `R` is below `θ`. -/
theorem theorem27_5_claim {d : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d) (wt : Fin b → ℕ) (x : Cylinder b)
    (c : Fin b → ℕ) (hsum : ∑ v, c v = d) (hmem : x.Mem c)
    (hS1 : b ^ (d - 1) ≤ wsum wt c) (hS2 : wsum wt c < b ^ d)
    (h10 : ¬ (topDigit b d (wsum wt c) 0 = 1 ∧ topDigit b d (wsum wt c) 1 = 0))
    (hbb : ¬ (topDigit b d (wsum wt c) 0 = b - 1 ∧ topDigit b d (wsum wt c) 1 = b - 1))
    {lam θ : ℕ} (hlam1 : 1 ≤ lam) (hlam : ∀ v : Fin b, prefixCount b d (wsum wt c) lam v ≤ c v)
    (hθ : ∀ u m : Fin b, θ ≤ (u : ℕ) → m < u → wt m + b ^ (d - lam - 1) ≤ wt u)
    (hrf : 1 ≤ x.rf d) (hU : 2 ≤ x.U.card) (hfail : x.Fails d wt) :
    ∀ u : Fin b, u ∉ x.R → (u : ℕ) < θ := by
  classical
  set n := wsum wt c with hn
  have hb0 : 0 < b := by omega
  -- the weight sum splits over `R` and `U`
  have hRsum : ∑ v ∈ x.R, x.cR v = ∑ v ∈ x.R, c v := Finset.sum_congr rfl fun v hv => (hmem v hv).symm
  have hsplit : ∀ f : Fin b → ℕ, ∑ v, f v = ∑ v ∈ x.R, f v + ∑ v ∈ x.U, f v := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ x.R) f]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hUc : ∑ v ∈ x.U, c v = x.rf d := by
    have := hsplit c; rw [hsum] at this
    simp only [Cylinder.rf, hRsum]; omega
  have hnt : n = x.t wt + ∑ v ∈ x.U, c v * wt v := by
    rw [hn, wsum, hsplit (fun v => c v * wt v), Cylinder.t]
    congr 1
    exact Finset.sum_congr rfl fun v hv => by rw [hmem v hv]
  have hUne : x.U.Nonempty := Finset.card_pos.1 (by omega)
  have hmin : x.rf d * x.minU wt ≤ ∑ v ∈ x.U, c v * wt v := by
    rw [← hUc, Finset.sum_mul]
    refine Finset.sum_le_sum fun v hv => Nat.mul_le_mul_left _ ?_
    simp only [Cylinder.minU, hUne, ↓reduceDIte]
    exact Finset.inf'_le _ hv
  have hmax : ∑ v ∈ x.U, c v * wt v ≤ x.rf d * x.maxU wt := by
    rw [← hUc, Finset.sum_mul]
    exact Finset.sum_le_sum fun v hv => Nat.mul_le_mul_left _ (Finset.le_sup (f := wt) hv)
  -- `S(c) ∈ I(x)`
  have hlo : x.lo d wt ≤ n := max_le (by omega) hS1
  have hhi : n ≤ x.hi d wt := le_min (by omega) (by omega)
  -- `P(x)` is a prefix of `S(c)`
  set L := x.pre d wt with hL
  have hLd : L ≤ d := Nat.findGreatest_le d
  have hLspec : x.lo d wt / b ^ (d - L) = x.hi d wt / b ^ (d - L) := by
    refine Nat.findGreatest_spec
      (P := fun l => x.lo d wt / b ^ (d - l) = x.hi d wt / b ^ (d - l)) (Nat.zero_le d) ?_
    simp only [Nat.sub_zero]
    have hhi2 : x.hi d wt ≤ b ^ d - 1 := min_le_right _ _
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by have := pow_pos hb0 d; omega)]
  have hpos : ∀ e, 0 < b ^ e := fun e => pow_pos hb0 e
  have hnL : n / b ^ (d - L) = x.lo d wt / b ^ (d - L) := by
    have h1 := Nat.div_le_div_right (c := b ^ (d - L)) hlo
    have h2 := Nat.div_le_div_right (c := b ^ (d - L)) hhi
    omega
  intro u hu
  by_contra hθu
  push Not at hθu
  -- `L ≤ lam`
  have hLlam : L ≤ lam := by
    by_contra hLl
    push Not at hLl
    have h2 : n / b ^ (d - 2) = x.lo d wt / b ^ (d - 2) :=
      div_eq_of_div_eq (by omega) hnL
    have h2' : n / b ^ (d - 2) = x.hi d wt / b ^ (d - 2) :=
      h2.trans (div_eq_of_div_eq (by omega) hLspec)
    have hd1 : b ^ (d - 1) = b * b ^ (d - 2) := by rw [← pow_succ']; congr 1; omega
    have hd2 : b ^ d = b * b * b ^ (d - 2) := by
      rw [mul_assoc, ← pow_succ', ← pow_succ']; congr 1; omega
    have hdig0 : ∀ m, topDigit b d m 0 = m / b ^ (d - 2) / b % b := by
      intro m; simp only [topDigit, Nat.sub_zero, Nat.div_div_eq_div_mul, hd1, mul_comm]
    have hdig1 : ∀ m, topDigit b d m 1 = m / b ^ (d - 2) % b := by
      intro m; simp only [topDigit, show d - 1 - 1 = d - 2 by omega]
    by_cases hA : b ^ (d - 1) ≤ x.t wt + x.rf d * x.minU wt
    · by_cases hB : x.t wt + x.rf d * x.maxU wt ≤ b ^ d - 1
      · -- no clipping: the width of `I(x)` is at least `b^(d - lam - 1)`
        have hlo' : x.lo d wt = x.t wt + x.rf d * x.minU wt := max_eq_left hA
        have hhi' : x.hi d wt = x.t wt + x.rf d * x.maxU wt := min_eq_left hB
        set u0 := x.U.max' hUne
        have hu0 : u0 ∈ x.U := Finset.max'_mem _ _
        have huU : u ∈ x.U := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩
        have huu0 : u ≤ u0 := Finset.le_max' _ _ huU
        obtain ⟨m, hmU, hmu0⟩ : ∃ m ∈ x.U, m ≠ u0 := by
          by_contra h
          push Not at h
          have : x.U ⊆ {u0} := fun y hy => Finset.mem_singleton.2 (h y hy)
          have := Finset.card_le_card this
          simp at this; omega
        have hmlt : m < u0 := lt_of_le_of_ne (Finset.le_max' _ _ hmU) hmu0
        have hwidth := hθ u0 m (le_trans hθu (by exact_mod_cast huu0)) hmlt
        have hwu0 : wt u0 ≤ x.maxU wt := Finset.le_sup (f := wt) hu0
        have hwm : x.minU wt ≤ wt m := by
          simp only [Cylinder.minU, hUne, ↓reduceDIte]; exact Finset.inf'_le _ hmU
        have hgap : x.lo d wt + b ^ (d - lam - 1) ≤ x.hi d wt := by
          rw [hlo', hhi']
          have h0 : x.minU wt + b ^ (d - lam - 1) ≤ x.maxU wt := by omega
          have h1 : x.rf d * (x.minU wt + b ^ (d - lam - 1)) ≤ x.rf d * x.maxU wt :=
            Nat.mul_le_mul_left _ h0
          rw [Nat.mul_add] at h1
          have h2 : b ^ (d - lam - 1) ≤ x.rf d * b ^ (d - lam - 1) := Nat.le_mul_of_pos_left _ hrf
          omega
        have heq := div_eq_of_div_eq (show d - L ≤ d - lam - 1 by omega) hLspec
        have := sub_lt_of_div_eq (hpos _) (by omega) heq
        omega
      · -- clipped at `b^d - 1`: `S(c)` starts with `b-1, b-1`
        have hhi' : x.hi d wt = b ^ d - 1 := min_eq_right (by omega)
        rw [hhi'] at h2'
        have hq : (b ^ d - 1) / b ^ (d - 2) = b * b - 1 := by
          rw [hd2]
          apply Nat.div_eq_of_lt_le
          · have := hpos (d - 2)
            have : 1 ≤ b * b := by nlinarith
            rw [Nat.sub_mul]; omega
          · have := hpos (d - 2)
            have : 1 ≤ b * b := by nlinarith
            rw [Nat.sub_add_cancel this]; omega
        apply hbb
        rw [hdig0, hdig1, h2', hq]
        have hbb1 : b * b - 1 = (b - 1) * b + (b - 1) := by
          obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
          simp only [Nat.add_sub_cancel]; ring_nf; omega
        have e1 : ((b - 1) * b + (b - 1)) / b = b - 1 := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb0, Nat.div_eq_of_lt (by omega), zero_add]
        have e2 : ((b - 1) * b + (b - 1)) % b = b - 1 := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        rw [hbb1, e1, e2, Nat.mod_eq_of_lt (by omega)]
        exact ⟨rfl, rfl⟩
    · -- clipped at `b^(d-1)`: `S(c)` starts with `1, 0`
      have hlo' : x.lo d wt = b ^ (d - 1) := max_eq_right (by omega)
      rw [hlo', hd1, Nat.mul_div_cancel _ (hpos _)] at h2
      apply h10
      rw [hdig0, hdig1, h2, Nat.div_self hb0, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
      exact ⟨rfl, rfl⟩
  -- so `P(x)` holds each value at most `c_v` times, and `x` passes
  refine not_fails_of_prefix hb wt x c hsum hmem hS1 hS2 (fun v => le_trans ?_ (hlam v)) hfail
  simp only [prefixCount]
  refine Finset.card_le_card fun j hj => ?_
  obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := Finset.mem_range.1 hj1; omega), hj2⟩

/-- **Theorem 27.5** (section 27.3.1) in the interval oracle. Let every `c ∈ G` have `d` copies,
`S(c)` of `d` digits not starting with `1, 0` or `b-1, b-1`, a prefix length `lam(c) ≥ 1` whose
top digits hold each value `v` at most `c_v` times, and a threshold `θ(c)` with
`w(u) - w(m) ≥ b^(d - lam(c) - 1)` for all `m < u`, `u ≥ θ(c)`. Then every certificate (a set
of failing cylinders that covers `G`) has at least `N_k` cylinders, where `N_k` counts the
restrictions `c|V_k` to the values `≥ k` of the `c ∈ G` with `θ(c) ≤ k`. -/
theorem theorem27_5_oracle {d : ℕ} (hb : 2 ≤ b) (hd : 2 ≤ d) (wt : Fin b → ℕ) (k : ℕ)
    (G : Finset (Fin b → ℕ)) (lam θ : (Fin b → ℕ) → ℕ)
    (hG : ∀ c ∈ G, ∑ v, c v = d ∧ b ^ (d - 1) ≤ wsum wt c ∧ wsum wt c < b ^ d ∧
      ¬ (topDigit b d (wsum wt c) 0 = 1 ∧ topDigit b d (wsum wt c) 1 = 0) ∧
      ¬ (topDigit b d (wsum wt c) 0 = b - 1 ∧ topDigit b d (wsum wt c) 1 = b - 1) ∧
      1 ≤ lam c ∧ (∀ v : Fin b, prefixCount b d (wsum wt c) (lam c) v ≤ c v) ∧
      ∀ u m : Fin b, θ c ≤ (u : ℕ) → m < u → wt m + b ^ (d - lam c - 1) ≤ wt u)
    (cert : Finset (Cylinder b)) (hfails : ∀ x ∈ cert, x.Fails d wt)
    (hcover : ∀ c ∈ G, ∃ x ∈ cert, x.Mem c) :
    ((G.filter fun c => θ c ≤ k).image fun c (v : {v : Fin b // k ≤ (v : ℕ)}) => c v).card ≤
      cert.card := by
  classical
  apply card_image_le_of_fooling _ _ (fun x => {c | x.Mem c ∧ ∑ v, c v = d}) cert
  · intro c hc
    obtain ⟨hcG, -⟩ := Finset.mem_filter.1 hc
    obtain ⟨x, hx, hxc⟩ := hcover c hcG
    exact ⟨x, hx, hxc, (hG c hcG).1⟩
  · intro x hx c hc c' hc' hxc hxc'
    obtain ⟨hcG, hck⟩ := Finset.mem_filter.1 hc
    obtain ⟨hsum, hS1, hS2, h10, hbb, hlam1, hlam, hθ⟩ := hG c hcG
    obtain ⟨hmc, -⟩ := hxc
    obtain ⟨hmc', hsum'⟩ := hxc'
    funext v
    by_cases hcc : c' = c
    · rw [hcc]
    -- `x` is not a single vector
    have hsplit : ∀ f : Fin b → ℕ, ∑ v, f v = ∑ v ∈ x.R, f v + ∑ v ∈ x.U, f v := by
      intro f
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ x.R) f]
      congr 1
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hRc : ∑ v ∈ x.R, c v = ∑ v ∈ x.R, x.cR v := Finset.sum_congr rfl fun v hv => hmc v hv
    have hRc' : ∑ v ∈ x.R, c' v = ∑ v ∈ x.R, x.cR v := Finset.sum_congr rfl fun v hv => hmc' v hv
    have hUc : ∑ v ∈ x.U, c v = x.rf d := by
      have := hsplit c; rw [hsum] at this; simp only [Cylinder.rf]; omega
    have hUc' : ∑ v ∈ x.U, c' v = x.rf d := by
      have := hsplit c'; rw [hsum'] at this; simp only [Cylinder.rf]; omega
    have hne : ∃ v ∈ x.U, c v ≠ c' v := by
      by_contra h
      push Not at h
      apply hcc
      funext v
      by_cases hv : v ∈ x.R
      · rw [hmc v hv, hmc' v hv]
      · exact (h v (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩)).symm
    obtain ⟨v0, hv0U, hv0⟩ := hne
    have hrf : 1 ≤ x.rf d := by
      by_contra h0
      have hz : x.rf d = 0 := by omega
      have h1 : c v0 = 0 := by
        have := Finset.single_le_sum (fun v _ => Nat.zero_le (c v)) hv0U; omega
      have h2 : c' v0 = 0 := by
        have := Finset.single_le_sum (fun v _ => Nat.zero_le (c' v)) hv0U; omega
      exact hv0 (h1.trans h2.symm)
    have hU : 2 ≤ x.U.card := by
      by_contra h2
      have hU1 : x.U = {v0} := by
        refine Finset.eq_singleton_iff_unique_mem.2 ⟨hv0U, fun y hy => ?_⟩
        by_contra hy'
        have : ({y, v0} : Finset (Fin b)) ⊆ x.U := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have := Finset.card_le_card this
        rw [Finset.card_pair hy'] at this; omega
      rw [hU1, Finset.sum_singleton] at hUc hUc'
      exact hv0 (hUc.trans hUc'.symm)
    have hall := theorem27_5_claim hb hd wt x c hsum hmc hS1 hS2 h10 hbb hlam1 hlam hθ hrf hU
      (hfails x hx)
    have hvR : (v : Fin b) ∈ x.R := by
      by_contra hvR
      have := hall v hvR
      have := v.2
      omega
    rw [hmc v hvR, hmc' v hvR]

end Oracle

end Munchausen
