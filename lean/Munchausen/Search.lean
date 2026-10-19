import Munchausen.Congruences

/-!
# Near-solutions and search (chapters 26 and 27)

* Lemma 26.1, the swap lemma: rearranging digits keeps `F` and moves the value by a multiple
  of `b - 1`; a transposition moves it by `(x - y)(b^j - b^i)` (also in base `-b`,
  Lemma 26.4);
* Corollary 26.2: when a transposition keeps the offset class modulo `2(b-1)`;
* Proposition 26.10: the image of `c ↦ S(c)` is the same under both conventions;
* Proposition 27.8 and Corollary 27.9: which digit values fix the bottom digits of `S`;
* Theorem 27.5 in abstract form: the fooling-set bound for certificates of emptiness.
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

end Munchausen
