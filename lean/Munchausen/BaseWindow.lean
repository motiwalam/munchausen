import Munchausen.Counting

/-!
# The window of the base (Lemma 20.1, Proposition 15.17)

A `k`-digit solution `n` with leading digit `p` and second digit at most `M` has
`p b^(k-1) ≤ n < p b^(k-1) + (M + 1) b^(k-2)`, so its base lies in a window of length
`(M + 1) / (p (k - 1))` above `(n / p)^(1/(k-1))`.
-/

open Real

namespace Munchausen

/-- **Lemma 20.1** (section 20.1.2). Let `(p, q, t)` be a solution in base `b` with
`k = |t| + 2` digits and `q ≤ M`. Then `p b^(k-1) ≤ n < p b^(k-1) + (M + 1) b^(k-2)`. -/
theorem lemma20_1 {b m p q M : ℕ} {t : List ℕ} (hs : IsSolution b m (p :: q :: t))
    (hq : q ≤ M) :
    p * b ^ (t.length + 1) ≤ P b (p :: q :: t) ∧
      P b (p :: q :: t) < p * b ^ (t.length + 1) + (M + 1) * b ^ t.length := by
  have hp := hs.lt_base p (by simp)
  have hb : 1 < b := by
    have := hs.head_ne_zero (by simp); simp at this; omega
  have ht : P b t < b ^ t.length := P_lt_pow hb fun d hd => hs.lt_base d (by simp [hd])
  simp only [P_cons, List.length_cons, Nat.cast_id]
  constructor
  · omega
  · have : q * b ^ t.length + b ^ t.length ≤ (M + 1) * b ^ t.length := by
      rw [← add_one_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

/-- **Lemma 20.1**, the root form (section 20.1.2). With `j = k - 1 = |t| + 1`:
`b ≤ (n / p)^(1/j) < b + (M + 1) / (p j)`. -/
theorem lemma20_1_root {b m p q M : ℕ} {t : List ℕ} (hs : IsSolution b m (p :: q :: t))
    (hq : q ≤ M) :
    (b : ℝ) ≤ (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ ∧
      (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ <
        b + (M + 1) / (p * (t.length + 1 : ℕ)) := by
  obtain ⟨h1, h2⟩ := lemma20_1 hs hq
  have hp1 : 1 ≤ p := by
    have := hs.head_ne_zero (by simp); simp at this; omega
  have hb : 1 < b := by have := hs.lt_base p (by simp); omega
  set j := t.length + 1 with hj
  set n := P b (p :: q :: t)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  have hbR : (0 : ℝ) < b := by positivity
  have hjR : (0 : ℝ) < j := by positivity
  have hj0 : j ≠ 0 := by omega
  have h1R : (p : ℝ) * b ^ j ≤ n := by exact_mod_cast h1
  have h2R : (n : ℝ) < p * b ^ j + (M + 1) * b ^ t.length := by exact_mod_cast h2
  have hbj : (b : ℝ) ^ j = b * b ^ t.length := by rw [hj, pow_succ']
  have hN0 : (0 : ℝ) ≤ n / p := by positivity
  have hinv : (0 : ℝ) < (j : ℝ)⁻¹ := inv_pos.2 hjR
  constructor
  · have : (b : ℝ) ^ j ≤ n / p := by rw [le_div_iff₀ hpR]; linarith
    calc (b : ℝ) = ((b : ℝ) ^ j) ^ (j : ℝ)⁻¹ := (pow_rpow_inv_natCast hbR.le hj0).symm
      _ ≤ (n / p) ^ (j : ℝ)⁻¹ := rpow_le_rpow (by positivity) this hinv.le
  · set u : ℝ := (M + 1) / (p * b)
    have hu : 0 ≤ u := by positivity
    have hlt : (n : ℝ) / p < (b : ℝ) ^ j * (1 + u) := by
      rw [div_lt_iff₀ hpR]
      have : (b : ℝ) ^ j * (1 + u) * p = p * b ^ j + (M + 1) * b ^ t.length := by
        simp only [u]; rw [hbj]; field_simp
      linarith
    have hB : (1 + u) ^ (j : ℝ)⁻¹ ≤ 1 + (j : ℝ)⁻¹ * u :=
      rpow_one_add_le_one_add_mul_self (by linarith) hinv.le
        (inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ j by omega)))
    calc ((n : ℝ) / p) ^ (j : ℝ)⁻¹ < ((b : ℝ) ^ j * (1 + u)) ^ (j : ℝ)⁻¹ :=
          rpow_lt_rpow hN0 hlt hinv
      _ = b * (1 + u) ^ (j : ℝ)⁻¹ := by
          rw [mul_rpow (by positivity) (by positivity), pow_rpow_inv_natCast hbR.le hj0]
      _ ≤ b * (1 + (j : ℝ)⁻¹ * u) := mul_le_mul_of_nonneg_left hB hbR.le
      _ = b + (M + 1) / (p * j) := by simp only [u]; field_simp

/-- **Proposition 15.17** (section 15.6). Let `X` bound every digit `d` with `d^d ≤ N`. A
solution `N` with `k = |t| + 2` digits, leading digit `p`, has
`b ≤ (N / p)^(1/(k-1)) < b + (X + 1) / (p (k - 1))`. -/
theorem prop15_17 {b m p q X : ℕ} {t : List ℕ} (hs : IsSolution b m (p :: q :: t))
    (hX : ∀ d, d ^ d ≤ P b (p :: q :: t) → d ≤ X) :
    (b : ℝ) ≤ (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ ∧
      (((P b (p :: q :: t) : ℕ) : ℝ) / p) ^ ((t.length + 1 : ℕ) : ℝ)⁻¹ <
        b + (X + 1) / (p * (t.length + 1 : ℕ)) := by
  refine lemma20_1_root hs (hX q ?_)
  rw [hs.eq]
  have hp1 : p ≠ 0 := by have := hs.head_ne_zero (by simp); simpa using this
  have := one_le_w (m := m) hp1
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp only [pow_zero, Fs_cons]; omega
  · have : q ^ q = w m q := (w_of_ne_zero m hq.ne').symm
    rw [this, Fs_cons, Fs_cons]
    omega

/-! ### Lemma 20.4: divisors in a short window -/

lemma gcd_prod_dvd_prod_gcd (d : ℕ) (s : Finset ℕ) :
    Nat.gcd d (∏ x ∈ s, x) ∣ ∏ x ∈ s, Nat.gcd d x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx]
    exact (gcd_mul_dvd_mul_gcd d x _).trans (mul_dvd_mul_left _ ih)

/-- The core of **Lemma 20.4**: if every element of `s` lies in `(a, a + h]`, then
`∏ d ≤ lcm(s) h^(r(r-1)/2)` with `r = |s|`, since `gcd(d_i, d_j)` divides `d_j - d_i < h`. -/
lemma prod_le_lcm_mul_pow {a h : ℕ} (s : Finset ℕ) (hs : ∀ d ∈ s, a < d ∧ d ≤ a + h) :
    ∏ d ∈ s, d ≤ s.lcm id * h ^ (s.card.choose 2) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert d s hlt ih =>
    have hds : d ∉ s := fun h => lt_irrefl d (hlt d h)
    have ih' := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    have hd := hs d (Finset.mem_insert_self d s)
    rw [Finset.prod_insert hds, Finset.lcm_insert, Finset.card_insert_of_notMem hds,
      Nat.choose_succ_succ', Nat.choose_one_right, id]
    set L := s.lcm id
    set g := Nat.gcd d L
    have hgl : g * lcm d L = d * L := by
      rw [lcm_eq_nat_lcm]; exact Nat.gcd_mul_lcm d L
    -- `g ≤ h^|s|`
    have hg : g ≤ h ^ s.card := by
      have h1 : L ∣ ∏ x ∈ s, x := Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx
      have h2 : g ∣ ∏ x ∈ s, Nat.gcd d x :=
        (Nat.gcd_dvd_gcd_of_dvd_right d h1).trans (gcd_prod_dvd_prod_gcd d s)
      have h3 : ∏ x ∈ s, Nat.gcd d x ≤ h ^ s.card := by
        apply Finset.prod_le_pow_card
        intro x hx
        have hxd := hlt x hx
        have hx' := (hs x (Finset.mem_insert_of_mem hx)).1
        have : Nat.gcd d x ∣ d - x := Nat.dvd_sub (Nat.gcd_dvd_left d x) (Nat.gcd_dvd_right d x)
        have := Nat.le_of_dvd (by omega) this
        omega
      have h4 : 0 < ∏ x ∈ s, Nat.gcd d x :=
        Finset.prod_pos fun x hx => Nat.gcd_pos_of_pos_left _ (by omega)
      exact (Nat.le_of_dvd h4 h2).trans h3
    calc d * ∏ x ∈ s, x ≤ d * (L * h ^ s.card.choose 2) := Nat.mul_le_mul_left d ih'
      _ = g * lcm d L * h ^ s.card.choose 2 := by rw [hgl]; ring
      _ ≤ h ^ s.card * lcm d L * h ^ s.card.choose 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hg)
      _ = lcm d L * h ^ (s.card + s.card.choose 2) := by rw [pow_add]; ring

/-- **Lemma 20.4** (section 20.1.4). Let `m ≥ 1` and let `d_1 < ... < d_r`, `r ≥ 1`, be divisors
of `m` in the window `(a, a + h]` (with `a = Y - h`). Then `a^r < m h^(r(r-1)/2)`, that is
`m > (Y - h)^r / h^(r(r-1)/2)`. -/
theorem lemma20_4 {m a h : ℕ} (hm : 1 ≤ m) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ∣ m ∧ a < d ∧ d ≤ a + h) (hne : s.Nonempty) :
    a ^ s.card < m * h ^ (s.card.choose 2) := by
  have h1 := prod_le_lcm_mul_pow s fun d hd => (hs d hd).2
  have h2 : s.lcm id ≤ m :=
    Nat.le_of_dvd (by omega) (Finset.lcm_dvd fun d hd => (hs d hd).1)
  have h3 : a ^ s.card < ∏ d ∈ s, d := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, zero_pow (Finset.card_ne_zero.2 hne)]
      exact Finset.prod_pos fun d hd => by have := (hs d hd).2.1; omega
    · rw [← Finset.prod_const]
      exact Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => h) (fun d hd => (hs d hd).2.1) hne
  calc a ^ s.card < ∏ d ∈ s, d := h3
    _ ≤ s.lcm id * h ^ (s.card.choose 2) := h1
    _ ≤ m * h ^ (s.card.choose 2) := Nat.mul_le_mul_right _ h2

/-! ### Proposition 20.2: counting bases by multisets -/

/-- `H_n` is monotone. -/
lemma harmonic_le_harmonic {n k : ℕ} (h : n ≤ k) : (harmonic n : ℝ) ≤ harmonic k := by
  induction k, h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    rw [harmonic_succ]; push_cast
    exact ih.trans (le_add_of_nonneg_right (by positivity))

/-- The reciprocals of `r` distinct positive integers sum to at most `H_r`. -/
lemma sum_inv_le_harmonic (P : Finset ℕ) (hP : 0 ∉ P) :
    ∑ p ∈ P, (1 / (p : ℝ)) ≤ harmonic P.card := by
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha0 : a ≠ 0 := fun h => hP (h ▸ Finset.mem_insert_self a s)
    have ih' := ih fun h => hP (Finset.mem_insert_of_mem h)
    have hcard : s.card + 1 ≤ a := by
      have : s ⊆ Finset.Ico 1 a := fun x hx => by
        have := hlt x hx
        have hx0 : x ≠ 0 := fun h => hP (Finset.mem_insert_of_mem (h ▸ hx))
        rw [Finset.mem_Ico]; omega
      have := Finset.card_le_card this
      rw [Nat.card_Ico] at this
      omega
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, harmonic_succ]
    push_cast
    have : (1 : ℝ) / a ≤ ((s.card : ℝ) + 1)⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast hcard)
    linarith

/-- A finite set of naturals inside a half-open window `(r - δ, r]` has at most `δ + 1`
elements. -/
lemma card_le_of_window (S : Finset ℕ) {r δ : ℝ} (hδ : 0 ≤ δ)
    (hS : ∀ b ∈ S, (b : ℝ) ≤ r ∧ r < b + δ) : (S.card : ℝ) ≤ δ + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp; linarith
  set b0 := S.min' hne
  have hsub : S ⊆ Finset.Icc b0 (b0 + ⌊δ⌋₊) := by
    intro b hb
    have hb0 : b0 ≤ b := S.min'_le b hb
    have h1 := hS b hb
    have h2 := hS b0 (S.min'_mem hne)
    rw [Finset.mem_Icc]
    refine ⟨hb0, ?_⟩
    have : ((b - b0 : ℕ) : ℝ) ≤ δ := by
      push_cast [Nat.cast_sub hb0]; linarith
    have := Nat.le_floor this
    omega
  have := Finset.card_le_card hsub
  rw [Nat.card_Icc] at this
  calc (S.card : ℝ) ≤ ((b0 + ⌊δ⌋₊ + 1 - b0 : ℕ) : ℝ) := by exact_mod_cast this
    _ = ⌊δ⌋₊ + 1 := by rw [show b0 + ⌊δ⌋₊ + 1 - b0 = ⌊δ⌋₊ + 1 by omega]; push_cast; ring
    _ ≤ δ + 1 := by linarith [Nat.floor_le hδ]

/-- The multisets of `k` digits from `{0, ..., X}` number at most `C(X + k, k)`. -/
lemma card_multisets_le (X k : ℕ) :
    ((stringsLE X k).image (fun s : List ℕ => (s : Multiset ℕ))).card ≤ (X + k).choose k := by
  classical
  let cf : ℕ → Fin (X + 1) := fun d => ⟨d % (X + 1), Nat.mod_lt _ (by omega)⟩
  let g : Multiset ℕ → Sym (Fin (X + 1)) k := fun c =>
    if h : Multiset.card c = k then ⟨c.map cf, by simpa using h⟩
    else ⟨Multiset.replicate k 0, by simp⟩
  have key : ∀ s ∈ stringsLE X k,
      ((g (s : Multiset ℕ) : Multiset (Fin (X + 1))).map Fin.val) = (s : Multiset ℕ) := by
    intro s hs
    rw [mem_stringsLE] at hs
    have hc1 : Multiset.card (s : Multiset ℕ) = k := by simp [hs.1]
    have hg : g (s : Multiset ℕ) = ⟨(s : Multiset ℕ).map cf, by simpa using hc1⟩ := by
      simp only [g, hc1, ↓reduceDIte]
      rfl
    rw [hg, Sym.coe_mk, Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id (s : Multiset ℕ)]
    refine Multiset.map_congr rfl fun d hd => ?_
    simp only [Function.comp_apply, cf, id]
    exact Nat.mod_eq_of_lt (by have := hs.2 d hd; omega)
  have hinj : Set.InjOn g ((stringsLE X k).image (fun s : List ℕ => (s : Multiset ℕ))) := by
    intro c hc c' hc' h
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hc hc'
    obtain ⟨s, hs, rfl⟩ := hc
    obtain ⟨s', hs', rfl⟩ := hc'
    have h' := congrArg (fun x : Sym (Fin (X + 1)) k => (x : Multiset (Fin (X + 1))).map Fin.val) h
    rwa [key s hs, key s' hs'] at h'
  calc _ ≤ (Finset.univ : Finset (Sym (Fin (X + 1)) k)).card :=
        Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = (X + k).choose k := by
        rw [Finset.card_univ, Sym.card_sym_fin_eq_multichoose, Nat.multichoose_eq]
        congr 1; omega

/-- **Proposition 20.2** (section 20.1.2). Let `k ≥ 2` and let `X` bound every digit `x` with
`x^x < B^k`. Under a fixed convention, at most `C(X + k, k) ((X + 1) H_k / (k - 1) + k)` bases
`b ≤ B` have a `k`-digit solution. A base is determined by its digit multiset `c`, its leading
digit `p`, and a window of at most `(X + 1)/(p (k - 1)) + 1` integers (Lemma 20.1). -/
theorem prop20_2 {m B k X : ℕ} (hk : 2 ≤ k) (hX : ∀ x, x ^ x < B ^ k → x ≤ X) :
    ((basesWith m B k).card : ℝ) ≤
      (X + k).choose k * ((X + 1) * (harmonic k : ℝ) / (k - 1) + k) := by
  classical
  let f : ℕ → List ℕ := fun b =>
    if h : ∃ s : List ℕ, s.length = k ∧ IsSolution b m s then Classical.choose h else []
  have hf : ∀ b ∈ basesWith m B k, (f b).length = k ∧ IsSolution b m (f b) := by
    intro b hb
    unfold basesWith at hb
    rw [Finset.mem_filter] at hb
    simp only [f, hb.2, ↓reduceDIte]
    exact Classical.choose_spec hb.2
  have hdig : ∀ b ∈ basesWith m B k, ∀ d ∈ f b, d ≤ X := by
    intro b hb d hd
    have hbB : 2 ≤ b ∧ b ≤ B := by
      have hb' := hb
      unfold basesWith at hb'
      rw [Finset.mem_filter, Finset.mem_Icc] at hb'
      exact hb'.1
    obtain ⟨hlen, hs⟩ := hf b hb
    exact hX d (by rw [← hlen]; exact hs.pow_self_lt hbB.1 hbB.2 hd)
  set Ms := (stringsLE X k).image (fun s : List ℕ => (s : Multiset ℕ))
  set T := (Ms ×ˢ Finset.range (X + 1)).filter (fun cp => cp.2 ∈ cp.1 ∧ cp.2 ≠ 0)
  set φ : ℕ → Multiset ℕ × ℕ := fun b => ((f b : Multiset ℕ), (f b).headI)
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- the leading digit and the multiset
  have hshape : ∀ b ∈ basesWith m B k, ∃ p q t, f b = p :: q :: t ∧ t.length + 2 = k := by
    intro b hb
    obtain ⟨hlen, -⟩ := hf b hb
    match h : f b, hlen with
    | p :: q :: t, hlen => exact ⟨p, q, t, rfl, by simpa using hlen⟩
    | [], hlen => simp at hlen; omega
    | [_], hlen => simp at hlen; omega
  have hmaps : ∀ b ∈ basesWith m B k, φ b ∈ T := by
    intro b hb
    obtain ⟨hlen, hs⟩ := hf b hb
    obtain ⟨p, q, t, hpq, -⟩ := hshape b hb
    have hp0 := hs.head_ne_zero (by rw [hpq]; simp)
    simp only [hpq, List.head_cons] at hp0
    simp only [T, φ, Ms, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
      Finset.mem_range, hpq, List.headI_cons, Multiset.mem_coe]
    refine ⟨⟨⟨p :: q :: t, mem_stringsLE.2 ⟨by rw [← hpq]; exact hlen, ?_⟩, rfl⟩, ?_⟩,
      by simp, hp0⟩
    · intro d hd; exact hdig b hb d (by rw [hpq]; exact hd)
    · have := hdig b hb p (by rw [hpq]; simp); omega
  -- each fiber is a window
  have hfiber : ∀ t ∈ T, ((((basesWith m B k).filter (fun b => φ b = t)).card : ℕ) : ℝ) ≤
      (X + 1) / (t.2 * ((k : ℝ) - 1)) + 1 := by
    rintro ⟨c, p⟩ ht
    simp only [T, Finset.mem_filter] at ht
    have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero ht.2.2
    set N := (c.map (w m)).sum
    set r : ℝ := ((N : ℝ) / p) ^ (((k - 1 : ℕ) : ℝ))⁻¹
    refine card_le_of_window _ (by positivity) (r := r) fun b hb => ?_
    rw [Finset.mem_filter] at hb
    obtain ⟨hlen, hs⟩ := hf b hb.1
    obtain ⟨p', q, t, hpq, htk⟩ := hshape b hb.1
    have hφ := hb.2
    simp only [φ, hpq, List.headI_cons, Prod.mk.injEq] at hφ
    obtain ⟨hc, rfl⟩ := hφ
    rw [hpq] at hs
    have hq : q ≤ X := hdig b hb.1 q (by rw [hpq]; simp)
    obtain ⟨h1, h2⟩ := lemma20_1_root hs hq
    have hN : P b (p' :: q :: t) = N := by
      rw [hs.eq]; simp only [N, ← hc, Fs, Multiset.map_coe, Multiset.sum_coe]
    have hkt : t.length + 1 = k - 1 := by omega
    rw [hN, hkt] at h1 h2
    refine ⟨h1, ?_⟩
    have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ k by omega)]; ring
    show r < ↑b + (↑X + 1) / (↑p' * ((k : ℝ) - 1))
    rw [← this]
    exact h2
  -- sum over the multisets
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  calc (∑ t ∈ T, ((((basesWith m B k).filter (fun b => φ b = t)).card : ℕ) : ℝ))
      ≤ ∑ t ∈ T, ((X + 1) / (t.2 * ((k : ℝ) - 1)) + 1) := Finset.sum_le_sum hfiber
    _ = ∑ c ∈ Ms, ∑ p ∈ (Finset.range (X + 1)).filter (fun p => p ∈ c ∧ p ≠ 0),
          ((X + 1) / (p * ((k : ℝ) - 1)) + 1) := by
        rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_filter]
    _ ≤ ∑ c ∈ Ms, ((X + 1) * (harmonic k : ℝ) / (k - 1) + k) := by
        refine Finset.sum_le_sum fun c hc => ?_
        set P := (Finset.range (X + 1)).filter (fun p => p ∈ c ∧ p ≠ 0)
        have hcard : P.card ≤ k := by
          simp only [Ms, Finset.mem_image] at hc
          obtain ⟨s, hs, rfl⟩ := hc
          have hsub : P ⊆ s.toFinset := fun p hp => by
            simp only [P, Finset.mem_filter, Multiset.mem_coe] at hp
            exact List.mem_toFinset.2 hp.2.1
          calc P.card ≤ s.toFinset.card := Finset.card_le_card hsub
            _ ≤ s.length := List.toFinset_card_le s
            _ = k := (mem_stringsLE.1 hs).1
        have hP0 : 0 ∉ P := by simp [P]
        have hH := (sum_inv_le_harmonic P hP0).trans (harmonic_le_harmonic hcard)
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        have e : ∑ p ∈ P, ((X : ℝ) + 1) / (p * ((k : ℝ) - 1)) =
            (X + 1) / ((k : ℝ) - 1) * ∑ p ∈ P, (1 / (p : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [mul_comm (p : ℝ)]; field_simp
        rw [e]
        have hXk : (0 : ℝ) ≤ (X + 1) / ((k : ℝ) - 1) := by positivity
        have : (X + 1) / ((k : ℝ) - 1) * ∑ p ∈ P, (1 / (p : ℝ)) ≤
            (X + 1) * (harmonic k : ℝ) / (k - 1) := by
          rw [mul_div_right_comm]
          exact mul_le_mul_of_nonneg_left hH hXk |>.trans_eq (by ring)
        have h2 : (P.card : ℝ) ≤ k := by exact_mod_cast hcard
        linarith
    _ = Ms.card * ((X + 1) * (harmonic k : ℝ) / (k - 1) + k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (X + k).choose k * ((X + 1) * (harmonic k : ℝ) / (k - 1) + k) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast card_multisets_le X k)
        have : (0 : ℝ) ≤ harmonic k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · simp [h]
          · exact_mod_cast (harmonic_pos h.ne').le
        positivity

end Munchausen
