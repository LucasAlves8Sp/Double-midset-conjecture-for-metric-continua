module

public import DoubleMidset.Parity

/-!
# Two types of strict pairs and the stability of a touch (Corollary 5.5, Lemma 5.6)

Standing assumption (Convention 5.1): `T` is a finite tree with a metric having the DMP.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem sgnf_preimage_zero (a b : T) : sgnf a b ⁻¹' {0} = midset a b := by
  ext y; exact sgnf_eq_zero_iff

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem midset_finite_of_dmp (hDMP : HasDMP T) {a b : T} (hab : a ≠ b) :
    (sgnf a b ⁻¹' {0}).Finite := by
  rw [sgnf_preimage_zero]; exact finite_of_encard_eq_coe (hDMP a b hab)

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem IsStrictPair.notMem_vertices {a b : T} (h : IsStrictPair a b) {y : T}
    (hy : y ∈ midset a b) : y ∉ vertices T := fun hV => h.2 y hV (sgnf_eq_zero_iff.2 hy)

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem sgnf_left_neg {a b : T} (hab : a ≠ b) : sgnf a b a < 0 := by
  unfold sgnf; rw [dist_self, zero_sub, neg_neg_iff_pos]; exact dist_pos.2 hab

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem sgnf_right_pos {a b : T} (hab : a ≠ b) : 0 < sgnf a b b := by
  unfold sgnf; rw [dist_self, sub_zero]; exact dist_pos.2 hab.symm

/-- The crossings of `f_{a,b}` along an arc from `a` to `b` correspond to the sign changes along
a parametrization of it. -/
theorem crossings_on_arc (hDMP : HasDMP T) {a b : T} (h : IsStrictPair a b) {k : ℝ → T}
    (hk : IsArcParam k) (hk0 : k 0 = a) (hk1 : k 1 = b) :
    {y | y ∈ k '' Icc 0 1 ∧ IsCrossing (sgnf a b) y} =
      k '' {s | s ∈ Ioo (0 : ℝ) 1 ∧ IsParamCrossing (sgnf a b ∘ k) s} := by
  have hfin := midset_finite_of_dmp hDMP h.1
  ext y; constructor
  · rintro ⟨⟨s, hs, rfl⟩, hcr⟩
    have hs0 : s ≠ 0 := fun e => by
      have := hcr.2.1; rw [e, hk0] at this; exact (sgnf_left_neg h.1).ne this
    have hs1 : s ≠ 1 := fun e => by
      have := hcr.2.1; rw [e, hk1] at this; exact (sgnf_right_pos h.1).ne' this
    have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hs1⟩
    exact ⟨s, ⟨hsI, hcr.2.1, hcr.along hT hk hsI rfl⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hcr⟩, rfl⟩
    refine ⟨⟨s, Ioo_subset_Icc_self hs, rfl⟩, ?_⟩
    have hzero : k s ∈ midset a b := sgnf_eq_zero_iff.1 hcr.1
    rcases isCrossing_or_isTouch hT (continuous_sgnf a b) hfin (h.notMem_vertices hzero) hcr.1
      with hc | ht
    · exact hc
    · obtain ⟨ε₁, hε₁, h1⟩ := ht.along hT hk hs rfl
      obtain ⟨-, ε₂, hε₂, h2⟩ := hcr
      set ε := min ε₁ ε₂
      have a1 := h1 (s - ε / 2) ⟨by linarith [min_le_left ε₁ ε₂, lt_min hε₁ hε₂], by
        linarith [lt_min hε₁ hε₂]⟩ (s + ε / 2) ⟨by linarith [lt_min hε₁ hε₂], by
        linarith [min_le_left ε₁ ε₂, lt_min hε₁ hε₂]⟩
      have a2 := h2 (s - ε / 2) ⟨by linarith [min_le_right ε₁ ε₂, lt_min hε₁ hε₂], by
        linarith [lt_min hε₁ hε₂]⟩ (s + ε / 2) ⟨by linarith [lt_min hε₁ hε₂], by
        linarith [min_le_right ε₁ ε₂, lt_min hε₁ hε₂]⟩
      exact absurd a1 (not_lt.2 a2.le)

/-- An arc from `a` to `b` contains an odd number of crossings of `f_{a,b}`. -/
theorem odd_crossings_on_arc (hDMP : HasDMP T) {a b : T} (h : IsStrictPair a b) {A : Set T}
    (hA : IsArcBetween A a b) : Odd {y | y ∈ A ∧ IsCrossing (sgnf a b) y}.ncard := by
  obtain ⟨k, hk, rfl, hk0, hk1⟩ := hA.exists_param
  rw [crossings_on_arc hT hDMP h hk hk0 hk1, (hk.2.mono fun s hs =>
    Ioo_subset_Icc_self hs.1 : InjOn k {s | s ∈ Ioo (0 : ℝ) 1 ∧
      IsParamCrossing (sgnf a b ∘ k) s}).ncard_image]
  have hpar := param_parity (h := sgnf a b ∘ k) _ zero_lt_one
    ((continuous_sgnf a b).comp hk.1).continuousOn
    (finite_paramZeros (midset_finite_of_dmp hDMP h.1) hk) rfl
    (by simp only [comp_apply, hk0]; exact (sgnf_left_neg h.1).ne)
    (by simp only [comp_apply, hk1]; exact (sgnf_right_pos h.1).ne')
  simp only [comp_apply, hk0, hk1, if_pos (sgnf_left_neg h.1),
    if_neg (not_lt.2 (sgnf_right_pos h.1).le)] at hpar
  rw [Nat.odd_iff]; omega

/-- **Corollary 5.5 (two types of strict pairs).** -/
theorem cor_5_5 (hDMP : HasDMP T) {a b : T} (h : IsStrictPair a b) :
    (∃ y₁ y₂, y₁ ≠ y₂ ∧ midset a b = {y₁, y₂} ∧ y₁ ∉ vertices T ∧ y₂ ∉ vertices T) ∧
    (∀ A, IsArcBetween A a b → Odd {y | y ∈ A ∧ IsCrossing (sgnf a b) y}.ncard) ∧
    (Even (oddCount a b) → ∀ y ∈ midset a b, IsCrossing (sgnf a b) y) ∧
    (Odd (oddCount a b) → ∃ y₁ y₂, midset a b = {y₁, y₂} ∧
      IsCrossing (sgnf a b) y₁ ∧ IsTouch (sgnf a b) y₂) := by
  have hfin := midset_finite_of_dmp hDMP h.1
  obtain ⟨y₁, y₂, hne, hM⟩ := encard_eq_two.1 (hDMP a b h.1)
  have hy₁ : y₁ ∈ midset a b := hM ▸ Or.inl rfl
  have hy₂ : y₂ ∈ midset a b := hM ▸ Or.inr rfl
  refine ⟨⟨y₁, y₂, hne, hM, h.notMem_vertices hy₁, h.notMem_vertices hy₂⟩,
    fun A hA => odd_crossings_on_arc hT hDMP h hA, ?_⟩
  -- the parity of the number of crossings
  have hpar := lemma_5_4 hT (continuous_sgnf a b) hfin fun u hu => h.2 u hu
  have hcsub : {y | IsCrossing (sgnf a b) y} ⊆ {y₁, y₂} := fun y hy =>
    hM ▸ sgnf_eq_zero_iff.1 hy.2.1
  have hpos : 1 ≤ {y | IsCrossing (sgnf a b) y}.ncard := by
    obtain ⟨A, hA⟩ := exists_arc (X := T) h.1
    have := (odd_crossings_on_arc hT hDMP h hA).pos
    exact this.trans_le (ncard_le_ncard (fun y hy => hy.2) ((toFinite {y₁, y₂}).subset hcsub))
  have hle : {y | IsCrossing (sgnf a b) y}.ncard ≤ 2 :=
    (ncard_le_ncard hcsub (toFinite _)).trans (ncard_pair hne).le
  have htype : ∀ y ∈ midset a b, IsCrossing (sgnf a b) y ∨ IsTouch (sgnf a b) y := fun y hy =>
    isCrossing_or_isTouch hT (continuous_sgnf a b) hfin (h.notMem_vertices hy)
      (sgnf_eq_zero_iff.2 hy)
  have hN : oddCount a b = {u | u ∈ oddVertices T ∧ sgnf a b u < 0}.ncard := rfl
  constructor
  · intro heven
    rw [← hN] at hpar
    have h2 : {y | IsCrossing (sgnf a b) y}.ncard = 2 := by
      rw [Nat.even_iff] at heven; omega
    have heq : {y | IsCrossing (sgnf a b) y} = {y₁, y₂} :=
      eq_of_subset_of_ncard_le hcsub (by rw [ncard_pair hne, h2]) (toFinite _)
    intro y hy
    have : y ∈ ({y₁, y₂} : Set T) := hM ▸ hy
    rw [← heq] at this; exact this
  · intro hodd
    rw [← hN] at hpar
    have h1 : {y | IsCrossing (sgnf a b) y}.ncard = 1 := by
      rw [Nat.odd_iff] at hodd; omega
    obtain ⟨y, hy⟩ := ncard_eq_one.1 h1
    have hyc : IsCrossing (sgnf a b) y := by
      have : y ∈ ({y} : Set T) := rfl
      rw [← hy] at this; exact this
    have hyM : y ∈ ({y₁, y₂} : Set T) := hcsub (by rw [hy]; rfl)
    -- the other point is a touch
    have hother : ∀ z ∈ midset a b, z ≠ y → IsTouch (sgnf a b) z := by
      intro z hz hzy
      rcases htype z hz with hc | ht
      · have : z ∈ ({y} : Set T) := by rw [← hy]; exact hc
        exact (hzy this).elim
      · exact ht
    rcases hyM with rfl | rfl
    · exact ⟨y, y₂, hM, hyc, hother y₂ hy₂ hne.symm⟩
    · exact ⟨y, y₁, by rw [hM, pair_comm], hyc, hother y₁ hy₁ hne⟩

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem signs_of_sigma {σ x z : ℝ} (hσ : σ = 1 ∨ σ = -1) (hx : 0 < σ * x) (hz : σ * z < 0) :
    (∃ w ∈ ({x, z} : Set ℝ), w < 0) ∧ (∃ w ∈ ({x, z} : Set ℝ), 0 < w) := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at hx hz
    exact ⟨⟨z, Or.inr rfl, hz⟩, ⟨x, Or.inl rfl, hx⟩⟩
  · simp only [neg_one_mul, neg_pos, neg_neg_iff_pos] at hx hz
    exact ⟨⟨x, Or.inl rfl, hx⟩, ⟨z, Or.inr rfl, hz⟩⟩

/-- **The stability core of Lemma 5.6.** Let `(a, b)` be a strict pair, `t` a touch and `y` a
crossing of `f_{a,b}`, `t ≠ y`. Then there are a sign `σ` and `ε > 0` such that moving `a` (or
`b`) by less than `ε` never moves `σ · d(t, ·)` below its value at `a` (above its value at
`b`). -/
theorem touch_stable_core (hDMP : HasDMP T) {a b t y : T} (h : IsStrictPair a b)
    (ht : IsTouch (sgnf a b) t) (hy : IsCrossing (sgnf a b) y) (hty : t ≠ y) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ ε > 0,
      (∀ a', dist a a' < ε → 0 ≤ σ * (dist t a' - dist t a)) ∧
      (∀ b', dist b b' < ε → 0 ≤ σ * (dist t b - dist t b')) := by
  have h2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  set f := sgnf a b
  have htM : t ∈ midset a b := sgnf_eq_zero_iff.1 ht.2.1
  have htab : dist t a = dist t b := htM
  obtain ⟨γ, s, hs, hγ, rfl, -, -⟩ := exists_edgeParam hT ht.1
  obtain ⟨κ, r, hr, hκ, rfl, -, -⟩ := exists_edgeParam hT hy.1
  obtain ⟨ε₁, hε₁, hT1⟩ := ht.along hT hγ.arc hs rfl
  obtain ⟨ε₂, hε₂, hY1⟩ := hy.along hT hκ.arc hr rfl
  set d := dist (γ s) (κ r)
  have hd : 0 < d := dist_pos.2 hty
  obtain ⟨ρ₁, hρ₁, hc1⟩ := Metric.continuous_iff.1 hγ.arc.1 s (d / 3) (by positivity)
  obtain ⟨ρ₂, hρ₂, hc2⟩ := Metric.continuous_iff.1 hκ.arc.1 r (d / 3) (by positivity)
  set m := min (min (min ε₁ ε₂) (min ρ₁ ρ₂)) (min (min s (1 - s)) (min r (1 - r)))
  have hm : 0 < m := lt_min (lt_min (lt_min hε₁ hε₂) (lt_min hρ₁ hρ₂))
    (lt_min (lt_min hs.1 (by linarith [hs.2])) (lt_min hr.1 (by linarith [hr.2])))
  have hm1 : m ≤ ε₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hm2 : m ≤ ε₂ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hm3 : m ≤ ρ₁ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm4 : m ≤ ρ₂ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm5 : m ≤ s := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hm6 : m ≤ 1 - s := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hm7 : m ≤ r := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm8 : m ≤ 1 - r := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set δ := m / 2
  have hδ : 0 < δ := by positivity
  have hδm : δ < m := by simp only [δ]; linarith
  set tm := γ (s - δ); set tp := γ (s + δ)
  set ym := κ (r - δ); set yp := κ (r + δ)
  have hftm_tp : 0 < f tm * f tp :=
    hT1 _ ⟨by linarith, by linarith⟩ _ ⟨by linarith, by linarith⟩
  have hfy : f ym * f yp < 0 := hY1 _ ⟨by linarith, by linarith⟩ _ ⟨by linarith, by linarith⟩
  have hftm : f tm ≠ 0 := fun e => by rw [e, zero_mul] at hftm_tp; exact lt_irrefl _ hftm_tp
  have hftp : f tp ≠ 0 := fun e => by rw [e, mul_zero] at hftm_tp; exact lt_irrefl _ hftm_tp
  have hfym : f ym ≠ 0 := fun e => by rw [e, zero_mul] at hfy; exact lt_irrefl _ hfy
  have hfyp : f yp ≠ 0 := fun e => by rw [e, mul_zero] at hfy; exact lt_irrefl _ hfy
  set σ : ℝ := if 0 < f tm then 1 else -1
  have hσ1 : σ = 1 ∨ σ = -1 := by simp only [σ]; split_ifs <;> simp
  have hσ : 0 < σ * f tm ∧ 0 < σ * f tp := by
    by_cases hpos : 0 < f tm
    · simp only [σ, if_pos hpos, one_mul]
      exact ⟨hpos, pos_of_mul_pos_right hftm_tp hpos.le⟩
    · have hneg : f tm < 0 := lt_of_le_of_ne (not_lt.1 hpos) hftm
      simp only [σ, if_neg hpos]
      have : f tp < 0 := by
        by_contra hh; push_neg at hh
        have := mul_nonpos_of_nonpos_of_nonneg hneg.le hh; linarith
      constructor <;> linarith
  set ε₀ := min (min (|f tm|) (|f tp|)) (min (|f ym|) (|f yp|))
  have hε₀ : 0 < ε₀ := lt_min (lt_min (abs_pos.2 hftm) (abs_pos.2 hftp))
    (lt_min (abs_pos.2 hfym) (abs_pos.2 hfyp))
  have hε₀1 : ε₀ ≤ |f tm| := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀2 : ε₀ ≤ |f tp| := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀3 : ε₀ ≤ |f ym| := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀4 : ε₀ ≤ |f yp| := (min_le_right _ _).trans (min_le_right _ _)
  -- the three pieces
  set A₁ := γ '' Icc (s - δ) s
  set A₂ := γ '' Icc s (s + δ)
  set A₃ := κ '' Icc (r - δ) (r + δ)
  have hI1 : Icc (s - δ) (s + δ) ⊆ Icc (0 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hA12 : A₁ ∩ A₂ ⊆ {γ s} := by
    rintro _ ⟨⟨u, hu, rfl⟩, ⟨v, hv, he⟩⟩
    have := hγ.arc.2 (hI1 ⟨hu.1, hu.2.trans (by linarith)⟩) (hI1 ⟨by linarith [hv.1], hv.2⟩) he.symm
    have hu' : u = s := le_antisymm hu.2 (this ▸ hv.1)
    rw [hu']; rfl
  have hnear1 : ∀ u ∈ Icc (s - δ) (s + δ), dist (γ u) (γ s) < d / 3 := fun u hu =>
    hc1 u (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
  have hnear2 : ∀ u ∈ Icc (r - δ) (r + δ), dist (κ u) (κ r) < d / 3 := fun u hu =>
    hc2 u (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2])
  have hfar : ∀ u ∈ Icc (s - δ) (s + δ), ∀ v ∈ Icc (r - δ) (r + δ), γ u ≠ κ v := by
    intro u hu v hv he
    have h1 := hnear1 u hu; have h2 := hnear2 v hv
    rw [he] at h1
    have := dist_triangle (γ s) (κ v) (κ r)
    rw [dist_comm] at h1; linarith
  have hA13 : Disjoint A₁ A₃ := disjoint_left.2 fun _ ⟨u, hu, hue⟩ ⟨v, hv, hve⟩ =>
    hfar u ⟨hu.1, hu.2.trans (by linarith)⟩ v hv (hue.trans hve.symm)
  have hA23 : Disjoint A₂ A₃ := disjoint_left.2 fun _ ⟨u, hu, hue⟩ ⟨v, hv, hve⟩ =>
    hfar u ⟨by linarith [hu.1], hu.2⟩ v hv (hue.trans hve.symm)
  -- the contradiction for a moved site pair `(a', b')` close to `(a, b)`
  have key : ∀ a' b', dist a a' + dist b b' < min ε₀ (dist a b) → a' ≠ b' →
      ¬ σ * sgnf a' b' (γ s) < 0 := by
    intro a' b' hab' hne' hneg
    have hsurv : ∀ q, ε₀ ≤ |f q| → (0 < f q → 0 < sgnf a' b' q) ∧ (f q < 0 → sgnf a' b' q < 0) :=
      fun q hq => lemma_2_2_a (lt_of_lt_of_le hab' ((min_le_left _ _).trans hq))
    have hsσ : ∀ q, ε₀ ≤ |f q| → 0 < σ * f q → 0 < σ * sgnf a' b' q := by
      intro q hq hσq
      rcases hσ1 with h1 | h1 <;> rw [h1] at hσq ⊢
      · simp only [one_mul] at hσq ⊢; exact (hsurv q hq).1 hσq
      · simp only [neg_one_mul, neg_pos] at hσq ⊢; exact (hsurv q hq).2 hσq
    have hs1 := hsσ tm hε₀1 hσ.1
    have hs2 := hsσ tp hε₀2 hσ.2
    have hy' : sgnf a' b' ym * sgnf a' b' yp < 0 := by
      rcases sign_cases hfy with ⟨n, p⟩ | ⟨p, n⟩
      · exact mul_neg_of_neg_of_pos ((hsurv ym hε₀3).2 n) ((hsurv yp hε₀4).1 p)
      · exact mul_neg_of_pos_of_neg ((hsurv ym hε₀3).1 p) ((hsurv yp hε₀4).2 n)
    obtain ⟨n1, p1⟩ := signs_of_sigma hσ1 hs1 hneg
    obtain ⟨n2, p2⟩ := signs_of_sigma hσ1 hs2 hneg
    have hmem1 : ∀ w ∈ ({sgnf a' b' tm, sgnf a' b' (γ s)} : Set ℝ), ∃ z ∈ A₁, sgnf a' b' z = w := by
      rintro w (rfl | rfl)
      · exact ⟨tm, ⟨s - δ, ⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
      · exact ⟨γ s, ⟨s, ⟨by linarith, le_rfl⟩, rfl⟩, rfl⟩
    have hmem2 : ∀ w ∈ ({sgnf a' b' tp, sgnf a' b' (γ s)} : Set ℝ), ∃ z ∈ A₂, sgnf a' b' z = w := by
      rintro w (rfl | rfl)
      · exact ⟨tp, ⟨s + δ, ⟨by linarith, le_rfl⟩, rfl⟩, rfl⟩
      · exact ⟨γ s, ⟨s, ⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
    have hneg1 : ∃ z ∈ A₁, sgnf a' b' z < 0 := by
      obtain ⟨w, hw, hw0⟩ := n1; obtain ⟨z, hz, rfl⟩ := hmem1 w hw; exact ⟨z, hz, hw0⟩
    have hpos1 : ∃ z ∈ A₁, 0 < sgnf a' b' z := by
      obtain ⟨w, hw, hw0⟩ := p1; obtain ⟨z, hz, rfl⟩ := hmem1 w hw; exact ⟨z, hz, hw0⟩
    have hneg2 : ∃ z ∈ A₂, sgnf a' b' z < 0 := by
      obtain ⟨w, hw, hw0⟩ := n2; obtain ⟨z, hz, rfl⟩ := hmem2 w hw; exact ⟨z, hz, hw0⟩
    have hpos2 : ∃ z ∈ A₂, 0 < sgnf a' b' z := by
      obtain ⟨w, hw, hw0⟩ := p2; obtain ⟨z, hz, rfl⟩ := hmem2 w hw; exact ⟨z, hz, hw0⟩
    have hy3 : (∃ z ∈ A₃, sgnf a' b' z < 0) ∧ (∃ z ∈ A₃, 0 < sgnf a' b' z) := by
      have hym : ym ∈ A₃ := ⟨r - δ, ⟨le_rfl, by linarith⟩, rfl⟩
      have hyp : yp ∈ A₃ := ⟨r + δ, ⟨by linarith, le_rfl⟩, rfl⟩
      rcases sign_cases hy' with ⟨n, p⟩ | ⟨p, n⟩
      · exact ⟨⟨ym, hym, n⟩, ⟨yp, hyp, p⟩⟩
      · exact ⟨⟨yp, hyp, n⟩, ⟨ym, hym, p⟩⟩
    have hsne : sgnf a' b' (γ s) ≠ 0 := fun e => by rw [e, mul_zero] at hneg; exact lt_irrefl _ hneg
    refine false_of_three hne' h2 (three_le_encard_of_sets hγ.arc.isPreconnected_image
      hγ.arc.isPreconnected_image hκ.arc.isPreconnected_image hneg1 hpos1 hneg2 hpos2 hy3.1 hy3.2
      ?_ ?_ ?_)
    · refine disjoint_left.2 fun z ⟨hz1, hzM⟩ ⟨hz2, _⟩ => hsne ?_
      rw [← mem_singleton_iff.1 (hA12 ⟨hz1, hz2⟩)]; exact sgnf_eq_zero_iff.2 hzM
    · exact disjoint_left.2 fun z ⟨hz1, _⟩ ⟨hz3, _⟩ => disjoint_left.1 hA13 hz1 hz3
    · exact disjoint_left.2 fun z ⟨hz1, _⟩ ⟨hz3, _⟩ => disjoint_left.1 hA23 hz1 hz3
  refine ⟨σ, hσ1, min ε₀ (dist a b), lt_min hε₀ (dist_pos.2 h.1), fun a' ha' => ?_,
    fun b' hb' => ?_⟩
  · have hne' : a' ≠ b := fun e => by
      rw [e] at ha'; exact (lt_irrefl _ (ha'.trans_le (min_le_right _ _)))
    have := key a' b (by rw [dist_self, add_zero]; exact ha') hne'
    push_neg at this
    have hval : sgnf a' b (γ s) = dist (γ s) a' - dist (γ s) a := by
      unfold sgnf; rw [htab]
    rwa [hval] at this
  · have hne' : a ≠ b' := fun e => by
      rw [← e, dist_comm] at hb'; exact (lt_irrefl _ (hb'.trans_le (min_le_right _ _)))
    have := key a b' (by rw [dist_self, zero_add]; exact hb') hne'
    push_neg at this
    have hval : sgnf a b' (γ s) = dist (γ s) b - dist (γ s) b' := by
      unfold sgnf; rw [htab]
    rwa [hval] at this

/-- Global form of Lemma 5.6 (what the proof actually gives): both sites are local extrema of
`h_t` on all of `T`. -/
theorem touch_isLocalExtr (hDMP : HasDMP T) {a b t : T} (h : IsStrictPair a b)
    (hodd : Odd (oddCount a b)) (ht : IsTouch (sgnf a b) t) :
    IsLocalExtr (dist t) a ∧ IsLocalExtr (dist t) b := by
  obtain ⟨-, -, -, h4⟩ := cor_5_5 hT hDMP h
  obtain ⟨y₁, y₂, hM, hy₁, hy₂⟩ := h4 hodd
  have hty : t ≠ y₁ := fun e => not_isCrossing_and_isTouch hT (e ▸ hy₁) ht
  obtain ⟨σ, hσ, ε, hε, hA, hB⟩ := touch_stable_core hT hDMP h ht hy₁ hty
  have hloc : ∀ σ' : ℝ, (σ' = 1 ∨ σ' = -1) → ∀ c : T,
      (∀ c', dist c c' < ε → 0 ≤ σ' * (dist t c' - dist t c)) → IsLocalExtr (dist t) c := by
    intro σ' hσ' c hc
    have hev : ∀ᶠ c' in 𝓝 c, dist c c' < ε := by
      filter_upwards [ball_mem_nhds c hε] with c' hc'; rw [mem_ball, dist_comm] at hc'; exact hc'
    rcases hσ' with rfl | rfl
    · left; filter_upwards [hev] with c' hc'; have := hc c' hc'; linarith
    · right; filter_upwards [hev] with c' hc'; have := hc c' hc'; linarith
  refine ⟨hloc σ hσ a hA, hloc (-σ) ?_ b fun b' hb' => ?_⟩
  · rcases hσ with h | h <;> rw [h] <;> norm_num
  · have := hB b' hb'; linarith

/-- **Lemma 5.6 (stability of a touch).** Let `(a, b)` be a strict pair with `N(a, b)` odd and
`t` the touch in `M(a, b)`. If `a` is an edge point, then `a` is a local extremum of `h_t`
restricted to the open edge containing `a`; the same holds for `b`. -/
theorem lemma_5_6 (hDMP : HasDMP T) {a b t : T} (h : IsStrictPair a b)
    (hodd : Odd (oddCount a b)) (ht : IsTouch (sgnf a b) t) :
    (a ∉ vertices T → IsLocalExtrOn (dist t) (connectedComponentIn (vertices T)ᶜ a) a) ∧
    (b ∉ vertices T → IsLocalExtrOn (dist t) (connectedComponentIn (vertices T)ᶜ b) b) :=
  ⟨fun _ => (touch_isLocalExtr hT hDMP h hodd ht).1.on _,
    fun _ => (touch_isLocalExtr hT hDMP h hodd ht).2.on _⟩

end DoubleMidset
