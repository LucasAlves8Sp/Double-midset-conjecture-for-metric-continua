module

public import DoubleMidset.ParamParity

/-!
# Crossings and touches (Definition 5.3)

* `IsCrossing.along`, `IsTouch.along`: along any arc through a crossing (touch) `y`, the function
  changes (keeps) its sign at `y`. The two sides of the arc lie in different components of
  `T \ {y}` (Lemma 2.4), hence in different components of `J \ {y}`.
* `isCrossing_of_param`, `isTouch_of_param`: a sign change (no sign change) at an isolated zero
  along an edge parametrization makes the point a crossing (touch); the open arc `J` is the image
  of a small parameter interval.
* `isCrossing_or_isTouch`: an isolated zero at an edge point is a crossing or a touch, and not
  both (`not_isCrossing_and_isTouch`).
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

/-- Open intervals are homeomorphic. -/
theorem nonempty_homeomorph_Ioo {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Nonempty (Ioo a b ≃ₜ Ioo c d) := by
  have hba : 0 < b - a := by linarith
  have hdc : 0 < d - c := by linarith
  let f : Ioo a b → Ioo c d := fun x => ⟨c + (x - a) / (b - a) * (d - c), by
    obtain ⟨x, hx1, hx2⟩ := x
    have h1 : 0 < (x - a) / (b - a) := div_pos (by linarith) hba
    have h2 : (x - a) / (b - a) < 1 := (div_lt_one hba).2 (by linarith)
    constructor <;> nlinarith⟩
  let g : Ioo c d → Ioo a b := fun y => ⟨a + (y - c) / (d - c) * (b - a), by
    obtain ⟨y, hy1, hy2⟩ := y
    have h1 : 0 < (y - c) / (d - c) := div_pos (by linarith) hdc
    have h2 : (y - c) / (d - c) < 1 := (div_lt_one hdc).2 (by linarith)
    constructor <;> nlinarith⟩
  have hfg : ∀ x, g (f x) = x := fun x => by
    apply Subtype.ext; simp only [f, g]; field_simp; ring
  have hgf : ∀ y, f (g y) = y := fun y => by
    apply Subtype.ext; simp only [f, g]; field_simp; ring
  have hfc : Continuous f := Continuous.subtype_mk (continuous_const.add
    (((continuous_subtype_val.sub continuous_const).div_const _).mul continuous_const)) _
  have hgc : Continuous g := Continuous.subtype_mk (continuous_const.add
    (((continuous_subtype_val.sub continuous_const).div_const _).mul continuous_const)) _
  exact ⟨⟨⟨f, g, hfg, hgf⟩, hfc, hgc⟩⟩

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

/-- The image of an open subinterval of `(0, 1)` under an edge parametrization is an open
arc. -/
theorem IsEdgeParam.isOpenArc_image {γ : ℝ → T} (hγ : IsEdgeParam γ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) : IsOpenArc (γ '' Ioo a b) := by
  refine ⟨hγ.isOpen_image_Ioo hT ha hb, ?_⟩
  -- `γ` is an embedding of `[a, b]`
  have hinj : InjOn γ (Icc a b) := hγ.arc.2.mono (Icc_subset_Icc ha hb)
  have hemb : IsEmbedding fun t : Ioo a b => γ t := by
    have hc : Continuous fun t : Icc a b => γ t := hγ.arc.1.comp continuous_subtype_val
    have hce := (hc.isClosedEmbedding fun x y h => Subtype.ext (hinj x.2 y.2 h)).isEmbedding
    have hi : IsEmbedding fun t : Ioo a b => (⟨t, Ioo_subset_Icc_self t.2⟩ : Icc a b) :=
      IsEmbedding.inclusion Ioo_subset_Icc_self
    exact hce.comp hi
  have hr : range (fun t : Ioo a b => γ t) = γ '' Ioo a b := by
    ext y; constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨e⟩ := nonempty_homeomorph_Ioo hab (zero_lt_one' ℝ)
  exact ⟨(Homeomorph.setCongr hr).symm.trans (hemb.toHomeomorph.symm.trans e)⟩

/-- **Along an arc through a crossing, the function changes sign.** -/
theorem IsCrossing.along {g : T → ℝ} {y : T} (hcr : IsCrossing g y) {k : ℝ → T}
    (hk : IsArcParam k) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (hky : k s₀ = y) :
    ∃ ε > 0, ∀ t ∈ Ioo (s₀ - ε) s₀, ∀ t' ∈ Ioo s₀ (s₀ + ε), g (k t) * g (k t') < 0 := by
  obtain ⟨-, -, J, hJ, hyJ, -, -, hside⟩ := hcr
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 (hJ.1.preimage hk.1) s₀
    (by rw [mem_preimage, hky]; exact hyJ)
  refine ⟨min ε₁ (min s₀ (1 - s₀)), lt_min hε₁ (lt_min hs₀.1 (by linarith [hs₀.2])),
    fun t ht t' ht' => ?_⟩
  have hm1 := min_le_left ε₁ (min s₀ (1 - s₀))
  have hm2 := (min_le_right ε₁ (min s₀ (1 - s₀))).trans (min_le_left _ _)
  have hm3 := (min_le_right ε₁ (min s₀ (1 - s₀))).trans (min_le_right _ _)
  have htJ : k t ∈ J := hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;>
    linarith [ht.1, ht.2])
  have ht'J : k t' ∈ J := hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;>
    linarith [ht'.1, ht'.2])
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hs₀.2]⟩
  have ht'01 : t' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht'.1, hs₀.1], by linarith [ht'.2]⟩
  have hs01 : s₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs₀
  have hty : k t ≠ y := fun e => ht.2.ne (hk.2 ht01 hs01 (e.trans hky.symm))
  have ht'y : k t' ≠ y := fun e => ht'.1.ne' (hk.2 ht'01 hs01 (e.trans hky.symm))
  have hsep := sides_separate hT.noSCC hk ht01.1 ht.2 ht'.1 ht'01.2
  rw [hky] at hsep
  refine hside (k t) ⟨htJ, hty⟩ (k t') ⟨ht'J, ht'y⟩ fun he => hsep ?_
  have hmem : k t' ∈ connectedComponentIn (J \ {y}) (k t) := he ▸ mem_connectedComponentIn
    ⟨ht'J, ht'y⟩
  have hsub : connectedComponentIn (J \ {y}) (k t) ⊆ connectedComponentIn {y}ᶜ (k t) :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨htJ, hty⟩) ((connectedComponentIn_subset _ _).trans
        fun z hz => hz.2)
  exact connectedComponentIn_eq (hsub hmem)

/-- **Along an arc through a touch, the function keeps its sign.** -/
theorem IsTouch.along {g : T → ℝ} {y : T} (hto : IsTouch g y) {k : ℝ → T}
    (hk : IsArcParam k) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (hky : k s₀ = y) :
    ∃ ε > 0, ∀ t ∈ Ioo (s₀ - ε) s₀, ∀ t' ∈ Ioo s₀ (s₀ + ε), 0 < g (k t) * g (k t') := by
  obtain ⟨-, -, J, hJ, hyJ, -, -, hside⟩ := hto
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 (hJ.1.preimage hk.1) s₀
    (by rw [mem_preimage, hky]; exact hyJ)
  refine ⟨min ε₁ (min s₀ (1 - s₀)), lt_min hε₁ (lt_min hs₀.1 (by linarith [hs₀.2])),
    fun t ht t' ht' => ?_⟩
  have hm1 := min_le_left ε₁ (min s₀ (1 - s₀))
  have hm2 := (min_le_right ε₁ (min s₀ (1 - s₀))).trans (min_le_left _ _)
  have hm3 := (min_le_right ε₁ (min s₀ (1 - s₀))).trans (min_le_right _ _)
  have htJ : k t ∈ J := hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;>
    linarith [ht.1, ht.2])
  have ht'J : k t' ∈ J := hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;>
    linarith [ht'.1, ht'.2])
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2, hs₀.2]⟩
  have ht'01 : t' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht'.1, hs₀.1], by linarith [ht'.2]⟩
  have hs01 : s₀ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs₀
  have hty : k t ≠ y := fun e => ht.2.ne (hk.2 ht01 hs01 (e.trans hky.symm))
  have ht'y : k t' ≠ y := fun e => ht'.1.ne' (hk.2 ht'01 hs01 (e.trans hky.symm))
  have hsep := sides_separate hT.noSCC hk ht01.1 ht.2 ht'.1 ht'01.2
  rw [hky] at hsep
  refine hside (k t) ⟨htJ, hty⟩ (k t') ⟨ht'J, ht'y⟩ fun he => hsep ?_
  have hmem : k t' ∈ connectedComponentIn (J \ {y}) (k t) := he ▸ mem_connectedComponentIn
    ⟨ht'J, ht'y⟩
  have hsub : connectedComponentIn (J \ {y}) (k t) ⊆ connectedComponentIn {y}ᶜ (k t) :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨htJ, hty⟩) ((connectedComponentIn_subset _ _).trans
        fun z hz => hz.2)
  exact connectedComponentIn_eq (hsub hmem)

omit hT in
/-- Zeros of a function with finitely many zeros are isolated along an arc. -/
theorem exists_isolated {g : T → ℝ} (hfin : (g ⁻¹' {0}).Finite) {k : ℝ → T} (hk : IsArcParam k)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∃ ε > 0, ∀ t ∈ Ioo (s - ε) (s + ε), t ≠ s → g (k t) ≠ 0 := by
  have hZ : {t | t ∈ Icc (0 : ℝ) 1 ∧ g (k t) = 0}.Finite :=
    Finite.of_finite_image (hfin.subset (by rintro _ ⟨t, ht, rfl⟩; exact ht.2))
      (hk.2.mono fun t ht => ht.1)
  set F := {t | t ∈ Icc (0 : ℝ) 1 ∧ g (k t) = 0} \ {s}
  have hFc : IsClosed F := (hZ.subset diff_subset).isClosed
  have hsF : s ∉ F := fun h => h.2 rfl
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl s hsF
  refine ⟨min ε₁ (min s (1 - s)), lt_min hε₁ (lt_min hs.1 (by linarith [hs.2])),
    fun t ht hts h0 => ?_⟩
  have hm1 := min_le_left ε₁ (min s (1 - s))
  have hm2 := (min_le_right ε₁ (min s (1 - s))).trans (min_le_left _ _)
  have hm3 := (min_le_right ε₁ (min s (1 - s))).trans (min_le_right _ _)
  refine hball (show t ∈ ball s ε₁ by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;>
    linarith [ht.1, ht.2]) ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, h0⟩, hts⟩

/-- An isolated zero with a sign change along an edge parametrization is a crossing. -/
theorem isCrossing_of_param {γ : ℝ → T} (hγ : IsEdgeParam γ) {g : T → ℝ}
    (hfin : (g ⁻¹' {0}).Finite) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hcr : IsParamCrossing (g ∘ γ) s) : IsCrossing g (γ s) := by
  obtain ⟨ε₀, hε₀, hiso⟩ := exists_isolated hfin hγ.arc hs
  obtain ⟨h0, ε₁, hε₁, hside⟩ := hcr
  set ε := min (min ε₀ ε₁) (min s (1 - s))
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (lt_min hs.1 (by linarith [hs.2]))
  have hm0 : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hm1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hm2 : ε ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : ε ≤ 1 - s := (min_le_right _ _).trans (min_le_right _ _)
  set J := γ '' Ioo (s - ε) (s + ε)
  have hJs : ∀ t ∈ Ioo (s - ε) (s + ε), t ∈ Ioo (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨hγ.interior s hs, h0, J, hγ.isOpenArc_image hT (by linarith) (by linarith)
    (by linarith), ⟨s, ⟨by linarith, by linarith⟩, rfl⟩,
    ⟨_, ⟨γ s, hγ.interior s hs, rfl⟩, by
      rw [← hγ.image_Ioo_eq hT hs]; exact image_mono fun t ht => hJs t ht⟩, ?_, ?_⟩
  · ext z; simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      by_contra hts
      exact hiso t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (fun e => hts (e ▸ rfl)) hz
    · rintro rfl; exact ⟨⟨s, ⟨by linarith, by linarith⟩, rfl⟩, h0⟩
  · rintro _ ⟨⟨t₁, ht₁, rfl⟩, hz₁⟩ _ ⟨⟨t₂, ht₂, rfl⟩, hz₂⟩ hne
    have ht₁s : t₁ ≠ s := fun e => hz₁ (e ▸ rfl)
    have ht₂s : t₂ ≠ s := fun e => hz₂ (e ▸ rfl)
    -- points on the same side lie in one component of `J \ {γ s}`
    have hsame : ∀ a ∈ Ioo (s - ε) (s + ε), ∀ b ∈ Ioo (s - ε) (s + ε), a ≠ s → b ≠ s →
        (a < s ↔ b < s) → connectedComponentIn (J \ {γ s}) (γ a) =
          connectedComponentIn (J \ {γ s}) (γ b) := by
      intro a ha b hb has hbs hab
      have hsub : γ '' uIcc a b ⊆ J \ {γ s} := by
        rintro _ ⟨c, hc, rfl⟩
        have hcI : c ∈ Ioo (s - ε) (s + ε) := by
          rw [mem_uIcc] at hc
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            exact ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩
        refine ⟨⟨c, hcI, rfl⟩, fun e => ?_⟩
        have hcs : c = s := hγ.arc.2 (Ioo_subset_Icc_self (hJs c hcI))
          (Ioo_subset_Icc_self hs) e
        rw [hcs, mem_uIcc] at hc
        rcases lt_or_gt_of_ne has with h | h
        · have := hab.1 h; rcases hc with ⟨-, h2⟩ | ⟨-, h2⟩ <;> linarith
        · have : s < b := lt_of_le_of_ne (not_lt.1 fun h' => absurd (hab.2 h')
            (not_lt.2 h.le)) (Ne.symm hbs)
          rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
      have hpc : IsPreconnected (γ '' uIcc a b) := isPreconnected_uIcc.image _
        hγ.arc.1.continuousOn
      exact connectedComponentIn_eq (hpc.subset_connectedComponentIn ⟨a, left_mem_uIcc, rfl⟩
        hsub ⟨b, right_mem_uIcc, rfl⟩)
    have hopp : ¬ (t₁ < s ↔ t₂ < s) := fun h => hne (hsame t₁ ht₁ t₂ ht₂ ht₁s ht₂s h)
    rcases lt_or_gt_of_ne ht₁s with h1 | h1
    · have h2 : s < t₂ := lt_of_le_of_ne (not_lt.1 fun h => hopp ⟨fun _ => h,
        fun _ => h1⟩) (Ne.symm ht₂s)
      exact hside t₁ ⟨by linarith [ht₁.1], h1⟩ t₂ ⟨h2, by linarith [ht₂.2]⟩
    · have h2 : t₂ < s := by
        by_contra h; push_neg at h
        exact hopp ⟨fun h' => absurd h' (not_lt.2 h1.le),
          fun h' => absurd h' (not_lt.2 h)⟩
      rw [mul_comm]
      exact hside t₂ ⟨by linarith [ht₂.1], h2⟩ t₁ ⟨h1, by linarith [ht₁.2]⟩

/-- An isolated zero without a sign change along an edge parametrization is a touch. -/
theorem isTouch_of_param {γ : ℝ → T} (hγ : IsEdgeParam γ) {g : T → ℝ}
    (hfin : (g ⁻¹' {0}).Finite) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (hcr : IsParamTouch (g ∘ γ) s) : IsTouch g (γ s) := by
  obtain ⟨ε₀, hε₀, hiso⟩ := exists_isolated hfin hγ.arc hs
  obtain ⟨h0, ε₁, hε₁, hside⟩ := hcr
  set ε := min (min ε₀ ε₁) (min s (1 - s))
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (lt_min hs.1 (by linarith [hs.2]))
  have hm0 : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hm1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hm2 : ε ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : ε ≤ 1 - s := (min_le_right _ _).trans (min_le_right _ _)
  set J := γ '' Ioo (s - ε) (s + ε)
  have hJs : ∀ t ∈ Ioo (s - ε) (s + ε), t ∈ Ioo (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨hγ.interior s hs, h0, J, hγ.isOpenArc_image hT (by linarith) (by linarith)
    (by linarith), ⟨s, ⟨by linarith, by linarith⟩, rfl⟩,
    ⟨_, ⟨γ s, hγ.interior s hs, rfl⟩, by
      rw [← hγ.image_Ioo_eq hT hs]; exact image_mono fun t ht => hJs t ht⟩, ?_, ?_⟩
  · ext z; simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      by_contra hts
      exact hiso t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (fun e => hts (e ▸ rfl)) hz
    · rintro rfl; exact ⟨⟨s, ⟨by linarith, by linarith⟩, rfl⟩, h0⟩
  · rintro _ ⟨⟨t₁, ht₁, rfl⟩, hz₁⟩ _ ⟨⟨t₂, ht₂, rfl⟩, hz₂⟩ hne
    have ht₁s : t₁ ≠ s := fun e => hz₁ (e ▸ rfl)
    have ht₂s : t₂ ≠ s := fun e => hz₂ (e ▸ rfl)
    -- points on the same side lie in one component of `J \ {γ s}`
    have hsame : ∀ a ∈ Ioo (s - ε) (s + ε), ∀ b ∈ Ioo (s - ε) (s + ε), a ≠ s → b ≠ s →
        (a < s ↔ b < s) → connectedComponentIn (J \ {γ s}) (γ a) =
          connectedComponentIn (J \ {γ s}) (γ b) := by
      intro a ha b hb has hbs hab
      have hsub : γ '' uIcc a b ⊆ J \ {γ s} := by
        rintro _ ⟨c, hc, rfl⟩
        have hcI : c ∈ Ioo (s - ε) (s + ε) := by
          rw [mem_uIcc] at hc
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
            exact ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩
        refine ⟨⟨c, hcI, rfl⟩, fun e => ?_⟩
        have hcs : c = s := hγ.arc.2 (Ioo_subset_Icc_self (hJs c hcI))
          (Ioo_subset_Icc_self hs) e
        rw [hcs, mem_uIcc] at hc
        rcases lt_or_gt_of_ne has with h | h
        · have := hab.1 h; rcases hc with ⟨-, h2⟩ | ⟨-, h2⟩ <;> linarith
        · have : s < b := lt_of_le_of_ne (not_lt.1 fun h' => absurd (hab.2 h')
            (not_lt.2 h.le)) (Ne.symm hbs)
          rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
      have hpc : IsPreconnected (γ '' uIcc a b) := isPreconnected_uIcc.image _
        hγ.arc.1.continuousOn
      exact connectedComponentIn_eq (hpc.subset_connectedComponentIn ⟨a, left_mem_uIcc, rfl⟩
        hsub ⟨b, right_mem_uIcc, rfl⟩)
    have hopp : ¬ (t₁ < s ↔ t₂ < s) := fun h => hne (hsame t₁ ht₁ t₂ ht₂ ht₁s ht₂s h)
    rcases lt_or_gt_of_ne ht₁s with h1 | h1
    · have h2 : s < t₂ := lt_of_le_of_ne (not_lt.1 fun h => hopp ⟨fun _ => h,
        fun _ => h1⟩) (Ne.symm ht₂s)
      exact hside t₁ ⟨by linarith [ht₁.1], h1⟩ t₂ ⟨h2, by linarith [ht₂.2]⟩
    · have h2 : t₂ < s := by
        by_contra h; push_neg at h
        exact hopp ⟨fun h' => absurd h' (not_lt.2 h1.le),
          fun h' => absurd h' (not_lt.2 h)⟩
      rw [mul_comm]
      exact hside t₂ ⟨by linarith [ht₂.1], h2⟩ t₁ ⟨h1, by linarith [ht₁.2]⟩

/-- **Dichotomy.** A zero of `g` at an edge point, `g` continuous with finitely many zeros, is a
crossing or a touch. -/
theorem isCrossing_or_isTouch {g : T → ℝ} (hg : Continuous g) (hfin : (g ⁻¹' {0}).Finite)
    {y : T} (hy : y ∉ vertices T) (hy0 : g y = 0) : IsCrossing g y ∨ IsTouch g y := by
  obtain ⟨γ, s, hs, hγ, rfl, -, -⟩ := exists_edgeParam hT hy
  obtain ⟨ε, hε, hiso⟩ := exists_isolated hfin hγ.arc hs
  have hc : Continuous (g ∘ γ) := hg.comp hγ.arc.1
  have hL := const_sign isPreconnected_Ioo hc.continuousOn fun t ht =>
    hiso t ⟨ht.1, by linarith [ht.2]⟩ ht.2.ne
  have hR := const_sign isPreconnected_Ioo hc.continuousOn fun t ht =>
    hiso t ⟨by linarith [ht.1], ht.2⟩ ht.1.ne'
  set t₁ := s - ε / 2
  set t₂ := s + ε / 2
  have ht₁ : t₁ ∈ Ioo (s - ε) s := ⟨by simp only [t₁]; linarith, by simp only [t₁]; linarith⟩
  have ht₂ : t₂ ∈ Ioo s (s + ε) := ⟨by simp only [t₂]; linarith, by simp only [t₂]; linarith⟩
  have hne : (g ∘ γ) t₁ * (g ∘ γ) t₂ ≠ 0 := mul_ne_zero
    (hiso t₁ ⟨ht₁.1, by linarith [ht₁.2]⟩ ht₁.2.ne) (hiso t₂ ⟨by linarith [ht₂.1], ht₂.2⟩ ht₂.1.ne')
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · left
    refine isCrossing_of_param hT hγ hfin hs ⟨hy0, ε, hε, fun t ht t' ht' => ?_⟩
    have h1 := hL t ht t₁ ht₁
    have h2 := hR t' ht' t₂ ht₂
    nlinarith [mul_pos h1 h2, sq_nonneg ((g ∘ γ) t₁), sq_nonneg ((g ∘ γ) t₂)]
  · right
    refine isTouch_of_param hT hγ hfin hs ⟨hy0, ε, hε, fun t ht t' ht' => ?_⟩
    have h1 := hL t ht t₁ ht₁
    have h2 := hR t' ht' t₂ ht₂
    nlinarith [mul_pos h1 h2, sq_nonneg ((g ∘ γ) t₁), sq_nonneg ((g ∘ γ) t₂)]

/-- A zero is not both a crossing and a touch. -/
theorem not_isCrossing_and_isTouch {g : T → ℝ} {y : T} (hcr : IsCrossing g y)
    (hto : IsTouch g y) : False := by
  obtain ⟨γ, s, hs, hγ, rfl, -, -⟩ := exists_edgeParam hT hcr.1
  obtain ⟨ε₁, hε₁, h1⟩ := hcr.along hT hγ.arc hs rfl
  obtain ⟨ε₂, hε₂, h2⟩ := hto.along hT hγ.arc hs rfl
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have a1 := h1 (s - ε / 2) ⟨by linarith [min_le_left ε₁ ε₂], by linarith⟩ (s + ε / 2)
    ⟨by linarith, by linarith [min_le_left ε₁ ε₂]⟩
  have a2 := h2 (s - ε / 2) ⟨by linarith [min_le_right ε₁ ε₂], by linarith⟩ (s + ε / 2)
    ⟨by linarith, by linarith [min_le_right ε₁ ε₂]⟩
  linarith

end DoubleMidset
