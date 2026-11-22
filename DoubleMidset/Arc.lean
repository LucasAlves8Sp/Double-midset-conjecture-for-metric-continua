module

public import DoubleMidset.Defs
public import DoubleMidset.Classical.ArcParam
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Connected.PathConnected

/-!
# Arcs and their real parametrizations

An arc is handled through a *real parametrization*: a continuous map `g : ℝ → X` which is
injective on `[0,1]` (`IsArcParam`). Its arc is `g '' [0,1]`. This file collects the operations
used throughout: passing between `IsArcBetween` and parametrizations, subarcs, reversal,
concatenation of two arcs meeting in a common end, and arcs joining points of a path connected
set (the arc theorem, `DoubleMidset.Arc.exists_arc`).
-/

@[expose] public section

open Set Topology Function

namespace DoubleMidset

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A real parametrization of an arc: continuous, and injective on `[0,1]`. -/
def IsArcParam (g : ℝ → X) : Prop := Continuous g ∧ InjOn g (Icc 0 1)

namespace IsArcParam

variable {g : ℝ → X}

theorem continuous (hg : IsArcParam g) : Continuous g := hg.1

theorem injOn (hg : IsArcParam g) : InjOn g (Icc 0 1) := hg.2

theorem isCompact_image (hg : IsArcParam g) {s t : ℝ} : IsCompact (g '' Icc s t) :=
  isCompact_Icc.image hg.1

theorem isConnected_image (hg : IsArcParam g) {s t : ℝ} (hst : s ≤ t) :
    IsConnected (g '' Icc s t) :=
  (isConnected_Icc hst).image _ hg.1.continuousOn

theorem isPreconnected_image (hg : IsArcParam g) {s t : ℝ} : IsPreconnected (g '' Icc s t) :=
  isPreconnected_Icc.image _ hg.1.continuousOn

theorem isPreconnected_image_Ioo (hg : IsArcParam g) {s t : ℝ} :
    IsPreconnected (g '' Ioo s t) :=
  isPreconnected_Ioo.image _ hg.1.continuousOn

theorem isPreconnected_image_Ico (hg : IsArcParam g) {s t : ℝ} :
    IsPreconnected (g '' Ico s t) :=
  isPreconnected_Ico.image _ hg.1.continuousOn

theorem isPreconnected_image_Ioc (hg : IsArcParam g) {s t : ℝ} :
    IsPreconnected (g '' Ioc s t) :=
  isPreconnected_Ioc.image _ hg.1.continuousOn

theorem ne (hg : IsArcParam g) : g 0 ≠ g 1 := fun h =>
  zero_ne_one (hg.2 (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) h)

theorem eq_iff (hg : IsArcParam g) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    g s = g t ↔ s = t :=
  ⟨fun h => hg.2 hs ht h, fun h => h ▸ rfl⟩

/-- The arc of a parametrization, as an arc between its ends. -/
theorem isArcBetween [T2Space X] (hg : IsArcParam g) :
    IsArcBetween (g '' Icc 0 1) (g 0) (g 1) := by
  refine ⟨fun x => g x, ?_, ?_, rfl, rfl⟩
  · have hc : Continuous fun x : unitInterval => g x := hg.1.comp continuous_subtype_val
    exact (hc.isClosedEmbedding fun x y h => Subtype.ext (hg.2 x.2 y.2 h)).isEmbedding
  · ext x; constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩

/-- The reversed parametrization. -/
theorem symm (hg : IsArcParam g) : IsArcParam fun t => g (1 - t) := by
  refine ⟨hg.1.comp (continuous_const.sub continuous_id), fun s hs t ht h => ?_⟩
  have h1 : (1 - s) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h2 : (1 - t) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have := hg.2 h1 h2 h
  linarith

theorem symm_image (g : ℝ → X) : (fun t => g (1 - t)) '' Icc 0 1 = g '' Icc 0 1 := by
  ext x; constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩

/-- The affine reparametrization of the subarc `g '' [s, t]`. -/
theorem sub (hg : IsArcParam g) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    IsArcParam fun u => g (s + u * (t - s)) := by
  refine ⟨hg.1.comp (continuous_const.add (continuous_id.mul continuous_const)),
    fun a ha b hb h => ?_⟩
  have hts : 0 < t - s := by linarith
  have hmem : ∀ c ∈ Icc (0 : ℝ) 1, s + c * (t - s) ∈ Icc (0 : ℝ) 1 := fun c hc =>
    ⟨by nlinarith [hc.1], by nlinarith [hc.2]⟩
  have := hg.2 (hmem a ha) (hmem b hb) h
  have : (a - b) * (t - s) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

theorem sub_image (g : ℝ → X) {s t : ℝ} (hst : s ≤ t) :
    (fun u => g (s + u * (t - s))) '' Icc 0 1 = g '' Icc s t := by
  ext x; constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    rcases eq_or_lt_of_le hst with h | h
    · subst h
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have : v = s := le_antisymm hv.2 hv.1
      simp [this]
    · refine ⟨(v - s) / (t - s), ⟨div_nonneg (by linarith [hv.1]) (by linarith),
        (div_le_one (by linarith)).2 (by linarith [hv.2])⟩, ?_⟩
      congr 1
      field_simp
      ring

end IsArcParam

/-- Every arc between `p` and `q` has a real parametrization. -/
theorem IsArcBetween.exists_param {A : Set X} {p q : X} (h : IsArcBetween A p q) :
    ∃ g : ℝ → X, IsArcParam g ∧ g '' Icc 0 1 = A ∧ g 0 = p ∧ g 1 = q := by
  obtain ⟨f, hf, rfl, rfl, rfl⟩ := h
  refine ⟨fun t => f (projIcc 0 1 zero_le_one t), ⟨hf.continuous.comp continuous_projIcc,
    fun s hs t ht hst => ?_⟩, ?_, ?_, ?_⟩
  · have := hf.injective hst
    rw [projIcc_of_mem _ hs, projIcc_of_mem _ ht] at this
    exact congrArg Subtype.val this
  · ext x; constructor
    · rintro ⟨t, -, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, y.2, by simp [projIcc_of_mem _ y.2]⟩
  · simp only [projIcc_left]; rfl
  · simp only [projIcc_right]; rfl

theorem isArcBetween_iff [T2Space X] {A : Set X} {p q : X} :
    IsArcBetween A p q ↔ ∃ g : ℝ → X, IsArcParam g ∧ g '' Icc 0 1 = A ∧ g 0 = p ∧ g 1 = q :=
  ⟨IsArcBetween.exists_param, fun ⟨g, hg, hA, hp, hq⟩ => hA ▸ hp ▸ hq ▸ hg.isArcBetween⟩

theorem IsArcBetween.isArc {A : Set X} {p q : X} (h : IsArcBetween A p q) : IsArc A := by
  obtain ⟨f, hf, rfl, -, -⟩ := h
  exact ⟨(hf.toHomeomorph).symm⟩

theorem IsArcBetween.symm [T2Space X] {A : Set X} {p q : X} (h : IsArcBetween A p q) :
    IsArcBetween A q p := by
  obtain ⟨g, hg, rfl, rfl, rfl⟩ := h.exists_param
  have := hg.symm.isArcBetween
  simpa [IsArcParam.symm_image] using this

theorem IsArcBetween.ne {A : Set X} {p q : X} (h : IsArcBetween A p q) : p ≠ q := by
  obtain ⟨g, hg, -, rfl, rfl⟩ := h.exists_param
  exact hg.ne

theorem IsArcBetween.left_mem {A : Set X} {p q : X} (h : IsArcBetween A p q) : p ∈ A := by
  obtain ⟨f, -, rfl, rfl, -⟩ := h; exact ⟨0, rfl⟩

theorem IsArcBetween.right_mem {A : Set X} {p q : X} (h : IsArcBetween A p q) : q ∈ A := by
  obtain ⟨f, -, rfl, -, rfl⟩ := h; exact ⟨1, rfl⟩

theorem IsArcBetween.isCompact {A : Set X} {p q : X} (h : IsArcBetween A p q) : IsCompact A := by
  obtain ⟨f, hf, rfl, -, -⟩ := h; exact isCompact_range hf.continuous

theorem IsArcBetween.isConnected {A : Set X} {p q : X} (h : IsArcBetween A p q) :
    IsConnected A := by
  obtain ⟨f, hf, rfl, -, -⟩ := h; exact isConnected_range hf.continuous

theorem IsArc.exists_isArcBetween {A : Set X} (h : IsArc A) : ∃ p q, IsArcBetween A p q := by
  obtain ⟨e⟩ := h
  refine ⟨e.symm 0, e.symm 1, fun t => (e.symm t : X), ?_, ?_, rfl, rfl⟩
  · exact IsEmbedding.subtypeVal.comp e.symm.isEmbedding
  · ext x; constructor
    · rintro ⟨t, rfl⟩; exact (e.symm t).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩

section Concat

variable {g h : ℝ → X}

/-- The concatenation of two parametrizations with `g 1 = h 0`. -/
noncomputable def concat (g h : ℝ → X) (t : ℝ) : X :=
  if t ≤ 1 / 2 then g (2 * t) else h (2 * t - 1)

theorem concat_of_le {t : ℝ} (ht : t ≤ 1 / 2) : concat g h t = g (2 * t) := if_pos ht

theorem concat_of_lt {t : ℝ} (ht : 1 / 2 < t) : concat g h t = h (2 * t - 1) :=
  if_neg (not_le.2 ht)

theorem continuous_concat (hg : Continuous g) (hh : Continuous h) (h1 : g 1 = h 0) :
    Continuous (concat g h) := by
  refine Continuous.if_le (hg.comp (continuous_const.mul continuous_id))
    (hh.comp ((continuous_const.mul continuous_id).sub continuous_const)) continuous_id
    continuous_const fun t ht => ?_
  rw [ht]; norm_num [h1]

theorem concat_image (h1 : g 1 = h 0) :
    concat g h '' Icc 0 1 = g '' Icc 0 1 ∪ h '' Icc 0 1 := by
  ext x; constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h2 : t ≤ 1 / 2
    · left; rw [concat_of_le h2]; exact ⟨_, ⟨by linarith [ht.1], by linarith⟩, rfl⟩
    · right; rw [concat_of_lt (not_le.1 h2)]
      exact ⟨_, ⟨by linarith [not_le.1 h2], by linarith [ht.2]⟩, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      rw [concat_of_le (by linarith [ht.2])]; congr 1; ring
    · rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        rw [concat_of_le le_rfl]; norm_num [h1]
      · refine ⟨(t + 1) / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
        rw [concat_of_lt (by linarith)]; congr 1; ring

/-- Two arcs meeting only in a common end form an arc. -/
theorem IsArcParam.concat (hg : IsArcParam g) (hh : IsArcParam h) (h1 : g 1 = h 0)
    (hmeet : g '' Icc 0 1 ∩ h '' Icc 0 1 ⊆ {g 1}) : IsArcParam (DoubleMidset.concat g h) := by
  refine ⟨continuous_concat hg.1 hh.1 h1, fun s hs t ht hst => ?_⟩
  have key : ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → s ≤ 1 / 2 → 1 / 2 < t →
      DoubleMidset.concat g h s = DoubleMidset.concat g h t → False := by
    intro s t hs ht h2 h3 he
    rw [concat_of_le h2, concat_of_lt h3] at he
    have hm : g (2 * s) ∈ g '' Icc 0 1 ∩ h '' Icc 0 1 :=
      ⟨⟨_, ⟨by linarith [hs.1], by linarith⟩, rfl⟩,
        ⟨_, ⟨by linarith, by linarith [ht.2]⟩, he.symm⟩⟩
    have hgs := hmeet hm
    rw [mem_singleton_iff] at hgs
    have e1 : 2 * s = 1 := hg.2 ⟨by linarith [hs.1], by linarith⟩
      ⟨zero_le_one, le_rfl⟩ hgs
    have e2 : 2 * t - 1 = 0 := hh.2 ⟨by linarith, by linarith [ht.2]⟩
      ⟨le_rfl, zero_le_one⟩ (by rw [← he, hgs, h1])
    linarith
  by_cases h2 : s ≤ 1 / 2 <;> by_cases h3 : t ≤ 1 / 2
  · rw [concat_of_le h2, concat_of_le h3] at hst
    have := hg.2 ⟨by linarith [hs.1], by linarith⟩ ⟨by linarith [ht.1], by linarith⟩ hst
    linarith
  · exact (key s t hs ht h2 (not_le.1 h3) hst).elim
  · exact (key t s ht hs h3 (not_le.1 h2) hst.symm).elim
  · rw [concat_of_lt (not_le.1 h2), concat_of_lt (not_le.1 h3)] at hst
    have := hh.2 ⟨by linarith [not_le.1 h2], by linarith [hs.2]⟩
      ⟨by linarith [not_le.1 h3], by linarith [ht.2]⟩ hst
    linarith

theorem concat_zero : DoubleMidset.concat g h 0 = g 0 := by
  rw [concat_of_le (by norm_num)]; norm_num

theorem concat_one : DoubleMidset.concat g h 1 = h 1 := by
  rw [concat_of_lt (by norm_num)]; norm_num

end Concat

/-- Two arcs `A` from `p` to `q` and `B` from `q` to `r` meeting only in `q` form an arc from
`p` to `r`. -/
theorem IsArcBetween.union [T2Space X] {A B : Set X} {p q r : X} (hA : IsArcBetween A p q)
    (hB : IsArcBetween B q r) (hAB : A ∩ B ⊆ {q}) : IsArcBetween (A ∪ B) p r := by
  obtain ⟨g, hg, rfl, rfl, rfl⟩ := hA.exists_param
  obtain ⟨h, hh, rfl, hq, rfl⟩ := hB.exists_param
  have := (hg.concat hh hq.symm hAB).isArcBetween
  rwa [concat_image hq.symm, concat_zero, concat_one] at this

/-- **The arc theorem**, for sets: two distinct points of a path connected set in a Hausdorff
space are the ends of an arc contained in it. -/
theorem exists_isArcBetween_of_joinedIn [T2Space X] {S : Set X} {p q : X} (h : JoinedIn S p q)
    (hpq : p ≠ q) : ∃ A, IsArcBetween A p q ∧ A ⊆ S := by
  obtain ⟨f, hf, h0, h1, hr⟩ := Arc.exists_arc h.somePath hpq
  refine ⟨range f, ⟨f, hf, rfl, h0, h1⟩, hr.trans ?_⟩
  rintro _ ⟨t, rfl⟩; exact h.somePath_mem t

end DoubleMidset
