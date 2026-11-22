module

public import DoubleMidset.Dendrite

/-!
# The order of a point; Lemma 2.4

`order p` is the number of components of `X \ {p}`. A set of points of `X \ {p}` lying in
pairwise different components has at most `order p` elements (`encard_le_order`), and there are
`order p` such points (`exists_points_of_le_order`).

Lemma 2.4 (`lemma_2_4_sides`, `two_le_order_of_mem_arc`, `three_le_order_of_triod`): in a
dendrite, the two components of `A \ {y}` for an interior point `y` of an arc `A` lie in different
components of `X \ {y}`; hence `y` has order at least two, and the center of a simple triod has
order at least three.
-/

@[expose] public section

open Set Topology Function

namespace DoubleMidset

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The set of components of `X \ {p}`. -/
def compsAt (p : X) : Set (Set X) := {C : Set X | ∃ x, x ≠ p ∧ C = connectedComponentIn {p}ᶜ x}

theorem order_eq (p : X) : order p = (compsAt p).encard := rfl

/-- Points of `X \ {p}` in pairwise different components number at most `order p`. -/
theorem encard_le_order {p : X} {S : Set X} (hS : S ⊆ {p}ᶜ)
    (hinj : InjOn (connectedComponentIn {p}ᶜ) S) : S.encard ≤ order p := by
  rw [← hinj.encard_image, order_eq]
  apply encard_le_encard
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hS hx, rfl⟩

/-- Conversely, `k ≤ order p` gives `k` points in pairwise different components. -/
theorem exists_points_of_le_order {p : X} {k : ℕ∞} (hk : k ≤ order p) :
    ∃ S : Set X, S ⊆ {p}ᶜ ∧ S.encard = k ∧ InjOn (connectedComponentIn {p}ᶜ) S := by
  obtain ⟨t, ht, htk⟩ := exists_subset_encard_eq hk
  have hrep : ∀ C ∈ t, ∃ x, x ≠ p ∧ C = connectedComponentIn {p}ᶜ x := fun C hC => ht hC
  haveI : Nonempty X := ⟨p⟩
  choose! r hr hrC using hrep
  have hinj : InjOn r t := fun C hC D hD h => by rw [hrC C hC, hrC D hD, h]
  refine ⟨r '' t, ?_, by rw [hinj.encard_image, htk], ?_⟩
  · rintro _ ⟨C, hC, rfl⟩; exact hr C hC
  · rintro _ ⟨C, hC, rfl⟩ _ ⟨D, hD, rfl⟩ h
    rw [← hrC C hC, ← hrC D hD] at h; rw [h]

theorem two_le_order {p x y : X} (hx : x ≠ p) (hy : y ≠ p)
    (h : connectedComponentIn {p}ᶜ x ≠ connectedComponentIn {p}ᶜ y) : 2 ≤ order p := by
  have hxy : x ≠ y := fun e => h (e ▸ rfl)
  rw [← encard_pair hxy]
  refine encard_le_order ?_ ?_
  · rintro z (rfl | rfl) <;> assumption
  · rintro a (rfl | rfl) b (rfl | rfl) e
    · rfl
    · exact (h e).elim
    · exact (h e.symm).elim
    · rfl

theorem three_le_order {p x y z : X} (hx : x ≠ p) (hy : y ≠ p) (hz : z ≠ p)
    (hxy : connectedComponentIn {p}ᶜ x ≠ connectedComponentIn {p}ᶜ y)
    (hxz : connectedComponentIn {p}ᶜ x ≠ connectedComponentIn {p}ᶜ z)
    (hyz : connectedComponentIn {p}ᶜ y ≠ connectedComponentIn {p}ᶜ z) : 3 ≤ order p := by
  have h1 : x ≠ y := fun e => hxy (e ▸ rfl)
  have h2 : x ≠ z := fun e => hxz (e ▸ rfl)
  have h3 : y ≠ z := fun e => hyz (e ▸ rfl)
  have : ({x, y, z} : Set X).encard = 3 := by
    rw [encard_insert_of_notMem (by simp [h1, h2]), encard_pair h3]; rfl
  rw [← this]
  refine encard_le_order ?_ ?_
  · rintro w (rfl | rfl | rfl) <;> assumption
  · rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) e <;> first | rfl | (exfalso; simp_all)

section Dendrite

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyConnectedSpace X] (hD : ∀ C : Set X, ¬ IsSimpleClosedCurve C)
include hD

/-- **Lemma 2.4.** If `y` is a point of the arc `A` other than its ends, then points in different
components of `A \ {y}` lie in different components of `X \ {y}`. -/
theorem lemma_2_4_sides {A : Set X} {p q y : X} (hA : IsArcBetween A p q) (hy : y ∈ A)
    (hyp : y ≠ p) (hyq : y ≠ q) {y₁ y₂ : X} (h₁ : y₁ ∈ A \ {y}) (h₂ : y₂ ∈ A \ {y})
    (h : connectedComponentIn (A \ {y}) y₁ ≠ connectedComponentIn (A \ {y}) y₂) :
    connectedComponentIn {y}ᶜ y₁ ≠ connectedComponentIn {y}ᶜ y₂ := by
  obtain ⟨g, hg, rfl, rfl, rfl⟩ := hA.exists_param
  obtain ⟨t, ht, rfl⟩ := hy
  obtain ⟨⟨s₁, hs₁, rfl⟩, hy₁⟩ := h₁
  obtain ⟨⟨s₂, hs₂, rfl⟩, hy₂⟩ := h₂
  have hne₁ : s₁ ≠ t := fun e => hy₁ (e ▸ rfl)
  have hne₂ : s₂ ≠ t := fun e => hy₂ (e ▸ rfl)
  -- points on the same side lie in one component of `A \ {y}`
  have same : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → a ≠ t → b ≠ t →
      (a < t ↔ b < t) →
      connectedComponentIn (g '' Icc 0 1 \ {g t}) (g a) =
        connectedComponentIn (g '' Icc 0 1 \ {g t}) (g b) := by
    intro a b ha hb hat hbt hab
    have hsub : g '' uIcc a b ⊆ g '' Icc 0 1 \ {g t} := by
      rintro _ ⟨c, hc, rfl⟩
      have hc01 : c ∈ Icc (0 : ℝ) 1 := by
        rcases le_total a b with h | h
        · rw [uIcc_of_le h] at hc; exact ⟨ha.1.trans hc.1, hc.2.trans hb.2⟩
        · rw [uIcc_of_ge h] at hc; exact ⟨hb.1.trans hc.1, hc.2.trans ha.2⟩
      refine ⟨⟨c, hc01, rfl⟩, fun e => ?_⟩
      have hct : c = t := hg.2 hc01 ht e
      rw [hct, mem_uIcc] at hc
      rcases lt_or_gt_of_ne hat with h' | h'
      · have hb' := hab.1 h'
        rcases hc with ⟨-, h3⟩ | ⟨-, h3⟩ <;> linarith
      · have hb' : t < b := lt_of_le_of_ne
          (not_lt.1 fun h3 => absurd (hab.2 h3) (not_lt.2 h'.le)) (Ne.symm hbt)
        rcases hc with ⟨h3, -⟩ | ⟨h3, -⟩ <;> linarith
    have hpc : IsPreconnected (g '' uIcc a b) := isPreconnected_uIcc.image _ hg.1.continuousOn
    have hb' : g b ∈ g '' uIcc a b := ⟨b, right_mem_uIcc, rfl⟩
    have ha' : g a ∈ g '' uIcc a b := ⟨a, left_mem_uIcc, rfl⟩
    exact connectedComponentIn_eq (hpc.subset_connectedComponentIn ha' hsub hb')
  -- so `s₁` and `s₂` lie on different sides of `t`
  have hside : s₁ < t ∧ t < s₂ ∨ s₂ < t ∧ t < s₁ := by
    rcases lt_or_gt_of_ne hne₁ with h1 | h1 <;> rcases lt_or_gt_of_ne hne₂ with h2 | h2
    · exact (h (same _ _ hs₁ hs₂ hne₁ hne₂ ⟨fun _ => h2, fun _ => h1⟩)).elim
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact (h (same _ _ hs₁ hs₂ hne₁ hne₂ ⟨fun h3 => absurd h3 (not_lt.2 h1.le),
        fun h3 => absurd h3 (not_lt.2 h2.le)⟩)).elim
  rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact sides_separate hD hg hs₁.1 h1 h2 hs₂.2
  · exact (sides_separate hD hg hs₂.1 h1 h2 hs₁.2).symm

/-- **Lemma 2.4**, second part: an interior point of an arc has order at least two. -/
theorem two_le_order_of_mem_arc {A : Set X} {p q y : X} (hA : IsArcBetween A p q) (hy : y ∈ A)
    (hyp : y ≠ p) (hyq : y ≠ q) : 2 ≤ order y :=
  two_le_order hyp.symm hyq.symm (ends_separate hD hA hy hyp hyq)

/-- **Lemma 2.4**, third part: the center of a simple triod has order at least three. -/
theorem three_le_order_of_triod {v p₁ p₂ p₃ : X} {A₁ A₂ A₃ : Set X} (h₁ : IsArcBetween A₁ v p₁)
    (h₂ : IsArcBetween A₂ v p₂) (h₃ : IsArcBetween A₃ v p₃) (h₁₂ : A₁ ∩ A₂ = {v})
    (h₁₃ : A₁ ∩ A₃ = {v}) (h₂₃ : A₂ ∩ A₃ = {v}) : 3 ≤ order v := by
  have key : ∀ {B₁ B₂ : Set X} {q₁ q₂ : X}, IsArcBetween B₁ v q₁ → IsArcBetween B₂ v q₂ →
      B₁ ∩ B₂ = {v} → connectedComponentIn {v}ᶜ q₁ ≠ connectedComponentIn {v}ᶜ q₂ := by
    intro B₁ B₂ q₁ q₂ hB₁ hB₂ hB
    have hu := hB₁.symm.union hB₂ (by rw [hB])
    exact ends_separate hD hu (Or.inl hB₁.left_mem) hB₁.ne hB₂.ne
  exact three_le_order h₁.ne.symm h₂.ne.symm h₃.ne.symm (key h₁ h₂ h₁₂) (key h₁ h₃ h₁₃)
    (key h₂ h₃ h₂₃)

end Dendrite

end DoubleMidset
