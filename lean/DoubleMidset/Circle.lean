module

public import DoubleMidset.Arc
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Simple closed curves

* `IsSimpleClosedCurve.exists_param`: a simple closed curve `C` is `c '' [0,1]` for a continuous
  `c : ℝ → X` of period one, injective on `[0,1)`.
* `isSimpleClosedCurve_union`: two arcs with the same ends that meet only in their ends form a
  simple closed curve.
-/

@[expose] public section

open Set Topology Function Real

namespace DoubleMidset

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The standard parametrization `t ↦ e⁻¹(exp(2πit))` of a simple closed curve. -/
theorem IsSimpleClosedCurve.exists_param {C : Set X} (hC : IsSimpleClosedCurve C) :
    ∃ c : ℝ → X, Continuous c ∧ (∀ t, c (t + 1) = c t) ∧ InjOn c (Ico 0 1) ∧
      c '' Icc 0 1 = C ∧ c '' Ico 0 1 = C := by
  obtain ⟨e⟩ := hC
  let c : ℝ → X := fun t => (e.symm (Circle.exp (2 * π * t)) : X)
  have hc : Continuous c :=
    continuous_subtype_val.comp (e.symm.continuous.comp
      (Circle.exp.continuous.comp (continuous_const.mul continuous_id)))
  have hper : ∀ t, c (t + 1) = c t := fun t => by
    simp only [c, mul_add, mul_one, Circle.exp_add_two_pi]
  have hinj : InjOn c (Ico 0 1) := by
    intro s hs t ht hst
    have h1 : Circle.exp (2 * π * s) = Circle.exp (2 * π * t) :=
      e.symm.injective (Subtype.ext hst)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h1
    have hpi : 0 < π := pi_pos
    have hm' : s - t = m := by
      have : 2 * π * (s - t) = 2 * π * m := by linarith
      exact mul_left_cancel₀ (by positivity) this
    have h2 : (m : ℝ) < 1 := by linarith [hs.2, ht.1]
    have h3 : (-1 : ℝ) < m := by linarith [hs.1, ht.2]
    have : m = 0 := by
      have := Int.cast_lt.1 (show (m : ℝ) < ((1 : ℤ) : ℝ) by simpa using h2)
      have := Int.cast_lt.1 (show ((-1 : ℤ) : ℝ) < (m : ℝ) by simpa using h3)
      omega
    subst this
    simp at hm'; linarith
  have hsurj : ∀ x ∈ C, ∃ t ∈ Ico (0 : ℝ) 1, c t = x := by
    intro x hx
    set z := e ⟨x, hx⟩
    have hpi : 0 < π := pi_pos
    have harg := Complex.arg_le_pi (z : ℂ)
    have harg' := Complex.neg_pi_lt_arg (z : ℂ)
    by_cases h0 : 0 ≤ Complex.arg (z : ℂ)
    · rcases eq_or_lt_of_le harg with hpi' | hlt
      · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
        have : Circle.exp (2 * π * (1 / 2)) = z := by
          rw [← Circle.exp_arg z, hpi']; ring_nf
        simp only [c, this, z, Homeomorph.symm_apply_apply]
      · refine ⟨Complex.arg z / (2 * π), ⟨by positivity, by
          rw [div_lt_one (by positivity)]; linarith⟩, ?_⟩
        have : Circle.exp (2 * π * (Complex.arg z / (2 * π))) = z := by
          rw [mul_div_cancel₀ _ (by positivity), Circle.exp_arg]
        simp only [c, this, z, Homeomorph.symm_apply_apply]
    · refine ⟨Complex.arg z / (2 * π) + 1, ⟨?_, ?_⟩, ?_⟩
      · have : -1 / 2 < Complex.arg z / (2 * π) := by
          rw [lt_div_iff₀ (by positivity)]; linarith
        linarith
      · have : Complex.arg z / (2 * π) < 0 := div_neg_of_neg_of_pos (not_le.1 h0) (by positivity)
        linarith
      · have : Circle.exp (2 * π * (Complex.arg z / (2 * π) + 1)) = z := by
          rw [mul_add, mul_div_cancel₀ _ (by positivity), mul_one, Circle.exp_add_two_pi,
            Circle.exp_arg]
        simp only [c, this, z, Homeomorph.symm_apply_apply]
  have hrange : ∀ t, c t ∈ C := fun t => (e.symm _).2
  have hIco : c '' Ico 0 1 = C := by
    refine Subset.antisymm (by rintro _ ⟨t, -, rfl⟩; exact hrange t) fun x hx => ?_
    obtain ⟨t, ht, rfl⟩ := hsurj x hx
    exact ⟨t, ht, rfl⟩
  refine ⟨c, hc, hper, hinj, Subset.antisymm (by rintro _ ⟨t, -, rfl⟩; exact hrange t) ?_, hIco⟩
  rw [← hIco]; exact image_mono Ico_subset_Icc_self

section Union

variable [T2Space X] {a b : ℝ → X}

private theorem circle_re_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have := Circle.normSq_coe z
  rw [Complex.normSq_apply] at this; nlinarith

private theorem circle_re_mem (z : Circle) : (z : ℂ).re ∈ Icc (-1 : ℝ) 1 := by
  have := circle_re_sq z
  constructor <;> nlinarith [sq_nonneg (z : ℂ).im, sq_nonneg ((z : ℂ).re + 1),
    sq_nonneg ((z : ℂ).re - 1)]

private theorem arccos_div_mem (x : ℝ) : arccos x / π ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (arccos_nonneg x) pi_pos.le, (div_le_one pi_pos).2 (arccos_le_pi x)⟩

/-- The loop through two arcs with common ends. -/
noncomputable def twoArcLoop (a b : ℝ → X) (z : Circle) : X :=
  if (0 : ℝ) ≤ (z : ℂ).im then a (arccos (z : ℂ).re / π) else b (arccos (z : ℂ).re / π)

private theorem circle_eq_of (z w : Circle) (hre : (z : ℂ).re = (w : ℂ).re)
    (him : 0 ≤ (z : ℂ).im ∧ 0 ≤ (w : ℂ).im ∨ (z : ℂ).im ≤ 0 ∧ (w : ℂ).im ≤ 0) : z = w := by
  have h1 := circle_re_sq z
  have h2 := circle_re_sq w
  have : (z : ℂ).im ^ 2 = (w : ℂ).im ^ 2 := by rw [hre] at h1; linarith
  have him' : (z : ℂ).im = (w : ℂ).im := by
    rcases him with ⟨hz, hw⟩ | ⟨hz, hw⟩
    · exact (sq_eq_sq₀ hz hw).1 this
    · have := (sq_eq_sq₀ (neg_nonneg.2 hz) (neg_nonneg.2 hw)).1 (by simpa using this)
      linarith
  exact Circle.coe_injective (Complex.ext hre him')

private theorem im_eq_zero_of (z : Circle) (h : (z : ℂ).re = 1 ∨ (z : ℂ).re = -1) :
    (z : ℂ).im = 0 := by
  have := circle_re_sq z
  rcases h with h | h <;> rw [h] at this <;> nlinarith [sq_nonneg (z : ℂ).im]

theorem isSimpleClosedCurve_union (ha : IsArcParam a) (hb : IsArcParam b) (h0 : a 0 = b 0)
    (h1 : a 1 = b 1) (hmeet : a '' Icc 0 1 ∩ b '' Icc 0 1 ⊆ {a 0, a 1}) :
    IsSimpleClosedCurve (a '' Icc 0 1 ∪ b '' Icc 0 1) := by
  have hpi : 0 < π := pi_pos
  have hcont : Continuous (twoArcLoop a b) := by
    refine Continuous.if_le ?_ ?_ continuous_const
      (Complex.continuous_im.comp continuous_subtype_val) fun z hz => ?_
    · exact ha.1.comp ((continuous_arccos.comp (Complex.continuous_re.comp
        continuous_subtype_val)).div_const _)
    · exact hb.1.comp ((continuous_arccos.comp (Complex.continuous_re.comp
        continuous_subtype_val)).div_const _)
    · have := circle_re_sq z
      rw [← hz] at this
      have hre : (z : ℂ).re = 1 ∨ (z : ℂ).re = -1 := by
        have : ((z : ℂ).re - 1) * ((z : ℂ).re + 1) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h | h
        · left; linarith
        · right; linarith
      rcases hre with h | h
      · rw [h, arccos_one, zero_div, h0]
      · rw [h, arccos_neg_one, div_self hpi.ne', h1]
  -- the value at a point of the closed upper / lower half
  have hupper : ∀ z : Circle, 0 ≤ (z : ℂ).im → twoArcLoop a b z = a (arccos (z : ℂ).re / π) :=
    fun z hz => if_pos hz
  have hlower : ∀ z : Circle, (z : ℂ).im < 0 →
      twoArcLoop a b z = b (arccos (z : ℂ).re / π) := fun z hz => if_neg (not_le.2 hz)
  have hre_of : ∀ z : Circle, arccos (z : ℂ).re / π = 0 → (z : ℂ).re = 1 := by
    intro z hz
    have : arccos (z : ℂ).re = 0 := by
      rcases div_eq_zero_iff.1 hz with h | h
      · exact h
      · exact absurd h hpi.ne'
    rw [← cos_arccos (circle_re_mem z).1 (circle_re_mem z).2, this, cos_zero]
  have hre_of' : ∀ z : Circle, arccos (z : ℂ).re / π = 1 → (z : ℂ).re = -1 := by
    intro z hz
    have : arccos (z : ℂ).re = π := by
      rw [div_eq_one_iff_eq hpi.ne'] at hz; exact hz
    rw [← cos_arccos (circle_re_mem z).1 (circle_re_mem z).2, this, cos_pi]
  have hinj : Injective (twoArcLoop a b) := by
    intro z w hzw
    have hinj_re : ∀ z w : Circle, arccos (z : ℂ).re / π = arccos (w : ℂ).re / π →
        (z : ℂ).re = (w : ℂ).re := by
      intro z w h
      have : arccos (z : ℂ).re = arccos (w : ℂ).re := by
        field_simp at h; linarith
      exact arccos_injOn (circle_re_mem z) (circle_re_mem w) this
    -- the mixed case: a point of `a` equal to a point of `b` is a common end
    have mixed : ∀ z w : Circle, 0 ≤ (z : ℂ).im → (w : ℂ).im < 0 →
        a (arccos (z : ℂ).re / π) = b (arccos (w : ℂ).re / π) → False := by
      intro z w hz hw he
      have hm : a (arccos (z : ℂ).re / π) ∈ a '' Icc 0 1 ∩ b '' Icc 0 1 :=
        ⟨⟨_, arccos_div_mem _, rfl⟩, ⟨_, arccos_div_mem _, he.symm⟩⟩
      rcases hmeet hm with h | h
      · have hw0 : arccos (w : ℂ).re / π = 0 :=
          hb.2 (arccos_div_mem _) ⟨le_rfl, zero_le_one⟩ (by rw [← he, h, h0])
        have := im_eq_zero_of w (Or.inl (hre_of w hw0))
        linarith
      · have hw1 : arccos (w : ℂ).re / π = 1 :=
          hb.2 (arccos_div_mem _) ⟨zero_le_one, le_rfl⟩ (by rw [← he, h, h1])
        have := im_eq_zero_of w (Or.inr (hre_of' w hw1))
        linarith
    by_cases hz : 0 ≤ (z : ℂ).im <;> by_cases hw : 0 ≤ (w : ℂ).im
    · rw [hupper z hz, hupper w hw] at hzw
      exact circle_eq_of z w (hinj_re z w (ha.2 (arccos_div_mem _) (arccos_div_mem _) hzw))
        (Or.inl ⟨hz, hw⟩)
    · rw [hupper z hz, hlower w (not_le.1 hw)] at hzw
      exact (mixed z w hz (not_le.1 hw) hzw).elim
    · rw [hlower z (not_le.1 hz), hupper w hw] at hzw
      exact (mixed w z hw (not_le.1 hz) hzw.symm).elim
    · rw [hlower z (not_le.1 hz), hlower w (not_le.1 hw)] at hzw
      exact circle_eq_of z w (hinj_re z w (hb.2 (arccos_div_mem _) (arccos_div_mem _) hzw))
        (Or.inr ⟨(not_le.1 hz).le, (not_le.1 hw).le⟩)
  have hrange : range (twoArcLoop a b) = a '' Icc 0 1 ∪ b '' Icc 0 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      by_cases hz : 0 ≤ (z : ℂ).im
      · rw [hupper z hz]; exact Or.inl ⟨_, arccos_div_mem _, rfl⟩
      · rw [hlower z (not_le.1 hz)]; exact Or.inr ⟨_, arccos_div_mem _, rfl⟩
    · rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · refine ⟨Circle.exp (π * s), ?_⟩
        have him : 0 ≤ ((Circle.exp (π * s) : Circle) : ℂ).im := by
          rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
          exact sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hs.1]) (by nlinarith [hs.2])
        rw [hupper _ him, Circle.coe_exp, Complex.exp_ofReal_mul_I_re,
          arccos_cos (by nlinarith [hs.1]) (by nlinarith [hs.2]), mul_div_cancel_left₀ _ hpi.ne']
      · refine ⟨Circle.exp (-(π * s)), ?_⟩
        have hre : ((Circle.exp (-(π * s)) : Circle) : ℂ).re = cos (π * s) := by
          rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, cos_neg]
        by_cases him : 0 ≤ ((Circle.exp (-(π * s)) : Circle) : ℂ).im
        · rw [hupper _ him, hre, arccos_cos (by nlinarith [hs.1]) (by nlinarith [hs.2]),
            mul_div_cancel_left₀ _ hpi.ne']
          -- here `sin (π s) = 0`, so `s` is an end
          have hsin : sin (π * s) = 0 := by
            have h2 : ((Circle.exp (-(π * s)) : Circle) : ℂ).im = - sin (π * s) := by
              rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im, sin_neg]
            have h3 : 0 ≤ sin (π * s) :=
              sin_nonneg_of_nonneg_of_le_pi (by nlinarith [hs.1]) (by nlinarith [hs.2])
            linarith
          rcases eq_or_lt_of_le hs.1 with h | h
          · subst h; exact h0
          rcases eq_or_lt_of_le hs.2 with h' | h'
          · subst h'; exact h1
          · exact absurd hsin (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)).ne'
        · rw [hlower _ (not_le.1 him), hre, arccos_cos (by nlinarith [hs.1]) (by nlinarith [hs.2]),
            mul_div_cancel_left₀ _ hpi.ne']
  have hemb : IsEmbedding (twoArcLoop a b) := (hcont.isClosedEmbedding hinj).isEmbedding
  rw [← hrange]
  exact ⟨(hemb.toHomeomorph).symm⟩

end Union

end DoubleMidset
