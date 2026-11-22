module

public import DoubleMidset.ArcCase

/-!
# Proofs of the main theorems (Section 12)

* `theorem_B`: no finite tree admits a compatible metric with the DMP;
* `theorem_A`: a nondegenerate compact connected metric space with the DMP is homeomorphic to
  the circle;
* `circle_hasDMP`: the unit circle with the Euclidean metric has the DMP;
* `theorem_A_iff`: a nondegenerate metrizable continuum admits a compatible metric with the DMP
  if and only if it is a simple closed curve.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

/-- **Theorem B.** No finite tree admits a compatible metric with the double midset
property. -/
theorem theorem_B {X : Type u} [MetricSpace X] (hX : IsFiniteTree X) : ¬ HasDMP X := by
  obtain ⟨⟨⟨hc, hconn, hnt, -⟩, hlc, hD⟩, hBf, hBo⟩ := hX
  have hT : TreeHyp X := ⟨hD, hBf, hBo⟩
  by_cases hbr : ∃ v : X, IsBranchPoint v
  · exact not_hasDMP_of_branched hT hbr
  · push_neg at hbr
    exact not_hasDMP_of_unbranched hT hbr

/-- **Theorem A.** Let `(X, d)` be a nondegenerate compact connected metric space. If
`|M(a, b)| = 2` for all distinct `a, b ∈ X`, then `X` is homeomorphic to `S¹`. -/
theorem theorem_A {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [Nontrivial X] (h : HasDMP X) : Nonempty (X ≃ₜ Circle) := by
  rcases cor_3_4 h with h' | h'
  · exact h'
  · exact absurd h (theorem_B (cor_4_6 h' fun a b hab => (h a b hab).le))

theorem norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

theorem circle_dist (z a : Circle) : dist z a = ‖(z : ℂ) - a‖ := by
  rw [← Complex.dist_eq]; rfl

theorem circle_unit (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  rw [← norm_sq_eq_re_im, Circle.norm_coe, one_pow]

theorem circle_dist_eq_iff (z a b : Circle) :
    dist z a = dist z b ↔
      (z : ℂ).re * ((a : ℂ).re - (b : ℂ).re) + (z : ℂ).im * ((a : ℂ).im - (b : ℂ).im) = 0 := by
  rw [circle_dist, circle_dist, ← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    norm_sq_eq_re_im, norm_sq_eq_re_im]
  have hz := circle_unit z
  have ha := circle_unit a
  have hb := circle_unit b
  simp only [Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> nlinarith

/-- The unit circle with the Euclidean metric has the double midset property: for distinct
`a, b`, the midset is the intersection of the circle with the perpendicular bisector of `ab`, a
line through the center. -/
theorem circle_hasDMP : HasDMP Circle := by
  intro a b hab
  have hA := circle_unit a
  have hB := circle_unit b
  set w1 := (a : ℂ).re - (b : ℂ).re
  set w2 := (a : ℂ).im - (b : ℂ).im
  have hw : 0 < w1 ^ 2 + w2 ^ 2 := by
    by_contra h
    push_neg at h
    have h1 : w1 = 0 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    have h2 : w2 = 0 := by nlinarith [sq_nonneg w1, sq_nonneg w2]
    exact hab (Circle.ext (Complex.ext (by simp only [w1] at h1; linarith)
      (by simp only [w2] at h2; linarith)))
  set n := Real.sqrt (w1 ^ 2 + w2 ^ 2)
  have hn : 0 < n := Real.sqrt_pos.2 hw
  have hn2 : n ^ 2 = w1 ^ 2 + w2 ^ 2 := Real.sq_sqrt hw.le
  set p : ℂ := ⟨-w2 / n, w1 / n⟩
  have hp : ‖p‖ = 1 := by
    have hsq : ‖p‖ ^ 2 = 1 ^ 2 := by
      rw [norm_sq_eq_re_im, one_pow]
      show (-w2 / n) ^ 2 + (w1 / n) ^ 2 = 1
      rw [div_pow, div_pow, neg_sq, ← add_div, add_comm, ← hn2, div_self (by positivity)]
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 hsq
  set P : Circle := ⟨p, mem_sphere_zero_iff_norm.2 hp⟩
  have hPre : (P : ℂ).re = -w2 / n := rfl
  have hPim : (P : ℂ).im = w1 / n := rfl
  have hPne : P ≠ -P := by
    intro h
    have h1 : (P : ℂ) = -(P : ℂ) := by rw [← Circle.coe_neg, ← h]
    have h0 : (P : ℂ) = 0 := by linear_combination h1 / 2
    have := Circle.norm_coe P
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hM : midset a b = {P, -P} := by
    ext z
    show dist z a = dist z b ↔ _
    rw [circle_dist_eq_iff, mem_insert_iff, mem_singleton_iff]
    have hZ := circle_unit z
    constructor
    · intro h
      set x := (z : ℂ).re
      set y := (z : ℂ).im
      have hs2 : (y * w1 - x * w2) ^ 2 = n ^ 2 := by
        rw [hn2]; linear_combination (w1 ^ 2 + w2 ^ 2) * hZ - (x * w1 + y * w2) * h
      have hx : x * n ^ 2 = -w2 * (y * w1 - x * w2) := by
        rw [hn2]; linear_combination w1 * h
      have hy : y * n ^ 2 = w1 * (y * w1 - x * w2) := by
        rw [hn2]; linear_combination w2 * h
      have hsn : (y * w1 - x * w2 - n) * (y * w1 - x * w2 + n) = 0 := by
        linear_combination hs2
      rcases mul_eq_zero.1 hsn with hs | hs
      · left
        have hs' : y * w1 - x * w2 = n := by linarith
        rw [hs'] at hx hy
        apply Circle.ext; apply Complex.ext
        · show x = -w2 / n
          rw [eq_div_iff hn.ne']
          have : (x * n + w2) * n = 0 := by linear_combination hx
          rcases mul_eq_zero.1 this with h1 | h1
          · linarith
          · exact absurd h1 hn.ne'
        · show y = w1 / n
          rw [eq_div_iff hn.ne']
          have : (y * n - w1) * n = 0 := by linear_combination hy
          rcases mul_eq_zero.1 this with h1 | h1
          · linarith
          · exact absurd h1 hn.ne'
      · right
        have hs' : y * w1 - x * w2 = -n := by linarith
        rw [hs'] at hx hy
        apply Circle.ext; apply Complex.ext
        · show x = -(-w2 / n)
          rw [neg_div, neg_neg, eq_div_iff hn.ne']
          have : (x * n - w2) * n = 0 := by linear_combination hx
          rcases mul_eq_zero.1 this with h1 | h1
          · linarith
          · exact absurd h1 hn.ne'
        · show y = -(w1 / n)
          rw [← neg_div, eq_div_iff hn.ne']
          have : (y * n + w1) * n = 0 := by linear_combination hy
          rcases mul_eq_zero.1 this with h1 | h1
          · linarith
          · exact absurd h1 hn.ne'
    · rintro (rfl | rfl)
      · rw [hPre, hPim]; ring
      · rw [Circle.coe_neg, Complex.neg_re, Complex.neg_im, hPre, hPim]; ring
  rw [hM, encard_pair hPne]

/-- **Theorem A (converse and characterization).** A nondegenerate metrizable continuum admits
a compatible metric with the double midset property if and only if it is a simple closed
curve. -/
theorem theorem_A_iff {X : Type u} [t : TopologicalSpace X] (hX : IsContinuum X) :
    (∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧ @HasDMP X m) ↔
      Nonempty (X ≃ₜ Circle) := by
  constructor
  · rintro ⟨m, rfl, hd⟩
    obtain ⟨hc, hconn, hnt, -⟩ := hX
    exact @theorem_A X m hc hconn hnt hd
  · rintro ⟨e⟩
    letI m : MetricSpace X := MetricSpace.induced e e.injective inferInstance
    refine ⟨m, ?_, ?_⟩
    · rw [e.isInducing.eq_induced]; rfl
    · intro a b hab
      show (e ⁻¹' midset (e a) (e b)).encard = 2
      rw [← e.injective.encard_image, image_preimage_eq _ e.surjective]
      exact circle_hasDMP (e a) (e b) (e.injective.ne hab)

end DoubleMidset
