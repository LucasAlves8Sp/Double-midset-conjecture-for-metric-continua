module

public import DoubleMidset.Order
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A dendrite without branch points is an arc

This is the consequence of R. L. Moore's theorem (Fact 2.5) that the paper uses. It is proved
here directly:

* (attaching) if `A = [p, q]` is an arc and `z ∉ A`, the first point `w` at which the arc
  `[z, p]` meets `A` is an end of `A`, unless `w` is a branch point; in either case of an end, a
  strictly larger arc contains `A` and `z` (`exists_larger_seg`);
* (a maximal arc) for a dense sequence `xₙ`, the function `φ(K) = ∑ 2⁻ⁿ d(xₙ, K)` is strictly
  decreasing for inclusion (`phi_lt_of_ssubset`), and `(p, q) ↦ φ([p, q])` is lower semicontinuous
  on the compact space `X × X` because arcs between close points are small; a minimizer gives an
  arc that cannot be enlarged, hence is all of `X`.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyConnectedSpace X] (hD : ∀ C : Set X, ¬ IsSimpleClosedCurve C)
include hD

/-- `K` has no branch point relative to `K`: no `w ∈ K` has three points of `K \ {w}` in pairwise
different components of `X \ {w}`. -/
def NoRelBranch (K : Set X) : Prop :=
  ∀ w ∈ K, ∀ z ∈ K, ∀ p ∈ K, ∀ q ∈ K, z ≠ w → p ≠ w → q ≠ w →
    connectedComponentIn {w}ᶜ z ≠ connectedComponentIn {w}ᶜ p →
    connectedComponentIn {w}ᶜ z ≠ connectedComponentIn {w}ᶜ q →
    connectedComponentIn {w}ᶜ p ≠ connectedComponentIn {w}ᶜ q → False

omit hD in
theorem noRelBranch_univ (hnb : ∀ p : X, ¬ IsBranchPoint p) : NoRelBranch (univ : Set X) :=
  fun w _ z _ p _ q _ hz hp hq h1 h2 h3 => hnb w (three_le_order hz hp hq h1 h2 h3)

/-- **Attaching.** If `K` is connected without relative branch points, an arc `[p, q]` in `K` and
a point `z ∈ K` off it lie in a common larger arc in `K`. -/
theorem exists_larger_seg {K : Set X} (hK : IsPreconnected K) (hnb : NoRelBranch K) {p q z : X}
    (hp : p ∈ K) (hq : q ∈ K) (hzK : z ∈ K) (hpq : p ≠ q) (hz : z ∉ seg p q) :
    ∃ p' ∈ K, ∃ q' ∈ K, seg p q ⊆ seg p' q' ∧ z ∈ seg p' q' := by
  set A := seg p q with hAdef
  have hA : IsArcBetween A p q := seg_isArcBetween hpq
  have hzp : z ≠ p := fun h => hz (h ▸ hA.left_mem)
  obtain ⟨h, hh, hhim, h0, h1⟩ := (seg_isArcBetween hzp).exists_param
  have hAc : IsClosed A := hA.isCompact.isClosed
  set Kp := Icc (0 : ℝ) 1 ∩ {t | h t ∈ A} with hKp
  have hKpc : IsCompact Kp := Metric.isCompact_of_isClosed_isBounded
    (isClosed_Icc.inter (hAc.preimage hh.1)) ((Metric.isBounded_Icc 0 1).subset inter_subset_left)
  have hKpne : Kp.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [mem_setOf_eq, h1]; exact hA.left_mem⟩
  set s := sInf Kp
  have hsK : s ∈ Kp := hKpc.sInf_mem hKpne
  have hsle : ∀ t ∈ Kp, s ≤ t := fun t ht => csInf_le hKpc.bddBelow ht
  have hs0 : 0 < s := lt_of_le_of_ne hsK.1.1 (fun e => hz (by rw [← h0, e]; exact hsK.2))
  have hoff : ∀ t ∈ Ico 0 s, h t ∉ A := fun t ht htA =>
    absurd (hsle t ⟨⟨ht.1, ht.2.le.trans hsK.1.2⟩, htA⟩) (not_le.2 ht.2)
  set w := h s
  have hwA : w ∈ A := hsK.2
  -- the arc `P = h '' [0, s]` from `z` to `w`
  have hPk := hh.sub le_rfl hs0 hsK.1.2
  have hP : IsArcBetween (h '' Icc 0 s) z w := by
    have := hPk.isArcBetween
    rwa [IsArcParam.sub_image h hs0.le, show (0 : ℝ) + 0 * (s - 0) = 0 by ring,
      show (0 : ℝ) + 1 * (s - 0) = s by ring, h0] at this
  have hPA : h '' Icc 0 s ∩ A ⊆ {w} := by
    rintro _ ⟨⟨t, ht, rfl⟩, htA⟩
    rcases eq_or_lt_of_le ht.2 with e | e
    · rw [e]; rfl
    · exact (hoff t ⟨ht.1, e⟩ htA).elim
  have hzP : z ∈ h '' Icc 0 s := hP.left_mem
  by_cases hwp : w = p
  · refine ⟨z, hzK, q, hq, ?_, ?_⟩ <;> rw [seg_eq hD (hP.union (hwp ▸ hA) (hwp ▸ hPA))]
    · exact subset_union_right
    · exact Or.inl hzP
  by_cases hwq : w = q
  · refine ⟨z, hzK, p, hp, ?_, ?_⟩ <;> rw [seg_eq hD (hP.union (hwq ▸ hA.symm) (hwq ▸ hPA))]
    · exact subset_union_right
    · exact Or.inl hzP
  -- otherwise `w` is a branch point
  have hwK : w ∈ K := seg_subset hD hK hp hq hwA
  have hwz : w ≠ z := fun e => hz (e ▸ hwA)
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := hA.exists_param
  obtain ⟨α, hα, hαw⟩ : w ∈ g '' Icc 0 1 := hgim ▸ hwA
  have hα1 : α ≠ 1 := fun e => hwq (by rw [← hαw, e, hg1])
  obtain ⟨k, hk, hk0, hk1, hkim⟩ := hg.exists_subarc hα ⟨zero_le_one, le_rfl⟩ hα1
  have hB : IsArcBetween (k '' Icc 0 1) w q := by
    have := hk.isArcBetween; rwa [hk0, hk1, hαw, hg1] at this
  have hBA : k '' Icc 0 1 ⊆ A := by
    rw [hkim, ← hgim]; apply image_mono
    rw [uIcc_of_le hα.2]; exact Icc_subset_Icc hα.1 le_rfl
  have hPB : h '' Icc 0 s ∩ k '' Icc 0 1 ⊆ {w} :=
    (inter_subset_inter_right _ hBA).trans hPA
  have hzq := hP.union hB hPB
  refine (hnb w hwK z hzK p hp q hq hwz.symm (Ne.symm hwp) (Ne.symm hwq) ?_ ?_
    (ends_separate hD hA hwA hwp hwq)).elim
  · exact ends_separate hD (seg_isArcBetween hzp) (hhim ▸ ⟨s, hsK.1, rfl⟩) hwz hwp
  · exact ends_separate hD hzq (Or.inl hP.right_mem) hwz hwq

omit hD in
/-- Arcs between close points are small. -/
theorem seg_subset_ball {ε : ℝ} (hε : 0 < ε) (hD : ∀ C : Set X, ¬ IsSimpleClosedCurve C) :
    ∃ δ > 0, ∀ a b : X, dist a b < δ → seg a b ⊆ ball a ε := by
  obtain ⟨δ, hδ, hC⟩ := Peano.ulc_of_compact (X := X) hε
  refine ⟨δ, hδ, fun a b hab => ?_⟩
  obtain ⟨C, hCc, haC, hbC, hCb⟩ := hC a b hab
  exact (seg_subset hD hCc haC hbC).trans hCb

/-- The arc between `p'` and `q'` lies in the union of the arcs `[p', p]`, `[p, q]`, `[q, q']`. -/
theorem seg_subset_union (p q p' q' : X) :
    seg p' q' ⊆ seg p' p ∪ seg p q ∪ seg q q' := by
  apply seg_subset hD _ (Or.inl (Or.inl (left_mem_seg _ _))) (Or.inr (right_mem_seg hD _ _))
  refine IsPreconnected.union q ?_ (left_mem_seg _ _) ?_ (isConnected_seg _ _).isPreconnected
  · exact Or.inr (right_mem_seg hD _ _)
  · exact IsPreconnected.union p (right_mem_seg hD _ _) (left_mem_seg _ _)
      (isConnected_seg _ _).isPreconnected (isConnected_seg _ _).isPreconnected

omit hD in
/-- The weighted sum of distances from a sequence. -/
noncomputable def phi (x : ℕ → X) (K : Set X) : ℝ := ∑' n, ((1 : ℝ) / 2) ^ n * infDist (x n) K

omit hD in
theorem phi_summable (x : ℕ → X) {K : Set X} (hK : K.Nonempty) :
    Summable fun n => ((1 : ℝ) / 2) ^ n * infDist (x n) K := by
  obtain ⟨k, hk⟩ := hK
  have hb : Bornology.IsBounded (univ : Set X) := isCompact_univ.isBounded
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) infDist_nonneg) (fun n => ?_)
    (summable_geometric_two.mul_right (diam (univ : Set X)))
  gcongr
  exact (infDist_le_dist_of_mem hk).trans (dist_le_diam_of_mem hb (mem_univ _) (mem_univ _))

omit hD in
/-- `φ` is strictly decreasing for inclusion of compact sets. -/
theorem phi_lt_of_ssubset {x : ℕ → X} (hx : DenseRange x) {K K' : Set X} (hK : K.Nonempty)
    (hKc : IsClosed K) (hKK' : K ⊆ K') {y : X} (hy : y ∈ K') (hyK : y ∉ K) :
    phi x K' < phi x K := by
  have hδ : 0 < infDist y K := (infDist_pos_iff_notMem_closure hK).1 (by rwa [hKc.closure_eq])
  obtain ⟨n, hn⟩ := hx.exists_dist_lt y (by positivity : 0 < infDist y K / 3)
  refine Summable.tsum_lt_tsum (i := n) (fun m => ?_) ?_ (phi_summable x ⟨y, hy⟩)
    (phi_summable x hK)
  · gcongr; exact infDist_le_infDist_of_subset hKK' hK
  · rw [dist_comm] at hn
    have h1 : infDist (x n) K' ≤ dist (x n) y := infDist_le_dist_of_mem hy
    have h2 : infDist y K ≤ infDist (x n) K + dist y (x n) := infDist_le_infDist_add_dist
    rw [dist_comm] at h2
    have : infDist (x n) K' < infDist (x n) K := by linarith
    have hpos : (0 : ℝ) < (1 / 2) ^ n := by positivity
    exact mul_lt_mul_of_pos_left this hpos

omit hD in
theorem infDist_le_add_of_forall {K K' : Set X} (hK' : K'.Nonempty) {ε : ℝ}
    (h : ∀ y ∈ K', infDist y K ≤ ε) (z : X) : infDist z K ≤ infDist z K' + ε := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  obtain ⟨y, hy, hzy⟩ := (infDist_lt_iff hK').1 (lt_add_of_pos_right (infDist z K') hη)
  have := infDist_le_infDist_add_dist (x := z) (y := y) (s := K)
  linarith [h y hy]

omit hD in
theorem phi_le_add_of_forall {x : ℕ → X} {K K' : Set X} (hK : K.Nonempty) (hK' : K'.Nonempty)
    {ε : ℝ} (h : ∀ y ∈ K', infDist y K ≤ ε) : phi x K ≤ phi x K' + 2 * ε := by
  have hs : Summable fun n => ((1 : ℝ) / 2) ^ n * (infDist (x n) K' + ε) := by
    simp_rw [mul_add]
    exact (phi_summable x hK').add (summable_geometric_two.mul_right ε)
  calc phi x K ≤ ∑' n, ((1 : ℝ) / 2) ^ n * (infDist (x n) K' + ε) :=
        Summable.tsum_le_tsum (fun n => by gcongr; exact infDist_le_add_of_forall hK' h _)
          (phi_summable x hK) hs
    _ = phi x K' + 2 * ε := by
        simp_rw [mul_add]
        rw [Summable.tsum_add (phi_summable x hK') (summable_geometric_two.mul_right ε),
          tsum_mul_right, tsum_geometric_two]
        rfl

/-- `(p, q) ↦ φ([p, q])` is lower semicontinuous. -/
theorem lowerSemicontinuous_phi_seg (x : ℕ → X) :
    LowerSemicontinuous fun z : X × X => phi x (seg z.1 z.2) := by
  intro z c hc
  set ε := (phi x (seg z.1 z.2) - c) / 4
  have hε : 0 < ε := by simp only [ε]; linarith
  obtain ⟨δ, hδ, hball⟩ := seg_subset_ball hε hD
  filter_upwards [ball_mem_nhds z hδ] with w hw
  have hw' : dist w z < δ := hw
  rw [Prod.dist_eq] at hw'
  have h1 : dist w.1 z.1 < δ := (le_max_left _ _).trans_lt hw'
  have h2 : dist w.2 z.2 < δ := (le_max_right _ _).trans_lt hw'
  have hclose : ∀ y ∈ seg w.1 w.2, infDist y (seg z.1 z.2) ≤ ε := by
    intro y hy
    rcases seg_subset_union hD z.1 z.2 w.1 w.2 hy with (hy | hy) | hy
    · rw [seg_symm hD] at hy
      have := hball z.1 w.1 (by rw [dist_comm]; exact h1) hy
      rw [mem_ball] at this
      exact (infDist_le_dist_of_mem (left_mem_seg _ _)).trans this.le
    · rw [infDist_zero_of_mem hy]; exact hε.le
    · have := hball z.2 w.2 (by rw [dist_comm]; exact h2) hy
      rw [mem_ball] at this
      exact (infDist_le_dist_of_mem (right_mem_seg hD _ _)).trans this.le
  have := phi_le_add_of_forall (x := x) ⟨_, left_mem_seg z.1 z.2⟩ ⟨_, left_mem_seg w.1 w.2⟩ hclose
  simp only [ε] at this
  linarith

/-- **A closed connected set without relative branch points is an arc.** -/
theorem exists_seg_eq {K : Set X} (hKc : IsClosed K) (hK : IsPreconnected K) (hnt : K.Nontrivial)
    (hnb : NoRelBranch K) : ∃ p ∈ K, ∃ q ∈ K, p ≠ q ∧ seg p q = K := by
  obtain ⟨x, hx⟩ := TopologicalSpace.exists_dense_seq X
  have hKK : IsCompact (K ×ˢ K) := hKc.isCompact.prod hKc.isCompact
  obtain ⟨z, hzK, hz⟩ := (lowerSemicontinuous_phi_seg hD x).lowerSemicontinuousOn (K ×ˢ K)
    |>.exists_isMinOn (hnt.nonempty.prod hnt.nonempty) hKK
  have hmin : ∀ w ∈ K ×ˢ K, phi x (seg z.1 z.2) ≤ phi x (seg w.1 w.2) := fun w hw => hz hw
  have hne : z.1 ≠ z.2 := by
    intro he
    obtain ⟨q, hqK, hq⟩ := hnt.exists_ne z.1
    have := hmin (z.1, q) ⟨hzK.1, hqK⟩
    dsimp only at this
    rw [he, seg_self] at this
    have hlt := phi_lt_of_ssubset hx (singleton_nonempty z.2) isClosed_singleton
      (singleton_subset_iff.2 (he ▸ left_mem_seg z.1 q : z.2 ∈ seg z.1 q))
      (right_mem_seg hD z.1 q) (by rw [mem_singleton_iff, ← he]; exact hq)
    rw [he] at hlt
    linarith
  refine ⟨z.1, hzK.1, z.2, hzK.2, hne, Subset.antisymm (seg_subset hD hK hzK.1 hzK.2) ?_⟩
  intro y hyK
  by_contra hy
  obtain ⟨p', hp', q', hq', hsub, hy'⟩ := exists_larger_seg hD hK hnb hzK.1 hzK.2 hyK hne hy
  have := hmin (p', q') ⟨hp', hq'⟩
  have hlt := phi_lt_of_ssubset hx ⟨_, left_mem_seg z.1 z.2⟩ (isCompact_seg z.1 z.2).isClosed
    hsub hy' hy
  linarith

/-- **A dendrite without branch points is an arc** (the consequence of Fact 2.5 used in the
paper). -/
theorem isArcBetween_univ_of_noBranch [Nontrivial X] (hnb : ∀ p : X, ¬ IsBranchPoint p) :
    ∃ p q : X, IsArcBetween (univ : Set X) p q := by
  obtain ⟨p, -, q, -, hpq, h⟩ := exists_seg_eq hD isClosed_univ isPreconnected_univ
    nontrivial_univ (noRelBranch_univ hnb)
  exact ⟨p, q, h ▸ seg_isArcBetween hpq⟩

/-- A dendrite without branch points is homeomorphic to `[0,1]`. -/
theorem nonempty_homeomorph_of_noBranch [Nontrivial X] (hnb : ∀ p : X, ¬ IsBranchPoint p) :
    Nonempty (X ≃ₜ unitInterval) := by
  obtain ⟨p, q, f, hf, hr, -, -⟩ := isArcBetween_univ_of_noBranch hD hnb
  exact ⟨((Homeomorph.Set.univ X).symm.trans ((Homeomorph.setCongr hr).symm.trans
    hf.toHomeomorph.symm))⟩

end DoubleMidset
