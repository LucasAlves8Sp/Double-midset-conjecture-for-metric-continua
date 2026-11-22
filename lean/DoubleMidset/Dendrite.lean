module

public import DoubleMidset.Circle
public import DoubleMidset.Classical.PeanoLPC
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Dendrites: arcs, uniqueness of arcs, separation (Fact 2.3, Lemma 2.4)

In a compact, connected, locally connected metric space every two distinct points of an open
connected set are joined by an arc inside it. If moreover the space contains no simple closed
curve, the arc between two points is unique (`arc_unique`); we write `seg p q` for it (and
`seg p p = {p}`). From uniqueness:

* Lemma 2.4 (`sides_separate`): the two sides of an interior point `y` of an arc lie in
  different components of `X \ {y}`; so `y` has order at least two, and the center of a simple
  triod has order at least three.
* Fact 2.3 (D1) `seg_subset`: an arc between two points of a connected set lies in it, so
  connected sets are arcwise connected; (D2) `IsPreconnected.inter`: the intersection of two
  connected sets is connected; (D3) `isDendrite_of_subcontinuum`: subcontinua are dendrites;
  (D4) components of open sets are open (Mathlib).
-/

@[expose] public section

open Set Topology Function Metric

namespace DoubleMidset

universe u

section Subarc

variable {X : Type u} [TopologicalSpace X]

/-- A parametrization of the subarc of `g` between the parameters `α` and `β`. -/
theorem IsArcParam.exists_subarc {g : ℝ → X} (hg : IsArcParam g) {α β : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc (0 : ℝ) 1) (hne : α ≠ β) :
    ∃ k : ℝ → X, IsArcParam k ∧ k 0 = g α ∧ k 1 = g β ∧ k '' Icc 0 1 = g '' uIcc α β := by
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨_, hg.sub hα.1 h hβ.2, by simp, by simp, ?_⟩
    rw [IsArcParam.sub_image g h.le, uIcc_of_le h.le]
  · refine ⟨_, (hg.sub hβ.1 h hα.2).symm, by simp, by simp, ?_⟩
    exact (IsArcParam.symm_image (fun u => g (β + u * (α - β)))).trans
      (by rw [IsArcParam.sub_image g h.le, uIcc_of_ge h.le])

end Subarc

open Classical in
/-- The arc between `p` and `q` chosen once and for all (`{p}` if there is none, in particular if
`p = q`). In a dendrite it is the unique arc between `p` and `q` (`seg_eq`). -/
noncomputable def seg {X : Type u} [TopologicalSpace X] (p q : X) : Set X :=
  if h : ∃ A, IsArcBetween A p q then h.choose else {p}

section Metric

variable {X : Type u} [MetricSpace X]

theorem seg_self (p : X) : seg p p = {p} := by
  rw [seg, dif_neg]; rintro ⟨A, hA⟩; exact hA.ne rfl

section LC

variable [CompactSpace X] [LocallyConnectedSpace X]

instance (priority := 100) locallyPathConnected_of_compact_lc : LocallyPathConnectedSpace X :=
  Peano.locallyPathConnectedSpace_of_compact_metric

/-- Two distinct points of an open connected set are joined by an arc inside it. -/
theorem exists_arc_in_open {U : Set X} (hU : IsOpen U) (hUc : IsPreconnected U) {p q : X}
    (hp : p ∈ U) (hq : q ∈ U) (hpq : p ≠ q) : ∃ A, IsArcBetween A p q ∧ A ⊆ U := by
  have hconn : IsConnected U := ⟨⟨p, hp⟩, hUc⟩
  have hpc := (hU.isConnected_iff_isPathConnected).1 hconn
  exact exists_isArcBetween_of_joinedIn (hpc.joinedIn p hp q hq) hpq

variable [ConnectedSpace X]

theorem exists_arc {p q : X} (hpq : p ≠ q) : ∃ A, IsArcBetween A p q := by
  obtain ⟨A, hA, -⟩ := exists_arc_in_open isOpen_univ isPreconnected_univ (mem_univ p)
    (mem_univ q) hpq
  exact ⟨A, hA⟩

theorem seg_isArcBetween {p q : X} (hpq : p ≠ q) : IsArcBetween (seg p q) p q := by
  have h := exists_arc hpq
  rw [seg, dif_pos h]; exact h.choose_spec

end LC

section Unique

/-- Two arcs with the same ends in a space without simple closed curves are equal. The first
point at which `B` leaves `A` and the first point at which it returns bound a subarc of `B`
which together with the subarc of `A` between them forms a simple closed curve. -/
theorem arc_subset_of_noSCC (hD : ∀ C : Set X, ¬ IsSimpleClosedCurve C) {A B : Set X} {p q : X}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) : B ⊆ A := by
  obtain ⟨g, hg, rfl, rfl, rfl⟩ := hA.exists_param
  obtain ⟨h, hh, rfl, h0, h1⟩ := hB.exists_param
  intro z hz
  by_contra hzA
  obtain ⟨t0, ht0, rfl⟩ := hz
  have hAc : IsClosed (g '' Icc 0 1) := hg.isCompact_image.isClosed
  set K := {t | h t ∈ g '' Icc 0 1} with hK
  have hKc : IsClosed K := hAc.preimage hh.1
  have hK0 : (0 : ℝ) ∈ K := by rw [hK, mem_setOf_eq, h0]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hK1 : (1 : ℝ) ∈ K := by rw [hK, mem_setOf_eq, h1]; exact ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have ht0K : t0 ∉ K := hzA
  -- last point of `K` before `t0`
  set L := K ∩ Icc 0 t0
  have hLc : IsCompact L := Metric.isCompact_of_isClosed_isBounded (hKc.inter isClosed_Icc)
    ((Metric.isBounded_Icc 0 t0).subset inter_subset_right)
  have hLne : L.Nonempty := ⟨0, hK0, le_rfl, ht0.1⟩
  set s := sSup L
  have hsL : s ∈ L := hLc.sSup_mem hLne
  have hsle : ∀ t ∈ L, t ≤ s := fun t ht => le_csSup hLc.bddAbove ht
  -- first point of `K` after `t0`
  set R := K ∩ Icc t0 1
  have hRc : IsCompact R := Metric.isCompact_of_isClosed_isBounded (hKc.inter isClosed_Icc)
    ((Metric.isBounded_Icc t0 1).subset inter_subset_right)
  have hRne : R.Nonempty := ⟨1, hK1, ht0.2, le_rfl⟩
  set s' := sInf R
  have hs'R : s' ∈ R := hRc.sInf_mem hRne
  have hs'le : ∀ t ∈ R, s' ≤ t := fun t ht => csInf_le hRc.bddBelow ht
  have hst0 : s < t0 := lt_of_le_of_ne hsL.2.2 (fun he => ht0K (he ▸ hsL.1))
  have ht0s' : t0 < s' := lt_of_le_of_ne hs'R.2.1 (fun he => ht0K (he.symm ▸ hs'R.1))
  have hss' : s < s' := hst0.trans ht0s'
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hsL.2.1, hsL.2.2.trans ht0.2⟩
  have hs'01 : s' ∈ Icc (0 : ℝ) 1 := ⟨ht0.1.trans hs'R.2.1, hs'R.2.2⟩
  -- between `s` and `s'` the arc `B` is off `A`
  have hoff : ∀ t ∈ Ioo s s', t ∉ K := by
    intro t ht htK
    rcases le_or_gt t t0 with htt | htt
    · have := hsle t ⟨htK, hs01.1.trans ht.1.le, htt⟩; linarith [ht.1]
    · have := hs'le t ⟨htK, htt.le, ht.2.le.trans hs'01.2⟩; linarith [ht.2]
  obtain ⟨α, hα, hαs⟩ := hsL.1
  obtain ⟨β, hβ, hβs'⟩ := hs'R.1
  have hne : h s ≠ h s' := fun he => hss'.ne (hh.2 hs01 hs'01 he)
  have hαβ : α ≠ β := fun he => hne (by rw [← hαs, ← hβs', he])
  obtain ⟨a, ha, ha0, ha1, haim⟩ := hg.exists_subarc hα hβ hαβ
  obtain ⟨b, hb, hb0, hb1, hbim⟩ := hh.exists_subarc hs01 hs'01 hss'.ne
  rw [hαs] at ha0; rw [hβs'] at ha1
  refine hD _ (isSimpleClosedCurve_union ha hb (by rw [ha0, hb0]) (by rw [ha1, hb1]) ?_)
  rintro x ⟨hxa, hxb⟩
  rw [haim] at hxa
  rw [hbim, uIcc_of_le hss'.le] at hxb
  obtain ⟨t, ht, rfl⟩ := hxb
  have hxA : h t ∈ g '' Icc 0 1 := by
    obtain ⟨c, hc, hce⟩ := hxa
    refine ⟨c, ?_, hce⟩
    rcases le_total α β with hab | hab
    · rw [uIcc_of_le hab] at hc; exact ⟨hα.1.trans hc.1, hc.2.trans hβ.2⟩
    · rw [uIcc_of_ge hab] at hc; exact ⟨hβ.1.trans hc.1, hc.2.trans hα.2⟩
  rcases eq_or_lt_of_le ht.1 with h' | h'
  · subst h'; left; exact ha0.symm
  rcases eq_or_lt_of_le ht.2 with h'' | h''
  · subst h''; right; exact ha1.symm
  exact (hoff t ⟨h', h''⟩ hxA).elim

theorem arc_unique (hD : ∀ C : Set X, ¬ IsSimpleClosedCurve C) {A B : Set X} {p q : X}
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q) : A = B :=
  Subset.antisymm (arc_subset_of_noSCC hD hB hA) (arc_subset_of_noSCC hD hA hB)

end Unique

section Dendrite

variable [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
  (hD : ∀ C : Set X, ¬ IsSimpleClosedCurve C)
include hD

theorem seg_eq {A : Set X} {p q : X} (hA : IsArcBetween A p q) : seg p q = A :=
  arc_unique hD (seg_isArcBetween hA.ne) hA

theorem seg_symm (p q : X) : seg p q = seg q p := by
  rcases eq_or_ne p q with rfl | h
  · rfl
  · exact seg_eq hD (seg_isArcBetween h.symm).symm

omit hD in
theorem left_mem_seg (p q : X) : p ∈ seg p q := by
  rcases eq_or_ne p q with rfl | h
  · rw [seg_self]; rfl
  · exact (seg_isArcBetween h).left_mem

theorem right_mem_seg (p q : X) : q ∈ seg p q := by
  rw [seg_symm hD]; exact left_mem_seg q p

omit hD in
theorem isConnected_seg (p q : X) : IsConnected (seg p q) := by
  rcases eq_or_ne p q with rfl | h
  · rw [seg_self]; exact isConnected_singleton
  · exact (seg_isArcBetween h).isConnected

omit hD in
theorem isCompact_seg (p q : X) : IsCompact (seg p q) := by
  rcases eq_or_ne p q with rfl | h
  · rw [seg_self]; exact isCompact_singleton
  · exact (seg_isArcBetween h).isCompact

/-- **Lemma 2.4, core.** If `y = g t` is an interior point of the arc `g`, then points of the arc
on the two sides of `y` lie in different components of `X \ {y}`. -/
theorem sides_separate {g : ℝ → X} (hg : IsArcParam g) {s t s' : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (hts' : t < s') (hs' : s' ≤ 1) :
    connectedComponentIn {g t}ᶜ (g s) ≠ connectedComponentIn {g t}ᶜ (g s') := by
  intro he
  have hgs : g s ∈ ({g t}ᶜ : Set X) := fun h' =>
    hst.ne (hg.2 ⟨hs, hst.le.trans (hts'.le.trans hs')⟩ ⟨hs.trans hst.le, hts'.le.trans hs'⟩ h')
  have hgs' : g s' ∈ ({g t}ᶜ : Set X) := fun h' =>
    hts'.ne' (hg.2 ⟨hs.trans (hst.le.trans hts'.le), hs'⟩ ⟨hs.trans hst.le, hts'.le.trans hs'⟩ h')
  have hU : IsOpen (connectedComponentIn {g t}ᶜ (g s)) :=
    isOpen_compl_singleton.connectedComponentIn
  have hmem' : g s' ∈ connectedComponentIn {g t}ᶜ (g s) := he ▸ mem_connectedComponentIn hgs'
  have hne : g s ≠ g s' := fun h' => (hst.trans hts').ne
    (hg.2 ⟨hs, (hst.trans hts').le.trans hs'⟩ ⟨hs.trans (hst.trans hts').le, hs'⟩ h')
  obtain ⟨B, hB, hBU⟩ := exists_arc_in_open hU isPreconnected_connectedComponentIn
    (mem_connectedComponentIn hgs) hmem' hne
  obtain ⟨k, hk, hk0, hk1, hkim⟩ := hg.exists_subarc ⟨hs, (hst.trans hts').le.trans hs'⟩
    ⟨hs.trans (hst.trans hts').le, hs'⟩ (hst.trans hts').ne
  have hAB := arc_unique hD (hkim ▸ hk0 ▸ hk1 ▸ hk.isArcBetween) hB
  have hy : g t ∈ B := by
    rw [← hAB, uIcc_of_le (hst.trans hts').le]; exact ⟨t, ⟨hst.le, hts'.le⟩, rfl⟩
  exact (connectedComponentIn_subset _ _ (hBU hy)) rfl

/-- The ends of an arc lie in different components of the complement of any interior point. -/
theorem ends_separate {A : Set X} {p q y : X} (hA : IsArcBetween A p q) (hy : y ∈ A)
    (hyp : y ≠ p) (hyq : y ≠ q) : connectedComponentIn {y}ᶜ p ≠ connectedComponentIn {y}ᶜ q := by
  obtain ⟨g, hg, rfl, rfl, rfl⟩ := hA.exists_param
  obtain ⟨t, ht, rfl⟩ := hy
  have h0 : 0 < t := lt_of_le_of_ne ht.1 (fun h => hyp (by rw [← h]))
  have h1 : t < 1 := lt_of_le_of_ne ht.2 (fun h => hyq (by rw [h]))
  exact sides_separate hD hg le_rfl h0 h1 le_rfl

/-- **(D1)** The arc between two points of a connected set lies in it. -/
theorem seg_subset {Y : Set X} (hY : IsPreconnected Y) {p q : X} (hp : p ∈ Y) (hq : q ∈ Y) :
    seg p q ⊆ Y := by
  rcases eq_or_ne p q with rfl | hpq
  · rw [seg_self]; exact singleton_subset_iff.2 hp
  intro z hz
  by_contra hzY
  have hzp : z ≠ p := fun h => hzY (h ▸ hp)
  have hzq : z ≠ q := fun h => hzY (h ▸ hq)
  have hsub : Y ⊆ {z}ᶜ := fun y hy h => hzY (h ▸ hy)
  have h1 := hY.subset_connectedComponentIn hp hsub
  exact ends_separate hD (seg_isArcBetween hpq) hz hzp hzq (connectedComponentIn_eq (h1 hq))

/-- **(D1)** Connected subsets of a dendrite are arcwise connected. -/
theorem exists_arc_in {Y : Set X} (hY : IsPreconnected Y) {p q : X} (hp : p ∈ Y) (hq : q ∈ Y)
    (hpq : p ≠ q) : ∃ A, IsArcBetween A p q ∧ A ⊆ Y :=
  ⟨seg p q, seg_isArcBetween hpq, seg_subset hD hY hp hq⟩

/-- A set is preconnected if any two of its points lie in a common preconnected subset. -/
theorem isPreconnected_of_segs {Y : Set X} (h : ∀ p ∈ Y, ∀ q ∈ Y, seg p q ⊆ Y) :
    IsPreconnected Y := by
  rcases Y.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact isPreconnected_empty
  exact isPreconnected_of_forall x fun y hy =>
    ⟨seg x y, h x hx y hy, left_mem_seg x y, right_mem_seg hD x y,
      (isConnected_seg x y).isPreconnected⟩

/-- **(D2)** The intersection of two connected subsets of a dendrite is connected. -/
theorem IsPreconnected.inter_of_dendrite {Y Z : Set X} (hY : IsPreconnected Y)
    (hZ : IsPreconnected Z) : IsPreconnected (Y ∩ Z) :=
  isPreconnected_of_segs hD fun p hp q hq =>
    subset_inter (seg_subset hD hY hp.1 hq.1) (seg_subset hD hZ hp.2 hq.2)

omit hD in
/-- Simple closed curves in a subspace are simple closed curves in the space. -/
theorem IsSimpleClosedCurve.image_val {K : Set X} {C : Set K} (hC : IsSimpleClosedCurve C) :
    IsSimpleClosedCurve ((Subtype.val : K → X) '' C) := by
  obtain ⟨e⟩ := hC
  let f : Circle → X := fun z => ((e.symm z : C) : K)
  have hf : Continuous f :=
    continuous_subtype_val.comp (continuous_subtype_val.comp e.symm.continuous)
  have hinj : Injective f := fun z w h => e.symm.injective (Subtype.ext (Subtype.ext h))
  have hemb := (hf.isClosedEmbedding hinj).isEmbedding
  have hr : range f = (Subtype.val : K → X) '' C := by
    ext x; constructor
    · rintro ⟨z, rfl⟩; exact ⟨_, (e.symm z).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨e ⟨y, hy⟩, by simp [f]⟩
  rw [← hr]; exact ⟨hemb.toHomeomorph.symm⟩

/-- **(D3)** A closed connected subset of a dendrite with at least two points is a dendrite. -/
theorem isDendrite_of_subcontinuum {K : Set X} (hKc : IsClosed K) (hK : IsPreconnected K)
    (hnt : K.Nontrivial) : IsDendrite K := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc.isCompact
  have hne : K.Nonempty := hnt.nonempty
  refine ⟨⟨this, isConnected_iff_connectedSpace.1 ⟨hne, hK⟩, hnt.coe_sort, inferInstance⟩,
    ?_, fun C hC => hD _ hC.image_val⟩
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨W', hW'o, hxW', hW'U⟩ : ∃ W' : Set X, IsOpen W' ∧ (x : X) ∈ W' ∧
      (Subtype.val ⁻¹' W' : Set K) ⊆ U := by
    obtain ⟨t, ht, hts⟩ := (mem_nhds_subtype _ _ _).1 hU
    obtain ⟨W', hW't, hW'o, hxW'⟩ := _root_.mem_nhds_iff.1 ht
    exact ⟨W', hW'o, hxW', fun y hy => hts (hW't hy)⟩
  obtain ⟨W, hWW', hWo, hxW, hWc⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.1 ‹_›) (x : X) W' (hW'o.mem_nhds hxW')
  refine ⟨Subtype.val ⁻¹' W, (preimage_mono hWW').trans hW'U, hWo.preimage continuous_subtype_val,
    hxW, ⟨x, hxW⟩, ?_⟩
  rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe]
  exact isPreconnected_of_segs hD fun p hp q hq =>
    subset_inter (seg_subset hD hK hp.1 hq.1) (seg_subset hD hWc.isPreconnected hp.2 hq.2)

end Dendrite

end Metric

end DoubleMidset
