module

public import DoubleMidset.Crossing

/-!
# Lemma 5.4 (parity) and the edge parametrization of edges

`edgeParam ℓ` is a chosen edge parametrization of an edge `ℓ` (`exists_param_of_isEdge`).
**Lemma 5.4** (`lemma_5_4`): on a finite tree, if `g` is continuous with finitely many zeros,
none of them a vertex, then the number of crossings of `g` has the parity of the number of
odd-degree vertices where `g < 0`.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

/-- Every edge has an edge parametrization. -/
theorem exists_param_of_isEdge {ℓ : Set T} (hℓ : IsEdge ℓ) :
    ∃ γ : ℝ → T, IsEdgeParam γ ∧ γ '' Icc 0 1 = ℓ := by
  obtain ⟨W, ⟨x, hx, rfl⟩, rfl⟩ := hℓ
  obtain ⟨γ, s, hs, hγ, -, -, hcl⟩ := exists_edgeParam hT hx
  exact ⟨γ, hγ, hcl⟩

/-- The vertices on an edge are the two ends of any edge parametrization of it. -/
theorem IsEdgeParam.inter_vertices {γ : ℝ → T} (hγ : IsEdgeParam γ) :
    γ '' Icc 0 1 ∩ vertices T = {γ 0, γ 1} := by
  ext y; constructor
  · rintro ⟨⟨t, ht, rfl⟩, hV⟩
    rcases eq_or_lt_of_le ht.1 with e | e
    · left; rw [← e]
    rcases eq_or_lt_of_le ht.2 with e' | e'
    · right; rw [e']; rfl
    exact (hγ.interior t ⟨e, e'⟩ hV).elim
  · rintro (rfl | rfl)
    · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hγ.end0⟩
    · exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, hγ.end1⟩

/-- An edge point lies in the open arc of any edge parametrization of its edge. -/
theorem IsEdgeParam.mem_Ioo {γ : ℝ → T} (hγ : IsEdgeParam γ) {y : T} (hy : y ∈ γ '' Icc 0 1)
    (hyV : y ∉ vertices T) : ∃ s ∈ Ioo (0 : ℝ) 1, γ s = y := by
  obtain ⟨s, hs, rfl⟩ := hy
  exact ⟨s, ⟨lt_of_le_of_ne hs.1 fun e => hyV (e ▸ hγ.end0),
    lt_of_le_of_ne hs.2 fun e => hyV (e ▸ hγ.end1)⟩, rfl⟩

/-- The closure of the open edge of an edge point is an edge containing it. -/
theorem isEdge_closure_cc {y : T} (hy : y ∉ vertices T) :
    IsEdge (closure (connectedComponentIn (vertices T)ᶜ y)) :=
  ⟨_, ⟨y, hy, rfl⟩, rfl⟩

omit hT in
theorem finite_paramZeros {g : T → ℝ} (hfin : (g ⁻¹' {0}).Finite) {k : ℝ → T}
    (hk : IsArcParam k) : {s | s ∈ Icc (0 : ℝ) 1 ∧ g (k s) = 0}.Finite :=
  Finite.of_finite_image (hfin.subset (by rintro _ ⟨t, ht, rfl⟩; exact ht.2))
    (hk.2.mono fun t ht => ht.1)

/-- **Lemma 5.4 (Parity).** -/
theorem lemma_5_4 {g : T → ℝ} (hg : Continuous g) (hfin : (g ⁻¹' {0}).Finite)
    (hV : ∀ u ∈ vertices T, g u ≠ 0) :
    {y | IsCrossing g y}.ncard % 2 = {u | u ∈ oddVertices T ∧ g u < 0}.ncard % 2 := by
  classical
  have hne : Nonempty (ℝ → T) := ⟨fun _ => Classical.arbitrary T⟩
  have hP : ∀ ℓ ∈ {ℓ : Set T | IsEdge ℓ}, ∃ γ : ℝ → T, IsEdgeParam γ ∧ γ '' Icc 0 1 = ℓ :=
    fun ℓ hℓ => exists_param_of_isEdge hT hℓ
  choose! P hPe hPim using hP
  set Ef := hT.edges_finite.toFinset
  set Vf := hT.vertices_finite.toFinset
  have hEf : ∀ ℓ, ℓ ∈ Ef ↔ IsEdge ℓ := fun ℓ => hT.edges_finite.mem_toFinset
  set C : Set T → Set ℝ := fun ℓ => {s | s ∈ Ioo (0 : ℝ) 1 ∧ IsParamCrossing (g ∘ P ℓ) s}
  have hCf : ∀ ℓ ∈ Ef, (C ℓ).Finite := fun ℓ hℓ =>
    (finite_paramZeros hfin (hPe ℓ ((hEf ℓ).1 hℓ)).arc).subset fun s hs =>
      ⟨Ioo_subset_Icc_self hs.1, hs.2.1⟩
  -- the crossings are the images of the parameter crossings, edge by edge
  have hcross : {y | IsCrossing g y} =
      ↑(Ef.biUnion fun ℓ => if h : ℓ ∈ Ef then (hCf ℓ h).toFinset.image (P ℓ) else ∅) := by
    ext y
    simp only [mem_setOf_eq, Finset.coe_biUnion, Finset.mem_coe, mem_iUnion, exists_prop]
    constructor
    · intro hcr
      set ℓ := closure (connectedComponentIn (vertices T)ᶜ y)
      have hℓ : IsEdge ℓ := isEdge_closure_cc hT hcr.1
      have hyℓ : y ∈ P ℓ '' Icc 0 1 := by
        rw [hPim ℓ hℓ]; exact subset_closure (mem_connectedComponentIn hcr.1)
      obtain ⟨s, hs, hsy⟩ := (hPe ℓ hℓ).mem_Ioo hT hyℓ hcr.1
      refine ⟨ℓ, (hEf ℓ).2 hℓ, ?_⟩
      rw [dif_pos ((hEf ℓ).2 hℓ), Finset.mem_image]
      refine ⟨s, (Finite.mem_toFinset _).2 ⟨hs, ?_, hcr.along hT (hPe ℓ hℓ).arc hs hsy⟩, hsy⟩
      show g (P ℓ s) = 0; rw [hsy]; exact hcr.2.1
    · rintro ⟨ℓ, hℓ, hy⟩
      rw [dif_pos hℓ, Finset.mem_image] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      rw [Finite.mem_toFinset] at hs
      exact isCrossing_of_param hT (hPe ℓ ((hEf ℓ).1 hℓ)) hfin hs.1 hs.2
  have hdisj : (↑Ef : Set (Set T)).PairwiseDisjoint fun ℓ =>
      if h : ℓ ∈ Ef then (hCf ℓ h).toFinset.image (P ℓ) else ∅ := by
    intro ℓ hℓ ℓ' hℓ' hne'
    simp only [Finset.mem_coe] at hℓ hℓ'
    rw [Function.onFun, dif_pos hℓ, dif_pos hℓ', Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_image] at hy hy'
    obtain ⟨s, hs, rfl⟩ := hy
    obtain ⟨s', hs', he⟩ := hy'
    rw [Finite.mem_toFinset] at hs hs'
    have h1 : P ℓ s ∈ ℓ := by
      have := (show P ℓ s ∈ P ℓ '' Icc 0 1 from ⟨s, Ioo_subset_Icc_self hs.1, rfl⟩)
      rwa [hPim ℓ ((hEf ℓ).1 hℓ)] at this
    have h2 : P ℓ s ∈ ℓ' := by
      have := (show P ℓ' s' ∈ P ℓ' '' Icc 0 1 from ⟨s', Ioo_subset_Icc_self hs'.1, rfl⟩)
      rwa [hPim ℓ' ((hEf ℓ').1 hℓ'), he] at this
    exact (hPe ℓ ((hEf ℓ).1 hℓ)).interior s hs.1
      (edge_inter_subset hT.noSCC hT.bfin ((hEf ℓ).1 hℓ) ((hEf ℓ').1 hℓ') hne' ⟨h1, h2⟩)
  have hcard : {y | IsCrossing g y}.ncard = ∑ ℓ ∈ Ef, (C ℓ).ncard := by
    rw [hcross, ncard_coe_finset, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [dif_pos hℓ, Finset.card_image_of_injOn, ← ncard_eq_toFinset_card _ (hCf ℓ hℓ)]
    intro s hs s' hs' he
    rw [Finset.mem_coe, Finite.mem_toFinset] at hs hs'
    exact (hPe ℓ ((hEf ℓ).1 hℓ)).arc.2 (Ioo_subset_Icc_self hs.1) (Ioo_subset_Icc_self hs'.1) he
  -- the parity of each edge
  have hedge : ∀ ℓ ∈ Ef, ((C ℓ).ncard + (if g (P ℓ 0) < 0 then 1 else 0) +
      (if g (P ℓ 1) < 0 then 1 else 0)) % 2 = 0 := by
    intro ℓ hℓ
    have hγ := hPe ℓ ((hEf ℓ).1 hℓ)
    exact param_parity _ zero_lt_one (hg.comp hγ.arc.1).continuousOn
      (finite_paramZeros hfin hγ.arc) rfl (hV _ hγ.end0) (hV _ hγ.end1)
  -- regrouping the end terms by vertices
  have hends : ∀ ℓ ∈ Ef, (if g (P ℓ 0) < 0 then 1 else 0) + (if g (P ℓ 1) < 0 then 1 else 0) =
      ∑ u ∈ Vf, if u ∈ ℓ ∧ g u < 0 then 1 else 0 := by
    intro ℓ hℓ
    have hγ := hPe ℓ ((hEf ℓ).1 hℓ)
    have hint := hγ.inter_vertices hT
    rw [hPim ℓ ((hEf ℓ).1 hℓ)] at hint
    have hne01 : P ℓ 0 ≠ P ℓ 1 := hγ.arc.ne
    rw [← Finset.sum_filter]
    have : Vf.filter (fun u => u ∈ ℓ ∧ g u < 0) =
        ({P ℓ 0, P ℓ 1} : Finset T).filter (fun u => g u < 0) := by
      ext u
      simp only [Finset.mem_filter, Finite.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton, Vf]
      constructor
      · rintro ⟨huV, huℓ, hgu⟩
        have : u ∈ ℓ ∩ vertices T := ⟨huℓ, huV⟩
        rw [hint] at this; exact ⟨this, hgu⟩
      · rintro ⟨hu, hgu⟩
        have : u ∈ ({P ℓ 0, P ℓ 1} : Set T) := hu
        rw [← hint] at this; exact ⟨this.2, this.1, hgu⟩
    rw [this, Finset.filter_insert, Finset.filter_singleton]
    by_cases h0 : g (P ℓ 0) < 0 <;> by_cases h1 : g (P ℓ 1) < 0 <;>
      simp [h0, h1, hne01, Finset.card_insert_of_notMem]
  have hswap : ∑ ℓ ∈ Ef, ∑ u ∈ Vf, (if u ∈ ℓ ∧ g u < 0 then 1 else 0) =
      ∑ u ∈ Vf, if g u < 0 then degree u else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [degree_eq_card hT ((Finite.mem_toFinset _).1 hu)]
    by_cases hgu : g u < 0
    · rw [if_pos hgu, Finset.card_filter]
      exact Finset.sum_congr rfl fun ℓ _ => by simp [hgu]
    · rw [if_neg hgu]; simp [hgu]
  have hodd : {u | u ∈ oddVertices T ∧ g u < 0} =
      ↑(Vf.filter fun u => Odd (if g u < 0 then degree u else 0)) := by
    ext u
    simp only [mem_setOf_eq, oddVertices, Finset.coe_filter, Finite.mem_toFinset, Vf]
    constructor
    · rintro ⟨⟨hu, n, hn, hodd⟩, hgu⟩
      refine ⟨hu, ?_⟩
      rw [if_pos hgu, degree, hn]; exact hodd
    · rintro ⟨hu, hodd⟩
      by_cases hgu : g u < 0
      · rw [if_pos hgu] at hodd
        exact ⟨⟨hu, degree u, order_eq_degree hT hu, hodd⟩, hgu⟩
      · rw [if_neg hgu] at hodd; exact absurd hodd (by decide)
  have hsum := sum_mod_two Vf fun u => if g u < 0 then degree u else 0
  rw [hodd, ncard_coe_finset, ← hsum, hcard]
  have htot : (∑ ℓ ∈ Ef, ((C ℓ).ncard + ((if g (P ℓ 0) < 0 then 1 else 0) +
      (if g (P ℓ 1) < 0 then 1 else 0)))) % 2 = 0 := by
    rw [Finset.sum_nat_mod, Finset.sum_eq_zero]
    · rfl
    · intro ℓ hℓ; rw [← add_assoc]; exact hedge ℓ hℓ
  rw [Finset.sum_add_distrib, Finset.sum_congr rfl hends, hswap] at htot
  omega

end DoubleMidset
