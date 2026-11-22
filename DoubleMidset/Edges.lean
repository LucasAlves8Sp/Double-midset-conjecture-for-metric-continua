module

public import DoubleMidset.TreeStructure
public import DoubleMidset.Branch

/-!
# Edges of a finite tree

The standing hypotheses on a finite tree are bundled in `TreeHyp`. Edges are handled through
*edge parametrizations* (`IsEdgeParam`): arc parametrizations `γ` with `γ 0, γ 1` vertices and
`γ (0, 1)` free of vertices. Every edge point lies in the open arc of such a parametrization,
which is its open edge (`exists_edgeParam`, `IsEdgeParam.image_Ioo_eq`), and images of open
subintervals are open in `T` (`IsEdgeParam.isOpen_image_Ioo`).

This file also proves the remaining assertions of the paragraph after Lemma 2.7: edge points
have order two, the number of odd-degree vertices is even, in a branched tree every edge has a
branch point as an end, the sum of the degrees is `2(|V| - 1)`, and the tip formula (3).
-/

@[expose] public section

open Set Topology Function Metric

namespace DoubleMidset

universe u

/-- The standing hypotheses on a finite tree (besides the instances). -/
structure TreeHyp (T : Type u) [MetricSpace T] : Prop where
  noSCC : ∀ C : Set T, ¬ IsSimpleClosedCurve C
  bfin : (branchSet T).Finite
  bord : ∀ p : T, IsBranchPoint p → order p ≠ ⊤

/-- An *edge parametrization*: an arc parametrization with vertices at `0` and `1` and no vertex
in between. -/
structure IsEdgeParam {T : Type u} [TopologicalSpace T] (γ : ℝ → T) : Prop where
  arc : IsArcParam γ
  end0 : γ 0 ∈ vertices T
  end1 : γ 1 ∈ vertices T
  interior : ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∉ vertices T

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

theorem TreeHyp.vertices_finite : (vertices T).Finite :=
  DoubleMidset.vertices_finite hT.noSCC hT.bfin hT.bord

theorem isClosed_vertices : IsClosed (vertices T) := hT.vertices_finite.isClosed

theorem isOpen_openEdge (x : T) : IsOpen (connectedComponentIn (vertices T)ᶜ x) :=
  (isClosed_vertices hT).isOpen_compl.connectedComponentIn

/-- **Edge points have order two.** -/
theorem order_eq_two_of_notMem {x : T} (hx : x ∉ vertices T) : order x = 2 := by
  have hxB : x ∉ branchSet T := fun h => hx (branchSet_subset_vertices h)
  obtain ⟨a, b, hab, hK⟩ := exists_ends hT.noSCC hT.bfin hxB
  have ha := end_mem_vertices_left hT.noSCC hT.bfin hxB hab hK
  have hb := end_mem_vertices_right hT.noSCC hT.bfin hxB hab hK
  exact order_eq_two_of_ne_ends hT.noSCC hT.bfin hxB hab hK (subset_closure (mem_bcomp hxB))
    (fun e => hx (e ▸ ha)) (fun e => hx (e ▸ hb))

/-- Every edge point lies in the open arc of an edge parametrization, which is its open edge. -/
theorem exists_edgeParam {x : T} (hx : x ∉ vertices T) :
    ∃ γ : ℝ → T, ∃ s ∈ Ioo (0 : ℝ) 1, IsEdgeParam γ ∧ γ s = x ∧
      γ '' Ioo 0 1 = connectedComponentIn (vertices T)ᶜ x ∧
      γ '' Icc 0 1 = closure (connectedComponentIn (vertices T)ᶜ x) := by
  have hxB : x ∉ branchSet T := fun h => hx (branchSet_subset_vertices h)
  obtain ⟨a, b, hab, hK⟩ := exists_ends hT.noSCC hT.bfin hxB
  have ha := end_mem_vertices_left hT.noSCC hT.bfin hxB hab hK
  have hb := end_mem_vertices_right hT.noSCC hT.bfin hxB hab hK
  obtain ⟨γ, hγ, hγim, hγ0, hγ1⟩ := (seg_isArcBetween hab).exists_param
  have hW := cc_vertices_eq hT.noSCC hT.bfin hx hab hK
  have hIoo := seg_diff_ends_eq hγ hγim hγ0 hγ1
  have hxW : x ∈ γ '' Ioo 0 1 := by rw [← hIoo, ← hW]; exact mem_connectedComponentIn hx
  obtain ⟨s, hs, rfl⟩ := hxW
  refine ⟨γ, s, hs, ⟨hγ, hγ0 ▸ ha, hγ1 ▸ hb, fun t ht => ?_⟩, rfl, by rw [hW, hIoo], ?_⟩
  · have : γ t ∈ connectedComponentIn (vertices T)ᶜ (γ s) := by rw [hW, hIoo]; exact ⟨t, ht, rfl⟩
    exact connectedComponentIn_subset _ _ this
  · rw [hW, closure_seg_diff_ends hab, hγim]

/-- The open arc of an edge parametrization is the open edge of each of its points, and its
closed arc is an edge. -/
theorem IsEdgeParam.image_Ioo_eq {γ : ℝ → T} (hγ : IsEdgeParam γ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : γ '' Ioo 0 1 = connectedComponentIn (vertices T)ᶜ (γ t) := by
  have hx := hγ.interior t ht
  obtain ⟨γ', s, hs, hγ', hγ's, hW', hcl'⟩ := exists_edgeParam hT hx
  -- `γ [0,1]` is the edge of `γ t`
  have hsub : γ '' Ioo 0 1 ⊆ connectedComponentIn (vertices T)ᶜ (γ t) :=
    hγ.arc.isPreconnected_image_Ioo.subset_connectedComponentIn ⟨t, ht, rfl⟩
      (by rintro _ ⟨r, hr, rfl⟩; exact hγ.interior r hr)
  have hsubcl : γ '' Icc 0 1 ⊆ γ' '' Icc 0 1 := by
    rw [hcl']
    calc γ '' Icc 0 1 ⊆ closure (γ '' Ioo 0 1) := by
          rw [← closure_Ioo (zero_ne_one' ℝ)]; exact image_closure_subset_closure_image hγ.arc.1
      _ ⊆ _ := closure_mono hsub
  have hends : ∀ r ∈ ({0, 1} : Set ℝ), γ r = γ' 0 ∨ γ r = γ' 1 := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) 1 := by rcases hr with rfl | rfl <;> norm_num
    obtain ⟨q, hq, hqe⟩ := hsubcl ⟨r, hrI, rfl⟩
    have hV : γ r ∈ vertices T := by rcases hr with rfl | rfl; exact hγ.end0; exact hγ.end1
    rcases eq_or_lt_of_le hq.1 with e | e
    · left; rw [← hqe, ← e]
    rcases eq_or_lt_of_le hq.2 with e' | e'
    · right; rw [← hqe, e']
    exact (hγ'.interior q ⟨e, e'⟩ (hqe ▸ hV)).elim
  have hne : γ 0 ≠ γ 1 := hγ.arc.ne
  have hne' : γ' 0 ≠ γ' 1 := hγ'.arc.ne
  have hseg : γ '' Icc 0 1 = γ' '' Icc 0 1 := by
    have h1 := seg_eq hT.noSCC hγ.arc.isArcBetween
    have h2 := seg_eq hT.noSCC hγ'.arc.isArcBetween
    rcases hends 0 (Or.inl rfl) with e0 | e0 <;> rcases hends 1 (Or.inr rfl) with e1 | e1
    · exact (hne (e0.trans e1.symm)).elim
    · rw [← h1, ← h2, e0, e1]
    · rw [← h1, ← h2, e0, e1, seg_symm hT.noSCC]
    · exact (hne (e0.trans e1.symm)).elim
  -- the open arcs agree
  refine Subset.antisymm hsub fun y hy => ?_
  have hyV : y ∉ vertices T := connectedComponentIn_subset _ _ hy
  rw [← hW'] at hy
  have : y ∈ γ '' Icc 0 1 := hseg ▸ image_mono Ioo_subset_Icc_self hy
  obtain ⟨r, hr, rfl⟩ := this
  refine ⟨r, ⟨lt_of_le_of_ne hr.1 fun e => hyV (e ▸ hγ.end0), lt_of_le_of_ne hr.2
    fun e => hyV (e ▸ hγ.end1)⟩, rfl⟩

/-- The closed arc of an edge parametrization is an edge. -/
theorem IsEdgeParam.isEdge {γ : ℝ → T} (hγ : IsEdgeParam γ) : IsEdge (γ '' Icc 0 1) := by
  refine ⟨_, ⟨γ (1 / 2), hγ.interior _ ⟨by norm_num, by norm_num⟩, rfl⟩, ?_⟩
  rw [← hγ.image_Ioo_eq hT ⟨by norm_num, by norm_num⟩]
  apply Subset.antisymm
  · calc γ '' Icc 0 1 = γ '' closure (Ioo 0 1) := by rw [closure_Ioo (zero_ne_one' ℝ)]
      _ ⊆ closure (γ '' Ioo 0 1) := image_closure_subset_closure_image hγ.arc.1
  · exact closure_minimal (image_mono Ioo_subset_Icc_self) hγ.arc.isCompact_image.isClosed

omit hT in
/-- The image of an open subinterval under an arc parametrization, intersected with the open
arc, is the open arc minus two compact pieces. -/
theorem IsArcParam.image_Ioo_eq_diff {γ : ℝ → T} (hγ : IsArcParam γ) {c d : ℝ} (hc : 0 ≤ c)
    (hcd : c < d) (hd : d ≤ 1) :
    γ '' Ioo c d = γ '' Ioo 0 1 \ (γ '' Icc 0 c ∪ γ '' Icc d 1) := by
  ext y; constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ⟨hc.trans_lt ht.1, ht.2.trans_le hd⟩, rfl⟩, ?_⟩
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨(hc.trans_lt ht.1).le, (ht.2.trans_le hd).le⟩
    rintro (⟨r, hr, hre⟩ | ⟨r, hr, hre⟩)
    · have := hγ.2 ⟨hr.1, hr.2.trans (hcd.le.trans hd)⟩ ht1 hre
      linarith [hr.2, ht.1]
    · have := hγ.2 ⟨(hc.trans hcd.le).trans hr.1, hr.2⟩ ht1 hre
      linarith [hr.1, ht.2]
  · rintro ⟨⟨t, ht, rfl⟩, hy⟩
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · by_contra h; push_neg at h; exact hy (Or.inl ⟨t, ⟨ht.1.le, h⟩, rfl⟩)
    · by_contra h; push_neg at h; exact hy (Or.inr ⟨t, ⟨h, ht.2.le⟩, rfl⟩)

/-- Images of open subintervals under an edge parametrization are open in `T`. -/
theorem IsEdgeParam.isOpen_image_Ioo {γ : ℝ → T} (hγ : IsEdgeParam γ) {c d : ℝ} (hc : 0 ≤ c)
    (hd : d ≤ 1) : IsOpen (γ '' Ioo c d) := by
  rcases le_or_gt d c with hdc | hcd
  · rw [Ioo_eq_empty (not_lt.2 hdc), image_empty]; exact isOpen_empty
  rw [hγ.arc.image_Ioo_eq_diff hc hcd hd, hγ.image_Ioo_eq hT ⟨by norm_num, by norm_num⟩
    (t := 1 / 2)]
  exact (isOpen_openEdge hT _).sdiff
    ((hγ.arc.isCompact_image).union (hγ.arc.isCompact_image)).isClosed

/-- The degree of a vertex: its order, as a natural number. -/
noncomputable def degree {X : Type u} [TopologicalSpace X] (x : X) : ℕ := (order x).toNat

theorem TreeHyp.edges_finite : {ℓ : Set T | IsEdge ℓ}.Finite :=
  DoubleMidset.edges_finite hT.noSCC hT.bfin hT.bord

open Classical in
/-- The degree of a vertex is its number of edges. -/
theorem degree_eq_card {u : T} (hu : u ∈ vertices T) :
    degree u = (hT.edges_finite.toFinset.filter (u ∈ ·)).card := by
  have h := order_eq_encard_edges hT.noSCC hT.bfin hT.bord hu
  have hfin : {ℓ : Set T | IsEdge ℓ ∧ u ∈ ℓ}.Finite :=
    hT.edges_finite.subset fun ℓ hℓ => hℓ.1
  have : {ℓ : Set T | IsEdge ℓ ∧ u ∈ ℓ} = ↑(hT.edges_finite.toFinset.filter (u ∈ ·)) := by
    ext ℓ; simp
  rw [degree, h, this, encard_coe_eq_coe_finsetCard]; rfl

theorem order_eq_degree {u : T} (hu : u ∈ vertices T) : order u = degree u := by
  rw [degree, ENat.coe_toNat]
  rw [order_eq_encard_edges hT.noSCC hT.bfin hT.bord hu]
  exact (hT.edges_finite.subset fun ℓ hℓ => hℓ.1).encard_lt_top.ne

omit hT in
/-- Parity of a sum. -/
theorem sum_mod_two {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) % 2 = (s.filter fun x => Odd (f x)).card % 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.filter_insert]
    by_cases hodd : Odd (f a)
    · rw [if_pos hodd, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_filter.1 h).1)]
      obtain ⟨k, hk⟩ := hodd; omega
    · rw [if_neg hodd]
      rw [Nat.not_odd_iff_even] at hodd; obtain ⟨k, hk⟩ := hodd; omega

/-- **The handshake identity.** The degrees of the vertices sum to twice the number of
edges. -/
theorem sum_degree :
    ∑ u ∈ hT.vertices_finite.toFinset, degree u = 2 * hT.edges_finite.toFinset.card := by
  classical
  set Vf := hT.vertices_finite.toFinset
  set Ef := hT.edges_finite.toFinset
  have h1 : ∑ u ∈ Vf, degree u = ∑ u ∈ Vf, ∑ ℓ ∈ Ef, if u ∈ ℓ then 1 else 0 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [degree_eq_card hT ((Set.Finite.mem_toFinset _).1 hu), Finset.card_filter]
  have h2 : ∀ ℓ ∈ Ef, (∑ u ∈ Vf, if u ∈ ℓ then 1 else 0) = 2 := by
    intro ℓ hℓ
    rw [← Finset.card_filter]
    obtain ⟨a, b, hab, -, hV⟩ := edge_isArc hT.noSCC hT.bfin (hT.edges_finite.mem_toFinset.1 hℓ)
    have : Vf.filter (· ∈ ℓ) = {a, b} := by
      ext u
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton, Vf]
      constructor
      · rintro ⟨huV, huℓ⟩
        have : u ∈ ℓ ∩ vertices T := ⟨huℓ, huV⟩
        rw [hV] at this; exact this
      · intro h
        have : u ∈ ({a, b} : Set T) := h
        rw [← hV] at this; exact ⟨this.2, this.1⟩
    rw [this, Finset.card_pair hab]
  rw [h1, Finset.sum_comm, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The degrees sum to `2(|V| - 1)`. -/
theorem sum_degree' :
    ∑ u ∈ hT.vertices_finite.toFinset, degree u = 2 * ((vertices T).ncard - 1) := by
  rw [sum_degree hT, ← ncard_eq_toFinset_card _ hT.edges_finite,
    ← ncard_edges_add_one hT.noSCC hT.bfin hT.bord, Nat.add_sub_cancel]

/-- **The number of odd-degree vertices is even.** -/
theorem even_ncard_oddVertices : Even (oddVertices T).ncard := by
  classical
  have h := sum_mod_two hT.vertices_finite.toFinset degree
  rw [sum_degree hT, Nat.mul_mod_right] at h
  have hodd : oddVertices T = ↑(hT.vertices_finite.toFinset.filter fun u => Odd (degree u)) := by
    ext u
    simp only [oddVertices, mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hu, n, hn, hodd⟩
      refine ⟨hu, ?_⟩
      rw [degree, hn]; exact hodd
    · rintro ⟨hu, hodd⟩
      exact ⟨hu, degree u, order_eq_degree hT hu, hodd⟩
  rw [hodd, ncard_coe_finset, Nat.even_iff]; omega

/-- In a branched finite tree every edge has an end that is a branch point. -/
theorem edge_has_branch_end (hbr : (branchSet T).Nonempty) {ℓ : Set T} (hℓ : IsEdge ℓ) :
    ∃ a b : T, a ≠ b ∧ seg a b = ℓ ∧ ℓ ∩ vertices T = {a, b} ∧ IsBranchPoint a := by
  obtain ⟨x, hx, rfl⟩ := (isEdge_iff hT.noSCC hT.bfin).1 hℓ
  obtain ⟨a, b, hab, hK⟩ := exists_ends hT.noSCC hT.bfin hx
  obtain ⟨a', b', hab', hK', hV⟩ := edge_isArc hT.noSCC hT.bfin hℓ
  -- if neither end is a branch point, the component is clopen
  by_cases ha : a ∈ branchSet T
  · refine ⟨a, b, hab, hK, ?_, ha⟩
    have h1 := (edge_isArc hT.noSCC hT.bfin hℓ)
    have e : seg a' b' = seg a b := hK'.trans hK.symm
    rw [hV]
    have ha'' : a ∈ closure (bcomp x) ∩ vertices T :=
      ⟨end_mem_closure_left hT.noSCC hT.bfin hx hab hK,
        end_mem_vertices_left hT.noSCC hT.bfin hx hab hK⟩
    have hb'' : b ∈ closure (bcomp x) ∩ vertices T :=
      ⟨end_mem_closure_right hT.noSCC hT.bfin hx hab hK,
        end_mem_vertices_right hT.noSCC hT.bfin hx hab hK⟩
    rw [hV] at ha'' hb''
    ext y; simp only [mem_insert_iff, mem_singleton_iff]
    rcases ha'' with rfl | rfl <;> rcases hb'' with rfl | rfl
    · exact (hab rfl).elim
    · rfl
    · constructor <;> rintro (h | h) <;> simp [h]
    · exact (hab rfl).elim
  by_cases hb : b ∈ branchSet T
  · refine ⟨b, a, hab.symm, by rw [seg_symm hT.noSCC]; exact hK, ?_, hb⟩
    have ha'' : a ∈ closure (bcomp x) ∩ vertices T :=
      ⟨end_mem_closure_left hT.noSCC hT.bfin hx hab hK,
        end_mem_vertices_left hT.noSCC hT.bfin hx hab hK⟩
    have hb'' : b ∈ closure (bcomp x) ∩ vertices T :=
      ⟨end_mem_closure_right hT.noSCC hT.bfin hx hab hK,
        end_mem_vertices_right hT.noSCC hT.bfin hx hab hK⟩
    rw [hV] at ha'' hb'' ⊢
    ext y; simp only [mem_insert_iff, mem_singleton_iff]
    rcases ha'' with rfl | rfl <;> rcases hb'' with rfl | rfl
    · exact (hab rfl).elim
    · constructor <;> rintro (h | h) <;> simp [h]
    · rfl
    · exact (hab rfl).elim
  exfalso
  have hcl : closure (bcomp x) ⊆ bcomp x := by
    intro y hy
    by_contra hyW
    have hyB : y ∈ branchSet T := by
      by_contra h; exact hyW (mem_bcomp_of_mem_closure hx hy h)
    by_cases hya : y = a
    · exact ha (hya ▸ hyB)
    by_cases hyb : y = b
    · exact hb (hyb ▸ hyB)
    exact hyW (mem_bcomp_of_ne_ends hT.noSCC hT.bfin hx hab hK hy hya hyb)
  have := IsClopen.eq_univ ⟨closure_subset_iff_isClosed.1 hcl, isOpen_bcomp hT.bfin x⟩
    ⟨x, mem_bcomp hx⟩
  obtain ⟨v, hv⟩ := hbr
  exact bcomp_subset x (this ▸ mem_univ v) hv

/-- **The tip formula (3)**: `t = 2 + ∑_{u branch point} (deg u - 2)`. -/
theorem tips_formula :
    {p : T | IsTip p}.ncard = 2 + ∑ u ∈ hT.bfin.toFinset, (degree u - 2) := by
  classical
  have htf : {p : T | IsTip p}.Finite := hT.vertices_finite.subset fun p hp => Or.inl hp
  set Vf := hT.vertices_finite.toFinset
  set Bf := hT.bfin.toFinset
  set Tf := htf.toFinset
  have hVsplit : Vf = Tf ∪ Bf := by
    ext u; simp only [Finset.mem_union, Set.Finite.mem_toFinset, Vf, Tf, Bf]; rfl
  have hdisj : Disjoint Tf Bf := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [Set.Finite.mem_toFinset, Tf, Bf] at hu hu'
    have h' : (3 : ℕ∞) ≤ 1 := (show order u = 1 from hu) ▸ hu'
    exact absurd h' (by decide)
  have hsum : ∑ u ∈ Vf, degree u = 2 * ((vertices T).ncard - 1) := sum_degree' hT
  rw [hVsplit, Finset.sum_union hdisj] at hsum
  have htips : ∑ u ∈ Tf, degree u = Tf.card := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Set.Finite.mem_toFinset, Tf] at hu
    rw [degree, show order u = 1 from hu]; rfl
  have hVcard : (vertices T).ncard = Tf.card + Bf.card := by
    rw [ncard_eq_toFinset_card _ hT.vertices_finite, show hT.vertices_finite.toFinset = Tf ∪ Bf
      from hVsplit, Finset.card_union_of_disjoint hdisj]
  have hge : ∀ u ∈ Bf, 3 ≤ degree u := by
    intro u hu
    simp only [Set.Finite.mem_toFinset, Bf] at hu
    have h3 : (3 : ℕ∞) ≤ order u := hu
    rw [order_eq_degree hT (Or.inr hu)] at h3; exact_mod_cast h3
  have hsub : ∑ u ∈ Bf, (degree u - 2) + 2 * Bf.card = ∑ u ∈ Bf, degree u := by
    rw [Finset.card_eq_sum_ones, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    have := hge u hu; omega
  rw [htips, hVcard] at hsum
  rw [ncard_eq_toFinset_card _ htf]
  change Tf.card = _
  have hBpos : 0 < Tf.card + Bf.card := by
    by_contra h0
    push_neg at h0
    have : (vertices T).ncard = 0 := by omega
    -- a finite tree has at least two vertices
    have hne := sum_degree hT
    have hE : 0 < hT.edges_finite.toFinset.card := by
      rw [Finset.card_pos]
      obtain ⟨y⟩ := (inferInstance : Nonempty T)
      obtain ⟨ℓ, hℓ, -⟩ : y ∈ ⋃₀ {ℓ : Set T | IsEdge ℓ} := by
        rw [sUnion_edges hT.noSCC hT.bfin hT.bord]; exact mem_univ y
      exact ⟨ℓ, (Set.Finite.mem_toFinset _).2 hℓ⟩
    have := ncard_edges_add_one hT.noSCC hT.bfin hT.bord
    rw [ncard_eq_toFinset_card _ hT.edges_finite] at this
    omega
  omega

end DoubleMidset
