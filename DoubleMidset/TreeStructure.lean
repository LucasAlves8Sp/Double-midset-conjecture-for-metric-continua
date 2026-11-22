module

public import DoubleMidset.NoBranch
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The structure of finite trees (Lemma 2.7)

Let `T` be a dendrite with finitely many branch points, each of finite order, and let `B` be the
set of branch points. The paper proves Lemma 2.7 by induction on `|B|`. Here the edges are
obtained directly from the components of `T \ B`:

* the closure `K` of a component `W` of `T \ B` has no branch point relative to itself, so it is
  an arc `[a, b]` (`exists_seg_eq` of `NoBranch.lean`); its points other than `a, b` lie in `W`
  and have order two; an end lying in `W` is a tip;
* `W ↦ (b, component of T \ {b} containing W)`, for a branch point `b ∈ K \ W`, is injective, so
  there are finitely many components, hence finitely many tips and vertices;
* the components of `T \ V` are the sets `K \ {a, b}`, so the edges (closures of components of
  `T \ V`, see `Defs.lean`) are exactly the arcs `K`;
* the edges containing a vertex `u` correspond to the components of `T \ {u}`, so the degree of
  `u` is its number of edges.
-/

@[expose] public section

open Set Topology Function Metric

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] (hD : ∀ C : Set T, ¬ IsSimpleClosedCurve C)

/-- The set of branch points. -/
def branchSet (T : Type u) [TopologicalSpace T] : Set T := {p | IsBranchPoint p}

/-- The component of `T \ B` containing `x`. -/
noncomputable def bcomp (x : T) : Set T := connectedComponentIn (branchSet T)ᶜ x

section Components

variable (hBf : (branchSet T).Finite)
include hBf

theorem isOpen_bcomp (x : T) : IsOpen (bcomp x) :=
  hBf.isClosed.isOpen_compl.connectedComponentIn

omit hBf in
theorem bcomp_subset (x : T) : bcomp x ⊆ (branchSet T)ᶜ := connectedComponentIn_subset _ _

omit hBf in
theorem mem_bcomp {x : T} (hx : x ∉ branchSet T) : x ∈ bcomp x := mem_connectedComponentIn hx

omit hBf in
theorem isPreconnected_bcomp (x : T) : IsPreconnected (bcomp x) :=
  isPreconnected_connectedComponentIn

omit hBf in
/-- A point of the closure of a component of `T \ B` that is not a branch point lies in the
component. -/
theorem mem_bcomp_of_mem_closure {x y : T} (hx : x ∉ branchSet T) (hy : y ∈ closure (bcomp x))
    (hyB : y ∉ branchSet T) : y ∈ bcomp x := by
  have hpc : IsPreconnected (insert y (bcomp x)) :=
    (isPreconnected_bcomp x).subset_closure (subset_insert _ _)
      (insert_subset hy subset_closure)
  exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (mem_bcomp hx))
    (insert_subset hyB (bcomp_subset x)) (mem_insert y _)

omit hBf in
theorem bcomp_eq {x y : T} (hy : y ∈ bcomp x) : bcomp y = bcomp x :=
  (connectedComponentIn_eq hy).symm

omit hBf in
/-- Two components of `T \ B` are equal or disjoint. -/
theorem bcomp_disjoint_or_eq (x y : T) : bcomp x = bcomp y ∨ Disjoint (bcomp x) (bcomp y) := by
  by_cases h : (bcomp x ∩ bcomp y).Nonempty
  · obtain ⟨z, hzx, hzy⟩ := h
    left; rw [← bcomp_eq hzx, bcomp_eq hzy]
  · right; exact disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h)

theorem bcomp_nontrivial [Nontrivial T] {x : T} (hx : x ∉ branchSet T) : (bcomp x).Nontrivial := by
  by_contra h
  rw [not_nontrivial_iff] at h
  have hsub : bcomp x = {x} := h.eq_singleton_of_mem (mem_bcomp hx)
  have hopen : IsOpen ({x} : Set T) := hsub ▸ isOpen_bcomp hBf x
  have := IsClopen.eq_univ ⟨isClosed_singleton, hopen⟩ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := exists_ne x
  exact hy (this ▸ mem_univ y : y ∈ ({x} : Set T))

omit hBf in
/-- Points of the closure of a component `W`, other than a given branch point `w`, lie in the
component of `T \ {w}` containing `W`. -/
theorem cc_eq_of_mem_closure_bcomp {x z w : T} (hx : x ∉ branchSet T) (hw : w ∈ branchSet T)
    (hz : z ∈ closure (bcomp x)) (hzw : z ≠ w) :
    connectedComponentIn {w}ᶜ z = connectedComponentIn {w}ᶜ x := by
  have hwW : w ∉ bcomp x := fun h => bcomp_subset x h hw
  have hpc : IsPreconnected (insert z (bcomp x)) :=
    (isPreconnected_bcomp x).subset_closure (subset_insert _ _)
      (insert_subset hz subset_closure)
  have hsub : insert z (bcomp x) ⊆ {w}ᶜ := by
    rintro y (rfl | hy)
    · exact hzw
    · rintro rfl; exact hwW hy
  exact (connectedComponentIn_eq (hpc.subset_connectedComponentIn (mem_insert_of_mem _
    (mem_bcomp hx)) hsub (mem_insert z _))).symm

end Components

/-- Natural-number arithmetic in `ℕ∞`: `2 ≤ o < 3` forces `o = 2`. -/
theorem enat_eq_two {o : ℕ∞} (h1 : 2 ≤ o) (h2 : ¬ 3 ≤ o) : o = 2 := by
  induction o using ENat.recTopCoe with
  | top => exact (h2 le_top).elim
  | coe n =>
    have h1' : 2 ≤ n := by exact_mod_cast h1
    have h2' : ¬ 3 ≤ n := fun h => h2 (by exact_mod_cast h)
    have : n = 2 := by omega
    rw [this]; rfl

omit [MetricSpace T] [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] in
/-- The first parameter at which a path enters a closed set. -/
theorem exists_first_entry {X : Type*} [TopologicalSpace X] {h : ℝ → X} (hh : Continuous h)
    {K : Set X} (hK : IsClosed K) (h0 : h 0 ∉ K) (h1 : h 1 ∈ K) :
    ∃ s ∈ Ioc (0 : ℝ) 1, h s ∈ K ∧ ∀ t ∈ Ico 0 s, h t ∉ K := by
  set Kp := Icc (0 : ℝ) 1 ∩ h ⁻¹' K
  have hKpc : IsCompact Kp := Metric.isCompact_of_isClosed_isBounded
    (isClosed_Icc.inter (hK.preimage hh)) ((Metric.isBounded_Icc 0 1).subset inter_subset_left)
  have hne : Kp.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  have hs := hKpc.sInf_mem hne
  have hle : ∀ t ∈ Kp, sInf Kp ≤ t := fun t ht => csInf_le hKpc.bddBelow ht
  have hpos : 0 < sInf Kp := lt_of_le_of_ne hs.1.1 fun e => h0 (by rw [e]; exact hs.2)
  exact ⟨sInf Kp, ⟨hpos, hs.1.2⟩, hs.2, fun t ht htK =>
    absurd (hle t ⟨⟨ht.1, ht.2.le.trans hs.1.2⟩, htK⟩) (not_le.2 ht.2)⟩

section Arcs

variable (hBf : (branchSet T).Finite)
include hD hBf

theorem noRelBranch_closure_bcomp {x : T} (hx : x ∉ branchSet T) :
    NoRelBranch (closure (bcomp x)) := by
  intro w hw z hz p hp q hq hzw hpw hqw h1 h2 h3
  by_cases hwB : w ∈ branchSet T
  · exact h1 (by rw [cc_eq_of_mem_closure_bcomp hx hwB hz hzw,
      cc_eq_of_mem_closure_bcomp hx hwB hp hpw])
  · exact hwB (three_le_order hzw hpw hqw h1 h2 h3)

/-- The closure of a component of `T \ B` is an arc. -/
theorem exists_ends [Nontrivial T] {x : T} (hx : x ∉ branchSet T) :
    ∃ a b : T, a ≠ b ∧ seg a b = closure (bcomp x) := by
  obtain ⟨a, -, b, -, hab, h⟩ := exists_seg_eq hD isClosed_closure
    (isPreconnected_bcomp x).closure ((bcomp_nontrivial hBf hx).mono subset_closure)
    (noRelBranch_closure_bcomp hD hBf hx)
  exact ⟨a, b, hab, h⟩

variable {x a b : T} (hx : x ∉ branchSet T) (hab : a ≠ b) (hK : seg a b = closure (bcomp x))
include hx hab hK

theorem end_mem_closure_left : a ∈ closure (bcomp x) := hK ▸ left_mem_seg a b

theorem end_mem_closure_right : b ∈ closure (bcomp x) := hK ▸ right_mem_seg hD a b

/-- Points of the closure of a component other than its two ends lie in the component. -/
theorem mem_bcomp_of_ne_ends {y : T} (hy : y ∈ closure (bcomp x)) (hya : y ≠ a) (hyb : y ≠ b) :
    y ∈ bcomp x := by
  by_contra hyW
  have hyB : y ∈ branchSet T := by
    by_contra h; exact hyW (mem_bcomp_of_mem_closure hx hy h)
  apply ends_separate hD (seg_isArcBetween hab) (hK ▸ hy) hya hyb
  rw [cc_eq_of_mem_closure_bcomp hx hyB (end_mem_closure_left hD hBf hx hab hK) hya.symm,
    cc_eq_of_mem_closure_bcomp hx hyB (end_mem_closure_right hD hBf hx hab hK) hyb.symm]

/-- Points of an edge other than its ends have order two. -/
theorem order_eq_two_of_ne_ends {y : T} (hy : y ∈ closure (bcomp x)) (hya : y ≠ a)
    (hyb : y ≠ b) : order y = 2 :=
  enat_eq_two (two_le_order_of_mem_arc hD (seg_isArcBetween hab) (hK ▸ hy) hya hyb)
    (fun h => bcomp_subset x (mem_bcomp_of_ne_ends hD hBf hx hab hK hy hya hyb) h)

/-- An end of the arc `closure W` lying in `W` is a tip. -/
theorem isTip_of_end_mem (haW : a ∈ bcomp x) : IsTip a := by
  have key : ∀ y, y ≠ a → connectedComponentIn {a}ᶜ y = connectedComponentIn {a}ᶜ b := by
    intro y hya
    by_cases hyK : y ∈ closure (bcomp x)
    · -- along the arc from `y` to `b`
      obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hab).exists_param
      rw [hK] at hgim
      obtain ⟨s, hs, rfl⟩ : y ∈ g '' Icc 0 1 := hgim ▸ hyK
      have hs0 : s ≠ 0 := fun e => hya (by rw [e, hg0])
      have hsub : g '' Icc s 1 ⊆ {a}ᶜ := by
        rintro _ ⟨t, ht, rfl⟩ he
        have : t = 0 := hg.2 ⟨hs.1.trans ht.1, ht.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hg0.symm)
        exact hs0 (le_antisymm (this ▸ ht.1) hs.1)
      have hpc : IsPreconnected (g '' Icc s 1) := hg.isPreconnected_image
      exact connectedComponentIn_eq (hpc.subset_connectedComponentIn ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩
        hsub ⟨1, ⟨hs.2, le_rfl⟩, hg1⟩)
    · -- along the arc from `y` to `a`, which enters the closure at `b`
      obtain ⟨h, hh, -, h0, h1⟩ := (seg_isArcBetween hya).exists_param
      obtain ⟨s, hs, hsK, hbefore⟩ := exists_first_entry hh.1 isClosed_closure
        (by rw [h0]; exact hyK) (by rw [h1]; exact subset_closure haW)
      have hsW : h s ∉ bcomp x := by
        intro hW
        have hop : IsOpen (h ⁻¹' bcomp x) := (isOpen_bcomp hBf x).preimage hh.1
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hop s hW
        set t := max (s - ε / 2) (s / 2)
        have ht : t ∈ Ico 0 s := ⟨le_max_of_le_right (by linarith [hs.1]),
          max_lt (by linarith) (by linarith [hs.1])⟩
        have htb : t ∈ ball s ε := by
          rw [mem_ball, Real.dist_eq, abs_lt]
          constructor
          · linarith [le_max_left (s - ε / 2) (s / 2)]
          · linarith [ht.2]
        exact hbefore t ht (subset_closure (hball htb))
      have hsb : h s = b := by
        rcases (show h s = a ∨ h s = b by
          by_contra hc; push_neg at hc
          exact hsW (mem_bcomp_of_ne_ends hD hBf hx hab hK hsK hc.1 hc.2)) with e | e
        · exact (hsW (e ▸ haW)).elim
        · exact e
      have hsub : h '' Icc 0 s ⊆ {a}ᶜ := by
        rintro _ ⟨t, ht, rfl⟩ he
        rcases eq_or_lt_of_le ht.2 with e | e
        · rw [e, hsb] at he; exact hab he.symm
        · exact hbefore t ⟨ht.1, e⟩ (he ▸ subset_closure haW)
      have hpc : IsPreconnected (h '' Icc 0 s) := hh.isPreconnected_image
      have := hpc.subset_connectedComponentIn ⟨0, ⟨le_rfl, hs.1.le⟩, h0⟩ hsub
        ⟨s, ⟨hs.1.le, le_rfl⟩, hsb⟩
      exact connectedComponentIn_eq this
  have hcomps : compsAt a = {connectedComponentIn {a}ᶜ b} := by
    ext C; constructor
    · rintro ⟨y, hya, rfl⟩; exact key y hya
    · rintro rfl; exact ⟨b, hab.symm, rfl⟩
  rw [IsTip, order_eq, hcomps, encard_singleton]

/-- The ends of the arc `closure W` are vertices. -/
theorem end_mem_vertices_left : a ∈ vertices T := by
  by_cases haW : a ∈ bcomp x
  · exact Or.inl (isTip_of_end_mem hD hBf hx hab hK haW)
  · right
    by_contra h
    exact haW (mem_bcomp_of_mem_closure hx (end_mem_closure_left hD hBf hx hab hK) h)


theorem end_mem_vertices_right : b ∈ vertices T :=
  end_mem_vertices_left hD hBf hx hab.symm (by rw [seg_symm hD]; exact hK)

/-- The arc from a point of `W` to the end `a` of `closure W` stays in `W ∪ {a}`. -/
theorem seg_to_end_subset {y : T} (hy : y ∈ bcomp x) : seg y a ⊆ insert a (bcomp x) := by
  have hyK : y ∈ closure (bcomp x) := subset_closure hy
  have hcy : b ∈ seg y a → b = y := by
    intro hb
    rcases eq_or_ne y a with rfl | hya
    · rw [seg_self] at hb; exact hb
    obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hab).exists_param
    obtain ⟨s, hs, rfl⟩ : y ∈ g '' Icc 0 1 := hgim ▸ hK ▸ hyK
    have hs0 : (0 : ℝ) ≠ s := fun e => hya (by rw [← e, hg0])
    obtain ⟨k, hk, hk0, hk1, hkim⟩ := hg.exists_subarc ⟨le_rfl, zero_le_one⟩ hs hs0
    have hseg : seg (g s) a = g '' uIcc 0 s := by
      rw [seg_symm hD, seg_eq hD (show IsArcBetween (k '' Icc 0 1) a (g s) by
        have := hk.isArcBetween; rwa [hk0, hk1, hg0] at this), hkim]
    rw [hseg, uIcc_of_le hs.1] at hb
    obtain ⟨t, ht, hte⟩ := hb
    have : t = 1 := hg.2 ⟨ht.1, ht.2.trans hs.2⟩ ⟨zero_le_one, le_rfl⟩ (hte.trans hg1.symm)
    rw [← hg1, show s = 1 from le_antisymm hs.2 (this ▸ ht.2)]
  intro z hz
  have hzK : z ∈ closure (bcomp x) := seg_subset hD (isPreconnected_bcomp x).closure hyK
    (end_mem_closure_left hD hBf hx hab hK) hz
  by_cases hza : z = a
  · exact Or.inl hza
  by_cases hzb : z = b
  · subst hzb; exact Or.inr (hcy hz ▸ hy)
  exact Or.inr (mem_bcomp_of_ne_ends hD hBf hx hab hK hzK hza hzb)

end Arcs

/-- The graph of a finite tree on its vertices: two distinct vertices are adjacent if they lie
on a common edge. -/
def treeGraph (T : Type u) [MetricSpace T] : SimpleGraph (vertices T) where
  Adj u v := (u : T) ≠ v ∧ ∃ ℓ, IsEdge ℓ ∧ (u : T) ∈ ℓ ∧ (v : T) ∈ ℓ
  symm := ⟨fun _ _ ⟨h, ℓ, hℓ, hu, hv⟩ => ⟨h.symm, ℓ, hℓ, hv, hu⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- The set of components of `T \ B`. -/
def bcomps (T : Type u) [MetricSpace T] : Set (Set T) :=
  {W | ∃ x, x ∉ branchSet T ∧ W = bcomp x}

section Finite

variable [Nontrivial T] (hBf : (branchSet T).Finite)
include hD hBf

/-- Two components of `T \ B` with a common boundary point `w` lie in different components of
`T \ {w}`. -/
theorem bcomp_eq_of_cc_eq {x₁ x₂ w : T} (hx₁ : x₁ ∉ branchSet T) (hx₂ : x₂ ∉ branchSet T)
    (hw₁ : w ∈ closure (bcomp x₁)) (hw₁' : w ∉ bcomp x₁) (hw₂ : w ∈ closure (bcomp x₂))
    (hw₂' : w ∉ bcomp x₂) (h : connectedComponentIn {w}ᶜ x₁ = connectedComponentIn {w}ᶜ x₂) :
    bcomp x₁ = bcomp x₂ := by
  rcases bcomp_disjoint_or_eq x₁ x₂ with e | hdisj
  · exact e
  exfalso
  -- `w` is an end of both arcs
  have hend : ∀ {x : T}, x ∉ branchSet T → w ∈ closure (bcomp x) → w ∉ bcomp x →
      ∃ c, w ≠ c ∧ seg w c = closure (bcomp x) := by
    intro x hx hw hw'
    obtain ⟨a, b, hab, hK⟩ := exists_ends hD hBf hx
    by_cases hwa : w = a
    · subst hwa; exact ⟨b, hab, hK⟩
    by_cases hwb : w = b
    · subst hwb; exact ⟨a, hab.symm, by rw [seg_symm hD]; exact hK⟩
    exact (hw' (mem_bcomp_of_ne_ends hD hBf hx hab hK hw hwa hwb)).elim
  obtain ⟨c₁, hwc₁, hK₁⟩ := hend hx₁ hw₁ hw₁'
  obtain ⟨c₂, hwc₂, hK₂⟩ := hend hx₂ hw₂ hw₂'
  have hs₁ := seg_to_end_subset hD hBf hx₁ hwc₁ hK₁ (mem_bcomp hx₁)
  have hs₂ := seg_to_end_subset hD hBf hx₂ hwc₂ hK₂ (mem_bcomp hx₂)
  have hxw₁ : x₁ ≠ w := fun e => hw₁' (e ▸ mem_bcomp hx₁)
  have hxw₂ : x₂ ≠ w := fun e => hw₂' (e ▸ mem_bcomp hx₂)
  have hmeet : seg x₁ w ∩ seg w x₂ ⊆ {w} := by
    rintro z ⟨hz₁, hz₂⟩
    rw [seg_symm hD] at hz₂
    rcases hs₁ hz₁ with e | h1
    · exact e
    rcases hs₂ hz₂ with e | h2
    · exact e
    exact (disjoint_left.1 hdisj h1 h2).elim
  have harc := (seg_isArcBetween hxw₁).union (seg_isArcBetween hxw₂.symm) hmeet
  exact ends_separate hD harc (Or.inl (right_mem_seg hD _ _)) hxw₁.symm hxw₂.symm h

/-- There are finitely many components of `T \ B`. -/
theorem bcomps_finite (hBo : ∀ p : T, IsBranchPoint p → order p ≠ ⊤) : (bcomps T).Finite := by
  -- the target: pairs (branch point, component of its complement)
  set S : Set (T × Set T) := ⋃ b ∈ branchSet T, (fun C => (b, C)) '' compsAt b
  have hS : S.Finite := hBf.biUnion fun b hb =>
    (encard_ne_top_iff.1 (by rw [← order_eq]; exact hBo b hb)).image _
  -- components with nonempty boundary inject into `S`
  have hsplit : bcomps T ⊆ {univ} ∪ {W | W ∈ bcomps T ∧ (closure W \ W).Nonempty} := by
    intro W hW
    by_cases h : (closure W \ W).Nonempty
    · exact Or.inr ⟨hW, h⟩
    · left
      obtain ⟨x, hx, rfl⟩ := hW
      have hcl : closure (bcomp x) ⊆ bcomp x := fun y hy => by
        by_contra hyW; exact h ⟨y, hy, hyW⟩
      have := IsClopen.eq_univ ⟨closure_subset_iff_isClosed.1 hcl, isOpen_bcomp hBf x⟩
        ⟨x, mem_bcomp hx⟩
      exact this
  refine (finite_singleton _).union ?_ |>.subset hsplit
  have hchoice : ∀ W ∈ {W | W ∈ bcomps T ∧ (closure W \ W).Nonempty},
      ∃ p : T × Set T, p ∈ S ∧ ∃ x, x ∉ branchSet T ∧ W = bcomp x ∧ p.1 ∈ closure W \ W ∧
        p.2 = connectedComponentIn {p.1}ᶜ x := by
    rintro W ⟨⟨x, hx, rfl⟩, ⟨w, hw, hw'⟩⟩
    have hwB : w ∈ branchSet T := by
      by_contra h; exact hw' (mem_bcomp_of_mem_closure hx hw h)
    have hxw : x ≠ w := fun e => hw' (e ▸ mem_bcomp hx)
    exact ⟨(w, connectedComponentIn {w}ᶜ x), mem_biUnion hwB ⟨_, ⟨x, hxw, rfl⟩, rfl⟩,
      x, hx, rfl, ⟨hw, hw'⟩, rfl⟩
  choose! f hfS hf using hchoice
  refine Finite.of_finite_image (f := f) (hS.subset ?_) ?_
  · rintro _ ⟨W, hW, rfl⟩; exact hfS W hW
  · intro W₁ hW₁ W₂ hW₂ he
    obtain ⟨x₁, hx₁, rfl, hb₁, hc₁⟩ := hf W₁ hW₁
    obtain ⟨x₂, hx₂, rfl, hb₂, hc₂⟩ := hf W₂ hW₂
    rw [he] at hb₁ hc₁
    exact bcomp_eq_of_cc_eq hD hBf hx₁ hx₂ hb₁.1 hb₁.2 hb₂.1 hb₂.2 (hc₁.symm.trans hc₂)

/-- The set of vertices is finite. -/
theorem vertices_finite (hBo : ∀ p : T, IsBranchPoint p → order p ≠ ⊤) : (vertices T).Finite := by
  have htips : {p : T | IsTip p}.Finite := by
    refine ((bcomps_finite hD hBf hBo).biUnion fun W hW =>
      (show {y | y ∈ closure W ∧ order y ≠ 2}.Finite from ?_)).subset ?_
    · obtain ⟨x, hx, rfl⟩ := hW
      obtain ⟨a, b, hab, hK⟩ := exists_ends hD hBf hx
      refine (toFinite {a, b}).subset fun y ⟨hy, hy2⟩ => ?_
      by_contra h
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at h
      exact hy2 (order_eq_two_of_ne_ends hD hBf hx hab hK hy h.1 h.2)
    · intro y hy
      have hyB : y ∉ branchSet T := fun h => by
        have h' : (3 : ℕ∞) ≤ 1 := hy ▸ h
        exact absurd h' (by decide)
      refine mem_biUnion ⟨y, hyB, rfl⟩ ⟨subset_closure (mem_bcomp hyB), ?_⟩
      rw [show order y = 1 from hy]; decide
  exact (htips.union hBf).subset fun p hp => hp


omit [Nontrivial T] hD hBf in
theorem branchSet_subset_vertices : branchSet T ⊆ vertices T := fun _ h => Or.inr h

omit [Nontrivial T] hD hBf in
/-- The open arc of a parametrization. -/
theorem seg_diff_ends_eq {a b : T} {g : ℝ → T} (hg : IsArcParam g) (hgim : g '' Icc 0 1 = seg a b)
    (hg0 : g 0 = a) (hg1 : g 1 = b) : seg a b \ {a, b} = g '' Ioo 0 1 := by
  rw [← hgim]; ext y; constructor
  · rintro ⟨⟨t, ht, rfl⟩, hy⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hy
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 (fun e => hy.1 (by rw [← e, hg0])),
      lt_of_le_of_ne ht.2 (fun e => hy.2 (by rw [e, hg1]))⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, Ioo_subset_Icc_self ht, rfl⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => ht.1.ne' (hg.2 ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, zero_le_one⟩ (e.trans hg0.symm)),
      fun e => ht.2.ne (hg.2 ⟨ht.1.le, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ (e.trans hg1.symm))⟩

omit [Nontrivial T] hD hBf in
theorem closure_seg_diff_ends {a b : T} (hab : a ≠ b) : closure (seg a b \ {a, b}) = seg a b := by
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hab).exists_param
  rw [seg_diff_ends_eq hg hgim hg0 hg1]
  apply Subset.antisymm
  · rw [← hgim]
    exact closure_minimal (image_mono Ioo_subset_Icc_self) hg.isCompact_image.isClosed
  · rw [← hgim, ← closure_Ioo (zero_ne_one' ℝ)]
    exact image_closure_subset_closure_image hg.1

omit [Nontrivial T] hD hBf in
theorem isPreconnected_seg_diff_ends {a b : T} (hab : a ≠ b) :
    IsPreconnected (seg a b \ {a, b}) := by
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hab).exists_param
  rw [seg_diff_ends_eq hg hgim hg0 hg1]; exact hg.isPreconnected_image_Ioo

/-- **Open edges.** The component of `T \ V` containing an edge point `x` is the open arc of the
closure of the component of `T \ B` containing `x`. -/
theorem cc_vertices_eq {x a b : T} (hx : x ∉ vertices T) (hab : a ≠ b)
    (hK : seg a b = closure (bcomp x)) :
    connectedComponentIn (vertices T)ᶜ x = seg a b \ {a, b} := by
  have hxB : x ∉ branchSet T := fun h => hx (branchSet_subset_vertices h)
  have ha := end_mem_vertices_left hD hBf hxB hab hK
  have hb := end_mem_vertices_right hD hBf hxB hab hK
  have hsubV : seg a b \ {a, b} ⊆ (vertices T)ᶜ := by
    rintro y ⟨hy, hy'⟩ hyV
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hy'
    have h2 := order_eq_two_of_ne_ends hD hBf hxB hab hK (hK ▸ hy) hy'.1 hy'.2
    rcases hyV with h | h
    · rw [IsTip, h2] at h; exact absurd h (by decide)
    · rw [IsBranchPoint, h2] at h; exact absurd h (by decide)
  have hxK : x ∈ seg a b \ {a, b} := by
    refine ⟨hK ▸ subset_closure (mem_bcomp hxB), ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => hx (e ▸ ha), fun e => hx (e ▸ hb)⟩
  apply Subset.antisymm
  · intro y hy
    have hyW : y ∈ bcomp x := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) (fun z hz hzB => (connectedComponentIn_subset _ _ hz :
        z ∉ vertices T) (branchSet_subset_vertices hzB)) hy
    have hyV : y ∉ vertices T := connectedComponentIn_subset _ _ hy
    refine ⟨hK ▸ subset_closure hyW, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun e => hyV (e ▸ ha), fun e => hyV (e ▸ hb)⟩
  · exact (isPreconnected_seg_diff_ends hab).subset_connectedComponentIn hxK hsubV

/-- **Edges** are the closures of the components of `T \ B`. -/
theorem isEdge_iff {ℓ : Set T} :
    IsEdge ℓ ↔ ∃ x, x ∉ branchSet T ∧ ℓ = closure (bcomp x) := by
  constructor
  · rintro ⟨W, ⟨x, hx, rfl⟩, rfl⟩
    have hxB : x ∉ branchSet T := fun h => hx (branchSet_subset_vertices h)
    obtain ⟨a, b, hab, hK⟩ := exists_ends hD hBf hxB
    refine ⟨x, hxB, ?_⟩
    rw [cc_vertices_eq hD hBf hx hab hK, closure_seg_diff_ends hab, hK]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, hab, hK⟩ := exists_ends hD hBf hx
    obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hab).exists_param
    set y := g (1 / 2)
    have hyo : y ∈ seg a b \ {a, b} := by
      rw [seg_diff_ends_eq hg hgim hg0 hg1]; exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
    have hyW : y ∈ bcomp x := by
      refine mem_bcomp_of_ne_ends hD hBf hx hab hK (hK ▸ hyo.1) ?_ ?_ <;>
      · intro e; apply hyo.2; simp [e]
    have hyB : y ∉ branchSet T := bcomp_subset x hyW
    have hK' : seg a b = closure (bcomp y) := by rw [bcomp_eq hyW]; exact hK
    have hyV : y ∉ vertices T := by
      rintro (h | h)
      · have := order_eq_two_of_ne_ends hD hBf hyB hab hK' (hK' ▸ hyo.1)
          (fun e => hyo.2 (by simp [e])) (fun e => hyo.2 (by simp [e]))
        rw [IsTip, this] at h; exact absurd h (by decide)
      · exact hyB h
    refine ⟨_, ⟨y, hyV, rfl⟩, ?_⟩
    rw [cc_vertices_eq hD hBf hyV hab hK', closure_seg_diff_ends hab, hK]

/-- Every edge is an arc whose only vertices are its two ends. -/
theorem edge_isArc {ℓ : Set T} (hℓ : IsEdge ℓ) :
    ∃ a b : T, a ≠ b ∧ seg a b = ℓ ∧ ℓ ∩ vertices T = {a, b} := by
  obtain ⟨x, hx, rfl⟩ := (isEdge_iff hD hBf).1 hℓ
  obtain ⟨a, b, hab, hK⟩ := exists_ends hD hBf hx
  refine ⟨a, b, hab, hK, Subset.antisymm ?_ ?_⟩
  · rintro y ⟨hy, hyV⟩
    by_contra h
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at h
    have h2 := order_eq_two_of_ne_ends hD hBf hx hab hK hy h.1 h.2
    rcases hyV with h' | h'
    · rw [IsTip, h2] at h'; exact absurd h' (by decide)
    · rw [IsBranchPoint, h2] at h'; exact absurd h' (by decide)
  · rintro y (rfl | rfl)
    · exact ⟨end_mem_closure_left hD hBf hx hab hK, end_mem_vertices_left hD hBf hx hab hK⟩
    · exact ⟨end_mem_closure_right hD hBf hx hab hK, end_mem_vertices_right hD hBf hx hab hK⟩

/-- Two distinct edges meet only in vertices. -/
theorem edge_inter_subset {ℓ ℓ' : Set T} (hℓ : IsEdge ℓ) (hℓ' : IsEdge ℓ') (hne : ℓ ≠ ℓ') :
    ℓ ∩ ℓ' ⊆ vertices T := by
  obtain ⟨x, hx, rfl⟩ := (isEdge_iff hD hBf).1 hℓ
  obtain ⟨x', hx', rfl⟩ := (isEdge_iff hD hBf).1 hℓ'
  rintro y ⟨hy, hy'⟩
  by_contra hyV
  have hyB : y ∉ branchSet T := fun h => hyV (branchSet_subset_vertices h)
  have h1 := mem_bcomp_of_mem_closure hx hy hyB
  have h2 := mem_bcomp_of_mem_closure hx' hy' hyB
  exact hne (by rw [← bcomp_eq h1, ← bcomp_eq h2])

/-- Two distinct edges meet in at most one point. -/
theorem edge_inter_subsingleton {ℓ ℓ' : Set T} (hℓ : IsEdge ℓ) (hℓ' : IsEdge ℓ')
    (hne : ℓ ≠ ℓ') : (ℓ ∩ ℓ').Subsingleton := by
  intro y hy z hz
  by_contra hyz
  obtain ⟨a, b, hab, rfl, hV⟩ := edge_isArc hD hBf hℓ
  obtain ⟨a', b', hab', rfl, hV'⟩ := edge_isArc hD hBf hℓ'
  have hyV := edge_inter_subset hD hBf hℓ hℓ' hne hy
  have hzV := edge_inter_subset hD hBf hℓ hℓ' hne hz
  have hy1 : y = a ∨ y = b := by
    have : y ∈ seg a b ∩ vertices T := ⟨hy.1, hyV⟩; rw [hV] at this; exact this
  have hz1 : z = a ∨ z = b := by
    have : z ∈ seg a b ∩ vertices T := ⟨hz.1, hzV⟩; rw [hV] at this; exact this
  have hy2 : y = a' ∨ y = b' := by
    have : y ∈ seg a' b' ∩ vertices T := ⟨hy.2, hyV⟩; rw [hV'] at this; exact this
  have hz2 : z = a' ∨ z = b' := by
    have : z ∈ seg a' b' ∩ vertices T := ⟨hz.2, hzV⟩; rw [hV'] at this; exact this
  apply hne
  have e1 : seg a b = seg y z := by
    rcases hy1 with rfl | rfl <;> rcases hz1 with rfl | rfl
    · exact (hyz rfl).elim
    · rfl
    · exact seg_symm hD _ _
    · exact (hyz rfl).elim
  have e2 : seg a' b' = seg y z := by
    rcases hy2 with rfl | rfl <;> rcases hz2 with rfl | rfl
    · exact (hyz rfl).elim
    · rfl
    · exact seg_symm hD _ _
    · exact (hyz rfl).elim
  rw [e1, e2]

/-- The set of edges is finite. -/
theorem edges_finite (hBo : ∀ p : T, IsBranchPoint p → order p ≠ ⊤) :
    {ℓ : Set T | IsEdge ℓ}.Finite := by
  refine ((bcomps_finite hD hBf hBo).image closure).subset ?_
  intro ℓ hℓ
  obtain ⟨x, hx, rfl⟩ := (isEdge_iff hD hBf).1 hℓ
  exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

/-- The complement of a finite set is dense in a connected nontrivial space. -/
theorem dense_compl_finite {F : Set T} (hF : F.Finite) : Dense Fᶜ := by
  rw [dense_iff_inter_open]
  intro U hU ⟨u, hu⟩
  by_contra h
  have h' : U ⊆ F := fun y hy => by by_contra hyF; exact h ⟨y, hy, hyF⟩
  have hUf : U.Finite := hF.subset h'
  have hopen : IsOpen ({u} : Set T) := by
    have : ({u} : Set T) = U ∩ (U \ {u})ᶜ := by
      ext y; simp only [mem_singleton_iff, mem_inter_iff, mem_compl_iff, mem_diff, not_and,
        not_not]
      constructor
      · rintro rfl; exact ⟨hu, fun _ => rfl⟩
      · rintro ⟨hy, h⟩; exact h hy
    rw [this]; exact hU.inter (hUf.subset diff_subset).isClosed.isOpen_compl
  have := IsClopen.eq_univ ⟨isClosed_singleton, hopen⟩ ⟨u, rfl⟩
  obtain ⟨y, hy⟩ := exists_ne u
  exact hy (this ▸ mem_univ y : y ∈ ({u} : Set T))

/-- The edges cover `T`. -/
theorem sUnion_edges (hBo : ∀ p : T, IsBranchPoint p → order p ≠ ⊤) :
    ⋃₀ {ℓ : Set T | IsEdge ℓ} = univ := by
  refine eq_univ_of_forall fun y => ?_
  have hcl : closure (branchSet T)ᶜ = univ := (dense_compl_finite hD hBf hBf).closure_eq
  have hunion : (branchSet T)ᶜ = ⋃ W ∈ bcomps T, W := by
    ext z; constructor
    · intro hz; exact mem_biUnion ⟨z, hz, rfl⟩ (mem_bcomp hz)
    · intro hz
      obtain ⟨W, ⟨x, hx, rfl⟩, hzW⟩ := mem_iUnion₂.1 hz
      exact bcomp_subset x hzW
  have hy : y ∈ closure (⋃ W ∈ bcomps T, W) := by rw [← hunion, hcl]; exact mem_univ y
  rw [(bcomps_finite hD hBf hBo).closure_biUnion] at hy
  obtain ⟨W, ⟨x, hx, rfl⟩, hyW⟩ := mem_iUnion₂.1 hy
  exact ⟨_, (isEdge_iff hD hBf).2 ⟨x, hx, rfl⟩, hyW⟩


/-- A vertex of an edge is one of its two ends; so an edge containing the vertex `u` is an arc
from `u`. -/
theorem edge_eq_seg_of_mem {ℓ : Set T} (hℓ : IsEdge ℓ) {u : T} (hu : u ∈ vertices T)
    (huℓ : u ∈ ℓ) : ∃ c, u ≠ c ∧ seg u c = ℓ := by
  obtain ⟨a, b, hab, rfl, hV⟩ := edge_isArc hD hBf hℓ
  have : u ∈ seg a b ∩ vertices T := ⟨huℓ, hu⟩
  rw [hV] at this
  rcases this with rfl | rfl
  · exact ⟨b, hab, rfl⟩
  · exact ⟨a, hab.symm, seg_symm hD _ _⟩

omit [Nontrivial T] hD hBf in
/-- An arc minus one end is connected. -/
theorem isPreconnected_seg_diff_left {u c : T} (huc : u ≠ c) : IsPreconnected (seg u c \ {u}) := by
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween huc).exists_param
  have : seg u c \ {u} = g '' Ioc 0 1 := by
    rw [← hgim]; ext y; constructor
    · rintro ⟨⟨t, ht, rfl⟩, hy⟩
      exact ⟨t, ⟨lt_of_le_of_ne ht.1 (fun e => hy (by rw [← e, hg0]; rfl)), ht.2⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, fun e => ht.1.ne'
        (hg.2 (Ioc_subset_Icc_self ht) ⟨le_rfl, zero_le_one⟩ (e.trans hg0.symm))⟩
  rw [this]; exact hg.isPreconnected_image_Ioc

omit [Nontrivial T] hD hBf in
/-- A point of the closure of a component of `T \ {u}` other than `u` lies in it. -/
theorem mem_cc_of_mem_closure {u y z : T} (hz : z ∈ closure (connectedComponentIn {u}ᶜ y))
    (hzu : z ≠ u) (hyu : y ≠ u) : z ∈ connectedComponentIn {u}ᶜ y := by
  have hpc : IsPreconnected (insert z (connectedComponentIn {u}ᶜ y)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hz subset_closure)
  exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hyu))
    (insert_subset hzu (connectedComponentIn_subset _ _)) (mem_insert z _)

/-- **Degrees.** The order of a vertex equals the number of edges containing it. -/
theorem order_eq_encard_edges (hBo : ∀ p : T, IsBranchPoint p → order p ≠ ⊤) {u : T}
    (hu : u ∈ vertices T) : order u = {ℓ : Set T | IsEdge ℓ ∧ u ∈ ℓ}.encard := by
  set E := {ℓ : Set T | IsEdge ℓ ∧ u ∈ ℓ}
  have hc : ∀ ℓ ∈ E, ∃ c, u ≠ c ∧ seg u c = ℓ := fun ℓ hℓ =>
    edge_eq_seg_of_mem hD hBf hℓ.1 hu hℓ.2
  choose! c hcu hcℓ using hc
  set Φ : Set T → Set T := fun ℓ => connectedComponentIn {u}ᶜ (c ℓ)
  -- every point of `ℓ \ {u}` lies in `Φ ℓ`
  have hΦ : ∀ ℓ ∈ E, ∀ y ∈ ℓ, y ≠ u → connectedComponentIn {u}ᶜ y = Φ ℓ := by
    intro ℓ hℓ y hy hyu
    have hpc := isPreconnected_seg_diff_left (hcu ℓ hℓ)
    have hsub : seg u (c ℓ) \ {u} ⊆ {u}ᶜ := fun z hz => hz.2
    have hcmem : c ℓ ∈ seg u (c ℓ) \ {u} := ⟨right_mem_seg hD _ _, (hcu ℓ hℓ).symm⟩
    have hymem : y ∈ seg u (c ℓ) \ {u} := ⟨(hcℓ ℓ hℓ).symm ▸ hy, hyu⟩
    exact connectedComponentIn_eq (hpc.subset_connectedComponentIn hymem hsub hcmem)
  have hinj : InjOn Φ E := by
    intro ℓ₁ h₁ ℓ₂ h₂ he
    by_contra hne
    have hint : seg u (c ℓ₁) ∩ seg u (c ℓ₂) ⊆ {u} := by
      intro z hz
      rw [hcℓ ℓ₁ h₁, hcℓ ℓ₂ h₂] at hz
      exact (edge_inter_subsingleton hD hBf h₁.1 h₂.1 hne) hz ⟨h₁.2, h₂.2⟩
    have harc := (seg_isArcBetween (hcu ℓ₁ h₁)).symm.union (seg_isArcBetween (hcu ℓ₂ h₂)) hint
    exact ends_separate hD harc (Or.inl (left_mem_seg u _)) (hcu ℓ₁ h₁) (hcu ℓ₂ h₂) he
  have himage : Φ '' E = compsAt u := by
    apply Subset.antisymm
    · rintro _ ⟨ℓ, hℓ, rfl⟩; exact ⟨c ℓ, (hcu ℓ hℓ).symm, rfl⟩
    · rintro C ⟨y, hyu, rfl⟩
      -- a neighbourhood of `u` covered by the edges at `u`
      set N := (⋃₀ {ℓ : Set T | IsEdge ℓ ∧ u ∉ ℓ})ᶜ ∩ (vertices T \ {u})ᶜ
      have hNo : IsOpen N := by
        refine IsOpen.inter ?_ ?_
        · refine (Finite.isClosed_sUnion ((edges_finite hD hBf hBo).subset
            fun ℓ hℓ => hℓ.1) fun ℓ hℓ => ?_).isOpen_compl
          obtain ⟨a, b, -, rfl, -⟩ := edge_isArc hD hBf hℓ.1
          exact (isCompact_seg a b).isClosed
        · exact ((vertices_finite hD hBf hBo).subset diff_subset).isClosed.isOpen_compl
      have huN : u ∈ N := ⟨fun ⟨ℓ, hℓ, huℓ⟩ => hℓ.2 huℓ, fun h => h.2 rfl⟩
      have hucl : u ∈ closure (connectedComponentIn {u}ᶜ y) := by
        by_contra hucl
        have hcl : closure (connectedComponentIn {u}ᶜ y) ⊆ connectedComponentIn {u}ᶜ y :=
          fun z hz => mem_cc_of_mem_closure hz (fun e => hucl (e ▸ hz)) hyu
        have := IsClopen.eq_univ ⟨closure_subset_iff_isClosed.1 hcl,
          isOpen_compl_singleton.connectedComponentIn⟩ ⟨y, mem_connectedComponentIn hyu⟩
        exact (connectedComponentIn_subset _ _ (this ▸ mem_univ u : u ∈ _) : u ∈ ({u}ᶜ : Set T))
          rfl
      obtain ⟨z, hzN, hzC⟩ := mem_closure_iff.1 hucl N hNo huN
      have hzu : z ≠ u := connectedComponentIn_subset _ _ hzC
      have hzV : z ∉ vertices T := fun h => hzN.2 ⟨h, hzu⟩
      obtain ⟨ℓ, hℓ, hzℓ⟩ : z ∈ ⋃₀ {ℓ : Set T | IsEdge ℓ} := by
        rw [sUnion_edges hD hBf hBo]; exact mem_univ z
      have huℓ : u ∈ ℓ := by
        by_contra h; exact hzN.1 ⟨ℓ, ⟨hℓ, h⟩, hzℓ⟩
      refine ⟨ℓ, ⟨hℓ, huℓ⟩, ?_⟩
      rw [← hΦ ℓ ⟨hℓ, huℓ⟩ z hzℓ hzu]
      exact (connectedComponentIn_eq hzC).symm
  rw [order_eq, ← himage, hinj.encard_image]


/-- An edge containing two distinct vertices is the arc between them. -/
theorem edge_eq_seg_of_two {ℓ : Set T} (hℓ : IsEdge ℓ) {u v : T} (hu : u ∈ vertices T)
    (hv : v ∈ vertices T) (huℓ : u ∈ ℓ) (hvℓ : v ∈ ℓ) (huv : u ≠ v) : seg u v = ℓ := by
  obtain ⟨a, b, hab, rfl, hV⟩ := edge_isArc hD hBf hℓ
  have h1 : u ∈ seg a b ∩ vertices T := ⟨huℓ, hu⟩
  have h2 : v ∈ seg a b ∩ vertices T := ⟨hvℓ, hv⟩
  rw [hV] at h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact (huv rfl).elim
  · rfl
  · exact seg_symm hD _ _
  · exact (huv rfl).elim

/-- The points of an edge other than its ends are not vertices. -/
theorem edge_diff_ends_inter_vertices {u v : T} (huv : u ≠ v) (hℓ : IsEdge (seg u v))
    (hu : u ∈ vertices T) (hv : v ∈ vertices T) : (seg u v \ {u, v}) ∩ vertices T = ∅ := by
  obtain ⟨a, b, hab, -, hV⟩ := edge_isArc hD hBf hℓ
  have hu' : u ∈ seg u v ∩ vertices T := ⟨left_mem_seg u v, hu⟩
  have hv' : v ∈ seg u v ∩ vertices T := ⟨right_mem_seg hD u v, hv⟩
  rw [hV] at hu' hv'
  have hends : ({u, v} : Set T) = {a, b} := by
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact (huv rfl).elim
    · rfl
    · exact pair_comm _ _
    · exact (huv rfl).elim
  ext y; simp only [mem_inter_iff, mem_diff, mem_empty_iff_false, iff_false, not_and]
  intro hy hyV
  have : y ∈ seg u v ∩ vertices T := ⟨hy.1, hyV⟩
  rw [hV, ← hends] at this
  exact hy.2 this

theorem treeGraph_preconnected (hBo : ∀ p : T, IsBranchPoint p → order p ≠ ⊤) :
    (treeGraph T).Preconnected := by
  intro u₀ v₀
  set R : Set T := {v | ∃ hv : v ∈ vertices T, (treeGraph T).Reachable u₀ ⟨v, hv⟩}
  have hR : ∀ ℓ, IsEdge ℓ → ∀ v ∈ R, v ∈ ℓ → ∀ w ∈ vertices T, w ∈ ℓ → w ∈ R := by
    rintro ℓ hℓ v ⟨hv, hr⟩ hvℓ w hw hwℓ
    by_cases hvw : v = w
    · subst hvw; exact ⟨hv, hr⟩
    exact ⟨hw, hr.trans (SimpleGraph.Adj.reachable ⟨hvw, ℓ, hℓ, hvℓ, hwℓ⟩)⟩
  set P := ⋃₀ {ℓ : Set T | IsEdge ℓ ∧ ∃ v ∈ R, v ∈ ℓ}
  set Q := ⋃₀ {ℓ : Set T | IsEdge ℓ ∧ ∀ v ∈ R, v ∉ ℓ}
  have hclosed : ∀ 𝒮 : Set (Set T), 𝒮 ⊆ {ℓ | IsEdge ℓ} → IsClosed (⋃₀ 𝒮) := fun 𝒮 h𝒮 =>
    Finite.isClosed_sUnion ((edges_finite hD hBf hBo).subset h𝒮) fun ℓ hℓ => by
      obtain ⟨a, b, -, rfl, -⟩ := edge_isArc hD hBf (h𝒮 hℓ)
      exact (isCompact_seg a b).isClosed
  have hPQ : Pᶜ = Q := by
    ext y; constructor
    · intro hy
      obtain ⟨ℓ, hℓ, hyℓ⟩ : y ∈ ⋃₀ {ℓ : Set T | IsEdge ℓ} := by
        rw [sUnion_edges hD hBf hBo]; exact mem_univ y
      refine ⟨ℓ, ⟨hℓ, fun v hv hvℓ => hy ⟨ℓ, ⟨hℓ, v, hv, hvℓ⟩, hyℓ⟩⟩, hyℓ⟩
    · rintro ⟨ℓ', ⟨hℓ', hnot⟩, hyℓ'⟩ ⟨ℓ, ⟨hℓ, v, hv, hvℓ⟩, hyℓ⟩
      have hne : ℓ ≠ ℓ' := fun e => hnot v hv (e ▸ hvℓ)
      have hyV := edge_inter_subset hD hBf hℓ hℓ' hne ⟨hyℓ, hyℓ'⟩
      exact hnot y (hR ℓ hℓ v hv hvℓ y hyV hyℓ) hyℓ'
  have hPo : IsOpen P := by
    rw [← isClosed_compl_iff, hPQ]; exact hclosed _ fun ℓ hℓ => hℓ.1
  have hPc : IsClosed P := hclosed _ fun ℓ hℓ => hℓ.1
  have hP : P.Nonempty := by
    obtain ⟨ℓ, hℓ, hℓu⟩ : (u₀ : T) ∈ ⋃₀ {ℓ : Set T | IsEdge ℓ} := by
      rw [sUnion_edges hD hBf hBo]; exact mem_univ _
    exact ⟨u₀, ℓ, ⟨hℓ, u₀, ⟨u₀.2, SimpleGraph.Reachable.refl _⟩, hℓu⟩, hℓu⟩
  have hPu := IsClopen.eq_univ ⟨hPc, hPo⟩ hP
  obtain ⟨ℓ, ⟨hℓ, v, hv, hvℓ⟩, hv₀ℓ⟩ : (v₀ : T) ∈ P := hPu ▸ mem_univ _
  obtain ⟨_, hr⟩ := hR ℓ hℓ v hv hvℓ v₀ v₀.2 hv₀ℓ
  exact hr

theorem treeGraph_isAcyclic : (treeGraph T).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  rintro v w ⟨hvw, ℓ, hℓ, hvℓ, hwℓ⟩
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  have hseg : seg (v : T) w = ℓ := edge_eq_seg_of_two hD hBf hℓ v.2 w.2 hvℓ hwℓ hvw
  set O := seg (v : T) w \ {(v : T), (w : T)}
  have hO : (O ∩ vertices T) = ∅ :=
    edge_diff_ends_inter_vertices hD hBf hvw (hseg ▸ hℓ) v.2 w.2
  -- along a walk avoiding the edge `vw`, there is a connected set avoiding its open part
  have key : ∀ {x y : vertices T} (q : ((treeGraph T).deleteEdges {s(v, w)}).Walk x y),
      ∃ S : Set T, IsPreconnected S ∧ (x : T) ∈ S ∧ (y : T) ∈ S ∧ S ∩ O = ∅ := by
    intro x y q
    induction q with
    | nil =>
      rename_i x
      refine ⟨{(x : T)}, isPreconnected_singleton, rfl, rfl, ?_⟩
      ext z; simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl hzO
      have : (x : T) ∈ O ∩ vertices T := ⟨hzO, x.2⟩
      rw [hO] at this; exact this
    | cons h q ih =>
      rename_i a b c
      obtain ⟨S, hS, hbS, hcS, hSO⟩ := ih
      rw [SimpleGraph.deleteEdges_adj] at h
      obtain ⟨⟨hab, ℓ', hℓ', haℓ', hbℓ'⟩, hnot⟩ := h
      have hℓ'eq : seg (a : T) b = ℓ' := edge_eq_seg_of_two hD hBf hℓ' a.2 b.2 haℓ' hbℓ' hab
      have hne : ℓ' ≠ ℓ := by
        intro e
        apply hnot
        rw [mem_singleton_iff]
        have hav : (a : T) ∈ ℓ ∩ vertices T := ⟨e ▸ haℓ', a.2⟩
        have hbv : (b : T) ∈ ℓ ∩ vertices T := ⟨e ▸ hbℓ', b.2⟩
        obtain ⟨a', b', -, hab', hV⟩ := edge_isArc hD hBf hℓ
        have hv' : (v : T) ∈ ℓ ∩ vertices T := ⟨hvℓ, v.2⟩
        have hw' : (w : T) ∈ ℓ ∩ vertices T := ⟨hwℓ, w.2⟩
        rw [hV] at hav hbv hv' hw'
        have hav' : a = v ∨ a = w := by
          rcases hav with h1 | h1 <;> rcases hv' with h2 | h2 <;> rcases hw' with h3 | h3 <;>
            first
            | (left; exact Subtype.ext (h1.trans h2.symm))
            | (right; exact Subtype.ext (h1.trans h3.symm))
            | (exfalso; exact hvw (h2.trans h3.symm))
        have hbv' : b = v ∨ b = w := by
          rcases hbv with h1 | h1 <;> rcases hv' with h2 | h2 <;> rcases hw' with h3 | h3 <;>
            first
            | (left; exact Subtype.ext (h1.trans h2.symm))
            | (right; exact Subtype.ext (h1.trans h3.symm))
            | (exfalso; exact hvw (h2.trans h3.symm))
        rcases hav' with rfl | rfl <;> rcases hbv' with rfl | rfl
        · exact (hab rfl).elim
        · rfl
        · exact Sym2.eq_swap
        · exact (hab rfl).elim
      refine ⟨ℓ' ∪ S, IsPreconnected.union (b : T) hbℓ' hbS ?_ hS, Or.inl haℓ', Or.inr hcS, ?_⟩
      · rw [← hℓ'eq]; exact (isConnected_seg _ _).isPreconnected
      · ext z; simp only [mem_inter_iff, mem_union, mem_empty_iff_false, iff_false, not_and]
        rintro (hz | hz) hzO
        · have hzV := edge_inter_subset hD hBf hℓ' hℓ hne ⟨hz, hseg ▸ hzO.1⟩
          have : z ∈ O ∩ vertices T := ⟨hzO, hzV⟩
          rw [hO] at this; exact this
        · have : z ∈ S ∩ O := ⟨hz, hzO⟩
          rw [hSO] at this; exact this
  obtain ⟨S, hS, hvS, hwS, hSO⟩ := key p
  have hsub := seg_subset hD hS hvS hwS
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hvw).exists_param
  have hmid : g (1 / 2) ∈ O := by
    show g (1 / 2) ∈ seg (v : T) w \ {(v : T), (w : T)}
    rw [seg_diff_ends_eq hg hgim hg0 hg1]; exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have : g (1 / 2) ∈ S ∩ O := ⟨hsub hmid.1, hmid⟩
  rw [hSO] at this; exact this

/-- **The number of edges is `|V| - 1`.** -/
theorem ncard_edges_add_one (hBo : ∀ p : T, IsBranchPoint p → order p ≠ ⊤) :
    {ℓ : Set T | IsEdge ℓ}.ncard + 1 = (vertices T).ncard := by
  have hVf := vertices_finite hD hBf hBo
  have : Finite (vertices T) := hVf.to_subtype
  have hne : Nonempty (vertices T) := by
    obtain ⟨y⟩ := (inferInstance : Nonempty T)
    obtain ⟨ℓ, hℓ, -⟩ : y ∈ ⋃₀ {ℓ : Set T | IsEdge ℓ} := by
      rw [sUnion_edges hD hBf hBo]; exact mem_univ y
    obtain ⟨a, b, -, -, hV⟩ := edge_isArc hD hBf hℓ
    have : a ∈ ℓ ∩ vertices T := by rw [hV]; exact Or.inl rfl
    exact ⟨⟨a, this.2⟩⟩
  have htree : (treeGraph T).IsTree :=
    ⟨⟨treeGraph_preconnected hD hBf hBo⟩, treeGraph_isAcyclic hD hBf⟩
  have hcard := (SimpleGraph.isTree_iff_connected_and_card.1 htree).2
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hcard
  rw [← hcard]
  congr 1
  -- edges of the graph correspond to edges of the tree
  have hends : ∀ ℓ ∈ {ℓ : Set T | IsEdge ℓ}, ∃ e : Sym2 (vertices T),
      ∃ a b : vertices T, e = s(a, b) ∧ (a : T) ≠ b ∧ seg (a : T) b = ℓ := by
    intro ℓ hℓ
    obtain ⟨a, b, hab, he, hV⟩ := edge_isArc hD hBf hℓ
    have ha : a ∈ ℓ ∩ vertices T := by rw [hV]; exact Or.inl rfl
    have hb : b ∈ ℓ ∩ vertices T := by rw [hV]; exact Or.inr rfl
    exact ⟨s(⟨a, ha.2⟩, ⟨b, hb.2⟩), ⟨a, ha.2⟩, ⟨b, hb.2⟩, rfl, hab, he⟩
  have : Nonempty (Sym2 (vertices T)) := ⟨s(hne.some, hne.some)⟩
  choose! ψ hψ using hends
  have hinj : InjOn ψ {ℓ : Set T | IsEdge ℓ} := by
    intro ℓ hℓ ℓ' hℓ' he
    obtain ⟨a, b, h1, hab, rfl⟩ := hψ ℓ hℓ
    obtain ⟨a', b', h2, hab', rfl⟩ := hψ _ hℓ'
    rw [h1, h2, Sym2.eq_iff] at he
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact seg_symm hD _ _
  have himg : ψ '' {ℓ : Set T | IsEdge ℓ} = (treeGraph T).edgeSet := by
    apply Subset.antisymm
    · rintro _ ⟨ℓ, hℓ, rfl⟩
      obtain ⟨a, b, h1, hab, hseg⟩ := hψ ℓ hℓ
      rw [h1, SimpleGraph.mem_edgeSet]
      exact ⟨hab, ℓ, hℓ, hseg ▸ left_mem_seg _ _, hseg ▸ right_mem_seg hD _ _⟩
    · intro e he
      induction e using Sym2.ind with
      | _ x y =>
        rw [SimpleGraph.mem_edgeSet] at he
        obtain ⟨hxy, ℓ, hℓ, hxℓ, hyℓ⟩ := he
        refine ⟨ℓ, hℓ, ?_⟩
        obtain ⟨a, b, h1, hab, hseg⟩ := hψ ℓ hℓ
        rw [h1]
        have hxy' := edge_eq_seg_of_two hD hBf hℓ x.2 y.2 hxℓ hyℓ hxy
        obtain ⟨a₀, b₀, -, -, hV⟩ := edge_isArc hD hBf hℓ
        have hx : (x : T) ∈ ℓ ∩ vertices T := ⟨hxℓ, x.2⟩
        have hy : (y : T) ∈ ℓ ∩ vertices T := ⟨hyℓ, y.2⟩
        have ha : (a : T) ∈ ℓ ∩ vertices T := ⟨hseg ▸ left_mem_seg _ _, a.2⟩
        have hb : (b : T) ∈ ℓ ∩ vertices T := ⟨hseg ▸ right_mem_seg hD _ _, b.2⟩
        rw [hV] at hx hy ha hb
        rw [Sym2.eq_iff]
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases ha with ha | ha <;>
          rcases hb with hb | hb <;>
          first
          | (exfalso; exact hxy (hx.trans hy.symm))
          | (exfalso; exact hab (ha.trans hb.symm))
          | (left; exact ⟨Subtype.ext (ha.trans hx.symm), Subtype.ext (hb.trans hy.symm)⟩)
          | (right; exact ⟨Subtype.ext (ha.trans hy.symm), Subtype.ext (hb.trans hx.symm)⟩)
  rw [← himg, hinj.ncard_image]

end Finite

end DoubleMidset
