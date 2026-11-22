module

public import DoubleMidset.OddBox

/-!
# Tools on edges and arcs of a finite tree (used in Sections 7–11)

* `IsArcParam.seg_image`: the arc between two points of a parametrized arc is the image of the
  parameter interval;
* `exists_zero_Ioo`, `isCrossing_of_unique_zero`, `isCrossing_of_arc`: zeros with a sign change
  along an arc through an edge point are crossings;
* `exists_Icc_of_subset_edge`: a closed connected nondegenerate subset of an edge is a parameter
  subarc;
* `isEdgeParam_of_isEdge`: every parametrization of an edge is an edge parametrization;
* `tip_nhds`: a tip has small neighbourhoods inside any arc issuing from it;
* `exists_exit`: the arc from an outside point to a subarc of an edge enters it at an end.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

theorem sub_neg_iff_of_strictMono {f : ℝ → ℝ} {S : Set ℝ}
    (hf : StrictMonoOn f S ∨ StrictAntiOn f S) {a b c d : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hd : d ∈ S) (hab : a ≠ b) (hcd : c ≠ d) (horder : a < b ↔ c < d) :
    f a - f b < 0 ↔ f c - f d < 0 := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hcd with h2 | h2
  · rcases hf with hf | hf
    · exact ⟨fun _ => by linarith [hf hc hd h2], fun _ => by linarith [hf ha hb h1]⟩
    · exact ⟨fun h => by linarith [hf ha hb h1], fun h => by linarith [hf hc hd h2]⟩
  · exact absurd (horder.1 h1) (not_lt.2 h2.le)
  · exact absurd (horder.2 h2) (not_lt.2 h1.le)
  · rcases hf with hf | hf
    · exact ⟨fun h => by linarith [hf hb ha h1], fun h => by linarith [hf hd hc h2]⟩
    · exact ⟨fun _ => by linarith [hf hd hc h2], fun _ => by linarith [hf hb ha h1]⟩

section General

variable {X : Type u} [MetricSpace X]

theorem exists_zero_Ioo {g : X → ℝ} (hg : Continuous g) {k : ℝ → X} (hk : Continuous k)
    {σ τ : ℝ} (hστ : σ < τ) (hs : g (k σ) * g (k τ) < 0) : ∃ ρ ∈ Ioo σ τ, g (k ρ) = 0 := by
  have hc : ContinuousOn (g ∘ k) (Icc σ τ) := (hg.comp hk).continuousOn
  have h0 : g (k σ) ≠ 0 := fun h => by rw [h, zero_mul] at hs; exact lt_irrefl _ hs
  rcases lt_or_gt_of_ne h0 with h1 | h1
  · have h2 : 0 < g (k τ) := by
      by_contra h; push_neg at h; nlinarith
    obtain ⟨ρ, hρ, e⟩ := intermediate_value_Ioo hστ.le hc ⟨h1, h2⟩
    exact ⟨ρ, hρ, e⟩
  · have h2 : g (k τ) < 0 := by
      by_contra h; push_neg at h; nlinarith
    obtain ⟨ρ, hρ, e⟩ := intermediate_value_Ioo' hστ.le hc ⟨h2, h1⟩
    exact ⟨ρ, hρ, e⟩

theorem IsArcParam.isArcBetween_Icc {k : ℝ → X} (hk : IsArcParam k) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) : IsArcBetween (k '' Icc a b) (k a) (k b) := by
  obtain ⟨k', hk', hk0, hk1, him⟩ := hk.exists_subarc ⟨ha, by linarith⟩ ⟨by linarith, hb⟩ hab.ne
  have := hk'.isArcBetween
  rwa [hk0, hk1, him, uIcc_of_le hab.le] at this

end General

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

theorem IsArcParam.seg_image {k : ℝ → T} (hk : IsArcParam k) {σ τ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) 1) : seg (k σ) (k τ) = k '' uIcc σ τ := by
  rcases eq_or_ne σ τ with rfl | hne
  · rw [seg_self, uIcc_self, image_singleton]
  · obtain ⟨k', hk', hk0, hk1, him⟩ := hk.exists_subarc hσ hτ hne
    rw [← him]
    have := hk'.isArcBetween
    rw [hk0, hk1] at this
    exact seg_eq hT.noSCC this

theorem IsArcParam.seg_image_Icc {k : ℝ → T} (hk : IsArcParam k) {σ τ : ℝ} (hσ : 0 ≤ σ)
    (hστ : σ ≤ τ) (hτ : τ ≤ 1) : seg (k σ) (k τ) = k '' Icc σ τ := by
  rw [hk.seg_image hT ⟨hσ, by linarith⟩ ⟨by linarith, hτ⟩, uIcc_of_le hστ]

/-- A zero with a sign change and no other zero on a parameter interval of an edge
parametrization is a crossing. -/
theorem isCrossing_of_unique_zero {γ : ℝ → T} (hγ : IsEdgeParam γ) {g : T → ℝ}
    (hg : Continuous g) (hfin : (g ⁻¹' {0}).Finite) {σ ρ τ : ℝ} (hσ : 0 ≤ σ) (hσρ : σ < ρ)
    (hρτ : ρ < τ) (hτ : τ ≤ 1) (hs : g (γ σ) * g (γ τ) < 0) (hz : g (γ ρ) = 0)
    (huniq : ∀ t ∈ Icc σ τ, g (γ t) = 0 → t = ρ) : IsCrossing g (γ ρ) := by
  have hgc : Continuous (g ∘ γ) := hg.comp hγ.arc.1
  have hleft : ∀ t ∈ Ico σ ρ, 0 < (g ∘ γ) t * (g ∘ γ) σ := fun t ht =>
    const_sign isPreconnected_Ico hgc.continuousOn
      (fun x hx e => by have := huniq x ⟨hx.1, by linarith [hx.2]⟩ e; linarith [hx.2])
      t ht σ ⟨le_rfl, hσρ⟩
  have hright : ∀ t ∈ Ioc ρ τ, 0 < (g ∘ γ) t * (g ∘ γ) τ := fun t ht =>
    const_sign isPreconnected_Ioc hgc.continuousOn
      (fun x hx e => by have := huniq x ⟨by linarith [hx.1], hx.2⟩ e; linarith [hx.1])
      t ht τ ⟨hρτ, le_rfl⟩
  have hpc : IsParamCrossing (g ∘ γ) ρ := by
    refine ⟨hz, min (ρ - σ) (τ - ρ), lt_min (by linarith) (by linarith), fun t ht t' ht' => ?_⟩
    have m1 : min (ρ - σ) (τ - ρ) ≤ ρ - σ := min_le_left _ _
    have m2 : min (ρ - σ) (τ - ρ) ≤ τ - ρ := min_le_right _ _
    exact neg_of_signs (hleft t ⟨by linarith [ht.1], ht.2⟩)
      (hright t' ⟨ht'.1, by linarith [ht'.2]⟩) hs
  exact isCrossing_of_param hT hγ hfin ⟨by linarith, by linarith⟩ hpc

/-- **Crossings along an arbitrary arc.** A zero at an edge point with a sign change and no
other zero along any arc through it is a crossing. -/
theorem isCrossing_of_arc {k : ℝ → T} (hk : IsArcParam k) {g : T → ℝ} (hg : Continuous g)
    (hfin : (g ⁻¹' {0}).Finite) {σ ρ τ : ℝ} (hσ : 0 ≤ σ) (hσρ : σ < ρ) (hρτ : ρ < τ)
    (hτ : τ ≤ 1) (hs : g (k σ) * g (k τ) < 0) (hz : g (k ρ) = 0) (hV : k ρ ∉ vertices T)
    (huniq : ∀ t ∈ Icc σ τ, g (k t) = 0 → t = ρ) : IsCrossing g (k ρ) := by
  obtain ⟨γ, s, hs₀, hγ, hγs, hW, -⟩ := exists_edgeParam hT hV
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 ((isOpen_openEdge hT _).preimage hk.1) ρ
    (mem_connectedComponentIn hV)
  set ε := min (ε₀ / 2) (min (ρ - σ) (τ - ρ))
  have hε : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have e1 : ε ≤ ε₀ / 2 := min_le_left _ _
  have e2 : ε ≤ ρ - σ := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : ε ≤ τ - ρ := (min_le_right _ _).trans (min_le_right _ _)
  have hLW : ∀ t ∈ Icc (ρ - ε) (ρ + ε), k t ∈ γ '' Ioo 0 1 := fun t ht => by
    rw [hW]; exact hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
  obtain ⟨a', ha', hka'⟩ := hLW (ρ - ε) ⟨le_rfl, by linarith⟩
  obtain ⟨b', hb', hkb'⟩ := hLW (ρ + ε) ⟨by linarith, le_rfl⟩
  have h01 : ∀ t ∈ Icc (ρ - ε) (ρ + ε), t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hseg : γ '' uIcc a' b' = k '' Icc (ρ - ε) (ρ + ε) := by
    rw [← hγ.arc.seg_image hT (Ioo_subset_Icc_self ha') (Ioo_subset_Icc_self hb'), hka', hkb',
      hk.seg_image_Icc hT (by linarith) (by linarith) (by linarith)]
  have hgc : Continuous (g ∘ k) := hg.comp hk.1
  have hl : 0 < g (k (ρ - ε)) * g (k σ) :=
    const_sign isPreconnected_Ico hgc.continuousOn
      (fun x hx e => by have := huniq x ⟨hx.1, by linarith [hx.2]⟩ e; linarith [hx.2])
      (ρ - ε) ⟨by linarith, by linarith⟩ σ ⟨le_rfl, hσρ⟩
  have hr : 0 < g (k (ρ + ε)) * g (k τ) :=
    const_sign isPreconnected_Ioc hgc.continuousOn
      (fun x hx e => by have := huniq x ⟨by linarith [hx.1], hx.2⟩ e; linarith [hx.1])
      (ρ + ε) ⟨by linarith, by linarith⟩ τ ⟨hρτ, le_rfl⟩
  have hsign : g (γ a') * g (γ b') < 0 := by rw [hka', hkb']; exact neg_of_signs hl hr hs
  have hsuniq : ∀ t ∈ uIcc a' b', g (γ t) = 0 → t = s := by
    intro t ht h0
    obtain ⟨t', ht', he⟩ : γ t ∈ k '' Icc (ρ - ε) (ρ + ε) := hseg ▸ ⟨t, ht, rfl⟩
    have := huniq t' ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ (he ▸ h0)
    subst this
    have ht01 : t ∈ Icc (0 : ℝ) 1 := by
      rcases le_total a' b' with h | h
      · rw [uIcc_of_le h] at ht; exact ⟨by linarith [ha'.1, ht.1], by linarith [hb'.2, ht.2]⟩
      · rw [uIcc_of_ge h] at ht; exact ⟨by linarith [hb'.1, ht.1], by linarith [ha'.2, ht.2]⟩
    exact hγ.arc.2 ht01 (Ioo_subset_Icc_self hs₀) (he.symm.trans hγs.symm)
  have hsmem : s ∈ uIcc a' b' := by
    obtain ⟨t, ht, he⟩ : k ρ ∈ γ '' uIcc a' b' := hseg ▸ ⟨ρ, ⟨by linarith, by linarith⟩, rfl⟩
    have := hsuniq t ht (by rw [he]; exact hz)
    exact this ▸ ht
  have hsa : s ≠ a' := fun e => by
    have := hk.2 (h01 ρ ⟨by linarith, by linarith⟩) (h01 (ρ - ε) ⟨le_rfl, by linarith⟩)
      (hγs.symm.trans ((congrArg γ e).trans hka'))
    linarith
  have hsb : s ≠ b' := fun e => by
    have := hk.2 (h01 ρ ⟨by linarith, by linarith⟩) (h01 (ρ + ε) ⟨by linarith, le_rfl⟩)
      (hγs.symm.trans ((congrArg γ e).trans hkb'))
    linarith
  rw [← hγs]
  rcases le_total a' b' with h | h
  · rw [uIcc_of_le h] at hsmem hsuniq
    exact isCrossing_of_unique_zero hT hγ hg hfin ha'.1.le (lt_of_le_of_ne hsmem.1 (Ne.symm hsa))
      (lt_of_le_of_ne hsmem.2 hsb) hb'.2.le hsign (hγs ▸ hz) hsuniq
  · rw [uIcc_of_ge h] at hsmem hsuniq
    exact isCrossing_of_unique_zero hT hγ hg hfin hb'.1.le (lt_of_le_of_ne hsmem.1 (Ne.symm hsb))
      (lt_of_le_of_ne hsmem.2 hsa) ha'.2.le (by rw [mul_comm]; exact hsign) (hγs ▸ hz) hsuniq

/-- An edge point lies in exactly one edge. -/
theorem edge_unique {ℓ ℓ' : Set T} (hℓ : IsEdge ℓ) (hℓ' : IsEdge ℓ') {z : T} (hz : z ∈ ℓ)
    (hz' : z ∈ ℓ') (hzV : z ∉ vertices T) : ℓ = ℓ' := by
  by_contra hne; exact hzV (edge_inter_subset hT.noSCC hT.bfin hℓ hℓ' hne ⟨hz, hz'⟩)

theorem edge_eq_closure_cc {ℓ : Set T} (hℓ : IsEdge ℓ) {z : T} (hz : z ∈ ℓ)
    (hzV : z ∉ vertices T) : ℓ = closure (connectedComponentIn (vertices T)ᶜ z) :=
  edge_unique hT hℓ (isEdge_closure_cc hT hzV) hz
    (subset_closure (mem_connectedComponentIn hzV)) hzV

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem IsOpenEdge.eq_cc {W : Set T} (hW : IsOpenEdge W) {z : T} (hz : z ∈ W) :
    W = connectedComponentIn (vertices T)ᶜ z := by
  obtain ⟨x, -, rfl⟩ := hW; exact connectedComponentIn_eq hz

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem IsOpenEdge.eq_of_mem {W W' : Set T} (hW : IsOpenEdge W) (hW' : IsOpenEdge W') {z : T}
    (hz : z ∈ W) (hz' : z ∈ W') : W = W' := by
  rw [hW.eq_cc hz, hW'.eq_cc hz']

/-- A closed connected subset of a parametrized arc containing two points is a parameter
subarc. -/
theorem exists_Icc_of_subset_edge {γ : ℝ → T} (hγ : IsArcParam γ) {K : Set T}
    (hK : IsClosed K) (hKc : IsPreconnected K) (hKℓ : K ⊆ γ '' Icc 0 1) {p q : T} (hp : p ∈ K)
    (hq : q ∈ K) (hpq : p ≠ q) : ∃ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 ∧ K = γ '' Icc α β := by
  set P := Icc (0 : ℝ) 1 ∩ γ ⁻¹' K
  have hPc : IsCompact P := isCompact_Icc.inter_right (hK.preimage hγ.1)
  obtain ⟨tp, htp, rfl⟩ := hKℓ hp
  obtain ⟨tq, htq, rfl⟩ := hKℓ hq
  have hPne : P.Nonempty := ⟨tp, htp, hp⟩
  have hbdd : BddBelow P := ⟨0, fun t ht => ht.1.1⟩
  have hbdd' : BddAbove P := ⟨1, fun t ht => ht.1.2⟩
  have hα : sInf P ∈ P := hPc.sInf_mem hPne
  have hβ : sSup P ∈ P := hPc.sSup_mem hPne
  have hαt : ∀ t ∈ P, sInf P ≤ t := fun t ht => csInf_le hbdd ht
  have htβ : ∀ t ∈ P, t ≤ sSup P := fun t ht => le_csSup hbdd' ht
  have hne : tp ≠ tq := fun e => hpq (congrArg γ e)
  have hαβ : sInf P < sSup P := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact lt_of_le_of_lt (hαt tp ⟨htp, hp⟩) (lt_of_lt_of_le h (htβ tq ⟨htq, hq⟩))
    · exact lt_of_le_of_lt (hαt tq ⟨htq, hq⟩) (lt_of_lt_of_le h (htβ tp ⟨htp, hp⟩))
  refine ⟨sInf P, sSup P, hα.1.1, hαβ, hβ.1.2, Subset.antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := hKℓ hz
    exact ⟨t, ⟨hαt t ⟨ht, hz⟩, htβ t ⟨ht, hz⟩⟩, rfl⟩
  · have := seg_subset hT.noSCC hKc hα.2 hβ.2
    rwa [hγ.seg_image_Icc hT hα.1.1 hαβ.le hβ.1.2] at this

/-- Every arc parametrization of an edge is an edge parametrization. -/
theorem isEdgeParam_of_isEdge {ℓ : Set T} (hℓ : IsEdge ℓ) {k : ℝ → T} (hk : IsArcParam k)
    (him : k '' Icc 0 1 = ℓ) : IsEdgeParam k := by
  obtain ⟨a, b, hab, hseg, hV⟩ := edge_isArc hT.noSCC hT.bfin hℓ
  have hint : ∀ t ∈ Ioo (0 : ℝ) 1, k t ∉ vertices T := by
    intro t ht hkV
    have hmem : k t ∈ ℓ ∩ vertices T := ⟨him ▸ ⟨t, Ioo_subset_Icc_self ht, rfl⟩, hkV⟩
    rw [hV] at hmem
    have hk01 : k 0 ≠ k t ∧ k 1 ≠ k t := ⟨fun e => by
        have := hk.2 ⟨le_rfl, zero_le_one⟩ (Ioo_subset_Icc_self ht) e; linarith [ht.1],
      fun e => by have := hk.2 ⟨zero_le_one, le_rfl⟩ (Ioo_subset_Icc_self ht) e; linarith [ht.2]⟩
    have hsep := ends_separate hT.noSCC (him ▸ hk.isArcBetween) (him ▸ ⟨t, Ioo_subset_Icc_self ht, rfl⟩)
      hk01.1.symm hk01.2.symm
    -- `ℓ` minus an end is connected
    have hconn : ∀ c : T, (c = a ∨ c = b) → IsPreconnected (ℓ \ {c}) := by
      rintro c hc
      have hcd : ∃ d, d ≠ c ∧ seg c d = ℓ := by
        rcases hc with rfl | rfl
        · exact ⟨b, hab.symm, hseg⟩
        · exact ⟨a, hab, by rw [seg_symm hT.noSCC]; exact hseg⟩
      obtain ⟨d, hdc, hcd⟩ := hcd
      obtain ⟨g, hg, hgim, hg0, -⟩ := (seg_isArcBetween hdc.symm).exists_param
      have : ℓ \ {c} = g '' Ioc 0 1 := by
        rw [← hcd, ← hgim]; ext z; constructor
        · rintro ⟨⟨u, hu, rfl⟩, hz⟩
          refine ⟨u, ⟨lt_of_le_of_ne hu.1 fun e => hz ?_, hu.2⟩, rfl⟩
          rw [← e, hg0]; rfl
        · rintro ⟨u, hu, rfl⟩
          refine ⟨⟨u, Ioc_subset_Icc_self hu, rfl⟩, fun hz => ?_⟩
          have := hg.2 (Ioc_subset_Icc_self hu) ⟨le_rfl, zero_le_one⟩ (hz.trans hg0.symm)
          linarith [hu.1]
      rw [this]; exact hg.isPreconnected_image_Ioc
    have hc : k t = a ∨ k t = b := by
      rcases hmem with h | h
      · exact Or.inl h
      · exact Or.inr h
    apply hsep
    have hsub : ℓ \ {k t} ⊆ {k t}ᶜ := diff_subset_iff.2 (fun z _ => by
      by_cases h : z = k t
      · exact Or.inl h
      · exact Or.inr h)
    have h0 : k 0 ∈ ℓ \ {k t} := ⟨him ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hk01.1⟩
    have h1 : k 1 ∈ ℓ \ {k t} := ⟨him ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, hk01.2⟩
    rw [connectedComponentIn_eq ((hconn _ hc).subset_connectedComponentIn h0 hsub h1)]
  have hends : ∀ c ∈ ({a, b} : Set T), c = k 0 ∨ c = k 1 := by
    intro c hc
    have hcℓ : c ∈ ℓ ∩ vertices T := hV ▸ hc
    obtain ⟨t, ht, rfl⟩ := him ▸ hcℓ.1
    rcases eq_or_lt_of_le ht.1 with e | e
    · left; rw [← e]
    rcases eq_or_lt_of_le ht.2 with e' | e'
    · right; rw [e']
    exact absurd hcℓ.2 (hint t ⟨e, e'⟩)
  have hab' : ({a, b} : Set T) = {k 0, k 1} := by
    have ha := hends a (mem_insert _ _)
    have hb := hends b (mem_insert_of_mem _ rfl)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact pair_comm _ _
    · exact absurd rfl hab
  have hV' : ∀ c ∈ ({k 0, k 1} : Set T), c ∈ vertices T := fun c hc => (hV ▸ (hab' ▸ hc :
    c ∈ ({a, b} : Set T)) : c ∈ ℓ ∩ vertices T).2
  exact ⟨hk, hV' _ (mem_insert _ _), hV' _ (mem_insert_of_mem _ rfl), hint⟩

/-- **A tip has small neighbourhoods inside any arc issuing from it**, which avoid the other
vertices. -/
theorem tip_nhds {x : T} (hx : IsTip x) {k : ℝ → T} (hk : IsArcParam k) (hk0 : k 0 = x)
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ δ > 0, ball x δ ⊆ k '' Ico 0 τ ∧ ∀ u ∈ vertices T, u ≠ x → δ ≤ dist x u := by
  have hτI : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ0.le, hτ1⟩
  have hkτ : k τ ≠ x := fun e => by
    have := hk.2 hτI ⟨le_rfl, zero_le_one⟩ (e.trans hk0.symm); linarith
  set F : Set T := (vertices T \ {x}) ∪ {k τ}
  have hF : F.Finite := (hT.vertices_finite.diff).union (finite_singleton _)
  have hxF : x ∉ F := by
    rintro (⟨-, h⟩ | h)
    · exact h rfl
    · exact hkτ (mem_singleton_iff.1 h).symm
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.isOpen_iff.1 hF.isClosed.isOpen_compl x hxF
  set N := connectedComponentIn (ball x δ₀) x
  have hNo : IsOpen N := isOpen_ball.connectedComponentIn
  have hxN : x ∈ N := mem_connectedComponentIn (mem_ball_self hδ₀)
  have hNF : N ⊆ Fᶜ := (connectedComponentIn_subset _ _).trans hball₀
  obtain ⟨δ, hδ, hballN⟩ := Metric.isOpen_iff.1 hNo x hxN
  refine ⟨δ, hδ, ?_, fun u hu hux => ?_⟩
  swap
  · by_contra hlt
    push_neg at hlt
    exact hNF (hballN (by rw [mem_ball, dist_comm]; exact hlt)) (Or.inl ⟨hu, hux⟩)
  intro z hz
  have hzN := hballN hz
  set A := k '' Icc 0 τ
  have hAc : IsClosed A := hk.isCompact_image.isClosed
  have hxA : x ∈ A := ⟨0, ⟨le_rfl, hτ0.le⟩, hk0⟩
  have hkτF : k τ ∈ F := Or.inr rfl
  by_cases hzA : z ∈ A
  · obtain ⟨t, ht, rfl⟩ := hzA
    refine ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 fun e => ?_⟩, rfl⟩
    rw [e] at hzN; exact hNF hzN hkτF
  exfalso
  have hzx : z ≠ x := fun e => hzA (e ▸ hxA)
  obtain ⟨m, hm, hmim, hm0, hm1⟩ := (seg_isArcBetween hzx).exists_param
  have hsegN : seg z x ⊆ N := seg_subset hT.noSCC isPreconnected_connectedComponentIn hzN hxN
  obtain ⟨s, hs, hmsA, hfirst⟩ := exists_first_entry hm.1 hAc (by rw [hm0]; exact hzA)
    (by rw [hm1]; exact hxA)
  have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
  obtain ⟨tw, htw, hktw⟩ := hmsA
  have hwN : m s ∈ N := hsegN (hmim ▸ ⟨s, hsI, rfl⟩)
  have hB : IsArcBetween (m '' Icc 0 s) z (m s) := by
    have := hm.isArcBetween_Icc le_rfl hs.1 hs.2; rwa [hm0] at this
  have hBA : m '' Icc 0 s ∩ A = {m s} := by
    ext w; constructor
    · rintro ⟨⟨t, ht, rfl⟩, hwA⟩
      rcases eq_or_lt_of_le ht.2 with e | e
      · rw [e]; rfl
      · exact absurd hwA (hfirst t ⟨ht.1, e⟩)
    · rintro rfl; exact ⟨⟨s, ⟨hs.1.le, le_rfl⟩, rfl⟩, ⟨tw, htw, hktw⟩⟩
  have htwτ : tw ≠ τ := fun e => by rw [e] at hktw; rw [hktw] at hkτF; exact hNF hwN hkτF
  rcases eq_or_lt_of_le htw.1 with e | e
  · -- the first entry is the tip itself: `x` is interior to an arc
    have hw : m s = x := by rw [← hktw, ← e, hk0]
    have hA : IsArcBetween A x (k τ) := by
      have := hk.isArcBetween_Icc le_rfl hτ0 hτ1; rwa [hk0] at this
    have hBA' : m '' Icc 0 s ∩ A = {x} := hw ▸ hBA
    have hU := IsArcBetween.union (hw ▸ hB) hA hBA'.le
    have h2 := two_le_order_of_mem_arc hT.noSCC hU (Or.inr hxA) hzx.symm hkτ.symm
    have h1 : order x = 1 := hx
    rw [h1] at h2
    exact absurd h2 (by decide)
  · -- the first entry is an interior point of `A`: a triod
    have htw' : tw < τ := lt_of_le_of_ne htw.2 htwτ
    have hA₁ : IsArcBetween (k '' Icc 0 tw) (k tw) x := by
      have := hk.isArcBetween_Icc le_rfl e (by linarith); rw [hk0] at this; exact this.symm
    have hA₂ : IsArcBetween (k '' Icc tw τ) (k tw) (k τ) :=
      hk.isArcBetween_Icc e.le htw' hτ1
    have hA₃ : IsArcBetween (m '' Icc 0 s) (k tw) z := hktw ▸ hB.symm
    have h01 : ∀ t ∈ Icc (0 : ℝ) τ, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨ht.1, ht.2.trans hτ1⟩
    have h12 : k '' Icc 0 tw ∩ k '' Icc tw τ = {k tw} := by
      ext w; constructor
      · rintro ⟨⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
        have := hk.2 (h01 t' ⟨by linarith [ht'.1], ht'.2⟩) (h01 t ⟨ht.1, by linarith [ht.2]⟩) he
        rw [mem_singleton_iff]; congr 1; linarith [ht.2, ht'.1]
      · rintro rfl; exact ⟨⟨tw, ⟨e.le, le_rfl⟩, rfl⟩, ⟨tw, ⟨le_rfl, htw'.le⟩, rfl⟩⟩
    have hsubA : ∀ a b, 0 ≤ a → b ≤ τ → k '' Icc a b ⊆ A := fun a b ha hb =>
      image_mono (Icc_subset_Icc ha hb)
    have h13 : k '' Icc 0 tw ∩ m '' Icc 0 s = {k tw} := by
      rw [inter_comm]
      refine Subset.antisymm (fun w hw => ?_) ?_
      · have : w ∈ m '' Icc 0 s ∩ A := ⟨hw.1, hsubA 0 tw le_rfl htw'.le hw.2⟩
        rw [hBA, ← hktw] at this; exact this
      · rintro _ rfl; exact ⟨hktw ▸ ⟨s, ⟨hs.1.le, le_rfl⟩, rfl⟩, ⟨tw, ⟨e.le, le_rfl⟩, rfl⟩⟩
    have h23 : k '' Icc tw τ ∩ m '' Icc 0 s = {k tw} := by
      rw [inter_comm]
      refine Subset.antisymm (fun w hw => ?_) ?_
      · have : w ∈ m '' Icc 0 s ∩ A := ⟨hw.1, hsubA tw τ e.le le_rfl hw.2⟩
        rw [hBA, ← hktw] at this; exact this
      · rintro _ rfl; exact ⟨hktw ▸ ⟨s, ⟨hs.1.le, le_rfl⟩, rfl⟩, ⟨tw, ⟨le_rfl, htw'.le⟩, rfl⟩⟩
    have h3 := three_le_order_of_triod hT.noSCC hA₁ hA₂ hA₃ h12 h13 h23
    have hwx : k tw ≠ x := fun e' => by
      have := hk.2 (h01 tw ⟨e.le, htw'.le⟩) ⟨le_rfl, zero_le_one⟩ (e'.trans hk0.symm); linarith
    exact hNF (hktw ▸ hwN) (Or.inl ⟨Or.inr h3, hwx⟩)

/-- **Exit point.** The arc from a point `x` outside a subarc `γ [α, β]` of an edge to `γ α`
first meets the subarc at one of its ends. -/
theorem exists_exit {γ : ℝ → T} (hγ : IsEdgeParam γ) {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β)
    (hβ : β ≤ 1) {x : T} (hx : x ∉ γ '' Icc α β) :
    ∃ τq, (τq = α ∨ τq = β) ∧ ∃ k : ℝ → T, IsArcParam k ∧ k 0 = x ∧ k 1 = γ τq ∧
      k '' Icc 0 1 = seg x (γ τq) ∧ ∀ t ∈ Ico (0 : ℝ) 1, k t ∉ γ '' Icc α β := by
  set K := γ '' Icc α β
  have hKc : IsClosed K := hγ.arc.isCompact_image.isClosed
  have hαK : γ α ∈ K := ⟨α, ⟨le_rfl, hαβ.le⟩, rfl⟩
  have hxα : x ≠ γ α := fun e => hx (e ▸ hαK)
  obtain ⟨m, hm, hmim, hm0, hm1⟩ := (seg_isArcBetween hxα).exists_param
  obtain ⟨s, hs, hmsK, hfirst⟩ := exists_first_entry hm.1 hKc (by rw [hm0]; exact hx)
    (by rw [hm1]; exact hαK)
  obtain ⟨tw, htw, hktw⟩ := hmsK
  have hend : tw = α ∨ tw = β := by
    by_contra hne
    push_neg at hne
    have htw' : tw ∈ Ioo α β := ⟨lt_of_le_of_ne htw.1 (Ne.symm hne.1),
      lt_of_le_of_ne htw.2 hne.2⟩
    have hO : IsOpen (γ '' Ioo α β) := hγ.isOpen_image_Ioo hT hα hβ
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (hO.preimage hm.1) s
      (show m s ∈ γ '' Ioo α β from hktw ▸ ⟨tw, htw', rfl⟩)
    set t := s - min (η / 2) (s / 2)
    have h1 : min (η / 2) (s / 2) ≤ η / 2 := min_le_left _ _
    have h2 : min (η / 2) (s / 2) ≤ s / 2 := min_le_right _ _
    have h3 : 0 < min (η / 2) (s / 2) := lt_min (by linarith) (by linarith [hs.1])
    have hmt : m t ∈ γ '' Ioo α β := hball (by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    exact hfirst t ⟨by linarith, by linarith⟩ (image_mono Ioo_subset_Icc_self hmt)
  have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
  refine ⟨tw, hend, fun u => m (0 + u * (s - 0)), hm.sub le_rfl hs.1 hs.2, by simp [hm0],
    by simp [hktw], ?_, fun t ht => ?_⟩
  · rw [IsArcParam.sub_image m hs.1.le, hktw, ← hm0, hm.seg_image_Icc hT le_rfl hs.1.le hs.2]
  · simp only [zero_add, sub_zero]
    exact hfirst (t * s) ⟨mul_nonneg ht.1 hs.1.le, by nlinarith [ht.2, hs.1]⟩

end DoubleMidset
