module

public import DoubleMidset.Centers

/-!
# Distances to the tips (Section 8)

* `lemma_8_1` (no flip at a tip), via `noflip_core`;
* `prop_8_2_a`: the distance from a tip is injective (strictly monotone) on every edge;
* `prop_8_2_b`: ties seen by a tip through a branch point are seen by the branch point.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

/-- An open set of edge points on a sphere contains a spherical arc. -/
theorem exists_sphericalArc_in {O : Set T} (hO : IsOpen O) {z : T} (hz : z ∈ O)
    (hzV : z ∉ vertices T) {c : T} {r : ℝ} (hr : 0 < r) (hOs : O ⊆ sphere c r) :
    ∃ I, IsSphericalArc I c r ∧ I ⊆ O := by
  obtain ⟨γ, hγ, -, α, β, h1, h2, h3, -, hsub⟩ := exists_param_interval hT hO hz hzV
  obtain ⟨I, -, -, hI, -, hIsub, -⟩ := exists_sphericalArc_of_param hγ.arc h1 h2 h3 hr
    (fun s hs => by
      have := hOs (hsub ⟨s, hs, rfl⟩); rw [mem_sphere, dist_comm] at this; exact this)
  exact ⟨I, hI, hIsub.trans hsub⟩

/-- Two spheres containing open neighbourhoods of a common edge point have the same center. -/
theorem center_eq_of_nhds (hD2 : MidsetsAtMostTwo T) {O₁ O₂ : Set T} (h₁ : IsOpen O₁)
    (h₂ : IsOpen O₂) {z : T} (hz₁ : z ∈ O₁) (hz₂ : z ∈ O₂) (hzV : z ∉ vertices T)
    {c₁ c₂ : T} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hs₁ : O₁ ⊆ sphere c₁ r₁) (hs₂ : O₂ ⊆ sphere c₂ r₂) :
    c₂ = c₁ := by
  obtain ⟨I, hI, hIO⟩ := exists_sphericalArc_in hT (h₁.inter h₂) ⟨hz₁, hz₂⟩ hzV hr₁
    (inter_subset_left.trans hs₁)
  exact (lemma_6_2 hT hD2 hI).2.1.1 c₂ r₂ (hIO.trans (inter_subset_right.trans hs₂))

theorem IsOpenEdge.mem_of_mem_closure {W : Set T} (hW : IsOpenEdge W) {z : T}
    (hz : z ∈ closure W) (hzV : z ∉ vertices T) : z ∈ W := by
  obtain ⟨x, hx, rfl⟩ := hW
  obtain ⟨γ, s, hs, hγ, -, hWeq, hcl⟩ := exists_edgeParam hT hx
  rw [← hcl] at hz
  obtain ⟨t, ht, he⟩ := hγ.mem_Ioo hT hz hzV
  rw [← hWeq, ← he]; exact ⟨t, ht, rfl⟩

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
/-- A local extremum on an open set, read along a continuous parametrization. -/
theorem IsLocalExtrOn.param {f : T → ℝ} {W : Set T} (hW : IsOpen W) {γ : ℝ → T}
    (hγ : Continuous γ) {t : ℝ} (ht : γ t ∈ W) (hf : IsLocalExtrOn f W (γ t)) :
    IsLocalExtr (f ∘ γ) t :=
  IsExtrFilter.comp_of_tendsto hf (tendsto_nhdsWithin_iff.2
    ⟨hγ.continuousAt.tendsto, hγ.continuousAt.preimage_mem_nhds (hW.mem_nhds ht)⟩)

/-- The core of Lemma 8.1, in parametric form along the edge of `a`: an odd segment ending at a
tie produces a forbidden center. -/
theorem noflip_core (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {e : T} (he : IsTip e)
    {γ : ℝ → T} (hγ : IsEdgeParam γ) {ta t₁ : ℝ} (h0 : 0 < ta) (h01 : ta < t₁) (h1 : t₁ < 1)
    {b : T} (hb : b ∉ vertices T) {σ0 : ℝ} (htie : dist e (γ ta) = dist e b)
    (ht₁ : 0 < σ0 * sgnf (γ t₁) b e)
    (hfroz : ∀ s ∈ γ '' Icc ta t₁, (∀ u ∈ vertices T, u ≠ e → sgnf s b u ≠ 0) ∧
      (0 < σ0 * sgnf s b e → IsStrictPair s b ∧ Odd (oddCount s b)) ∧
      seg s b ⊆ γ '' Icc 0 1 ∪ closure (connectedComponentIn (vertices T)ᶜ b) ∧ s ≠ b) :
    False := by
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  have heV : e ∈ vertices T := Or.inl he
  have hI01 : ∀ t ∈ Icc ta t₁, t ∈ Ioo (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hFc : Continuous fun t => sgnf (γ t) b e :=
    continuous_sgnf_param hγ.arc.1 continuous_const continuous_const
  -- the last tie `τ₀`
  set Ties := {t | t ∈ Icc ta t₁ ∧ dist e (γ t) = dist e b}
  have hTc : IsCompact Ties := isCompact_Icc.inter_right
    (isClosed_eq (continuous_const.dist hγ.arc.1) continuous_const)
  have hτ : sSup Ties ∈ Ties := hTc.sSup_mem ⟨ta, ⟨le_rfl, h01.le⟩, htie⟩
  have hle : ∀ t ∈ Ties, t ≤ sSup Ties := fun t ht => le_csSup ⟨t₁, fun t ht => ht.1.2⟩ ht
  set τ₀ := sSup Ties
  have hF₁ : sgnf (γ t₁) b e ≠ 0 := fun h => by rw [h, mul_zero] at ht₁; exact lt_irrefl _ ht₁
  have hτt₁ : τ₀ < t₁ := lt_of_le_of_ne hτ.1.2 fun e' => hF₁ (by
    show dist e (γ t₁) - dist e b = 0; rw [← e', hτ.2, sub_self])
  -- the odd segment `L = (τ₀, t₁]`
  have hgood : ∀ t ∈ Ioc τ₀ t₁, 0 < σ0 * sgnf (γ t) b e := by
    have hnz : ∀ t ∈ Ioc τ₀ t₁, (fun t => σ0 * sgnf (γ t) b e) t ≠ 0 := by
      intro t ht h0
      have hF0 : sgnf (γ t) b e = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · rw [h, zero_mul] at ht₁; exact absurd ht₁ (lt_irrefl _)
        · exact h
      have hT' : t ∈ Ties := ⟨⟨by linarith [ht.1, hτ.1.1], ht.2⟩, by
        have : dist e (γ t) - dist e b = 0 := hF0; linarith⟩
      linarith [hle t hT', ht.1]
    intro t ht
    have := const_sign isPreconnected_Ioc (continuous_const.mul hFc).continuousOn hnz t ht t₁
      ⟨hτt₁, le_rfl⟩
    exact pos_of_mul_pos_left this ht₁.le
  have hLI : ∀ t ∈ Ioc τ₀ t₁, t ∈ Icc ta t₁ := fun t ht => ⟨by linarith [ht.1, hτ.1.1], ht.2⟩
  have hstrodd : ∀ t ∈ Ioc τ₀ t₁, IsStrictPair (γ t) b ∧ Odd (oddCount (γ t) b) := fun t ht =>
    (hfroz (γ t) ⟨t, hLI t ht, rfl⟩).2.1 (hgood t ht)
  -- one center along `L`
  obtain ⟨c, ⟨r₁, hr₁, U₁, V₁, hU₁, hV₁, hU₁m, hV₁m, ⟨W₁, hW₁, hU₁W⟩, ⟨W₂, hW₂, hV₁W⟩, hsph₁, -⟩,
      hcV, -⟩ := cor_6_7 hT hDMP (hstrodd t₁ ⟨hτt₁, le_rfl⟩).1
    (hγ.interior t₁ (hI01 t₁ ⟨h01.le, le_rfl⟩)) hb (hstrodd t₁ ⟨hτt₁, le_rfl⟩).2
  have hinv : ∀ t ∈ Ioc τ₀ t₁, dist c (γ t) = dist c b := by
    intro t ht
    obtain ⟨c', ⟨r', -, U', V', -, hV', hU'm, hV'm, -, -, hsph', -⟩, -, -⟩ :=
      cor_6_7 hT hDMP (hstrodd t ht).1 (hγ.interior t (hI01 t (hLI t ht))) hb (hstrodd t ht).2
    have hcc : c' = c := center_eq_of_nhds hT hD2 hV₁.1 hV'.1 hV₁m hV'm hb hr₁
      (subset_union_right.trans hsph₁) (subset_union_right.trans hsph')
    have e1 := hsph' (Or.inl hU'm)
    have e2 := hsph' (Or.inr hV'm)
    rw [mem_sphere, dist_comm, hcc] at e1 e2
    rw [e1, e2]
  -- passage to the boundary
  have hτ0c : dist c (γ τ₀) = dist c b := by
    have hcl : Icc τ₀ t₁ ⊆ {t | dist c (γ t) = dist c b} := by
      rw [← closure_Ioc hτt₁.ne]
      exact closure_minimal (fun t ht => hinv t ht)
        (isClosed_eq (continuous_const.dist hγ.arc.1) continuous_const)
    exact hcl ⟨le_rfl, hτt₁.le⟩
  -- the boundary midset
  obtain ⟨hfu, -, hloc, ha₀b⟩ := hfroz (γ τ₀) ⟨τ₀, hτ.1, rfl⟩
  have heM : e ∈ midset (γ τ₀) b := hτ.2
  obtain ⟨m, hm, hmim, hm0, hm1⟩ := (seg_isArcBetween ha₀b).exists_param
  obtain ⟨ρ, hρ, hρ0⟩ := exists_zero_Ioo (continuous_sgnf (γ τ₀) b) hm.1 zero_lt_one
    (by rw [hm0, hm1]; exact mul_neg_of_neg_of_pos (sgnf_left_neg ha₀b) (sgnf_right_pos ha₀b))
  have hy₀seg : m ρ ∈ seg (γ τ₀) b := hmim ▸ ⟨ρ, Ioo_subset_Icc_self hρ, rfl⟩
  have hy₀a : m ρ ≠ γ τ₀ := fun e' => by
    have := hm.2 (Ioo_subset_Icc_self hρ) ⟨le_rfl, zero_le_one⟩ (e'.trans hm0.symm)
    linarith [hρ.1]
  have hy₀b : m ρ ≠ b := fun e' => by
    have := hm.2 (Ioo_subset_Icc_self hρ) ⟨zero_le_one, le_rfl⟩ (e'.trans hm1.symm)
    linarith [hρ.2]
  have hy₀e : m ρ ≠ e := fun e' => by
    have h2o := two_le_order_of_mem_arc hT.noSCC (seg_isArcBetween ha₀b) hy₀seg hy₀a hy₀b
    have h1o : order e = 1 := he
    rw [e', h1o] at h2o; exact absurd h2o (by decide)
  have hy₀V : m ρ ∉ vertices T := fun hV => hfu _ hV hy₀e hρ0
  have hM : midset (γ τ₀) b = {e, m ρ} := by
    have hsub : ({e, m ρ} : Set T) ⊆ midset (γ τ₀) b := by
      rintro w (rfl | rfl)
      exacts [heM, sgnf_eq_zero_iff.1 hρ0]
    exact ((toFinite _).eq_of_subset_of_encard_le hsub
      (by rw [hDMP _ _ ha₀b, encard_pair (Ne.symm hy₀e)])).symm
  have hcM : c ∈ midset (γ τ₀) b := hτ0c
  rw [hM] at hcM
  have hcy : c = m ρ := by
    rcases hcM with h | h
    · exact absurd (h ▸ heV) hcV
    · exact h
  rcases hloc hy₀seg with hya | hyb
  · obtain ⟨t, ht, he'⟩ := hγ.mem_Ioo hT hya hy₀V
    have hW₁eq : W₁ = γ '' Ioo 0 1 :=
      (hW₁.eq_cc (hU₁W hU₁m)).trans (hγ.image_Ioo_eq hT (hI01 t₁ ⟨h01.le, le_rfl⟩)).symm
    obtain ⟨I, hI, hIU⟩ := exists_sphericalArc_in hT hU₁.1 hU₁m
      (hγ.interior t₁ (hI01 t₁ ⟨h01.le, le_rfl⟩)) hr₁ (subset_union_left.trans hsph₁)
    exact lemma_7_4 hT hDMP hbr hI hW₁ (hIU.trans hU₁W)
      (by rw [hW₁eq, hcy, ← he']; exact ⟨t, ht, rfl⟩)
  · have hyW : m ρ ∈ connectedComponentIn (vertices T)ᶜ b :=
      IsOpenEdge.mem_of_mem_closure hT ⟨b, hb, rfl⟩ hyb hy₀V
    have hW₂eq : W₂ = connectedComponentIn (vertices T)ᶜ b := hW₂.eq_cc (hV₁W hV₁m)
    obtain ⟨I, hI, hIV⟩ := exists_sphericalArc_in hT hV₁.1 hV₁m hb hr₁
      (subset_union_right.trans hsph₁)
    exact lemma_7_4 hT hDMP hbr hI hW₂ (hIV.trans hV₁W) (by rw [hW₂eq, hcy]; exact hyW)

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
/-- Frozen vertex signs determine strictness and the count `N`. -/
theorem count_of_frozen {e s a b : T} (he : e ∈ oddVertices T) (hfin : (vertices T).Finite)
    (hfroz : ∀ u ∈ vertices T \ {e}, 0 < sgnf s b u * sgnf a b u) (hsb : s ≠ b)
    (he0 : sgnf s b e ≠ 0) :
    IsStrictPair s b ∧ oddCount s b =
      {u | u ∈ oddVertices T ∧ u ≠ e ∧ sgnf a b u < 0}.ncard + if sgnf s b e < 0 then 1 else 0 := by
  have hset : ∀ u, u ∈ oddVertices T → u ≠ e → (sgnf s b u < 0 ↔ sgnf a b u < 0) := by
    intro u hu hue
    have := hfroz u ⟨hu.1, hue⟩
    constructor
    · intro h; by_contra h'; push_neg at h'; nlinarith
    · intro h; by_contra h'; push_neg at h'; nlinarith
  refine ⟨⟨hsb, fun u hu h0 => ?_⟩, ?_⟩
  · by_cases hue : u = e
    · rw [hue] at h0; exact he0 h0
    · have := hfroz u ⟨hu, hue⟩; rw [h0, zero_mul] at this; exact lt_irrefl _ this
  · unfold oddCount
    by_cases hlt : sgnf s b e < 0
    · rw [if_pos hlt]
      have : {u | u ∈ oddVertices T ∧ sgnf s b u < 0} =
          insert e {u | u ∈ oddVertices T ∧ u ≠ e ∧ sgnf a b u < 0} := by
        ext u; simp only [mem_setOf_eq, mem_insert_iff]
        constructor
        · rintro ⟨hu, hu'⟩
          by_cases hue : u = e
          · exact Or.inl hue
          · exact Or.inr ⟨hu, hue, (hset u hu hue).1 hu'⟩
        · rintro (rfl | ⟨hu, hue, hu'⟩)
          · exact ⟨he, hlt⟩
          · exact ⟨hu, (hset u hu hue).2 hu'⟩
      rw [this, ncard_insert_of_notMem (fun h => h.2.1 rfl)
        (hfin.subset fun u hu => hu.1.1)]
    · rw [if_neg hlt, add_zero]
      congr 1; ext u; simp only [mem_setOf_eq]
      constructor
      · rintro ⟨hu, hu'⟩
        have hue : u ≠ e := fun h => by rw [h] at hu'; exact hlt hu'
        exact ⟨hu, hue, (hset u hu hue).1 hu'⟩
      · rintro ⟨hu, hue, hu'⟩; exact ⟨hu, (hset u hu hue).2 hu'⟩

/-- **Lemma 8.1 (no flip at a tip).** Let `T` be branched, `e` a tip, and `a, b` distinct edge
points lying either in one open edge or in two open edges with a common end `v`. If
`h_e(a) = h_e(b)` and `f_{a,b}(u) ≠ 0` for every vertex `u ≠ e`, then `a` is a local extremum of
`h_e` on its open edge. -/
theorem lemma_8_1 (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {e : T} (he : IsTip e)
    {a b : T} (hab : a ≠ b) (ha : a ∉ vertices T) (hb : b ∉ vertices T)
    (hpos : (∃ W, IsOpenEdge W ∧ a ∈ W ∧ b ∈ W) ∨
      ∃ v ∈ vertices T, v ∈ closure (connectedComponentIn (vertices T)ᶜ a) ∧
        v ∈ closure (connectedComponentIn (vertices T)ᶜ b))
    (htie : dist e a = dist e b) (hsign : ∀ u ∈ vertices T, u ≠ e → sgnf a b u ≠ 0) :
    IsLocalExtrOn (dist e) (connectedComponentIn (vertices T)ᶜ a) a := by
  by_contra hne
  have hF : (vertices T \ {e}).Finite := hT.vertices_finite.diff
  have hev := sign_persist hF (fun u hu => hsign u hu.1 hu.2)
  have hcont : Continuous fun s : T => (s, b) := continuous_id.prodMk continuous_const
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 ((hcont.tendsto a).eventually hev)
  have hd : 0 < dist a b := dist_pos.2 hab
  have hm : 0 < min ε (dist a b / 2) := lt_min hε (by linarith)
  obtain ⟨γ, hγ, hWa, α₁, β₁, hα₁, hαβ₁, hβ₁, ⟨ta, hta, hγta⟩, hsub⟩ :=
    exists_param_interval hT isOpen_ball (mem_ball_self hm) ha
  have hnear : ∀ t ∈ Ioo α₁ β₁, dist (γ t) a < ε ∧ dist (γ t) a < dist a b / 2 := fun t ht => by
    have := hsub ⟨t, ht, rfl⟩; rw [mem_ball] at this
    exact ⟨this.trans_le (min_le_left _ _), this.trans_le (min_le_right _ _)⟩
  have hsb : ∀ t ∈ Ioo α₁ β₁, γ t ≠ b := fun t ht e' => by
    have := (hnear t ht).2; rw [e', dist_comm] at this; linarith
  set N₀ := {u | u ∈ oddVertices T ∧ u ≠ e ∧ sgnf a b u < 0}.ncard
  set σ0 : ℝ := if Even N₀ then -1 else 1 with hσ0
  have hodd : ∀ t ∈ Ioo α₁ β₁, 0 < σ0 * sgnf (γ t) b e →
      IsStrictPair (γ t) b ∧ Odd (oddCount (γ t) b) := by
    intro t ht hpos'
    have he0 : sgnf (γ t) b e ≠ 0 := fun h => by
      rw [h, mul_zero] at hpos'; exact lt_irrefl _ hpos'
    obtain ⟨hstr, hcount⟩ := count_of_frozen he.mem_oddVertices hT.vertices_finite
      (hεb (hnear t ht).1) (hsb t ht) he0
    refine ⟨hstr, ?_⟩
    rw [hcount]
    by_cases hev' : Even N₀
    · have : σ0 = -1 := if_pos hev'
      rw [this] at hpos'
      rw [if_pos (by linarith)]; exact hev'.add_one
    · have : σ0 = 1 := if_neg hev'
      rw [this] at hpos'
      rw [if_neg (by linarith), add_zero]; exact Nat.not_even_iff_odd.1 hev'
  have hfu : ∀ t ∈ Ioo α₁ β₁, ∀ u ∈ vertices T, u ≠ e → sgnf (γ t) b u ≠ 0 :=
    fun t ht u hu hue h0 => by
      have := hεb (hnear t ht).1 u ⟨hu, hue⟩
      simp only at this; rw [h0, zero_mul] at this; exact lt_irrefl _ this
  have hloc : ∀ t ∈ Ioo α₁ β₁, seg (γ t) b ⊆
      γ '' Icc 0 1 ∪ closure (connectedComponentIn (vertices T)ᶜ b) := by
    intro t ht
    have hγt : γ t ∈ γ '' Icc 0 1 := ⟨t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    rcases hpos with ⟨W, hW, haW, hbW⟩ | ⟨v, -, hva, hvb⟩
    · have hWeq : W = γ '' Ioo 0 1 := by rw [hW.eq_cc haW, hWa]
      have hbγ : b ∈ γ '' Ioo 0 1 := hWeq ▸ hbW
      exact (seg_subset hT.noSCC hγ.arc.isPreconnected_image hγt
        (image_mono Ioo_subset_Icc_self hbγ)).trans subset_union_left
    · have hvγ : v ∈ γ '' Icc 0 1 := by
        rw [← hWa] at hva
        exact closure_minimal (image_mono Ioo_subset_Icc_self) hγ.arc.isCompact_image.isClosed hva
      have hu : IsPreconnected (γ '' Icc 0 1 ∪ closure (connectedComponentIn (vertices T)ᶜ b)) :=
        hγ.arc.isPreconnected_image.union v hvγ hvb isPreconnected_connectedComponentIn.closure
      exact seg_subset hT.noSCC hu (Or.inl hγt)
        (Or.inr (subset_closure (mem_connectedComponentIn hb)))
  have hsgn : ∀ t, sgnf (γ t) b e = dist e (γ t) - dist e (γ ta) := fun t => by
    show dist e (γ t) - dist e b = dist e (γ t) - dist e (γ ta); rw [hγta, htie]
  -- a site with the odd sign
  obtain ⟨t₁, ht₁, ht₁pos⟩ : ∃ t₁ ∈ Ioo α₁ β₁, 0 < σ0 * (dist e (γ t₁) - dist e (γ ta)) := by
    by_contra hall
    push_neg at hall
    apply hne
    have hO : γ '' Ioo α₁ β₁ ∈ 𝓝 a :=
      (hγ.isOpen_image_Ioo hT hα₁ hβ₁).mem_nhds ⟨ta, hta, hγta⟩
    by_cases hev' : Even N₀
    · have hσ : σ0 = -1 := if_pos hev'
      have hmin : IsLocalMin (dist e) a := Filter.mem_of_superset hO (by
        rintro _ ⟨t, ht, rfl⟩
        have := hall t ht; rw [hσ] at this
        show dist e a ≤ dist e (γ t); rw [← hγta]; linarith)
      exact (hmin.on _).isExtr
    · have hσ : σ0 = 1 := if_neg hev'
      have hmax : IsLocalMax (dist e) a := Filter.mem_of_superset hO (by
        rintro _ ⟨t, ht, rfl⟩
        have := hall t ht; rw [hσ] at this
        show dist e (γ t) ≤ dist e a; rw [← hγta]; linarith)
      exact (hmax.on _).isExtr
  have hta' : ta ≠ t₁ := fun h => by
    rw [h, sub_self, mul_zero] at ht₁pos; exact lt_irrefl _ ht₁pos
  have hfroz : ∀ s ∈ γ '' Icc (min ta t₁) (max ta t₁),
      (∀ u ∈ vertices T, u ≠ e → sgnf s b u ≠ 0) ∧
      (0 < σ0 * sgnf s b e → IsStrictPair s b ∧ Odd (oddCount s b)) ∧
      seg s b ⊆ γ '' Icc 0 1 ∪ closure (connectedComponentIn (vertices T)ᶜ b) ∧ s ≠ b := by
    rintro _ ⟨t, ht, rfl⟩
    have htI : t ∈ Ioo α₁ β₁ := ⟨lt_of_lt_of_le (lt_min hta.1 ht₁.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hta.2 ht₁.2)⟩
    exact ⟨hfu t htI, hodd t htI, hloc t htI, hsb t htI⟩
  rcases lt_or_gt_of_ne hta' with hlt | hgt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hfroz
    exact noflip_core hT hDMP hbr he hγ (by linarith [hta.1]) hlt (by linarith [ht₁.2]) hb
      (by rw [hγta]; exact htie) (by rw [hsgn]; exact ht₁pos) hfroz
  · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hfroz
    refine noflip_core hT hDMP hbr he hγ.symm (ta := 1 - ta) (t₁ := 1 - t₁)
      (by linarith [hta.2]) (by linarith) (by linarith [ht₁.1]) hb
      (by simp only [sub_sub_cancel]; rw [hγta]; exact htie)
      (by simp only [sub_sub_cancel]; rw [hsgn]; exact ht₁pos) ?_
    simp only [image_symm_Icc, sub_sub_cancel, sub_zero, sub_self]
    exact hfroz

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem strictMonoOn_Icc_of_Ioo {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h : StrictMonoOn f (Ioo a b)) : StrictMonoOn f (Icc a b) := by
  intro x hx y hy hxy
  set m₁ := (2 * x + y) / 3
  set m₂ := (x + 2 * y) / 3
  have hm₁ : m₁ ∈ Ioo a b := ⟨by simp only [m₁]; linarith [hx.1], by simp only [m₁]; linarith [hy.2]⟩
  have hm₂ : m₂ ∈ Ioo a b := ⟨by simp only [m₂]; linarith [hx.1], by simp only [m₂]; linarith [hy.2]⟩
  have hm₁₂ : m₁ < m₂ := by simp only [m₁, m₂]; linarith
  have hxm : f x ≤ f m₁ := by
    have hsub : Icc x m₁ ⊆ {s | f s ≤ f m₁} := by
      rw [← closure_Ioo (show x ≠ m₁ by simp only [m₁]; intro h; linarith)]
      exact closure_minimal (fun s hs => (h ⟨by linarith [hx.1, hs.1], by linarith [hs.2, hm₁.2]⟩
        hm₁ hs.2).le) (isClosed_le hf continuous_const)
    exact hsub ⟨le_rfl, by simp only [m₁]; linarith⟩
  have hmy : f m₂ ≤ f y := by
    have hsub : Icc m₂ y ⊆ {s | f m₂ ≤ f s} := by
      rw [← closure_Ioo (show m₂ ≠ y by simp only [m₂]; intro h; linarith)]
      exact closure_minimal (fun s hs => (h hm₂ ⟨by linarith [hs.1, hm₂.1], by linarith [hy.2, hs.2]⟩
        hs.1).le) (isClosed_le continuous_const hf)
    exact hsub ⟨by simp only [m₂]; linarith, le_rfl⟩
  linarith [h hm₁ hm₂ hm₁₂]

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem strictAntiOn_Icc_of_Ioo {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (h : StrictAntiOn f (Ioo a b)) : StrictAntiOn f (Icc a b) := by
  have h' : StrictMonoOn (fun x => -f x) (Ioo a b) := fun x hx y hy hxy => by
    have := h hx hy hxy; simp only; linarith
  intro x hx y hy hxy
  have key : -f x < -f y := strictMonoOn_Icc_of_Ioo (f := fun x => -f x) hf.neg h' hx hy hxy
  linarith

/-- **Proposition 8.2 (a).** Let `e` be a tip of the branched tree `T`. Then `h_e` is injective
(equivalently, strictly monotone) on every edge. -/
theorem prop_8_2_a (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {e : T} (he : IsTip e)
    {ℓ : Set T} (hℓ : IsEdge ℓ) : InjOn (dist e) ℓ := by
  obtain ⟨γ, hγ, rfl⟩ := exists_param_of_isEdge hT hℓ
  set φ := fun t => dist e (γ t)
  have hφc : Continuous φ := continuous_const.dist hγ.arc.1
  have hinj : InjOn φ (Ioo 0 1) := by
    intro t₁ ht₁ t₂ ht₂ heq
    by_contra hne
    wlog hlt : t₁ < t₂ generalizing t₁ t₂
    · exact this ht₂ ht₁ heq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    obtain ⟨t, ht, hφt⟩ : ∃ t ∈ Ioo t₁ t₂, φ t ≠ φ t₁ := by
      by_contra hall
      push_neg at hall
      obtain ⟨I, r, hI⟩ := mem_centers_of_const hγ.arc ht₁.1.le hlt ht₂.2.le
        (fun y hy y' hy' => (hall y hy).trans (hall y' hy').symm)
      exact lemma_7_1 hT hDMP he hI
    obtain ⟨lv, hlv, hlvS⟩ := exists_mem_Ioo_notMem (lemma_2_8_i φ) (min_lt_max.2 hφt.symm)
    have hlv' : lv ∈ uIcc (φ t₁) (φ t) := by
      rw [← Icc_min_max]; exact Ioo_subset_Icc_self hlv
    have hne₁ : lv ≠ φ t₁ := fun h => by
      rw [h] at hlv; rcases le_total (φ t₁) (φ t) with h' | h'
      · rw [min_eq_left h'] at hlv; exact lt_irrefl _ hlv.1
      · rw [max_eq_left h'] at hlv; exact lt_irrefl _ hlv.2
    have hne₂ : lv ≠ φ t := fun h => by
      rw [h] at hlv; rcases le_total (φ t₁) (φ t) with h' | h'
      · rw [max_eq_right h'] at hlv; exact lt_irrefl _ hlv.2
      · rw [min_eq_right h'] at hlv; exact lt_irrefl _ hlv.1
    obtain ⟨a, ha, hφa⟩ := intermediate_value_uIcc hφc.continuousOn hlv'
    obtain ⟨b, hb, hφb⟩ := intermediate_value_uIcc (a := t) (b := t₂) hφc.continuousOn
      (show lv ∈ uIcc (φ t) (φ t₂) by rw [← heq, uIcc_comm]; exact hlv')
    rw [uIcc_of_le ht.1.le] at ha
    rw [uIcc_of_le ht.2.le] at hb
    have ha' : a ∈ Ioo t₁ t := ⟨lt_of_le_of_ne ha.1 fun h => hne₁ (by rw [← hφa, ← h]),
      lt_of_le_of_ne ha.2 fun h => hne₂ (by rw [← hφa, h])⟩
    have hb' : b ∈ Ioo t t₂ := ⟨lt_of_le_of_ne hb.1 fun h => hne₂ (by rw [← hφb, ← h]),
      lt_of_le_of_ne hb.2 fun h => hne₁ (by rw [← hφb, h, heq])⟩
    have ha01 : a ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ha'.1, ht₁.1], by linarith [ha'.2, ht.2, ht₂.2]⟩
    have hb01 : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb'.1, ht.1, ht₁.1], by linarith [hb'.2, ht₂.2]⟩
    have hγab : γ a ≠ γ b := fun h => by
      have := hγ.arc.2 (Ioo_subset_Icc_self ha01) (Ioo_subset_Icc_self hb01) h
      linarith [ha'.2, hb'.1]
    -- the midset of `(γ a, γ b)` is `{e, y}` with `y` an edge point
    have hsign : ∀ u ∈ vertices T, u ≠ e → sgnf (γ a) (γ b) u ≠ 0 := by
      intro u hu hue h0
      obtain ⟨ρ, hρ, hρ0⟩ := exists_zero_Ioo (continuous_sgnf (γ a) (γ b)) hγ.arc.1
        (show a < b by linarith [ha'.2, hb'.1])
        (mul_neg_of_neg_of_pos (sgnf_left_neg hγab) (sgnf_right_pos hγab))
      have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1, ha01.1], by linarith [hρ.2, hb01.2]⟩
      have heρ : e ≠ γ ρ := fun h => hγ.interior ρ hρ01 (h ▸ Or.inl he)
      have hM : midset (γ a) (γ b) = {e, γ ρ} := by
        have hsub : ({e, γ ρ} : Set T) ⊆ midset (γ a) (γ b) := by
          rintro w (rfl | rfl)
          · show dist w (γ a) = dist w (γ b); exact hφa.trans hφb.symm
          · exact sgnf_eq_zero_iff.1 hρ0
        exact ((toFinite _).eq_of_subset_of_encard_le hsub
          (by rw [hDMP _ _ hγab, encard_pair heρ])).symm
      have huM : u ∈ midset (γ a) (γ b) := sgnf_eq_zero_iff.1 h0
      rw [hM] at huM
      rcases huM with h | h
      · exact hue h
      · rw [mem_singleton_iff] at h; exact hγ.interior ρ hρ01 (h ▸ hu)
    have hext := lemma_8_1 hT hDMP hbr he hγab (hγ.interior a ha01) (hγ.interior b hb01)
      (Or.inl ⟨γ '' Ioo 0 1, ⟨γ a, hγ.interior a ha01, hγ.image_Ioo_eq hT ha01⟩,
        ⟨a, ha01, rfl⟩, ⟨b, hb01, rfl⟩⟩) (hφa.trans hφb.symm) hsign
    have hloc := IsLocalExtrOn.param (isOpen_openEdge hT _) hγ.arc.1
      (mem_connectedComponentIn (hγ.interior a ha01)) hext
    exact hlvS ⟨a, hloc, hφa⟩
  have hext : StrictMonoOn φ (Icc 0 1) ∨ StrictAntiOn φ (Icc 0 1) := by
    rcases hφc.continuousOn.strictMonoOn_of_injOn_Ioo zero_lt_one hinj with h | h
    · exact Or.inl (strictMonoOn_Icc_of_Ioo hφc h)
    · exact Or.inr (strictAntiOn_Icc_of_Ioo hφc h)
  rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ h
  rcases hext with hm | hm
  · exact congrArg γ (hm.injOn hs hs' h)
  · exact congrArg γ (hm.injOn hs hs' h)

/-- The arc from an interior point of an edge to an end contains no other vertex. -/
theorem vertex_on_seg_to_end {δ : ℝ → T} (hδ : IsEdgeParam δ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {v : T} (hv : v ∈ δ '' Icc 0 1) (hvV : v ∈ vertices T) {w : T} (hw : w ∈ seg (δ s) v)
    (hwV : w ∈ vertices T) : w = v := by
  have hv' : v ∈ ({δ 0, δ 1} : Set T) := by rw [← hδ.inter_vertices hT]; exact ⟨hv, hvV⟩
  rcases hv' with rfl | hv'
  · rw [hδ.arc.seg_image hT (Ioo_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩,
      uIcc_of_ge hs.1.le] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]
    · exact absurd hwV (hδ.interior u ⟨h, by linarith [hu.2, hs.2]⟩)
  · rw [mem_singleton_iff] at hv'; subst hv'
    rw [hδ.arc.seg_image hT (Ioo_subset_Icc_self hs) ⟨zero_le_one, le_rfl⟩,
      uIcc_of_le hs.2.le] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]
    · exact absurd hwV (hδ.interior u ⟨by linarith [hu.1, hs.1], h⟩)

/-- **Proposition 8.2 (b).** If `v` is a branch point and `a, b` lie in two distinct open edges
at `v` with `h_e(a) = h_e(b)` for a tip `e`, then `h_v(a) = h_v(b)`. -/
theorem prop_8_2_b (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {e : T} (he : IsTip e)
    {v : T} (hv : IsBranchPoint v) {a b : T} (ha : a ∉ vertices T) (hb : b ∉ vertices T)
    (hab : connectedComponentIn (vertices T)ᶜ a ≠ connectedComponentIn (vertices T)ᶜ b)
    (hva : v ∈ closure (connectedComponentIn (vertices T)ᶜ a))
    (hvb : v ∈ closure (connectedComponentIn (vertices T)ᶜ b))
    (htie : dist e a = dist e b) : dist v a = dist v b := by
  by_contra hne
  have hvV : v ∈ vertices T := Or.inr hv
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  obtain ⟨γ, sa, hsa, hγ, hγa, -, hcla⟩ := exists_edgeParam hT ha
  obtain ⟨κ, sb, hsb, hκ, hκb, -, hclb⟩ := exists_edgeParam hT hb
  have hva' : v ∈ γ '' Icc 0 1 := by rw [hcla]; exact hva
  have hvb' : v ∈ κ '' Icc 0 1 := by rw [hclb]; exact hvb
  obtain ⟨m, hm, hmim, hm0, hm1⟩ := (seg_isArcBetween hab').exists_param
  obtain ⟨ρ, hρ, hρ0⟩ := exists_zero_Ioo (continuous_sgnf a b) hm.1 zero_lt_one
    (by rw [hm0, hm1]; exact mul_neg_of_neg_of_pos (sgnf_left_neg hab') (sgnf_right_pos hab'))
  have hyseg : m ρ ∈ seg a b := hmim ▸ ⟨ρ, Ioo_subset_Icc_self hρ, rfl⟩
  have hya : m ρ ≠ a := fun e' => by
    have := hm.2 (Ioo_subset_Icc_self hρ) ⟨le_rfl, zero_le_one⟩ (e'.trans hm0.symm)
    linarith [hρ.1]
  have hyb : m ρ ≠ b := fun e' => by
    have := hm.2 (Ioo_subset_Icc_self hρ) ⟨zero_le_one, le_rfl⟩ (e'.trans hm1.symm)
    linarith [hρ.2]
  have hye : m ρ ≠ e := fun e' => by
    have h2o := two_le_order_of_mem_arc hT.noSCC (seg_isArcBetween hab') hyseg hya hyb
    have h1o : order e = 1 := he
    rw [e', h1o] at h2o; exact absurd h2o (by decide)
  have hyv : m ρ ≠ v := fun e' => hne (by
    have := sgnf_eq_zero_iff.1 hρ0; rw [e'] at this; exact this)
  have hsegsub : seg a b ⊆ seg a v ∪ seg b v := by
    have hu : IsPreconnected (seg a v ∪ seg b v) :=
      (isConnected_seg a v).isPreconnected.union v (right_mem_seg hT.noSCC a v)
        (right_mem_seg hT.noSCC b v) (isConnected_seg b v).isPreconnected
    exact seg_subset hT.noSCC hu (Or.inl (left_mem_seg a v)) (Or.inr (left_mem_seg b v))
  have hyV : m ρ ∉ vertices T := by
    intro hyV
    rcases hsegsub hyseg with h | h
    · rw [← hγa] at h; exact hyv (vertex_on_seg_to_end hT hγ hsa hva' hvV h hyV)
    · rw [← hκb] at h; exact hyv (vertex_on_seg_to_end hT hκ hsb hvb' hvV h hyV)
  have hM : midset a b = {e, m ρ} := by
    have hsub : ({e, m ρ} : Set T) ⊆ midset a b := by
      rintro w (rfl | rfl)
      exacts [htie, sgnf_eq_zero_iff.1 hρ0]
    exact ((toFinite _).eq_of_subset_of_encard_le hsub
      (by rw [hDMP _ _ hab', encard_pair (Ne.symm hye)])).symm
  have hsign : ∀ u ∈ vertices T, u ≠ e → sgnf a b u ≠ 0 := by
    intro u hu hue h0
    have huM : u ∈ midset a b := sgnf_eq_zero_iff.1 h0
    rw [hM] at huM
    rcases huM with h | h
    · exact hue h
    · rw [mem_singleton_iff] at h; exact hyV (h ▸ hu)
  have hext := lemma_8_1 hT hDMP hbr he hab' ha hb (Or.inr ⟨v, hvV, hva, hvb⟩) htie hsign
  -- but `h_e` is strictly monotone on the edge of `a`
  have hinj := prop_8_2_a hT hDMP hbr he (hγ.isEdge hT)
  have hφinj : InjOn (fun t => dist e (γ t)) (Icc 0 1) := fun s hs s' hs' h =>
    hγ.arc.2 hs hs' (hinj ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩ h)
  have hmono := (continuous_const.dist hγ.arc.1).continuousOn.strictMonoOn_of_injOn_Icc'
    zero_le_one hφinj
  rw [← hγa] at hext
  have hloc := IsLocalExtrOn.param (isOpen_openEdge hT _) hγ.arc.1
    (mem_connectedComponentIn (hγ.interior sa hsa)) hext
  exact not_isLocalExtr_of_strictMono hsa hmono hloc

end DoubleMidset
