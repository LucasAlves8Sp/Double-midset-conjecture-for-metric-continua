module

public import DoubleMidset.Tips

/-!
# Counting tips (Section 9)

* `lemma_9_2`: at a branch point no pair of edges is used by two distinct tips;
* `prop_9_3`: a branched finite tree with the DMP is a simple triod.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

/-- An edge through a vertex `v` has an edge parametrization starting at `v`. -/
theorem edge_param_from {ℓ : Set T} (hℓ : IsEdge ℓ) {v : T} (hv : v ∈ ℓ)
    (hvV : v ∈ vertices T) : ∃ κ : ℝ → T, IsEdgeParam κ ∧ κ '' Icc 0 1 = ℓ ∧ κ 0 = v := by
  obtain ⟨γ, hγ, rfl⟩ := exists_param_of_isEdge hT hℓ
  have hv' : v ∈ ({γ 0, γ 1} : Set T) := by rw [← hγ.inter_vertices hT]; exact ⟨hv, hvV⟩
  rcases hv' with rfl | hv'
  · exact ⟨γ, hγ, rfl, rfl⟩
  · rw [mem_singleton_iff] at hv'; subst hv'
    refine ⟨_, hγ.symm, ?_, by simp⟩
    rw [image_symm_Icc]; simp

/-- Along an edge, the distance from a tip is strictly monotone. -/
theorem tip_strictMono (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {e : T}
    (he : IsTip e) {κ : ℝ → T} (hκ : IsEdgeParam κ) :
    StrictMonoOn (fun t => dist e (κ t)) (Icc 0 1) ∨
      StrictAntiOn (fun t => dist e (κ t)) (Icc 0 1) := by
  have hinj := prop_8_2_a hT hDMP hbr he (hκ.isEdge hT)
  refine (continuous_const.dist hκ.arc.1).continuousOn.strictMonoOn_of_injOn_Icc' zero_le_one
    fun s hs s' hs' h => hκ.arc.2 hs hs' (hinj ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩ h)

/-- **Lemma 9.2 (distinct tips use disjoint pairs).** Let `T` be branched. At a branch point `v`,
no pair of edges is used by two distinct tips. -/
theorem lemma_9_2 (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {v : T}
    (hv : IsBranchPoint v) {ℓ ℓ' : Set T} (hℓ : IsEdge ℓ) (hℓ' : IsEdge ℓ') (hvℓ : v ∈ ℓ)
    (hvℓ' : v ∈ ℓ') (hne : ℓ ≠ ℓ') {e e' : T} (he : IsTip e) (he' : IsTip e') (hee' : e ≠ e') :
    ¬ (UsesPair e v ℓ ℓ' ∧ UsesPair e' v ℓ ℓ') := by
  rintro ⟨hu, hu'⟩
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  have hvV : v ∈ vertices T := Or.inr hv
  obtain ⟨κ, hκ, hκℓ, hκ0⟩ := edge_param_from hT hℓ hvℓ hvV
  obtain ⟨κ', hκ', hκℓ', hκ'0⟩ := edge_param_from hT hℓ' hvℓ' hvV
  set φ := fun t => dist v (κ t)
  set ψ := fun t => dist v (κ' t)
  have hφc : Continuous φ := continuous_const.dist hκ.arc.1
  have hψc : Continuous ψ := continuous_const.dist hκ'.arc.1
  have hφm : MonotoneOn φ (Icc 0 1) := lemma_4_3 hT.noSCC hD2 hv hκ.arc hκ0
  have hψm : MonotoneOn ψ (Icc 0 1) := lemma_4_3 hT.noSCC hD2 hv hκ'.arc hκ'0
  have hφ0 : φ 0 = 0 := by simp only [φ, hκ0, dist_self]
  have hψ0 : ψ 0 = 0 := by simp only [ψ, hκ'0, dist_self]
  have hφ1 : 0 < φ 1 := dist_pos.2 (by rw [← hκ0]; exact hκ.arc.ne)
  have hψ1 : 0 < ψ 1 := dist_pos.2 (by rw [← hκ'0]; exact hκ'.arc.ne)
  -- countably many flat levels
  set C := φ '' {s | IsLocalExtr φ s} ∪ ψ '' {s | IsLocalExtr ψ s}
  have hC : C.Countable := (lemma_2_8_i φ).union (lemma_2_8_i ψ)
  have huniq : ∀ f : ℝ → ℝ, MonotoneOn f (Icc 0 1) → (f '' {s | IsLocalExtr f s} ⊆ C) →
      ∀ ρ ∉ C, ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, f t = ρ → f t' = ρ → t = t' := by
    intro f hfm hfC ρ hρ t ht t' ht' h1 h2
    by_contra hne'
    wlog hlt : t < t' generalizing t t'
    · exact this t' ht' t ht h2 h1 (Ne.symm hne') (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne'))
    have hflat : ∀ y ∈ Icc t t', f y = ρ := fun y hy => by
      have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨ht.1.trans hy.1, hy.2.trans ht'.2⟩
      exact le_antisymm (h2 ▸ hfm hyI ht' hy.2) (h1 ▸ hfm ht hyI hy.1)
    apply hρ
    refine hfC ⟨(t + t') / 2, ?_, hflat _ ⟨by linarith, by linarith⟩⟩
    left
    filter_upwards [Ioo_mem_nhds (show t < (t + t') / 2 by linarith)
      (show (t + t') / 2 < t' by linarith)] with y hy
    rw [hflat _ ⟨by linarith, by linarith⟩, hflat y ⟨hy.1.le, hy.2.le⟩]
  have huniqφ := huniq φ hφm subset_union_left
  have huniqψ := huniq ψ hψm subset_union_right
  -- radial levels `ρ n → 0` avoiding `C`
  have hR : 0 < min (φ 1) (ψ 1) := lt_min hφ1 hψ1
  have hρn : ∀ n : ℕ, ∃ ρ ∈ Ioo 0 (min (min (φ 1) (ψ 1)) (1 / ((n : ℝ) + 1))), ρ ∉ C :=
    fun n => exists_mem_Ioo_notMem hC (lt_min hR (by positivity))
  choose ρ hρ hρC using hρn
  have hρ1 : ∀ n, ρ n < φ 1 := fun n =>
    (hρ n).2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hρ2 : ∀ n, ρ n < ψ 1 := fun n =>
    (hρ n).2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlev : ∀ n, ∃ t ∈ Ioo (0 : ℝ) 1, φ t = ρ n := fun n => by
    obtain ⟨t, ht, h⟩ := intermediate_value_Ioo zero_le_one hφc.continuousOn
      (show ρ n ∈ Ioo (φ 0) (φ 1) by rw [hφ0]; exact ⟨(hρ n).1, hρ1 n⟩)
    exact ⟨t, ht, h⟩
  have hlev' : ∀ n, ∃ s ∈ Ioo (0 : ℝ) 1, ψ s = ρ n := fun n => by
    obtain ⟨s, hs, h⟩ := intermediate_value_Ioo zero_le_one hψc.continuousOn
      (show ρ n ∈ Ioo (ψ 0) (ψ 1) by rw [hψ0]; exact ⟨(hρ n).1, hρ2 n⟩)
    exact ⟨s, hs, h⟩
  choose t ht hφt using hlev
  choose s hs hψs using hlev'
  have htend : Tendsto (fun n => κ (t n)) atTop (𝓝 v) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [dist_comm]; exact (hφt n).le.trans ((hρ n).2.le.trans (min_le_right _ _))
  -- points of the open edges
  have hκV : ∀ t ∈ Ioo (0 : ℝ) 1, κ t ∉ vertices T := fun t ht => hκ.interior t ht
  have hκ'V : ∀ t ∈ Ioo (0 : ℝ) 1, κ' t ∉ vertices T := fun t ht => hκ'.interior t ht
  have hκℓmem : ∀ t ∈ Icc (0 : ℝ) 1, κ t ∈ ℓ := fun t ht => hκℓ ▸ ⟨t, ht, rfl⟩
  have hκ'ℓmem : ∀ t ∈ Icc (0 : ℝ) 1, κ' t ∈ ℓ' := fun t ht => hκℓ' ▸ ⟨t, ht, rfl⟩
  have hclℓ : ∀ t ∈ Ioo (0 : ℝ) 1, ℓ = closure (connectedComponentIn (vertices T)ᶜ (κ t)) :=
    fun t ht => edge_eq_closure_cc hT hℓ (hκℓmem t (Ioo_subset_Icc_self ht)) (hκV t ht)
  have hclℓ' : ∀ t ∈ Ioo (0 : ℝ) 1, ℓ' = closure (connectedComponentIn (vertices T)ᶜ (κ' t)) :=
    fun t ht => edge_eq_closure_cc hT hℓ' (hκ'ℓmem t (Ioo_subset_Icc_self ht)) (hκ'V t ht)
  -- the `e`-matching preserves the radial level
  have hmatch : ∀ e : T, IsTip e → UsesPair e v ℓ ℓ' →
      ∀ᶠ n in atTop, dist e (κ (t n)) = dist e (κ' (s n)) := by
    intro e he hue
    have hm1 := tip_strictMono hT hDMP hbr he hκ
    have hm2 := tip_strictMono hT hDMP hbr he hκ'
    have hne1 : dist e (κ' 1) ≠ dist e v := fun h => by
      rw [← hκ'0] at h
      have := hm2.elim (fun h' => h'.injOn) (fun h' => h'.injOn) ⟨zero_le_one, le_rfl⟩
        ⟨le_rfl, zero_le_one⟩ h
      norm_num at this
    have hD : 0 < |dist e (κ' 1) - dist e v| := abs_pos.2 (sub_ne_zero.2 hne1)
    have hlim : Tendsto (fun n => dist e (κ (t n))) atTop (𝓝 (dist e v)) :=
      tendsto_const_nhds.dist htend
    have hev := (Metric.tendsto_nhds.1 hlim) _ hD
    filter_upwards [hev] with n hn
    rw [Real.dist_eq] at hn
    have htn : t n ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self (ht n)
    have hne2 : dist e (κ (t n)) ≠ dist e v := fun h => by
      rw [← hκ0] at h
      have := hm1.elim (fun h' => h'.injOn) (fun h' => h'.injOn) htn ⟨le_rfl, zero_le_one⟩ h
      linarith [(ht n).1]
    have hav : κ (t n) ≠ v := fun h => hne2 (by rw [h])
    have hu'v : κ' 1 ≠ v := fun h => hne1 (by rw [h])
    have hside := hue _ (hκℓmem _ htn) _ (hκ'ℓmem 1 ⟨zero_le_one, le_rfl⟩) hav hu'v
    -- the value lies strictly between `h_e(v)` and `h_e(u')`
    have hval : dist e (κ (t n)) ∈ Ioo (min (dist e (κ' 0)) (dist e (κ' 1)))
        (max (dist e (κ' 0)) (dist e (κ' 1))) := by
      rw [hκ'0]
      rcases lt_or_gt_of_ne hne1 with h | h
      · have h1 : dist e (κ (t n)) < dist e v := by
          by_contra hc; push_neg at hc
          exact (not_lt.2 h.le) (hside.1 (lt_of_le_of_ne hc (Ne.symm hne2)))
        have habs : |dist e (κ' 1) - dist e v| = dist e v - dist e (κ' 1) := by
          rw [abs_sub_comm]; exact abs_of_pos (by linarith)
        rw [habs, abs_lt] at hn
        rw [min_eq_right h.le, max_eq_left h.le]
        exact ⟨by linarith [hn.1], h1⟩
      · have h1 : dist e v < dist e (κ (t n)) := hside.2 h
        have habs : |dist e (κ' 1) - dist e v| = dist e (κ' 1) - dist e v := abs_of_pos (by linarith)
        rw [habs, abs_lt] at hn
        rw [min_eq_left h.le, max_eq_right h.le]
        exact ⟨h1, by linarith [hn.2]⟩
    obtain ⟨σ, hσ, hχσ⟩ : ∃ σ ∈ Ioo (0 : ℝ) 1, dist e (κ' σ) = dist e (κ (t n)) := by
      have hχ : ContinuousOn (fun s => dist e (κ' s)) (uIcc 0 1) :=
        (continuous_const.dist hκ'.arc.1).continuousOn
      obtain ⟨σ, hσ, h⟩ := intermediate_value_uIcc hχ
        (show dist e (κ (t n)) ∈ uIcc (dist e (κ' 0)) (dist e (κ' 1)) by
          rw [← Icc_min_max]; exact Ioo_subset_Icc_self hval)
      rw [uIcc_of_le zero_le_one] at hσ
      have h'' : dist e (κ' σ) = dist e (κ (t n)) := h
      refine ⟨σ, ⟨lt_of_le_of_ne hσ.1 fun h0 => ?_, lt_of_le_of_ne hσ.2 fun h1 => ?_⟩, h⟩
      · rw [← h0] at h''; rw [← h''] at hval
        rcases le_total (dist e (κ' 0)) (dist e (κ' 1)) with h' | h'
        · rw [min_eq_left h'] at hval; exact lt_irrefl _ hval.1
        · rw [max_eq_left h'] at hval; exact lt_irrefl _ hval.2
      · rw [h1] at h''; rw [← h''] at hval
        rcases le_total (dist e (κ' 0)) (dist e (κ' 1)) with h' | h'
        · rw [max_eq_right h'] at hval; exact lt_irrefl _ hval.2
        · rw [min_eq_right h'] at hval; exact lt_irrefl _ hval.1
    -- Proposition 8.2 (b)
    have hcc : connectedComponentIn (vertices T)ᶜ (κ (t n)) ≠
        connectedComponentIn (vertices T)ᶜ (κ' σ) := fun h =>
      hne ((hclℓ _ (ht n)).trans (h ▸ (hclℓ' σ hσ).symm))
    have hvv := prop_8_2_b hT hDMP hbr he hv (hκV _ (ht n)) (hκ'V σ hσ) hcc
      (by rw [← hclℓ _ (ht n)]; exact hvℓ) (by rw [← hclℓ' σ hσ]; exact hvℓ') hχσ.symm
    have hσs : σ = s n := huniqψ (ρ n) (hρC n) σ (Ioo_subset_Icc_self hσ) (s n)
      (Ioo_subset_Icc_self (hs n)) (by show dist v (κ' σ) = ρ n; rw [← hvv]; exact hφt n)
      (hψs n)
    rw [← hσs, hχσ]
  obtain ⟨n, hn1, hn2⟩ := ((hmatch e he hu).and (hmatch e' he' hu')).exists
  have hab : κ (t n) ≠ κ' (s n) := fun h => by
    have := edge_inter_subset hT.noSCC hT.bfin hℓ hℓ' hne
      ⟨hκℓmem _ (Ioo_subset_Icc_self (ht n)), h ▸ hκ'ℓmem _ (Ioo_subset_Icc_self (hs n))⟩
    exact hκV _ (ht n) this
  have hvM : v ∈ midset (κ (t n)) (κ' (s n)) := by
    show dist v (κ (t n)) = dist v (κ' (s n)); exact (hφt n).trans (hψs n).symm
  have hve : v ≠ e := fun h => by
    have h3 : 3 ≤ order v := hv
    have h1 : order e = 1 := he
    rw [h, h1] at h3; exact absurd h3 (by decide)
  have hve' : v ≠ e' := fun h => by
    have h3 : 3 ≤ order v := hv
    have h1 : order e' = 1 := he'
    rw [h, h1] at h3; exact absurd h3 (by decide)
  exact false_of_three hab hD2 (three_le_encard_midset hvM hn1 hn2 hve hve' hee')

omit hT in
theorem choose_bound {m k : ℕ} (hm3 : 3 ≤ m) (hm4 : m ≤ 4) (hk : k ≤ m) :
    m - 2 ≤ k.choose 2 + (m - k).choose 2 := by
  interval_cases m <;> interval_cases k <;> decide

/-- A tip has a direction on every edge at `v`. -/
theorem tip_direction (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {e : T} (he : IsTip e)
    {v : T} (hvV : v ∈ vertices T) {ℓ : Set T} (hℓ : IsEdge ℓ) (hvℓ : v ∈ ℓ) :
    (∀ a ∈ ℓ, a ≠ v → dist e v < dist e a) ∨ (∀ a ∈ ℓ, a ≠ v → dist e a < dist e v) := by
  obtain ⟨κ, hκ, rfl, hκ0⟩ := edge_param_from hT hℓ hvℓ hvV
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, κ t ≠ v → 0 < t := fun t ht h =>
    lt_of_le_of_ne ht.1 fun h0 => h (by rw [← h0, hκ0])
  rcases tip_strictMono hT hDMP hbr he hκ with hm | hm
  · left; rintro _ ⟨t, ht, rfl⟩ h
    have : dist e (κ 0) < dist e (κ t) := hm ⟨le_rfl, zero_le_one⟩ ht (hpos t ht h)
    rw [hκ0] at this; exact this
  · right; rintro _ ⟨t, ht, rfl⟩ h
    have : dist e (κ t) < dist e (κ 0) := hm ⟨le_rfl, zero_le_one⟩ ht (hpos t ht h)
    rw [hκ0] at this; exact this

/-- An edge through a vertex `v` is the arc from `v` to its other end. -/
theorem edge_from_vertex {ℓ : Set T} (hℓ : IsEdge ℓ) {v : T} (hv : v ∈ ℓ) (hvV : v ∈ vertices T) :
    ∃ c, c ∈ vertices T ∧ v ≠ c ∧ seg v c = ℓ ∧ ℓ ∩ vertices T = {v, c} := by
  obtain ⟨a, b, hab, hseg, hV⟩ := edge_isArc hT.noSCC hT.bfin hℓ
  have : v ∈ ℓ ∩ vertices T := ⟨hv, hvV⟩
  rw [hV] at this
  rcases this with rfl | h
  · refine ⟨b, ?_, hab, hseg, hV⟩
    have : b ∈ ℓ ∩ vertices T := by rw [hV]; exact Or.inr rfl
    exact this.2
  · rw [mem_singleton_iff] at h; subst h
    refine ⟨a, ?_, hab.symm, by rw [seg_symm hT.noSCC]; exact hseg, by rw [hV, pair_comm]⟩
    have : a ∈ ℓ ∩ vertices T := by rw [hV]; exact Or.inl rfl
    exact this.2

/-- The structure behind **Proposition 9.3**: a branched finite tree with the DMP has exactly one
branch point `v`, of degree three, and exactly three edges, all at `v`. -/
theorem triod_structure (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) :
    ∃ v : T, IsBranchPoint v ∧ branchSet T = {v} ∧ degree v = 3 ∧
      ∃ ℓ₁ ℓ₂ ℓ₃ : Set T, ℓ₁ ≠ ℓ₂ ∧ ℓ₁ ≠ ℓ₃ ∧ ℓ₂ ≠ ℓ₃ ∧
        {ℓ : Set T | IsEdge ℓ} = {ℓ₁, ℓ₂, ℓ₃} ∧ ∀ ℓ ∈ ({ℓ₁, ℓ₂, ℓ₃} : Set (Set T)),
          IsEdge ℓ ∧ v ∈ ℓ := by
  classical
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  have htf : {p : T | IsTip p}.Finite := hT.vertices_finite.subset fun p hp => Or.inl hp
  -- at most three tips, seen from any branch point
  have htips : ∀ v : T, IsBranchPoint v → {p : T | IsTip p}.ncard ≤ 3 ∧ 3 ≤ degree v ∧ degree v ≤ 4 := by
    intro v hv
    have hvV : v ∈ vertices T := Or.inr hv
    have hm := order_eq_degree hT hvV
    have hm3 : 3 ≤ degree v := by
      have : (3 : ℕ∞) ≤ (degree v : ℕ∞) := hm ▸ hv; exact_mod_cast this
    have hm4 : degree v ≤ 4 := by
      have : (degree v : ℕ∞) ≤ (4 : ℕ) := hm ▸ lemma_4_4 hT.noSCC hD2 v; exact_mod_cast this
    refine ⟨?_, hm3, hm4⟩
    set Ev := hT.edges_finite.toFinset.filter (v ∈ ·)
    have hEv : Ev.card = degree v := (degree_eq_card hT hvV).symm
    have hEvmem : ∀ ℓ ∈ Ev, IsEdge ℓ ∧ v ∈ ℓ := fun ℓ hℓ => by
      rw [Finset.mem_filter, Finite.mem_toFinset] at hℓ; exact hℓ
    set P := Ev.powersetCard 2
    set tipsF := htf.toFinset
    set used : T → Finset (Finset (Set T)) := fun e =>
      P.filter fun p => ∀ ℓ ∈ p, ∀ ℓ' ∈ p, ℓ ≠ ℓ' → UsesPair e v ℓ ℓ'
    -- distinct tips use disjoint pairs
    have hdisj : (tipsF : Set T).PairwiseDisjoint used := by
      intro e he e' he' hee'
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp hp'
      rw [Finset.mem_filter] at hp hp'
      obtain ⟨ℓ, ℓ', hℓℓ', rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 hp.1).2
      have hsub := (Finset.mem_powersetCard.1 hp.1).1
      have h1 := hEvmem ℓ (hsub (Finset.mem_insert_self _ _))
      have h2 := hEvmem ℓ' (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      have he1 : IsTip e := (Finite.mem_toFinset htf).1 he
      have he2 : IsTip e' := (Finite.mem_toFinset htf).1 he'
      exact lemma_9_2 hT hDMP hbr hv h1.1 h2.1 h1.2 h2.2 hℓℓ' he1 he2 hee'
        ⟨hp.2 ℓ (Finset.mem_insert_self _ _) ℓ' (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _)) hℓℓ',
         hp'.2 ℓ (Finset.mem_insert_self _ _) ℓ' (Finset.mem_insert_of_mem
          (Finset.mem_singleton_self _)) hℓℓ'⟩
    -- each tip uses at least `m - 2` pairs
    have hlb : ∀ e ∈ tipsF, degree v - 2 ≤ (used e).card := by
      intro e he
      have he1 : IsTip e := (Finite.mem_toFinset htf).1 he
      set inc : Set T → Prop := fun ℓ => ∀ a ∈ ℓ, a ≠ v → dist e v < dist e a
      set I := Ev.filter inc
      set D := Ev.filter fun ℓ => ¬ inc ℓ
      have hID : I.card + D.card = degree v := by
        rw [← hEv]; exact Finset.card_filter_add_card_filter_not _
      have hdec : ∀ ℓ ∈ D, ∀ a ∈ ℓ, a ≠ v → dist e a < dist e v := by
        intro ℓ hℓ
        rw [Finset.mem_filter] at hℓ
        have := hEvmem ℓ hℓ.1
        exact (tip_direction hT hDMP hbr he1 hvV this.1 this.2).resolve_left hℓ.2
      have hsubI : I.powersetCard 2 ⊆ used e := by
        intro p hp
        rw [Finset.mem_powersetCard] at hp
        refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2
          ⟨hp.1.trans (Finset.filter_subset _ _), hp.2⟩, fun ℓ hℓ ℓ' hℓ' _ => ?_⟩
        have h1 := (Finset.mem_filter.1 (hp.1 hℓ)).2
        have h2 := (Finset.mem_filter.1 (hp.1 hℓ')).2
        intro a ha a' ha' hav ha'v
        exact ⟨fun _ => h2 a' ha' ha'v, fun _ => h1 a ha hav⟩
      have hsubD : D.powersetCard 2 ⊆ used e := by
        intro p hp
        rw [Finset.mem_powersetCard] at hp
        refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2
          ⟨hp.1.trans (Finset.filter_subset _ _), hp.2⟩, fun ℓ hℓ ℓ' hℓ' _ => ?_⟩
        intro a ha a' ha' hav ha'v
        have h1 := hdec ℓ (hp.1 hℓ) a ha hav
        have h2 := hdec ℓ' (hp.1 hℓ') a' ha' ha'v
        exact ⟨fun h => absurd h (not_lt.2 h1.le), fun h => absurd h (not_lt.2 h2.le)⟩
      have hdisjID : Disjoint (I.powersetCard 2) (D.powersetCard 2) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        rw [Finset.mem_powersetCard] at hp hp'
        obtain ⟨ℓ, ℓ', -, rfl⟩ := Finset.card_eq_two.1 hp.2
        have h1 := (Finset.mem_filter.1 (hp.1 (Finset.mem_insert_self _ _))).2
        have h2 := (Finset.mem_filter.1 (hp'.1 (Finset.mem_insert_self _ _))).2
        exact h2 h1
      have hcard := Finset.card_le_card (Finset.union_subset hsubI hsubD)
      rw [Finset.card_union_of_disjoint hdisjID, Finset.card_powersetCard,
        Finset.card_powersetCard] at hcard
      have hD' : D.card = degree v - I.card := by omega
      rw [hD'] at hcard
      exact (choose_bound hm3 hm4 (by omega)).trans hcard
    have hsum : ∑ e ∈ tipsF, (used e).card ≤ P.card := by
      rw [← Finset.card_biUnion hdisj]
      exact Finset.card_le_card (Finset.biUnion_subset.2 fun e _ => Finset.filter_subset _ _)
    have hnsmul := Finset.card_nsmul_le_sum tipsF (fun e => (used e).card) (degree v - 2) hlb
    rw [Finset.card_powersetCard, hEv, smul_eq_mul] at *
    rw [ncard_eq_toFinset_card _ htf]
    show tipsF.card ≤ 3
    have := hnsmul.trans hsum
    rcases (show degree v = 3 ∨ degree v = 4 by omega) with h | h
    · rw [h, show Nat.choose 3 2 = 3 by decide] at this; omega
    · rw [h, show Nat.choose 4 2 = 6 by decide] at this; omega
  obtain ⟨v, hv⟩ := hbr
  obtain ⟨ht3, hm3, -⟩ := htips v hv
  -- the tips formula forces one branch point of degree three
  have hform := tips_formula hT
  set Bf := hT.bfin.toFinset
  have hvB : v ∈ Bf := (Finite.mem_toFinset _).2 hv
  have hsum : (degree v - 2) + (Bf.erase v).card ≤ ∑ u ∈ Bf, (degree u - 2) := by
    rw [← Finset.add_sum_erase _ _ hvB]
    refine Nat.add_le_add_left ?_ _
    have := Finset.card_nsmul_le_sum (Bf.erase v) (fun u => degree u - 2) 1 (fun u hu => by
      have hu' : IsBranchPoint u := (Finite.mem_toFinset hT.bfin).1 (Finset.mem_of_mem_erase hu)
      have := (htips u hu').2.1; omega)
    simpa using this
  have hcard := Finset.card_erase_add_one hvB
  have hdeg : degree v = 3 := by omega
  have hBcard : Bf.card = 1 := by omega
  have htips3 : {p : T | IsTip p}.ncard = 3 := by omega
  -- vertices and edges
  have hBset : branchSet T = {v} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hBcard
    have : v = w := by rw [hw] at hvB; exact Finset.mem_singleton.1 hvB
    subst this
    ext p; constructor
    · intro hp
      have : p ∈ Bf := (Finite.mem_toFinset _).2 hp
      rw [hw] at this; exact Finset.mem_singleton.1 this
    · rintro rfl; exact hv
  have hVsplit : vertices T = {p : T | IsTip p} ∪ branchSet T := by
    ext p; simp only [vertices, branchSet, mem_setOf_eq, mem_union]
  have hdisjTB : Disjoint {p : T | IsTip p} (branchSet T) := by
    rw [Set.disjoint_left]
    intro p hp hp'
    have h1 : order p = 1 := hp
    have h3 : 3 ≤ order p := hp'
    rw [h1] at h3; exact absurd h3 (by decide)
  have hVcard : (vertices T).ncard = 4 := by
    rw [hVsplit, ncard_union_eq hdisjTB htf hT.bfin, htips3, hBset, ncard_singleton]
  have hEcard : {ℓ : Set T | IsEdge ℓ}.ncard = 3 := by
    have := ncard_edges_add_one hT.noSCC hT.bfin hT.bord; omega
  have hvV : v ∈ vertices T := Or.inr hv
  have hEv : {ℓ : Set T | IsEdge ℓ ∧ v ∈ ℓ} = {ℓ : Set T | IsEdge ℓ} := by
    refine eq_of_subset_of_ncard_le (fun ℓ hℓ => hℓ.1) ?_ hT.edges_finite
    have h := order_eq_encard_edges hT.noSCC hT.bfin hT.bord hvV
    rw [order_eq_degree hT hvV, hdeg] at h
    have hfin : {ℓ : Set T | IsEdge ℓ ∧ v ∈ ℓ}.Finite :=
      hT.edges_finite.subset fun ℓ hℓ => hℓ.1
    rw [hEcard, ← hfin.cast_ncard_eq] at *
    have : ({ℓ : Set T | IsEdge ℓ ∧ v ∈ ℓ}.ncard : ℕ∞) = 3 := h.symm
    exact_mod_cast this.ge
  obtain ⟨ℓ₁, ℓ₂, ℓ₃, h12, h13, h23, hE⟩ := ncard_eq_three.1 hEcard
  have hmem : ∀ ℓ ∈ ({ℓ₁, ℓ₂, ℓ₃} : Set (Set T)), IsEdge ℓ ∧ v ∈ ℓ := by
    intro ℓ hℓ
    rw [← hE, ← hEv] at hℓ; exact hℓ
  have hm1 := hmem ℓ₁ (mem_insert _ _)
  have hm2 := hmem ℓ₂ (mem_insert_of_mem _ (mem_insert _ _))
  have hm3' := hmem ℓ₃ (mem_insert_of_mem _ (mem_insert_of_mem _ rfl))
  exact ⟨v, hv, hBset, hdeg, ℓ₁, ℓ₂, ℓ₃, h12, h13, h23, hE, hmem⟩

/-- **Proposition 9.3 (reduction to the triod).** A branched finite tree with the DMP is a
simple triod. -/
theorem prop_9_3 (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) :
    IsSimpleTriod (univ : Set T) := by
  obtain ⟨v, hv, -, -, ℓ₁, ℓ₂, ℓ₃, h12, h13, h23, hE, hmem⟩ := triod_structure hT hDMP hbr
  have hvV : v ∈ vertices T := Or.inr hv
  have hm1 := hmem ℓ₁ (mem_insert _ _)
  have hm2 := hmem ℓ₂ (mem_insert_of_mem _ (mem_insert _ _))
  have hm3' := hmem ℓ₃ (mem_insert_of_mem _ (mem_insert_of_mem _ rfl))
  obtain ⟨c₁, -, hc₁, hs₁, -⟩ := edge_from_vertex hT hm1.1 hm1.2 hvV
  obtain ⟨c₂, -, hc₂, hs₂, -⟩ := edge_from_vertex hT hm2.1 hm2.2 hvV
  obtain ⟨c₃, -, hc₃, hs₃, -⟩ := edge_from_vertex hT hm3'.1 hm3'.2 hvV
  have hint : ∀ ℓ ℓ' : Set T, IsEdge ℓ ∧ v ∈ ℓ → IsEdge ℓ' ∧ v ∈ ℓ' → ℓ ≠ ℓ' → ℓ ∩ ℓ' = {v} :=
    fun ℓ ℓ' h h' hne => (edge_inter_subsingleton hT.noSCC hT.bfin h.1 h'.1 hne).eq_singleton_of_mem
      ⟨h.2, h'.2⟩
  refine ⟨v, c₁, c₂, c₃, ℓ₁, ℓ₂, ℓ₃, hs₁ ▸ seg_isArcBetween hc₁, hs₂ ▸ seg_isArcBetween hc₂,
    hs₃ ▸ seg_isArcBetween hc₃, hint _ _ hm1 hm2 h12, hint _ _ hm1 hm3' h13,
    hint _ _ hm2 hm3' h23, ?_⟩
  rw [← sUnion_edges hT.noSCC hT.bfin hT.bord, hE, sUnion_insert, sUnion_insert,
    sUnion_singleton, union_assoc]

end DoubleMidset
