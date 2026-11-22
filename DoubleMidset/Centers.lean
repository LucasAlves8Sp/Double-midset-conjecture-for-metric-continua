module

public import DoubleMidset.EdgeTools

/-!
# Where the center of a spherical arc can lie (Section 7)

* `lemma_7_2`: a nondegenerate component of a sphere about an edge point is an arc in one edge;
  all its pairs are strict with `N` even, and both midset points are crossings;
* `lemma_7_1`: tips are not centers;
* `lemma_7_3`: matching beyond the center;
* `lemma_7_4`: in a branched tree no center lies in the open edge carrying its arc.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

theorem even_oddCount_swap {a b : T} (h : IsStrictPair a b) (hev : Even (oddCount a b)) :
    Even (oddCount b a) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  exact (Nat.not_even_iff_odd.2 (odd_oddCount_swap hT h.symm hodd)) hev

/-- **Lemma 7.2 (the center is a crossing).** Let `x` be an edge point, `r > 0`, and `K` a
nondegenerate component of `S(x, r)`. Then `K` is an arc contained in one edge. For all distinct
`p, q ∈ K`, the pair `(p, q)` is strict, `N(p, q)` is even, and `M(p, q) = {x, y}` with
`y ∈ (p, q)`, where both `x` and `y` are crossings. -/
theorem lemma_7_2 (hDMP : HasDMP T) {x : T} (hx : x ∉ vertices T) {r : ℝ} (hr : 0 < r)
    {K : Set T} (hKdef : ∃ z ∈ sphere x r, K = connectedComponentIn (sphere x r) z)
    (hKnt : K.Nontrivial) :
    IsArc K ∧ (∃ ℓ, IsEdge ℓ ∧ K ⊆ ℓ) ∧
    ∀ p ∈ K, ∀ q ∈ K, p ≠ q → IsStrictPair p q ∧ Even (oddCount p q) ∧
      ∃ y, midset p q = {x, y} ∧ (∀ A, IsArcBetween A p q → y ∈ A ∧ y ≠ p ∧ y ≠ q) ∧
        IsCrossing (sgnf p q) x ∧ IsCrossing (sgnf p q) y := by
  have h2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  obtain ⟨z₀, hz₀, rfl⟩ := hKdef
  set K := connectedComponentIn (sphere x r) z₀ with hKeq
  have hKs : K ⊆ sphere x r := connectedComponentIn_subset _ _
  have hKc : IsClosed K := isClosed_of_closure_subset
    (isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hz₀))
      (closure_minimal hKs isClosed_sphere))
  have hKp : IsPreconnected K := isPreconnected_connectedComponentIn
  have hxK : x ∉ K := fun h => by
    have := hKs h; rw [mem_sphere, dist_self] at this; linarith
  have hsph : ∀ a ∈ K, ∀ b ∈ K, a ≠ b → IsSphericalArc (seg a b) x r := fun a ha b hb hab =>
    ⟨(seg_isArcBetween hab).isArc, hr, (seg_subset hT.noSCC hKp ha hb).trans hKs⟩
  obtain ⟨p₁, hp₁, q₁, hq₁, hpq₁⟩ := hKnt
  obtain ⟨-, -, ⟨hint, ℓ, hℓ, hℓsub⟩, -⟩ := lemma_6_2 hT h2 (hsph p₁ hp₁ q₁ hq₁ hpq₁)
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hpq₁).exists_param
  have hmseg : g (1 / 2) ∈ seg p₁ q₁ := hgim ▸ ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hmp : g (1 / 2) ≠ p₁ := fun e => by
    have := hg.2 ⟨by norm_num, by norm_num⟩ ⟨le_rfl, zero_le_one⟩ (e.trans hg0.symm)
    norm_num at this
  have hmq : g (1 / 2) ≠ q₁ := fun e => by
    have := hg.2 ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩ (e.trans hg1.symm)
    norm_num at this
  have hmV : g (1 / 2) ∉ vertices T := hint p₁ q₁ (seg_isArcBetween hpq₁) _ hmseg hmp hmq
  have hmK : g (1 / 2) ∈ K := seg_subset hT.noSCC hKp hp₁ hq₁ hmseg
  have hKℓ : K ⊆ ℓ := by
    intro w hw
    by_cases hwm : w = g (1 / 2)
    · rw [hwm]; exact hℓsub hmseg
    · obtain ⟨-, -, ⟨-, ℓ', hℓ', hsub'⟩, -⟩ :=
        lemma_6_2 hT h2 (hsph _ hmK w hw (Ne.symm hwm))
      have := edge_unique hT hℓ hℓ' (hℓsub hmseg) (hsub' (left_mem_seg _ w)) hmV
      rw [this]; exact hsub' (right_mem_seg hT.noSCC _ w)
  obtain ⟨γ, hγ, hγℓ⟩ := exists_param_of_isEdge hT hℓ
  obtain ⟨α, β, hα, hαβ, hβ, hKeqγ⟩ :=
    exists_Icc_of_subset_edge hT hγ.arc hKc hKp (hγℓ ▸ hKℓ) hp₁ hq₁ hpq₁
  have hKarc : IsArcBetween K (γ α) (γ β) := by
    rw [hKeqγ]; exact hγ.arc.isArcBetween_Icc hα hαβ hβ
  have hγK : ∀ t ∈ Icc α β, γ t ∈ K := fun t ht => by rw [hKeqγ]; exact ⟨t, ht, rfl⟩
  have h01 : ∀ t ∈ Icc α β, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨hα.trans ht.1, ht.2.trans hβ⟩
  have hγV : ∀ t ∈ Ioo α β, γ t ∉ vertices T := fun t ht =>
    hγ.interior t ⟨lt_of_le_of_lt hα ht.1, lt_of_lt_of_le ht.2 hβ⟩
  have hsphγ : ∀ t ∈ Icc α β, dist x (γ t) = r := fun t ht => by
    have := hKs (hγK t ht); rw [mem_sphere, dist_comm] at this; exact this
  have hxK' : x ∉ γ '' Icc α β := by rw [← hKeqγ]; exact hxK
  -- the exit end `q₀` of `K` towards `x`
  obtain ⟨τq, hτq, k, hk, hk0, hk1, -, hkout⟩ := exists_exit hT hγ hα hαβ hβ hxK'
  have hτqI : τq ∈ Icc α β := by
    rcases hτq with rfl | rfl
    exacts [⟨le_rfl, hαβ.le⟩, ⟨hαβ.le, le_rfl⟩]
  have hq₀K : γ τq ∈ K := hγK τq hτqI
  -- points off the sphere accumulate at `q₀`
  have hacc : ∀ ε > 0, ∃ b, dist b (γ τq) < ε ∧ dist x b ≠ r := by
    intro ε hε
    by_contra hall
    push_neg at hall
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuous_iff.1 hk.1 1 ε hε
    have hm1 : min (δ / 2) (1 / 2) ≤ δ / 2 := min_le_left _ _
    have hm2 : min (δ / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hm3 : 0 < min (δ / 2) (1 / 2) := lt_min (by linarith) (by norm_num)
    have hsub : k '' Icc (1 - min (δ / 2) (1 / 2)) 1 ⊆ sphere x r := by
      rintro _ ⟨t, ht, rfl⟩
      have hd : dist (k t) (k 1) < ε := hδb t (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [hk1] at hd
      rw [mem_sphere, dist_comm]; exact hall _ hd
    have hcc : k '' Icc (1 - min (δ / 2) (1 / 2)) 1 ⊆ K := by
      rw [hKeq, connectedComponentIn_eq (show γ τq ∈ connectedComponentIn (sphere x r) z₀
        from hq₀K)]
      exact hk.isPreconnected_image.subset_connectedComponentIn
        ⟨1, ⟨by linarith, le_rfl⟩, hk1⟩ hsub
    have := hcc ⟨1 - min (δ / 2) (1 / 2), ⟨le_rfl, by linarith⟩, rfl⟩
    rw [hKeqγ] at this
    exact hkout _ ⟨by linarith, by linarith⟩ this
  -- the midset of a pair in `K`
  have hpair : ∀ t₁ ∈ Icc α β, ∀ t₂ ∈ Icc α β, t₁ ≠ t₂ →
      ∃ ρ ∈ Ioo (min t₁ t₂) (max t₁ t₂), midset (γ t₁) (γ t₂) = {x, γ ρ} := by
    intro t₁ ht₁ t₂ ht₂ hne
    have hne' : γ t₁ ≠ γ t₂ := fun e => hne (hγ.arc.2 (h01 _ ht₁) (h01 _ ht₂) e)
    have hs : sgnf (γ t₁) (γ t₂) (γ (min t₁ t₂)) * sgnf (γ t₁) (γ t₂) (γ (max t₁ t₂)) < 0 := by
      rcases le_total t₁ t₂ with h | h
      · rw [min_eq_left h, max_eq_right h]
        exact mul_neg_of_neg_of_pos (sgnf_left_neg hne') (sgnf_right_pos hne')
      · rw [min_eq_right h, max_eq_left h]
        exact mul_neg_of_pos_of_neg (sgnf_right_pos hne') (sgnf_left_neg hne')
    obtain ⟨ρ, hρ, hρ0⟩ := exists_zero_Ioo (continuous_sgnf _ _) hγ.arc.1 (min_lt_max.2 hne) hs
    have hyM : γ ρ ∈ midset (γ t₁) (γ t₂) := sgnf_eq_zero_iff.1 hρ0
    have hxM : x ∈ midset (γ t₁) (γ t₂) := by
      show dist x (γ t₁) = dist x (γ t₂); rw [hsphγ t₁ ht₁, hsphγ t₂ ht₂]
    have hρI : ρ ∈ Icc α β := ⟨le_trans (le_min ht₁.1 ht₂.1) hρ.1.le,
      hρ.2.le.trans (max_le ht₁.2 ht₂.2)⟩
    have hxy : x ≠ γ ρ := fun e => hxK (e ▸ hγK ρ hρI)
    refine ⟨ρ, hρ, ?_⟩
    have hsub : ({x, γ ρ} : Set T) ⊆ midset (γ t₁) (γ t₂) := by
      rintro w (rfl | rfl)
      exacts [hxM, hyM]
    exact ((toFinite _).eq_of_subset_of_encard_le hsub
      (by rw [hDMP _ _ hne', encard_pair hxy])).symm
  have hstrict : ∀ t₁ ∈ Icc α β, ∀ t₂ ∈ Icc α β, t₁ ≠ t₂ → IsStrictPair (γ t₁) (γ t₂) := by
    intro t₁ ht₁ t₂ ht₂ hne
    obtain ⟨ρ, hρ, hM⟩ := hpair t₁ ht₁ t₂ ht₂ hne
    refine ⟨fun e => hne (hγ.arc.2 (h01 _ ht₁) (h01 _ ht₂) e), fun u hu h0 => ?_⟩
    have huM : u ∈ midset (γ t₁) (γ t₂) := sgnf_eq_zero_iff.1 h0
    rw [hM] at huM
    rcases huM with rfl | rfl
    · exact hx hu
    · exact hγV ρ ⟨lt_of_le_of_lt (le_min ht₁.1 ht₂.1) hρ.1,
        lt_of_lt_of_le hρ.2 (max_le ht₁.2 ht₂.2)⟩ hu
  -- an interior point `p` of `K`; `N(p, q₀)` is even
  have hρp : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have hρpτq : (α + β) / 2 ≠ τq := by
    rcases hτq with rfl | rfl
    · exact ne_of_gt hρp.1
    · exact ne_of_lt hρp.2
  have hstr0 := hstrict _ (Ioo_subset_Icc_self hρp) τq hτqI hρpτq
  have heven0 : Even (oddCount (γ ((α + β) / 2)) (γ τq)) := by
    have hS := strict_nhds hT hstr0
    have hcont : Continuous fun b : T => (γ ((α + β) / 2), b) :=
      continuous_const.prodMk continuous_id
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.1 (hcont.continuousAt.preimage_mem_nhds hS)
    obtain ⟨b, hb, hbr⟩ := hacc ε hε
    obtain ⟨hstrb, hcount⟩ := hεb (mem_ball.2 hb)
    have hpe : ∀ t ∈ Icc α β, t ≠ (α + β) / 2 → γ ((α + β) / 2) ≠ γ t := fun t ht hne e =>
      hne (hγ.arc.2 (h01 _ ht) (h01 _ (Ioo_subset_Icc_self hρp)) e.symm)
    have := lemma_6_3 hT hDMP (⟨hKarc.isArc, hr, hKs⟩ : IsSphericalArc K x r) hKarc
      (hγK _ (Ioo_subset_Icc_self hρp)) (hpe α ⟨le_rfl, hαβ.le⟩ (ne_of_lt hρp.1))
      (hpe β ⟨hαβ.le, le_rfl⟩ (ne_of_gt hρp.2)) hbr hstrb
    rw [hcount] at this; exact this
  refine ⟨hKarc.isArc, ⟨ℓ, hℓ, hKℓ⟩, fun p' hp' q' hq' hpq' => ?_⟩
  rw [hKeqγ] at hp' hq'
  obtain ⟨t₁, ht₁, rfl⟩ := hp'
  obtain ⟨t₂, ht₂, rfl⟩ := hq'
  have ht : t₁ ≠ t₂ := fun e => hpq' (congrArg γ e)
  -- distances from vertices are strictly monotone along `K`
  have hmono : ∀ u ∈ vertices T, StrictMonoOn (fun t => dist u (γ t)) (Icc α β) ∨
      StrictAntiOn (fun t => dist u (γ t)) (Icc α β) := by
    intro u hu
    refine (continuous_const.dist hγ.arc.1).continuousOn.strictMonoOn_of_injOn_Icc' hαβ.le ?_
    intro a ha b hb hab
    by_contra hne
    wlog hlt : a < b generalizing a b
    · exact this hb ha hab.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    have hux : u ≠ x := fun e => hx (e ▸ hu)
    by_cases hon : ∃ t ∈ Icc a b, γ t = u
    · obtain ⟨t, htI, rfl⟩ := hon
      have htab : t = a ∨ t = b := by
        by_contra hc
        push_neg at hc
        exact hγV t ⟨lt_of_le_of_lt ha.1 (lt_of_le_of_ne htI.1 (Ne.symm hc.1)),
          lt_of_lt_of_le (lt_of_le_of_ne htI.2 hc.2) hb.2⟩ hu
      have hab' : dist (γ t) (γ a) = dist (γ t) (γ b) := hab
      rcases htab with rfl | rfl
      · rw [dist_self] at hab'
        exact hne (hγ.arc.2 (h01 _ ha) (h01 _ hb) (dist_eq_zero.1 hab'.symm))
      · rw [dist_self] at hab'
        exact hne (hγ.arc.2 (h01 _ ha) (h01 _ hb) (dist_eq_zero.1 hab').symm)
    · push_neg at hon
      rcases sphere_strictMonoOn h2 hγ.arc (hα.trans ha.1) hlt.le (hb.2.trans hβ) hr
        (fun t ht => hsphγ t ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩) hon hux with h | h
      · exact absurd hab (h ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt).ne
      · exact absurd hab (h ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt).ne'
  have hstr := hstrict t₁ ht₁ t₂ ht₂ ht
  have hmid : (α + β) / 2 ∈ Icc α β := Ioo_subset_Icc_self hρp
  have heven : Even (oddCount (γ t₁) (γ t₂)) := by
    by_cases hord : (t₁ < t₂ ↔ (α + β) / 2 < τq)
    · have : oddCount (γ t₁) (γ t₂) = oddCount (γ ((α + β) / 2)) (γ τq) := by
        unfold oddCount; congr 1; ext u
        simp only [mem_setOf_eq]
        refine and_congr_right fun hu => ?_
        exact sub_neg_iff_of_strictMono (hmono u hu.1) ht₁ ht₂ hmid hτqI ht hρpτq hord
      rw [this]; exact heven0
    · have hord' : (t₁ < t₂ ↔ τq < (α + β) / 2) := by
        constructor
        · intro h; by_contra h'; push_neg at h'
          exact hord ⟨fun _ => lt_of_le_of_ne h' hρpτq, fun _ => h⟩
        · intro h; by_contra h'; push_neg at h'
          exact hord ⟨fun h'' => absurd h'' (not_lt.2 h'), fun h'' => absurd h (not_lt.2 h''.le)⟩
      have : oddCount (γ t₁) (γ t₂) = oddCount (γ τq) (γ ((α + β) / 2)) := by
        unfold oddCount; congr 1; ext u
        simp only [mem_setOf_eq]
        refine and_congr_right fun hu => ?_
        exact sub_neg_iff_of_strictMono (hmono u hu.1) ht₁ ht₂ hτqI hmid ht (Ne.symm hρpτq) hord'
      rw [this]; exact even_oddCount_swap hT hstr0 heven0
  obtain ⟨ρ, hρ, hM⟩ := hpair t₁ ht₁ t₂ ht₂ ht
  obtain ⟨-, -, h3, -⟩ := cor_5_5 hT hDMP hstr
  have hcr := h3 heven
  refine ⟨hstr, heven, γ ρ, hM, fun A hA => ?_, hcr x (hM ▸ mem_insert _ _),
    hcr (γ ρ) (hM ▸ mem_insert_of_mem _ rfl)⟩
  have hρI : ρ ∈ Icc (0 : ℝ) 1 := ⟨(hα.trans (le_min ht₁.1 ht₂.1)).trans hρ.1.le,
    hρ.2.le.trans ((max_le ht₁.2 ht₂.2).trans hβ)⟩
  rw [← seg_eq hT.noSCC hA, hγ.arc.seg_image hT (h01 _ ht₁) (h01 _ ht₂), ← Icc_min_max]
  refine ⟨⟨ρ, Ioo_subset_Icc_self hρ, rfl⟩, fun e => ?_, fun e => ?_⟩
  · have := hγ.arc.2 hρI (h01 _ ht₁) e
    rw [this] at hρ
    rcases le_total t₁ t₂ with h | h
    · rw [min_eq_left h] at hρ; linarith [hρ.1]
    · rw [max_eq_left h] at hρ; linarith [hρ.2]
  · have := hγ.arc.2 hρI (h01 _ ht₂) e
    rw [this] at hρ
    rcases le_total t₁ t₂ with h | h
    · rw [max_eq_right h] at hρ; linarith [hρ.2]
    · rw [min_eq_right h] at hρ; linarith [hρ.1]

/-- **Lemma 7.1 (tips are not centers).** No tip of `T` is the center of a spherical arc. -/
theorem lemma_7_1 (hDMP : HasDMP T) {x : T} (hx : IsTip x) {I : Set T} {r : ℝ} :
    ¬ IsSphericalArc I x r := by
  intro hI
  have h2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  have hxV : x ∈ vertices T := Or.inl hx
  have hr := hI.2.1
  obtain ⟨-, -, ⟨-, ℓ, hℓ, hIℓ⟩, -⟩ := lemma_6_2 hT h2 hI
  obtain ⟨γ, hγ, hγℓ⟩ := exists_param_of_isEdge hT hℓ
  obtain ⟨e₁, e₂, hIe⟩ := hI.1.exists_isArcBetween
  obtain ⟨α, β, hα, hαβ, hβ, hIeq⟩ := exists_Icc_of_subset_edge hT hγ.arc hIe.isCompact.isClosed
    hIe.isConnected.isPreconnected (hγℓ ▸ hIℓ) hIe.left_mem hIe.right_mem hIe.ne
  have hsphγ : ∀ t ∈ Icc α β, dist x (γ t) = r := fun t ht => by
    have := hI.2.2 (show γ t ∈ I by rw [hIeq]; exact ⟨t, ht, rfl⟩)
    rw [mem_sphere, dist_comm] at this; exact this
  -- shrink `I` into the open edge
  set α' := (2 * α + β) / 3
  set β' := (α + 2 * β) / 3
  have hα' : 0 < α' := by simp only [α']; linarith
  have hαβ' : α' < β' := by simp only [α', β']; linarith
  have hβ' : β' < 1 := by simp only [β']; linarith
  have hsub' : Icc α' β' ⊆ Icc α β := Icc_subset_Icc (by simp only [α']; linarith)
    (by simp only [β']; linarith)
  set I₀ := γ '' Icc α' β'
  have hI₀ab : IsArcBetween I₀ (γ α') (γ β') := hγ.arc.isArcBetween_Icc hα'.le hαβ' hβ'.le
  have hI₀ : IsSphericalArc I₀ x r := ⟨hI₀ab.isArc, hr, by
    rintro _ ⟨t, ht, rfl⟩; rw [mem_sphere, dist_comm]; exact hsphγ t (hsub' ht)⟩
  have hI₀V : ∀ z ∈ I₀, z ∉ vertices T := by
    rintro _ ⟨t, ht, rfl⟩; exact hγ.interior t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hxI₀ : x ∉ I₀ := fun h => hI₀V x h hxV
  have h01' : ∀ t ∈ Icc α' β', t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the exit end `s` and the arc `k` from `x` to `s`
  obtain ⟨τs, hτs, k, hk, hk0, hk1, -, hkout⟩ := exists_exit hT hγ hα'.le hαβ' hβ'.le hxI₀
  have hτsI : τs ∈ Icc α' β' := by
    rcases hτs with rfl | rfl
    exacts [⟨le_rfl, hαβ'.le⟩, ⟨hαβ'.le, le_rfl⟩]
  have hsI₀ : k 1 ∈ I₀ := by rw [hk1]; exact ⟨τs, hτsI, rfl⟩
  -- the point `q`: closest to `x` on `[s, x]` at distance `r`
  set Q := {t | t ∈ Icc (0 : ℝ) 1 ∧ dist x (k t) = r}
  have hQc : IsCompact Q := isCompact_Icc.inter_right
    (isClosed_eq (continuous_const.dist hk.1) continuous_const)
  have h1Q : (1 : ℝ) ∈ Q := ⟨⟨zero_le_one, le_rfl⟩, by
    have := hI₀.2.2 hsI₀; rw [mem_sphere, dist_comm] at this; exact this⟩
  have hτQ : sInf Q ∈ Q := hQc.sInf_mem ⟨1, h1Q⟩
  set τ := sInf Q
  have hτpos : 0 < τ := by
    rcases eq_or_lt_of_le hτQ.1.1 with e | e
    · exfalso; have := hτQ.2; rw [← e, hk0, dist_self] at this; linarith
    · exact e
  have hτ1 : τ ≤ 1 := hτQ.1.2
  have hbelow : ∀ t ∈ Ico (0 : ℝ) τ, dist x (k t) < r := by
    intro t ht
    by_contra hge
    push_neg at hge
    have hc : ContinuousOn (fun t => dist x (k t)) (Icc 0 t) :=
      (continuous_const.dist hk.1).continuousOn
    obtain ⟨t', ht', he⟩ := intermediate_value_Icc ht.1 hc
      (show r ∈ Icc (dist x (k 0)) (dist x (k t)) by rw [hk0, dist_self]; exact ⟨hr.le, hge⟩)
    have : τ ≤ t' := csInf_le ⟨0, fun t ht => ht.1.1⟩
      ⟨⟨ht'.1, ht'.2.trans (ht.2.le.trans hτ1)⟩, he⟩
    linarith [ht'.2, ht.2]
  set q := k τ
  have hxq : dist x q = r := hτQ.2
  have hτI : τ ∈ Icc (0 : ℝ) 1 := ⟨hτpos.le, hτ1⟩
  -- the site `p`
  have hbad : (⋃ u ∈ vertices T \ {x}, {t | t ∈ Ioo α' β' ∧ dist u (γ t) = dist u q}).Finite := by
    refine (hT.vertices_finite.diff).biUnion fun u hu => Subsingleton.finite ?_
    rintro t ⟨ht, hte⟩ t' ⟨ht', hte'⟩
    have hinj := (lemma_6_2 hT h2 hI₀).1 u (fun h => hI₀V u h hu.1) hu.2
    exact hγ.arc.2 (h01' t (Ioo_subset_Icc_self ht)) (h01' t' (Ioo_subset_Icc_self ht'))
      (hinj ⟨t, Ioo_subset_Icc_self ht, rfl⟩ ⟨t', Ioo_subset_Icc_self ht', rfl⟩
        (hte.trans hte'.symm))
  obtain ⟨tp, htp, htpbad⟩ := ((Ioo_infinite hαβ').diff hbad).nonempty
  set p := γ tp
  have hpI₀ : p ∈ I₀ := ⟨tp, Ioo_subset_Icc_self htp, rfl⟩
  have hxp : dist x p = r := hsphγ tp (hsub' (Ioo_subset_Icc_self htp))
  have hpu : ∀ u ∈ vertices T, u ≠ x → dist u p ≠ dist u q := fun u hu hux he =>
    htpbad (mem_biUnion (x := u) ⟨hu, hux⟩ ⟨htp, he⟩)
  have hpα : p ≠ γ α' := fun e => by
    have := hγ.arc.2 (h01' _ (Ioo_subset_Icc_self htp)) (h01' α' ⟨le_rfl, hαβ'.le⟩) e
    linarith [htp.1]
  have hpβ : p ≠ γ β' := fun e => by
    have := hγ.arc.2 (h01' _ (Ioo_subset_Icc_self htp)) (h01' β' ⟨hαβ'.le, le_rfl⟩) e
    linarith [htp.2]
  have hpq : p ≠ q := by
    intro e
    rcases eq_or_lt_of_le hτ1 with e1 | e1
    · rw [show q = k 1 by rw [← e1], hk1] at e
      have := hγ.arc.2 (h01' _ (Ioo_subset_Icc_self htp)) (h01' _ hτsI) e
      rcases hτs with h | h <;> rw [h] at this <;> linarith [htp.1, htp.2]
    · exact hkout τ ⟨hτpos.le, e1⟩ (show q ∈ I₀ from e ▸ hpI₀)
  -- the arc `[p, q]` avoids `x`
  have hsegpq : seg p q ⊆ I₀ ∪ k '' Icc τ 1 := by
    have hu : IsPreconnected (I₀ ∪ k '' Icc τ 1) :=
      hI₀ab.isConnected.isPreconnected.union (k 1) hsI₀ ⟨1, ⟨hτ1, le_rfl⟩, rfl⟩
        hk.isPreconnected_image
    exact seg_subset hT.noSCC hu (Or.inl hpI₀) (Or.inr ⟨τ, ⟨le_rfl, hτ1⟩, rfl⟩)
  have hxseg : x ∉ seg p q := by
    intro h
    rcases hsegpq h with h | ⟨t, ht, he⟩
    · exact hxI₀ h
    · have := hk.2 ⟨hτpos.le.trans ht.1, ht.2⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hk0.symm)
      linarith [ht.1]
  have hinter : seg p q ∩ k '' Icc 0 τ ⊆ {q} := by
    rintro w ⟨hw, ⟨t, ht, rfl⟩⟩
    rcases hsegpq hw with h | ⟨t', ht', he⟩
    · rcases eq_or_lt_of_le (ht.2.trans hτ1) with e1 | e1
      · have : t = τ := le_antisymm ht.2 (e1 ▸ hτ1)
        rw [this]; rfl
      · exact absurd h (hkout t ⟨ht.1, e1⟩)
    · have := hk.2 ⟨hτpos.le.trans ht'.1, ht'.2⟩ ⟨ht.1, ht.2.trans hτ1⟩ he
      have : t = τ := le_antisymm ht.2 (this ▸ ht'.1)
      rw [this]; rfl
  -- the second midset point `y` is a crossing
  obtain ⟨m, hm, hmim, hm0, hm1⟩ := (seg_isArcBetween hpq).exists_param
  set f := sgnf p q
  have hfs : f (m 0) * f (m 1) < 0 := by
    rw [hm0, hm1]; exact mul_neg_of_neg_of_pos (sgnf_left_neg hpq) (sgnf_right_pos hpq)
  obtain ⟨ρ, hρ, hρ0⟩ := exists_zero_Ioo (continuous_sgnf p q) hm.1 zero_lt_one hfs
  set y := m ρ
  have hyseg : y ∈ seg p q := hmim ▸ ⟨ρ, Ioo_subset_Icc_self hρ, rfl⟩
  have hxy : x ≠ y := fun e => hxseg (e ▸ hyseg)
  have hxM : x ∈ midset p q := by show dist x p = dist x q; rw [hxp, hxq]
  have hM : midset p q = {x, y} := by
    have hsub : ({x, y} : Set T) ⊆ midset p q := by
      rintro w (rfl | rfl)
      exacts [hxM, sgnf_eq_zero_iff.1 hρ0]
    exact ((toFinite _).eq_of_subset_of_encard_le hsub
      (by rw [hDMP _ _ hpq, encard_pair hxy])).symm
  have hyV : y ∉ vertices T := fun hyV => hpu y hyV (Ne.symm hxy) (sgnf_eq_zero_iff.1 hρ0)
  have hmuniq : ∀ t ∈ Icc (0 : ℝ) 1, ∀ (g : T → ℝ), (∀ z, g z = 0 → z = y) → g (m t) = 0 →
      t = ρ := fun t ht g hg h0 => hm.2 ht (Ioo_subset_Icc_self hρ) (hg _ h0)
  have hfzero : ∀ z, f z = 0 → z = x ∨ z = y := fun z hz => by
    have : z ∈ midset p q := sgnf_eq_zero_iff.1 hz
    rw [hM] at this; exact this
  -- `f > 0` on `(x, q]`
  have hfq : 0 < f q := sgnf_right_pos hpq
  have hpos : ∀ t ∈ Ioc (0 : ℝ) τ, 0 < f (k t) := by
    have hnz : ∀ t ∈ Ioc (0 : ℝ) τ, (f ∘ k) t ≠ 0 := by
      intro t ht h0
      rcases hfzero _ h0 with h | h
      · have := hk.2 ⟨ht.1.le, ht.2.trans hτ1⟩ ⟨le_rfl, zero_le_one⟩ (h.trans hk0.symm)
        linarith [ht.1]
      · have hyq : y ∈ ({q} : Set T) :=
          hinter ⟨hyseg, ⟨t, ⟨ht.1.le, ht.2⟩, h⟩⟩
        rw [mem_singleton_iff] at hyq
        rw [hyq] at hρ0; exact absurd hρ0 hfq.ne'
    intro t ht
    have := const_sign isPreconnected_Ioc ((continuous_sgnf p q).comp hk.1).continuousOn hnz
      t ht τ ⟨hτpos, le_rfl⟩
    exact pos_of_mul_pos_left this hfq.le |>.trans_le' le_rfl
  -- a neighbourhood of the tip
  obtain ⟨δ₁, hδ₁, hball₁, hδV⟩ := tip_nhds hT hx hk hk0 hτpos hτ1
  set δ := min (δ₁ / 2) (r / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ δ₁ / 2 := min_le_left _ _
  have hδ2 : δ ≤ r / 2 := min_le_right _ _
  have hnear : ∀ z, dist x z ≤ δ → z ≠ x → 0 < f z := by
    intro z hz hzx
    obtain ⟨t, ht, rfl⟩ := hball₁ (show z ∈ ball x δ₁ by
      rw [mem_ball, dist_comm]; linarith)
    refine hpos t ⟨lt_of_le_of_ne ht.1 fun e => hzx ?_, ht.2.le⟩
    rw [← e, hk0]
  -- the modified function `g` (instead of cutting the tree)
  set g : T → ℝ := fun z => max (f z) (δ - dist x z)
  have hgc : Continuous g :=
    (continuous_sgnf p q).max (continuous_const.sub (continuous_const.dist continuous_id))
  have hgx : 0 < g x := lt_max_of_lt_right (by rw [dist_self]; linarith)
  have hgzero : ∀ z, g z = 0 ↔ z = y := by
    intro z
    constructor
    · intro hz
      by_cases hzδ : dist x z ≤ δ
      · exfalso
        by_cases hzx : z = x
        · rw [hzx] at hz; linarith
        · have := hnear z hzδ hzx
          have : f z ≤ g z := le_max_left _ _
          linarith
      · push_neg at hzδ
        have hf0 : f z = 0 := by
          have h1 : f z ≤ 0 := hz ▸ le_max_left _ _
          by_contra hne
          have h3 : f z < 0 := lt_of_le_of_ne h1 hne
          have : g z < 0 := max_lt h3 (by linarith)
          linarith
        rcases hfzero z hf0 with h | h
        · rw [h, dist_self] at hzδ; linarith
        · exact h
    · rintro rfl
      have hyδ : δ < dist x y := by
        by_contra hle
        push_neg at hle
        have := hnear y hle (Ne.symm hxy)
        have hfy : f y = 0 := hρ0
        rw [hfy] at this; exact lt_irrefl _ this
      show max (f y) (δ - dist x y) = 0
      have hfy : f y = 0 := hρ0
      rw [hfy]; exact max_eq_left (by linarith)
  have hgfin : (g ⁻¹' {0}).Finite := (finite_singleton y).subset fun z hz => (hgzero z).1 hz
  have hgV : ∀ u ∈ vertices T, g u ≠ 0 := fun u hu h0 => hyV ((hgzero u).1 h0 ▸ hu)
  have hgp : g p < 0 := max_lt (sgnf_left_neg hpq) (by rw [hxp]; linarith)
  have hgq : 0 < g q := lt_max_of_lt_left hfq
  have hcross : IsCrossing g y := by
    refine isCrossing_of_arc hT hm hgc hgfin le_rfl hρ.1 hρ.2 le_rfl ?_ ((hgzero y).2 rfl) hyV
      fun t ht h0 => hmuniq t ht g (fun z hz => (hgzero z).1 hz) h0
    rw [hm0, hm1]; exact mul_neg_of_neg_of_pos hgp hgq
  have hcr : {z | IsCrossing g z} = {y} := by
    ext z; constructor
    · intro hz; exact (hgzero z).1 hz.2.1
    · rintro rfl; exact hcross
  have hpar := lemma_5_4 hT hgc hgfin hgV
  rw [hcr, ncard_singleton] at hpar
  -- `g` and `f` have the same signs at the vertices other than `x`
  have hfar : ∀ u ∈ vertices T, u ≠ x → δ < dist x u := fun u hu hux => by
    have := hδV u hu hux; linarith
  have hS : {u | u ∈ oddVertices T ∧ g u < 0} = {u | u ∈ oddVertices T ∧ u ≠ x ∧ f u < 0} := by
    ext u
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hu, hgu⟩
      have hux : u ≠ x := fun e => by rw [e] at hgu; linarith
      exact ⟨hu, hux, lt_of_le_of_lt (le_max_left _ _) hgu⟩
    · rintro ⟨hu, hux, hfu⟩
      exact ⟨hu, max_lt hfu (by linarith [hfar u hu.1 hux])⟩
  rw [hS] at hpar
  -- a site `b` just beyond `q`
  have hfu : ∀ u ∈ vertices T \ {x}, f u ≠ 0 := fun u hu h0 => by
    rcases hfzero u h0 with h | h
    · exact hu.2 h
    · exact hyV (h ▸ hu.1)
  have hev : ∀ᶠ b in 𝓝 q, ∀ u ∈ vertices T \ {x}, 0 < sgnf p b u * f u := by
    refine (eventually_all_finite hT.vertices_finite.diff).2 fun u hu => ?_
    have hc : Continuous fun b => sgnf p b u * f u :=
      (continuous_sgnf_param continuous_const continuous_id continuous_const).mul continuous_const
    exact hc.continuousAt.eventually (lt_mem_nhds (mul_self_pos.2 (hfu u hu)))
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨η, hη, hηk⟩ := Metric.continuous_iff.1 hk.1 τ ε hε
  set tb := τ - min (η / 2) (τ / 2)
  have hm1' : min (η / 2) (τ / 2) ≤ η / 2 := min_le_left _ _
  have hm2' : min (η / 2) (τ / 2) ≤ τ / 2 := min_le_right _ _
  have hm3' : 0 < min (η / 2) (τ / 2) := lt_min (by linarith) (by linarith)
  have htb : tb ∈ Ico (0 : ℝ) τ := ⟨by simp only [tb]; linarith, by simp only [tb]; linarith⟩
  set b := k tb
  have hbq : dist b q < ε := hηk tb (by
    rw [Real.dist_eq, abs_lt]; constructor <;> simp only [tb] <;> linarith)
  have hsignb := hεb hbq
  have hxb : dist x b < r := hbelow tb htb
  have hbp : p ≠ b := fun e => hkout tb ⟨htb.1, htb.2.trans_le hτ1⟩ (show b ∈ I₀ from e ▸ hpI₀)
  have hpbx : 0 < sgnf p b x := by
    show 0 < dist x p - dist x b; rw [hxp]; linarith
  have hstr : IsStrictPair p b := by
    refine ⟨hbp, fun u hu h0 => ?_⟩
    by_cases hux : u = x
    · rw [hux] at h0; linarith
    · have := hsignb u ⟨hu, hux⟩; rw [h0, zero_mul] at this; exact lt_irrefl _ this
  have hcount : oddCount p b = {u | u ∈ oddVertices T ∧ u ≠ x ∧ f u < 0}.ncard := by
    unfold oddCount; congr 1; ext u
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hu, hbu⟩
      have hux : u ≠ x := fun e => by rw [e] at hbu; linarith
      have := hsignb u ⟨hu.1, hux⟩
      refine ⟨hu, hux, ?_⟩
      by_contra hc; push_neg at hc; nlinarith
    · rintro ⟨hu, hux, hfu'⟩
      have := hsignb u ⟨hu.1, hux⟩
      refine ⟨hu, ?_⟩
      by_contra hc; push_neg at hc; nlinarith
  have hodd : Odd (oddCount p b) := by rw [hcount, Nat.odd_iff]; omega
  exact (Nat.not_even_iff_odd.2 hodd) (lemma_6_3 hT hDMP hI₀ hI₀ab hpI₀ hpα hpβ hxb.ne hstr)

omit hT in
theorem IsTip.mem_oddVertices {e : T} (he : IsTip e) : e ∈ oddVertices T :=
  ⟨Or.inl he, 1, by rw [he]; rfl, odd_one⟩

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
/-- Signs at finitely many points persist for nearby sites. -/
theorem sign_persist {F : Set T} (hF : F.Finite) {a b : T} (h : ∀ u ∈ F, sgnf a b u ≠ 0) :
    ∀ᶠ p : T × T in 𝓝 (a, b), ∀ u ∈ F, 0 < sgnf p.1 p.2 u * sgnf a b u := by
  refine (eventually_all_finite hF).2 fun u hu => ?_
  have hc : Continuous fun p : T × T => sgnf p.1 p.2 u * sgnf a b u :=
    (continuous_sgnf_param continuous_fst continuous_snd continuous_const).mul continuous_const
  exact hc.continuousAt.eventually (lt_mem_nhds (mul_self_pos.2 (h u hu)))

/-- **Lemma 7.3 (matching beyond the center).** Let `ℓ` be an edge parametrized by `k` with the
tip `e = k 1` as an end, and `s = k σ`, `s' = k σ'`, `x = k ξ` with `0 < σ < σ' < ξ < 1`, and
`I = [s, s'] ⊆ S(x, r)`, `r > 0`. Then
(a) `h_e` is strictly increasing on `I` from `s` to `s'`;
(b) `Z = {z ∈ (s', e) : h_e(s) < h_e(z) < h_e(s')}` is open, and for every `a ∈ (s, s')` it
contains a point `b` with `h_e(b) = h_e(a)`;
(c) `Z ⊆ S(x, r) ∩ (x, e)`, and `M(p_z, z) = {e, x}` for `z ∈ Z` and `p_z ∈ (s, s')` with
`h_e(p_z) = h_e(z)`. -/
theorem lemma_7_3 (hDMP : HasDMP T) {ℓ : Set T} (hℓ : IsEdge ℓ) {k : ℝ → T} (hkc : Continuous k)
    (hki : InjOn k (Icc 0 1)) (hkℓ : k '' Icc 0 1 = ℓ) (he : IsTip (k 1)) {σ σ' ξ : ℝ}
    (h0 : 0 < σ) (h1 : σ < σ') (h2 : σ' < ξ) (h3 : ξ < 1) {r : ℝ} (hr : 0 < r)
    (hI : k '' Icc σ σ' ⊆ sphere (k ξ) r) :
    StrictMonoOn (fun t => dist (k 1) (k t)) (Icc σ σ') ∧
    (IsOpen {z | z ∈ k '' Ioo σ' 1 ∧ dist (k 1) (k σ) < dist (k 1) z ∧
        dist (k 1) z < dist (k 1) (k σ')} ∧
      ∀ a ∈ k '' Ioo σ σ', ∃ b ∈ {z | z ∈ k '' Ioo σ' 1 ∧ dist (k 1) (k σ) < dist (k 1) z ∧
        dist (k 1) z < dist (k 1) (k σ')}, dist (k 1) b = dist (k 1) a) ∧
    ({z | z ∈ k '' Ioo σ' 1 ∧ dist (k 1) (k σ) < dist (k 1) z ∧
        dist (k 1) z < dist (k 1) (k σ')} ⊆ sphere (k ξ) r ∩ k '' Ioo ξ 1 ∧
      ∀ z ∈ {z | z ∈ k '' Ioo σ' 1 ∧ dist (k 1) (k σ) < dist (k 1) z ∧
        dist (k 1) z < dist (k 1) (k σ')}, ∀ pz ∈ k '' Ioo σ σ', dist (k 1) pz = dist (k 1) z →
        midset pz z = {k 1, k ξ}) := by
  have hk : IsArcParam k := ⟨hkc, hki⟩
  have hγ : IsEdgeParam k := isEdgeParam_of_isEdge hT hℓ hk hkℓ
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  set e := k 1
  set x := k ξ
  set φ := fun t => dist e (k t)
  have hφc : Continuous φ := continuous_const.dist hkc
  have hxV : x ∉ vertices T := hγ.interior ξ ⟨by linarith, h3⟩
  have hI01 : ∀ t ∈ Icc σ σ', t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsphI : ∀ t ∈ Icc σ σ', dist x (k t) = r := fun t ht => by
    have := hI ⟨t, ht, rfl⟩; rw [mem_sphere, dist_comm] at this; exact this
  -- (a) strict increase of `h_e` on `I`
  have ha : StrictMonoOn φ (Icc σ σ') := by
    intro t₁ ht₁ t₂ ht₂ hlt
    have hne : k t₁ ≠ k t₂ := fun e' => hlt.ne (hki (hI01 _ ht₁) (hI01 _ ht₂) e')
    set K := connectedComponentIn (sphere x r) (k t₁)
    have hIK : k '' Icc σ σ' ⊆ K :=
      hk.isPreconnected_image.subset_connectedComponentIn ⟨t₁, ht₁, rfl⟩ hI
    obtain ⟨-, -, hpairs⟩ := lemma_7_2 hT hDMP hxV hr ⟨k t₁, hI ⟨t₁, ht₁, rfl⟩, rfl⟩
      ⟨k t₁, hIK ⟨t₁, ht₁, rfl⟩, k t₂, hIK ⟨t₂, ht₂, rfl⟩, hne⟩
    obtain ⟨hstr, -, y, hM, hyA, hxcr, -⟩ :=
      hpairs _ (hIK ⟨t₁, ht₁, rfl⟩) _ (hIK ⟨t₂, ht₂, rfl⟩) hne
    obtain ⟨hyA', hy1, hy2⟩ := hyA _ (hk.isArcBetween_Icc (by linarith [ht₁.1]) hlt
      (by linarith [ht₂.2]))
    obtain ⟨ρ, hρ, rfl⟩ := hyA'
    have hρ' : ρ ∈ Ioo t₁ t₂ := ⟨lt_of_le_of_ne hρ.1 fun e' => hy1 (by rw [e']),
      lt_of_le_of_ne hρ.2 fun e' => hy2 (by rw [e'])⟩
    set f := sgnf (k t₁) (k t₂)
    have hfc : Continuous (f ∘ k) := (continuous_sgnf _ _).comp hkc
    have hzeros : ∀ t ∈ Icc (0 : ℝ) 1, f (k t) = 0 → t = ρ ∨ t = ξ := by
      intro t ht h0
      have : k t ∈ midset (k t₁) (k t₂) := sgnf_eq_zero_iff.1 h0
      rw [hM] at this
      rcases this with h | h
      · right; exact hki ht ⟨by linarith, by linarith⟩ h
      · left; exact hki ht ⟨by linarith [hρ'.1, ht₁.1], by linarith [hρ'.2, ht₂.2]⟩ h
    have hft₂ : 0 < f (k t₂) := sgnf_right_pos hne
    -- positive between `y` and `x`
    have hmid : ∀ t ∈ Ioo ρ ξ, 0 < f (k t) := by
      intro t ht
      have := const_sign isPreconnected_Ioo hfc.continuousOn (fun t' ht' h0 => by
        rcases hzeros t' ⟨by linarith [ht'.1, hρ'.1, ht₁.1], by linarith [ht'.2]⟩ h0 with h | h
        · linarith [ht'.1]
        · linarith [ht'.2]) t ht t₂ ⟨hρ'.2, by linarith [ht₂.2]⟩
      exact pos_of_mul_pos_left this hft₂.le |>.trans_le' le_rfl
    obtain ⟨ε, hε, hside⟩ := hxcr.along hT hk ⟨by linarith, h3⟩ rfl
    set δ := min (ε / 2) (min ((ξ - t₂) / 2) ((1 - ξ) / 2))
    have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith [ht₂.2]) (by linarith))
    have hδ1 : δ ≤ ε / 2 := min_le_left _ _
    have hδ2 : δ ≤ (ξ - t₂) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hδ3 : δ ≤ (1 - ξ) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have hpos := hmid (ξ - δ) ⟨by linarith [hρ'.2], by linarith⟩
    have hneg : f (k (ξ + δ)) < 0 := by
      have := hside (ξ - δ) ⟨by linarith, by linarith⟩ (ξ + δ) ⟨by linarith, by linarith⟩
      by_contra hc; push_neg at hc
      have : 0 ≤ f (k (ξ - δ)) * f (k (ξ + δ)) := mul_nonneg hpos.le hc
      linarith
    have hfe : f e < 0 := by
      have hnz : ∀ t' ∈ Ioc ξ 1, (f ∘ k) t' ≠ 0 := fun t' ht' h0 => by
        rcases hzeros t' ⟨by linarith [ht'.1], ht'.2⟩ h0 with h | h
        · linarith [ht'.1, hρ'.2, ht₂.2]
        · linarith [ht'.1]
      have hprod : 0 < f (k 1) * f (k (ξ + δ)) :=
        const_sign isPreconnected_Ioc hfc.continuousOn hnz 1 ⟨h3, le_rfl⟩ (ξ + δ)
          ⟨by linarith, by linarith⟩
      by_contra hc; push_neg at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos hc hneg.le]
    show dist e (k t₁) < dist e (k t₂)
    have : f e = dist e (k t₁) - dist e (k t₂) := rfl
    linarith
  -- the set `Z`
  set Z := {z | z ∈ k '' Ioo σ' 1 ∧ dist e (k σ) < dist e z ∧ dist e z < dist e (k σ')}
  have hZo : IsOpen Z := (hγ.isOpen_image_Ioo hT (by linarith) le_rfl).inter
    ((isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
      (isOpen_lt (continuous_const.dist continuous_id) continuous_const))
  have hφpos : ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 1 → 0 < φ t := fun t ht h1' =>
    dist_pos.2 fun e' => h1' (hki ⟨zero_le_one, le_rfl⟩ ht e').symm
  have hmatch : ∀ t ∈ Ioo σ σ', ∃ b ∈ Z, dist e b = dist e (k t) := by
    intro t ht
    have hφt : φ t < φ σ' := ha ⟨ht.1.le, ht.2.le⟩ ⟨h1.le, le_rfl⟩ ht.2
    have hφ1 : φ 1 = 0 := dist_self e
    have hφt0 : 0 < φ t := hφpos t ⟨by linarith [ht.1], by linarith [ht.2]⟩
      (ne_of_lt (by linarith [ht.2]))
    obtain ⟨tb, htb, hφb⟩ := intermediate_value_Ioo' (show σ' ≤ 1 by linarith)
      hφc.continuousOn (show φ t ∈ Ioo (φ 1) (φ σ') from ⟨by rw [hφ1]; exact hφt0, hφt⟩)
    refine ⟨k tb, ⟨⟨tb, htb, rfl⟩, ?_, ?_⟩, hφb⟩
    · rw [show dist e (k tb) = φ tb from rfl, hφb]
      exact ha ⟨le_rfl, h1.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    · rw [show dist e (k tb) = φ tb from rfl, hφb]; exact hφt
  -- (c)
  have hc : ∀ z ∈ Z, z ∈ sphere x r ∧ z ∈ k '' Ioo ξ 1 ∧
      ∀ pz ∈ k '' Ioo σ σ', dist e pz = dist e z → midset pz z = {e, x} := by
    rintro z ⟨⟨tz, htz, rfl⟩, hz1, hz2⟩
    obtain ⟨tp, htp, hφp⟩ := intermediate_value_Ioo h1.le hφc.continuousOn
      (show φ tz ∈ Ioo (φ σ) (φ σ') from ⟨hz1, hz2⟩)
    have htpz : k tp ≠ k tz := fun e' => by
      have := hki ⟨by linarith [htp.1], by linarith [htp.2]⟩ ⟨by linarith [htz.1], htz.2.le⟩ e'
      linarith [htp.2, htz.1]
    have heM : ∀ p', dist e p' = dist e (k tz) → e ∈ midset p' (k tz) := fun p' h => h
    -- `z` lies on the sphere
    have hzs : dist x (k tz) = r := by
      by_contra hzr
      -- the midset of `(k tp, z)`
      have hs0 : sgnf (k tp) (k tz) (k tp) * sgnf (k tp) (k tz) (k tz) < 0 :=
        mul_neg_of_neg_of_pos (sgnf_left_neg htpz) (sgnf_right_pos htpz)
      obtain ⟨ρ', hρ', hρ'0⟩ := exists_zero_Ioo (continuous_sgnf _ _) hkc
        (show tp < tz by linarith [htp.2, htz.1]) hs0
      have hρ'01 : ρ' ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ'.1, htp.1], by linarith [hρ'.2, htz.2]⟩
      have hey : e ≠ k ρ' := fun e' => by
        have := hki ⟨zero_le_one, le_rfl⟩ (Ioo_subset_Icc_self hρ'01) e'; linarith [hρ'01.2]
      have hM : midset (k tp) (k tz) = {e, k ρ'} := by
        have hsub : ({e, k ρ'} : Set T) ⊆ midset (k tp) (k tz) := by
          rintro w (rfl | rfl)
          exacts [heM _ (show φ tp = φ tz from hφp), sgnf_eq_zero_iff.1 hρ'0]
        exact ((toFinite _).eq_of_subset_of_encard_le hsub
          (by rw [hDMP _ _ htpz, encard_pair hey])).symm
      have hfu : ∀ u ∈ vertices T \ {e}, sgnf (k tp) (k tz) u ≠ 0 := fun u hu h0 => by
        have : u ∈ midset (k tp) (k tz) := sgnf_eq_zero_iff.1 h0
        rw [hM] at this
        rcases this with h | h
        · exact hu.2 h
        · rw [mem_singleton_iff] at h; exact hγ.interior ρ' hρ'01 (h ▸ hu.1)
      have hev := sign_persist hT.vertices_finite.diff hfu
      have hcont : Continuous fun t : ℝ => (k t, k tz) := hkc.prodMk continuous_const
      obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.1 ((hcont.tendsto tp).eventually hev)
      set η' := min (η / 2) (min ((tp - σ) / 2) ((σ' - tp) / 2))
      have hη' : 0 < η' := lt_min (by linarith) (lt_min (by linarith [htp.1]) (by linarith [htp.2]))
      have e1 : η' ≤ η / 2 := min_le_left _ _
      have e2 : η' ≤ (tp - σ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
      have e3 : η' ≤ (σ' - tp) / 2 := (min_le_right _ _).trans (min_le_right _ _)
      have hn₀ : ((vertices T \ {e}) ∩ {u | u ∈ oddVertices T ∧ sgnf (k tp) (k tz) u < 0}).Finite :=
        hT.vertices_finite.diff.inter_of_left _
      -- the two nearby sites
      have hsite : ∀ t', |t' - tp| < η → t' ∈ Ioo σ σ' → t' ≠ tp →
          IsStrictPair (k t') (k tz) ∧ (oddCount (k t') (k tz) =
            {u | u ∈ oddVertices T ∧ u ≠ e ∧ sgnf (k tp) (k tz) u < 0}.ncard +
              if t' < tp then 1 else 0) := by
        intro t' ht' ht'I hne'
        have hsg := hηb (show dist t' tp < η by rw [Real.dist_eq]; exact ht')
        have hef : sgnf (k t') (k tz) e = φ t' - φ tp := by
          show dist e (k t') - dist e (k tz) = φ t' - φ tp
          rw [hφp]
        have hI' : t' ∈ Icc σ σ' := Ioo_subset_Icc_self ht'I
        have hIp : tp ∈ Icc σ σ' := Ioo_subset_Icc_self htp
        have hne0 : sgnf (k t') (k tz) e ≠ 0 := by
          rw [hef]; intro h0
          exact hne' (ha.injOn hI' hIp (by linarith))
        have hk't : k t' ≠ k tz := fun e' => by
          have := hki (hI01 _ hI') ⟨by linarith [htz.1], htz.2.le⟩ e'
          linarith [ht'I.2, htz.1]
        refine ⟨⟨hk't, fun u hu h0 => ?_⟩, ?_⟩
        · by_cases hue : u = e
          · rw [hue] at h0; exact hne0 h0
          · have := hsg u ⟨hu, hue⟩; simp only at this; rw [h0, zero_mul] at this
            exact lt_irrefl _ this
        · unfold oddCount
          have hset : ∀ u, u ∈ oddVertices T → u ≠ e →
              (sgnf (k t') (k tz) u < 0 ↔ sgnf (k tp) (k tz) u < 0) := by
            intro u hu hue
            have := hsg u ⟨hu.1, hue⟩
            simp only at this
            constructor
            · intro h; by_contra h'; push_neg at h'; nlinarith
            · intro h; by_contra h'; push_neg at h'; nlinarith
          by_cases hlt : t' < tp
          · rw [if_pos hlt]
            have heneg : sgnf (k t') (k tz) e < 0 := by
              rw [hef]; have := ha hI' hIp hlt; linarith
            have : {u | u ∈ oddVertices T ∧ sgnf (k t') (k tz) u < 0} =
                insert e {u | u ∈ oddVertices T ∧ u ≠ e ∧ sgnf (k tp) (k tz) u < 0} := by
              ext u; simp only [mem_setOf_eq, mem_insert_iff]
              constructor
              · rintro ⟨hu, hu'⟩
                by_cases hue : u = e
                · exact Or.inl hue
                · exact Or.inr ⟨hu, hue, (hset u hu hue).1 hu'⟩
              · rintro (rfl | ⟨hu, hue, hu'⟩)
                · exact ⟨he.mem_oddVertices, heneg⟩
                · exact ⟨hu, (hset u hu hue).2 hu'⟩
            rw [this, ncard_insert_of_notMem (fun h => h.2.1 rfl)
              (hT.vertices_finite.subset fun u hu => hu.1.1)]
          · rw [if_neg hlt, add_zero]
            have hgt : tp < t' := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne')
            have hepos : 0 < sgnf (k t') (k tz) e := by
              rw [hef]; have := ha hIp hI' hgt; linarith
            congr 1; ext u; simp only [mem_setOf_eq]
            constructor
            · rintro ⟨hu, hu'⟩
              have hue : u ≠ e := fun h => by rw [h] at hu'; linarith
              exact ⟨hu, hue, (hset u hu hue).1 hu'⟩
            · rintro ⟨hu, hue, hu'⟩; exact ⟨hu, (hset u hu hue).2 hu'⟩
      have hspharc : IsSphericalArc (k '' Icc σ σ') x r :=
        ⟨(hk.isArcBetween_Icc h0.le h1 (by linarith)).isArc, hr, hI⟩
      have hev' : ∀ t' ∈ Ioo σ σ', IsStrictPair (k t') (k tz) → Even (oddCount (k t') (k tz)) :=
        fun t' ht' hstr => lemma_6_3 hT hDMP hspharc (hk.isArcBetween_Icc h0.le h1 (by linarith))
          ⟨t', Ioo_subset_Icc_self ht', rfl⟩
          (fun e' => by have := hki (hI01 _ (Ioo_subset_Icc_self ht')) (hI01 σ ⟨le_rfl, h1.le⟩) e'
                        linarith [ht'.1])
          (fun e' => by have := hki (hI01 _ (Ioo_subset_Icc_self ht')) (hI01 σ' ⟨h1.le, le_rfl⟩) e'
                        linarith [ht'.2]) hzr hstr
      obtain ⟨hsm, hcm⟩ := hsite (tp - η') (by rw [abs_lt]; constructor <;> linarith)
        ⟨by linarith, by linarith⟩ (by linarith)
      obtain ⟨hsp, hcp⟩ := hsite (tp + η') (by rw [abs_lt]; constructor <;> linarith)
        ⟨by linarith, by linarith⟩ (by linarith)
      have Em := hev' (tp - η') ⟨by linarith, by linarith⟩ hsm
      have Ep := hev' (tp + η') ⟨by linarith, by linarith⟩ hsp
      rw [hcm, if_pos (by linarith)] at Em
      rw [hcp, if_neg (by linarith), add_zero] at Ep
      exact (Nat.not_even_iff_odd.2 (Even.add_one Ep)) Em
    have hM' : ∀ pz ∈ k '' Ioo σ σ', dist e pz = dist e (k tz) → midset pz (k tz) = {e, x} := by
      rintro _ ⟨t, ht, rfl⟩ hpe
      have hne : k t ≠ k tz := fun e' => by
        have := hki ⟨by linarith [ht.1], by linarith [ht.2]⟩ ⟨by linarith [htz.1], htz.2.le⟩ e'
        linarith [ht.2, htz.1]
      have hex : e ≠ x := fun e' => by
        have := hki ⟨zero_le_one, le_rfl⟩ ⟨by linarith, h3.le⟩ e'; linarith
      have hsub : ({e, x} : Set T) ⊆ midset (k t) (k tz) := by
        rintro w (rfl | rfl)
        · exact hpe
        · show dist x (k t) = dist x (k tz)
          rw [hzs, hsphI t (Ioo_subset_Icc_self ht)]
      exact ((toFinite _).eq_of_subset_of_encard_le hsub
        (by rw [hDMP _ _ hne, encard_pair hex])).symm
    refine ⟨by rw [mem_sphere, dist_comm]; exact hzs, ?_, hM'⟩
    -- `z` lies beyond `x`
    have htpz' : tp < tz := by linarith [htp.2, htz.1]
    obtain ⟨ρ', hρ', hρ'0⟩ := exists_zero_Ioo (continuous_sgnf (k tp) (k tz)) hkc htpz'
      (mul_neg_of_neg_of_pos (sgnf_left_neg htpz) (sgnf_right_pos htpz))
    have hmem : k ρ' ∈ midset (k tp) (k tz) := sgnf_eq_zero_iff.1 hρ'0
    rw [hM' _ ⟨tp, htp, rfl⟩ (show φ tp = φ tz from hφp)] at hmem
    have hρ'01 : ρ' ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hρ'.1, htp.1], by linarith [hρ'.2, htz.2]⟩
    rcases hmem with h | h
    · have := hki hρ'01 ⟨zero_le_one, le_rfl⟩ h; linarith [hρ'.2, htz.2]
    · rw [mem_singleton_iff] at h
      have := hki hρ'01 ⟨by linarith, h3.le⟩ h
      exact ⟨tz, ⟨by linarith [hρ'.2], htz.2⟩, rfl⟩
  refine ⟨ha, ⟨hZo, ?_⟩, fun z hz => ⟨(hc z hz).1, (hc z hz).2.1⟩, fun z hz => (hc z hz).2.2⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hmatch t ht

omit [MetricSpace T] [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T]
  [Nontrivial T] hT in
theorem image_symm_Icc (γ : ℝ → T) (a b : ℝ) :
    (fun t => γ (1 - t)) '' Icc a b = γ '' Icc (1 - b) (1 - a) := by
  ext z; constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp only [sub_sub_cancel]⟩

omit hT in
theorem IsEdgeParam.symm {γ : ℝ → T} (hγ : IsEdgeParam γ) : IsEdgeParam fun t => γ (1 - t) :=
  ⟨hγ.arc.symm, by simp only [sub_zero]; exact hγ.end1, by simp only [sub_self]; exact hγ.end0,
    fun t ht => hγ.interior _ ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

/-- Case 1 of Lemma 7.4: the center lies between a branch point end and the arc. -/
theorem ownedge_case1 (hDMP : HasDMP T) {γ : ℝ → T} (hγ : IsEdgeParam γ)
    (hw : IsBranchPoint (γ 0)) {ξ α β : ℝ} (h0 : 0 < ξ) (h1 : ξ < α) (h2 : α < β) (h3 : β < 1)
    {r : ℝ} (hr : 0 < r) (hI : γ '' Icc α β ⊆ sphere (γ ξ) r) : False := by
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  have hxV : γ ξ ∉ vertices T := hγ.interior ξ ⟨h0, by linarith⟩
  have hne : γ α ≠ γ β := fun e => h2.ne (hγ.arc.2 ⟨by linarith, by linarith⟩ ⟨by linarith, h3.le⟩ e)
  set K := connectedComponentIn (sphere (γ ξ) r) (γ α)
  have hIK : γ '' Icc α β ⊆ K :=
    hγ.arc.isPreconnected_image.subset_connectedComponentIn ⟨α, ⟨le_rfl, h2.le⟩, rfl⟩ hI
  obtain ⟨-, -, hpairs⟩ := lemma_7_2 hT hDMP hxV hr ⟨γ α, hI ⟨α, ⟨le_rfl, h2.le⟩, rfl⟩, rfl⟩
    ⟨γ α, hIK ⟨α, ⟨le_rfl, h2.le⟩, rfl⟩, γ β, hIK ⟨β, ⟨h2.le, le_rfl⟩, rfl⟩, hne⟩
  obtain ⟨-, -, y, hM, hyA, hxcr, -⟩ :=
    hpairs _ (hIK ⟨α, ⟨le_rfl, h2.le⟩, rfl⟩) _ (hIK ⟨β, ⟨h2.le, le_rfl⟩, rfl⟩) hne
  obtain ⟨⟨ρ, hρ, rfl⟩, hy1, hy2⟩ := hyA _ (hγ.arc.isArcBetween_Icc (by linarith) h2 h3.le)
  have hρ' : ρ ∈ Ioo α β := ⟨lt_of_le_of_ne hρ.1 fun e => hy1 (by rw [e]),
    lt_of_le_of_ne hρ.2 fun e => hy2 (by rw [e])⟩
  set f := sgnf (γ α) (γ β)
  have hfc : Continuous (f ∘ γ) := (continuous_sgnf _ _).comp hγ.arc.1
  have hzeros : ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) = 0 → t = ρ ∨ t = ξ := by
    intro t ht h0
    have : γ t ∈ midset (γ α) (γ β) := sgnf_eq_zero_iff.1 h0
    rw [hM] at this
    rcases this with h | h
    · right; exact hγ.arc.2 ht ⟨by linarith, by linarith⟩ h
    · left; exact hγ.arc.2 ht ⟨by linarith [hρ'.1], by linarith [hρ'.2]⟩ h
  have hfα : f (γ α) < 0 := sgnf_left_neg hne
  have hneg : ∀ t ∈ Ioc ξ α, f (γ t) < 0 := by
    intro t ht
    have hprod : 0 < f (γ t) * f (γ α) := const_sign isPreconnected_Ioc hfc.continuousOn
      (fun t' ht' h0 => by
        rcases hzeros t' ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ h0 with h | h
        · linarith [ht'.2, hρ'.1]
        · linarith [ht'.1]) t ht α ⟨h1, le_rfl⟩
    by_contra hc; push_neg at hc
    linarith [mul_nonpos_of_nonneg_of_nonpos hc hfα.le]
  obtain ⟨ε, hε, hside⟩ := hxcr.along hT hγ.arc ⟨h0, by linarith⟩ rfl
  set δ := min (ε / 2) (min (ξ / 2) ((α - ξ) / 2))
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ ξ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ (α - ξ) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hn := hneg (ξ + δ) ⟨by linarith, by linarith⟩
  have hp : 0 < f (γ (ξ - δ)) := by
    have := hside (ξ - δ) ⟨by linarith, by linarith⟩ (ξ + δ) ⟨by linarith, by linarith⟩
    by_contra hc; push_neg at hc
    linarith [mul_nonneg_of_nonpos_of_nonpos hc hn.le]
  have hfw : 0 < f (γ 0) := by
    have hprod : 0 < f (γ 0) * f (γ (ξ - δ)) := const_sign isPreconnected_Ico hfc.continuousOn
      (fun t' ht' h0 => by
        rcases hzeros t' ⟨ht'.1, by linarith [ht'.2]⟩ h0 with h | h
        · linarith [ht'.2, hρ'.1]
        · linarith [ht'.2]) 0 ⟨le_rfl, h0⟩ (ξ - δ) ⟨by linarith, by linarith⟩
    by_contra hc; push_neg at hc
    linarith [mul_nonpos_of_nonpos_of_nonneg hc hp.le]
  have hmono := lemma_4_3 hT.noSCC hD2 hw hγ.arc rfl
  have := hmono ⟨by linarith, by linarith⟩ ⟨by linarith, h3.le⟩ h2.le
  have hfw' : f (γ 0) = dist (γ 0) (γ α) - dist (γ 0) (γ β) := rfl
  simp only at this
  linarith

/-- Case 2 of Lemma 7.4: the arc lies between a branch point end and the center. -/
theorem ownedge_case2 (hDMP : HasDMP T) {γ : ℝ → T} (hγ : IsEdgeParam γ)
    (hw : IsBranchPoint (γ 0)) {ξ α β : ℝ} (h0 : 0 < α) (h1 : α < β) (h2 : β < ξ) (h3 : ξ < 1)
    {r : ℝ} (hr : 0 < r) (hI : γ '' Icc α β ⊆ sphere (γ ξ) r) : False := by
  by_cases hb : IsBranchPoint (γ 1)
  · refine ownedge_case1 hT hDMP hγ.symm (by simpa using hb) (ξ := 1 - ξ) (α := 1 - β)
      (β := 1 - α) (by linarith) (by linarith) (by linarith) (by linarith) hr ?_
    rw [image_symm_Icc]; simpa using hI
  · have he : IsTip (γ 1) := (hγ.end1).resolve_right hb
    obtain ⟨-, ⟨-, hmatch⟩, ⟨hZ, -⟩⟩ := lemma_7_3 hT hDMP (hγ.isEdge hT) hγ.arc.1 hγ.arc.2 rfl he
      h0 h1 h2 h3 hr hI
    obtain ⟨z₀, hz₀Z, -⟩ := hmatch (γ ((α + β) / 2)) ⟨(α + β) / 2, ⟨by linarith, by linarith⟩, rfl⟩
    have hZo := (lemma_7_3 hT hDMP (hγ.isEdge hT) hγ.arc.1 hγ.arc.2 rfl he h0 h1 h2 h3 hr hI).2.1.1
    obtain ⟨-, t₀, ht₀, rfl⟩ := hZ hz₀Z
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (hZo.preimage hγ.arc.1) t₀ hz₀Z
    set η' := min (η / 2) (min ((t₀ - ξ) / 2) ((1 - t₀) / 2))
    have hη' : 0 < η' := lt_min (by linarith) (lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2]))
    have e1 : η' ≤ η / 2 := min_le_left _ _
    have e2 : η' ≤ (t₀ - ξ) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have e3 : η' ≤ (1 - t₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    refine ownedge_case1 hT hDMP hγ hw (ξ := ξ) (α := t₀ - η') (β := t₀ + η') (by linarith)
      (by linarith) (by linarith) (by linarith) hr ?_
    rintro _ ⟨t, ht, rfl⟩
    have hmem := hball (show t ∈ ball t₀ η by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
    exact (hZ hmem).1

/-- **Lemma 7.4 (no center in the arc's own edge).** Let `T` be branched. If a spherical arc `I`
with center `x` lies in an open edge `W`, then `x ∉ W`. -/
theorem lemma_7_4 (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {I : Set T} {x : T}
    {r : ℝ} (hI : IsSphericalArc I x r) {W : Set T} (hW : IsOpenEdge W) (hIW : I ⊆ W) :
    x ∉ W := by
  intro hxW
  have hxV : x ∉ vertices T := hW.notMem_vertices hxW
  obtain ⟨γ, ξ, hξ, hγ, rfl, hWeq, hcl⟩ := exists_edgeParam hT hxV
  rw [hW.eq_cc hxW, ← hWeq] at hIW
  obtain ⟨e₁, e₂, hIe⟩ := hI.1.exists_isArcBetween
  obtain ⟨α, β, hα, hαβ, hβ, hIeq⟩ := exists_Icc_of_subset_edge hT hγ.arc hIe.isCompact.isClosed
    hIe.isConnected.isPreconnected (hIW.trans (image_mono Ioo_subset_Icc_self)) hIe.left_mem
    hIe.right_mem hIe.ne
  have hin : ∀ t ∈ Icc α β, t ∈ Ioo (0 : ℝ) 1 := fun t ht => by
    obtain ⟨t', ht', he⟩ := hIW (show γ t ∈ I by rw [hIeq]; exact ⟨t, ht, rfl⟩)
    have := hγ.arc.2 (Ioo_subset_Icc_self ht') ⟨hα.trans ht.1, ht.2.trans hβ⟩ he
    rw [← this]; exact ht'
  have hα0 := (hin α ⟨le_rfl, hαβ.le⟩).1
  have hβ1 := (hin β ⟨hαβ.le, le_rfl⟩).2
  have hsph : γ '' Icc α β ⊆ sphere (γ ξ) r := hIeq ▸ hI.2.2
  have hξ' : ξ ∉ Icc α β := fun h => by
    have := hsph ⟨ξ, h, rfl⟩; rw [mem_sphere, dist_self] at this; linarith [hI.2.1]
  obtain ⟨v, hv⟩ := hbr
  obtain ⟨a, b, -, hseg, -, ha⟩ := edge_has_branch_end hT ⟨v, hv⟩ (hγ.isEdge hT)
  have ha' : a ∈ ({γ 0, γ 1} : Set T) := by
    rw [← hγ.inter_vertices hT]; exact ⟨hseg ▸ left_mem_seg a b, Or.inr ha⟩
  have hsph' : (fun t => γ (1 - t)) '' Icc (1 - β) (1 - α) ⊆
      sphere ((fun t => γ (1 - t)) (1 - ξ)) r := by
    rw [image_symm_Icc]; simpa using hsph
  rcases ha' with h | h
  · rw [h] at ha
    by_cases hlt : ξ < α
    · exact ownedge_case1 hT hDMP hγ ha hξ.1 hlt hαβ hβ1 hI.2.1 hsph
    · have : β < ξ := by
        by_contra h'; push_neg at h'; exact hξ' ⟨not_lt.1 hlt, h'⟩
      exact ownedge_case2 hT hDMP hγ ha hα0 hαβ this hξ.2 hI.2.1 hsph
  · rw [mem_singleton_iff] at h
    rw [h] at ha
    have ha'' : IsBranchPoint ((fun t => γ (1 - t)) 0) := by simpa using ha
    by_cases hlt : β < ξ
    · exact ownedge_case1 hT hDMP hγ.symm ha'' (by linarith [hξ.2]) (by linarith) (by linarith)
        (by linarith) hI.2.1 hsph'
    · have : ξ < α := by
        by_contra h'; push_neg at h'; exact hξ' ⟨h', not_lt.1 hlt⟩
      exact ownedge_case2 hT hDMP hγ.symm ha'' (by linarith) (by linarith) (by linarith)
        (by linarith [hξ.1]) hI.2.1 hsph'

end DoubleMidset
