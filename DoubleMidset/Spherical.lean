module

public import DoubleMidset.Types

/-!
# Spherical arcs (Lemma 6.2) and off-sphere parity (Lemma 6.3)

The core statements are about parameter intervals of arc parametrizations:

* `sphere_strictMonoOn`: if `k [c, d]` lies on a sphere `S(x, r)`, `r > 0`, and `y` is neither
  `x` nor on `k [c, d]`, then `d(y, k(·))` is strictly monotone on `[c, d]` (Lemma 6.2 (a));
* `no_vertex_inside`: no interior point of a spherical arc is a vertex (Lemma 6.2 (c));
* `centers_countable`: the set of centers of spherical arcs is countable (Lemma 6.2 (d));
* `lemma_6_3`: Lemma 6.3 (off-sphere parity).
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T]

section Sphere

variable (h2 : MidsetsAtMostTwo T)
include h2

/-- **Lemma 6.2 (a)**, parametric form. -/
theorem sphere_strictMonoOn {k : ℝ → T} (hk : IsArcParam k) {c d : ℝ} (hc : 0 ≤ c)
    (hcd : c ≤ d) (hd : d ≤ 1) {x : T} {r : ℝ} (hr : 0 < r)
    (hsph : ∀ t ∈ Icc c d, dist x (k t) = r) {y : T} (hyI : ∀ t ∈ Icc c d, k t ≠ y)
    (hyx : y ≠ x) :
    StrictMonoOn (fun t => dist y (k t)) (Icc c d) ∨
      StrictAntiOn (fun t => dist y (k t)) (Icc c d) := by
  refine (continuous_const.dist hk.1).continuousOn.strictMonoOn_of_injOn_Icc' hcd ?_
  intro u hu v hv he
  by_contra huv
  wlog hlt : u < v generalizing u v
  · exact this hv hu he.symm (Ne.symm huv) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm huv))
  have hI : ∀ t ∈ Icc c d, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨hc.trans ht.1, ht.2.trans hd⟩
  set p := k u
  set q := k v
  have hpq : p ≠ q := fun e => huv (hk.2 (hI u hu) (hI v hv) e)
  have hxM : x ∈ midset p q := by
    show dist x p = dist x q; rw [hsph u hu, hsph v hv]
  have hyM : y ∈ midset p q := he
  -- a zero between `p` and `q`
  have hpc : IsPreconnected (k '' Icc u v) := hk.isPreconnected_image
  obtain ⟨z, ⟨w, hw, rfl⟩, hz⟩ := hpc.intermediate_value (⟨u, ⟨le_rfl, hlt.le⟩, rfl⟩ :
    p ∈ k '' Icc u v) (⟨v, ⟨hlt.le, le_rfl⟩, rfl⟩ : q ∈ k '' Icc u v)
    (continuous_sgnf p q).continuousOn
    ⟨by unfold sgnf; rw [dist_self, zero_sub, neg_nonpos]; exact dist_nonneg,
      by unfold sgnf; rw [dist_self, sub_zero]; exact dist_nonneg⟩
  have hwI : w ∈ Icc c d := ⟨hu.1.trans hw.1, hw.2.trans hv.2⟩
  have hxk : x ≠ k w := fun e => by
    have := hsph w hwI; rw [← e, dist_self] at this; exact hr.ne this
  have hyk : y ≠ k w := fun e => hyI w hwI e.symm
  exact false_of_three hpq h2 (three_le_encard_midset hxM hyM (sgnf_eq_zero_iff.1 hz)
    (Ne.symm hyx) hxk hyk)

/-- **Lemma 6.2 (b)**, parametric form: a second center would be a point off the arc at constant
distance. -/
theorem sphere_center_unique {k : ℝ → T} (hk : IsArcParam k) {c d : ℝ} (hc : 0 ≤ c)
    (hcd : c < d) (hd : d ≤ 1) {x : T} {r : ℝ} (hr : 0 < r)
    (hsph : ∀ t ∈ Icc c d, dist x (k t) = r) {x' : T} {r' : ℝ} (hr' : 0 < r')
    (hsph' : ∀ t ∈ Icc c d, dist x' (k t) = r') : x' = x := by
  by_contra hne
  have hx'I : ∀ t ∈ Icc c d, k t ≠ x' := fun t ht e => by
    have := hsph' t ht; rw [e, dist_self] at this; exact hr'.ne this
  rcases sphere_strictMonoOn h2 hk hc hcd.le hd hr hsph hx'I hne with h | h
  · have := h ⟨le_rfl, hcd.le⟩ ⟨hcd.le, le_rfl⟩ hcd
    simp only [hsph' c ⟨le_rfl, hcd.le⟩, hsph' d ⟨hcd.le, le_rfl⟩] at this
    exact lt_irrefl _ this
  · have := h ⟨le_rfl, hcd.le⟩ ⟨hcd.le, le_rfl⟩ hcd
    simp only [hsph' c ⟨le_rfl, hcd.le⟩, hsph' d ⟨hcd.le, le_rfl⟩] at this
    exact lt_irrefl _ this


omit h2 in
/-- In a connected space, a point lies in the closure of every component of its complement. -/
theorem mem_closure_cc [ConnectedSpace T] [LocallyConnectedSpace T] {y z : T} (hzy : z ≠ y) :
    y ∈ closure (connectedComponentIn {y}ᶜ z) := by
  by_contra hcl
  have hsub : closure (connectedComponentIn {y}ᶜ z) ⊆ connectedComponentIn {y}ᶜ z := by
    intro w hw
    have hwy : w ≠ y := fun e => hcl (e ▸ hw)
    have hpc : IsPreconnected (insert w (connectedComponentIn {y}ᶜ z)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hw subset_closure)
    exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hzy))
      (insert_subset hwy (connectedComponentIn_subset _ _)) (mem_insert w _)
  have := IsClopen.eq_univ ⟨closure_subset_iff_isClosed.1 hsub,
    isOpen_compl_singleton.connectedComponentIn⟩ ⟨z, mem_connectedComponentIn hzy⟩
  exact (connectedComponentIn_subset _ _ (this ▸ mem_univ y : y ∈ _) : y ∈ ({y}ᶜ : Set T)) rfl

/-- **Lemma 6.2 (c)**, parametric form: no interior point of a spherical arc is a vertex. -/
theorem no_vertex_inside [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T]
    (hD : ∀ C : Set T, ¬ IsSimpleClosedCurve C) {k : ℝ → T} (hk : IsArcParam k) {c d : ℝ}
    (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ 1) {x : T} {r : ℝ} (hr : 0 < r)
    (hsph : ∀ t ∈ Icc c d, dist x (k t) = r) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo c d) :
    k t₀ ∉ vertices T := by
  have hI : ∀ t ∈ Icc c d, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨hc.trans ht.1, ht.2.trans hd⟩
  have ht₀I : t₀ ∈ Icc c d := Ioo_subset_Icc_self ht₀
  set y := k t₀
  have hne : ∀ t ∈ Icc c d, t ≠ t₀ → k t ≠ y := fun t ht htt e =>
    htt (hk.2 (hI t ht) (hI t₀ ht₀I) e)
  rintro (htip | hbr)
  · -- an interior point of an arc has order at least two
    have hy0 : y ≠ k 0 := fun e => by
      have := hk.2 (hI t₀ ht₀I) ⟨le_rfl, zero_le_one⟩ e; linarith [ht₀.1]
    have hy1 : y ≠ k 1 := fun e => by
      have := hk.2 (hI t₀ ht₀I) ⟨zero_le_one, le_rfl⟩ e; linarith [ht₀.2]
    have := two_le_order_of_mem_arc hD hk.isArcBetween ⟨t₀, hI t₀ ht₀I, rfl⟩ hy0 hy1
    rw [show order y = 1 from htip] at this; exact absurd this (by decide)
  · -- a third component, approached by points off the arc
    have hcy := hne c ⟨le_rfl, hcd.le⟩ ht₀.1.ne
    have hdy := hne d ⟨hcd.le, le_rfl⟩ ht₀.2.ne'
    obtain ⟨S, hSy, hS3, hSinj⟩ := exists_points_of_le_order (show ((3 : ℕ) : ℕ∞) ≤ order y
      from hbr)
    obtain ⟨w, hwS, hw1, hw2⟩ : ∃ w ∈ S, connectedComponentIn {y}ᶜ w ≠
        connectedComponentIn {y}ᶜ (k c) ∧ connectedComponentIn {y}ᶜ w ≠
        connectedComponentIn {y}ᶜ (k d) := by
      by_contra hall
      push_neg at hall
      have hsub : connectedComponentIn {y}ᶜ '' S ⊆
          {connectedComponentIn {y}ᶜ (k c), connectedComponentIn {y}ᶜ (k d)} := by
        rintro _ ⟨w, hw, rfl⟩
        by_cases h1 : connectedComponentIn {y}ᶜ w = connectedComponentIn {y}ᶜ (k c)
        · exact Or.inl h1
        · exact Or.inr (hall w hw h1)
      have := encard_le_encard hsub
      rw [hSinj.encard_image, hS3] at this
      have h2' : ((3 : ℕ) : ℕ∞) ≤ 2 := this.trans ((encard_insert_le _ _).trans
        (by rw [encard_singleton]; rfl))
      exact absurd h2' (by decide)
    have hwy : w ≠ y := hSy hwS
    have hxy : x ≠ y := fun e => hr.ne (by rw [← hsph t₀ ht₀I, e]; exact (dist_self _).symm)
    set m := min (dist y (k c)) (dist y (k d))
    have hm : 0 < m := lt_min (dist_pos.2 (Ne.symm hcy)) (dist_pos.2 (Ne.symm hdy))
    obtain ⟨z, hzC, hzy⟩ := Metric.mem_closure_iff.1 (mem_closure_cc hwy)
      (min (m / 2) (dist y x)) (lt_min (by positivity) (dist_pos.2 (Ne.symm hxy)))
    have hzy' : dist z y < m / 2 := by rw [dist_comm]; exact hzy.trans_le (min_le_left _ _)
    have hzx : z ≠ x := fun e => by
      rw [e] at hzy; exact lt_irrefl _ (hzy.trans_le (min_le_right _ _))
    -- `z` is not on the arc: the two halves lie in the components of its ends
    have hhalf : ∀ t ∈ Icc c d, t ≠ t₀ → connectedComponentIn {y}ᶜ (k t) =
        connectedComponentIn {y}ᶜ (k c) ∨ connectedComponentIn {y}ᶜ (k t) =
        connectedComponentIn {y}ᶜ (k d) := by
      intro t ht htt
      rcases lt_or_gt_of_ne htt with h | h
      · left
        have hpc : IsPreconnected (k '' Icc c t) := hk.isPreconnected_image
        have hsub : k '' Icc c t ⊆ {y}ᶜ := by
          rintro _ ⟨u, hu, rfl⟩
          exact hne u ⟨hu.1, hu.2.trans ht.2⟩ (by linarith [hu.2])
        exact (connectedComponentIn_eq (hpc.subset_connectedComponentIn
          ⟨c, ⟨le_rfl, ht.1⟩, rfl⟩ hsub ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩)).symm
      · right
        have hpc : IsPreconnected (k '' Icc t d) := hk.isPreconnected_image
        have hsub : k '' Icc t d ⊆ {y}ᶜ := by
          rintro _ ⟨u, hu, rfl⟩
          exact hne u ⟨ht.1.trans hu.1, hu.2⟩ (by linarith [hu.1])
        exact connectedComponentIn_eq (hpc.subset_connectedComponentIn
          ⟨t, ⟨le_rfl, ht.2⟩, rfl⟩ hsub ⟨d, ⟨ht.2, le_rfl⟩, rfl⟩)
    have hzI : ∀ t ∈ Icc c d, k t ≠ z := by
      intro t ht e
      by_cases htt : t = t₀
      · rw [htt] at e; exact (connectedComponentIn_subset _ _ hzC : z ∈ ({y}ᶜ : Set T)) e.symm
      have hz' : connectedComponentIn {y}ᶜ z = connectedComponentIn {y}ᶜ w :=
        (connectedComponentIn_eq hzC).symm
      rcases hhalf t ht htt with h | h <;> rw [e, hz'] at h
      · exact hw1 h
      · exact hw2 h
    rcases sphere_strictMonoOn h2 hk hc hcd.le hd hr hsph hzI hzx with hmono | hanti
    · have := hmono ⟨le_rfl, hcd.le⟩ ht₀I ht₀.1
      simp only at this
      have h1 := dist_triangle y z (k c)
      have h3 : m ≤ dist y (k c) := min_le_left _ _
      rw [dist_comm y z] at h1; linarith
    · have := hanti ht₀I ⟨hcd.le, le_rfl⟩ ht₀.2
      simp only at this
      have h1 := dist_triangle y z (k d)
      have h3 : m ≤ dist y (k d) := min_le_right _ _
      rw [dist_comm y z] at h1; linarith

end Sphere

section Tree

variable [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T]
  (hT : TreeHyp T) (h2 : MidsetsAtMostTwo T)
include hT h2

/-- **Lemma 6.2 (c)**, second part: a spherical arc lies in one edge. -/
theorem sphere_in_edge {k : ℝ → T} (hk : IsArcParam k) {c d : ℝ} (hc : 0 ≤ c) (hcd : c < d)
    (hd : d ≤ 1) {x : T} {r : ℝ} (hr : 0 < r) (hsph : ∀ t ∈ Icc c d, dist x (k t) = r) :
    ∃ ℓ, IsEdge ℓ ∧ k '' Icc c d ⊆ ℓ := by
  set t₀ := (c + d) / 2
  have ht₀ : t₀ ∈ Ioo c d := ⟨by simp only [t₀]; linarith, by simp only [t₀]; linarith⟩
  have hV := no_vertex_inside h2 hT.noSCC hk hc hcd hd hr hsph ht₀
  refine ⟨_, isEdge_closure_cc hT hV, ?_⟩
  have hsub : k '' Ioo c d ⊆ connectedComponentIn (vertices T)ᶜ (k t₀) :=
    hk.isPreconnected_image_Ioo.subset_connectedComponentIn ⟨t₀, ht₀, rfl⟩
      (by rintro _ ⟨t, ht, rfl⟩; exact no_vertex_inside h2 hT.noSCC hk hc hcd hd hr hsph ht)
  calc k '' Icc c d = k '' closure (Ioo c d) := by rw [closure_Ioo hcd.ne]
    _ ⊆ closure (k '' Ioo c d) := image_closure_subset_closure_image hk.1
    _ ⊆ _ := closure_mono hsub

/-- An arc parametrization of a spherical arc contains, inside a fixed edge parametrization,
a spherical subarc with rational parameters. -/
theorem exists_rational_subarc {γ : ℝ → T} (hγ : IsEdgeParam γ) {A : Set T}
    (hA : IsPreconnected A) (hAℓ : A ⊆ γ '' Icc 0 1) {p q : T} (hp : p ∈ A) (hq : q ∈ A)
    (hpq : p ≠ q) : ∃ q₁ q₂ : ℚ, 0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) < q₂ ∧ (q₂ : ℝ) ≤ 1 ∧
      γ '' Icc (q₁ : ℝ) q₂ ⊆ A := by
  obtain ⟨α, hα, rfl⟩ := hAℓ hp
  obtain ⟨β, hβ, rfl⟩ := hAℓ hq
  have hαβ : α ≠ β := fun e => hpq (e ▸ rfl)
  obtain ⟨k, hk, hk0, hk1, hkim⟩ := hγ.arc.exists_subarc hα hβ hαβ
  have hseg : seg (γ α) (γ β) = γ '' uIcc α β := by
    rw [← hkim, seg_eq hT.noSCC (show IsArcBetween (k '' Icc 0 1) (γ α) (γ β) by
      have := hk.isArcBetween; rwa [hk0, hk1] at this)]
  have hsub : γ '' uIcc α β ⊆ A := hseg ▸ seg_subset hT.noSCC hA hp hq
  rcases lt_or_gt_of_ne hαβ with h | h
  · obtain ⟨q₁, hq₁⟩ := exists_rat_btwn h
    obtain ⟨q₂, hq₂⟩ := exists_rat_btwn hq₁.2
    refine ⟨q₁, q₂, hα.1.trans hq₁.1.le, hq₂.1, hq₂.2.le.trans hβ.2, ?_⟩
    refine (image_mono fun t ht => ?_).trans hsub
    rw [uIcc_of_le h.le]; exact ⟨hq₁.1.le.trans ht.1, ht.2.trans hq₂.2.le⟩
  · obtain ⟨q₁, hq₁⟩ := exists_rat_btwn h
    obtain ⟨q₂, hq₂⟩ := exists_rat_btwn hq₁.2
    refine ⟨q₁, q₂, hβ.1.trans hq₁.1.le, hq₂.1, hq₂.2.le.trans hα.2, ?_⟩
    refine (image_mono fun t ht => ?_).trans hsub
    rw [uIcc_of_ge h.le]; exact ⟨hq₁.1.le.trans ht.1, ht.2.trans hq₂.2.le⟩

/-- **Lemma 6.2 (d)**: the set of centers of spherical arcs is countable. -/
theorem centers_countable : {x : T | ∃ I r, IsSphericalArc I x r}.Countable := by
  classical
  have hne : Nonempty (ℝ → T) := ⟨fun _ => Classical.arbitrary T⟩
  have hP : ∀ ℓ ∈ {ℓ : Set T | IsEdge ℓ}, ∃ γ : ℝ → T, IsEdgeParam γ ∧ γ '' Icc 0 1 = ℓ :=
    fun ℓ hℓ => exists_param_of_isEdge hT hℓ
  choose! P hPe hPim using hP
  set Cent : Set T × ℚ × ℚ → Set T := fun e => {x | ∃ r > 0, ∀ t ∈ Icc (e.2.1 : ℝ) e.2.2,
    dist x (P e.1 t) = r}
  have hsub : {x : T | ∃ I r, IsSphericalArc I x r} ⊆
      ⋃ e ∈ {e : Set T × ℚ × ℚ | IsEdge e.1 ∧ 0 ≤ (e.2.1 : ℝ) ∧ (e.2.1 : ℝ) < e.2.2 ∧
        (e.2.2 : ℝ) ≤ 1}, Cent e := by
    rintro x ⟨I, r, ⟨hI, hr, hIs⟩⟩
    obtain ⟨p, q, hpq⟩ := hI.exists_isArcBetween
    obtain ⟨k, hk, hkim, hk0, hk1⟩ := hpq.exists_param
    have hsph : ∀ t ∈ Icc (0 : ℝ) 1, dist x (k t) = r := fun t ht => by
      have := hIs (hkim ▸ ⟨t, ht, rfl⟩ : k t ∈ I); rw [mem_sphere, dist_comm] at this; exact this
    obtain ⟨ℓ, hℓ, hIℓ⟩ := sphere_in_edge hT h2 hk le_rfl zero_lt_one le_rfl hr hsph
    rw [hkim, ← hPim ℓ hℓ] at hIℓ
    obtain ⟨q₁, q₂, h1, h12, h2', hsubI⟩ := exists_rational_subarc hT h2 (hPe ℓ hℓ)
      (hkim ▸ hk.isPreconnected_image) hIℓ hpq.left_mem hpq.right_mem hpq.ne
    refine mem_biUnion (x := (ℓ, q₁, q₂)) ⟨hℓ, h1, h12, h2'⟩ ⟨r, hr, fun t ht => ?_⟩
    have := hIs (hsubI ⟨t, ht, rfl⟩); rw [mem_sphere, dist_comm] at this; exact this
  refine Countable.mono hsub (Countable.biUnion ?_ fun e he => (Subsingleton.countable ?_))
  · have hE : {ℓ : Set T | IsEdge ℓ}.Countable := hT.edges_finite.countable
    refine Countable.mono ?_ (hE.prod (Set.countable_univ.prod Set.countable_univ))
    intro e he
    exact ⟨he.1, mem_univ _, mem_univ _⟩
  · rintro x ⟨r, hr, hx⟩ x' ⟨r', hr', hx'⟩
    exact (sphere_center_unique h2 (hPe e.1 he.1).arc he.2.1 he.2.2.1 he.2.2.2 hr hx hr' hx').symm


omit hT h2 in
/-- A function strictly monotone (or antitone) on `[c, d]` has no local extremum inside. -/
theorem not_isLocalExtr_of_strictMono {f : ℝ → ℝ} {c d s : ℝ} (hs : s ∈ Ioo c d)
    (hf : StrictMonoOn f (Icc c d) ∨ StrictAntiOn f (Icc c d)) : ¬ IsLocalExtr f s := by
  intro hloc
  have key : ∃ ε > 0, ∀ y, dist y s < ε → y ∈ Icc c d := by
    refine ⟨min (s - c) (d - s), lt_min (by linarith [hs.1]) (by linarith [hs.2]), fun y hy => ?_⟩
    rw [Real.dist_eq, abs_lt] at hy
    exact ⟨by linarith [min_le_left (s - c) (d - s)], by linarith [min_le_right (s - c) (d - s)]⟩
  obtain ⟨ε₀, hε₀, hI⟩ := key
  have hsI : s ∈ Icc c d := Ioo_subset_Icc_self hs
  -- two test points on both sides inside any given radius
  have test : ∀ ε₁ > 0, ∃ y₁ y₂, y₁ < s ∧ s < y₂ ∧ y₁ ∈ Icc c d ∧ y₂ ∈ Icc c d ∧
      dist y₁ s < ε₁ ∧ dist y₂ s < ε₁ := by
    intro ε₁ hε₁
    set ε := min ε₀ ε₁ / 2
    have hε : 0 < ε := by positivity
    have hεlt : ε < min ε₀ ε₁ := by simp only [ε]; linarith [lt_min hε₀ hε₁]
    have d1 : dist (s - ε) s < min ε₀ ε₁ := by
      rw [Real.dist_eq, show s - ε - s = -ε by ring, abs_neg, abs_of_pos hε]; exact hεlt
    have d2 : dist (s + ε) s < min ε₀ ε₁ := by
      rw [Real.dist_eq, show s + ε - s = ε by ring, abs_of_pos hε]; exact hεlt
    exact ⟨s - ε, s + ε, by linarith, by linarith, hI _ (d1.trans_le (min_le_left _ _)),
      hI _ (d2.trans_le (min_le_left _ _)), d1.trans_le (min_le_right _ _),
      d2.trans_le (min_le_right _ _)⟩
  rcases hloc with h | h
  · obtain ⟨ε₁, hε₁, hb⟩ := Metric.eventually_nhds_iff.1 h
    obtain ⟨y₁, y₂, l1, l2, m1, m2, d1, d2⟩ := test ε₁ hε₁
    have b1 : f s ≤ f y₁ := hb d1
    have b2 : f s ≤ f y₂ := hb d2
    rcases hf with hf | hf
    · exact not_le.2 (hf m1 hsI l1) b1
    · exact not_le.2 (hf hsI m2 l2) b2
  · obtain ⟨ε₁, hε₁, hb⟩ := Metric.eventually_nhds_iff.1 h
    obtain ⟨y₁, y₂, l1, l2, m1, m2, d1, d2⟩ := test ε₁ hε₁
    have b1 : f y₁ ≤ f s := hb d1
    have b2 : f y₂ ≤ f s := hb d2
    rcases hf with hf | hf
    · exact not_le.2 (hf hsI m2 l2) b2
    · exact not_le.2 (hf m1 hsI l1) b1

/-- **Lemma 6.2** (intrinsic form). Let `I` be a spherical arc with center `x` and radius `r`.
(a) for every `y ∉ I ∪ {x}`, `h_y` is injective (equivalently, strictly monotone) on `I`;
(b) the center is unique, and every nondegenerate subarc of `I` is spherical with the same center;
(c) no point of `I` other than its ends is a vertex, and `I` lies in one edge;
(d) the set of centers of spherical arcs is countable. -/
theorem lemma_6_2 {I : Set T} {x : T} {r : ℝ} (hI : IsSphericalArc I x r) :
    (∀ y, y ∉ I → y ≠ x → InjOn (dist y) I) ∧
    ((∀ x' r', I ⊆ sphere x' r' → x' = x) ∧ ∀ J ⊆ I, IsArc J → IsSphericalArc J x r) ∧
    ((∀ p q, IsArcBetween I p q → ∀ z ∈ I, z ≠ p → z ≠ q → z ∉ vertices T) ∧
      ∃ ℓ, IsEdge ℓ ∧ I ⊆ ℓ) ∧
    {x : T | ∃ I r, IsSphericalArc I x r}.Countable := by
  obtain ⟨hIa, hr, hIs⟩ := hI
  obtain ⟨p, q, hpq⟩ := hIa.exists_isArcBetween
  obtain ⟨k, hk, hkim, hk0, hk1⟩ := hpq.exists_param
  have hsph : ∀ t ∈ Icc (0 : ℝ) 1, dist x (k t) = r := fun t ht => by
    have := hIs (hkim ▸ ⟨t, ht, rfl⟩ : k t ∈ I); rw [mem_sphere, dist_comm] at this; exact this
  refine ⟨?_, ⟨?_, fun J hJ hJa => ⟨hJa, hr, hJ.trans hIs⟩⟩, ⟨?_, ?_⟩, centers_countable hT h2⟩
  · intro y hy hyx
    have hyI : ∀ t ∈ Icc (0 : ℝ) 1, k t ≠ y := fun t ht e => hy (hkim ▸ ⟨t, ht, e⟩)
    have hmono := sphere_strictMonoOn h2 hk le_rfl zero_le_one le_rfl hr hsph hyI hyx
    rw [← hkim]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    rcases hmono with h | h
    · exact congrArg k (h.injOn hu hv huv)
    · exact congrArg k (h.injOn hu hv huv)
  · intro x' r' hx'
    by_cases hr' : 0 < r'
    · have hsph' : ∀ t ∈ Icc (0 : ℝ) 1, dist x' (k t) = r' := fun t ht => by
        have := hx' (hkim ▸ ⟨t, ht, rfl⟩ : k t ∈ I); rw [mem_sphere, dist_comm] at this
        exact this
      exact sphere_center_unique h2 hk le_rfl zero_lt_one le_rfl hr hsph hr' hsph'
    · exfalso
      have h0 := hx' (hkim ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ : k 0 ∈ I)
      have h1 := hx' (hkim ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩ : k 1 ∈ I)
      rw [mem_sphere] at h0 h1
      have e0 : k 0 = x' := dist_le_zero.1 (h0.le.trans (not_lt.1 hr'))
      have e1 : k 1 = x' := dist_le_zero.1 (h1.le.trans (not_lt.1 hr'))
      exact zero_ne_one (hk.2 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ (e0.trans e1.symm))
  · intro p' q' hpq' z hz hzp hzq
    obtain ⟨k', hk', hkim', hk0', hk1'⟩ := hpq'.exists_param
    have hsph' : ∀ t ∈ Icc (0 : ℝ) 1, dist x (k' t) = r := fun t ht => by
      have := hIs (hkim' ▸ ⟨t, ht, rfl⟩ : k' t ∈ I); rw [mem_sphere, dist_comm] at this
      exact this
    obtain ⟨s, hs, rfl⟩ : z ∈ k' '' Icc 0 1 := hkim' ▸ hz
    have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (fun e => hzp (by rw [← e, hk0'])),
      lt_of_le_of_ne hs.2 (fun e => hzq (by rw [e, hk1']))⟩
    exact no_vertex_inside h2 hT.noSCC hk' le_rfl zero_lt_one le_rfl hr hsph' hs'
  · rw [← hkim]; exact sphere_in_edge hT h2 hk le_rfl zero_lt_one le_rfl hr hsph

omit h2 in
/-- **Lemma 6.3 (off-sphere parity).** Let `I` be a spherical arc with center `x` and radius `r`,
`p` an interior point of `I`, and `b ≠ p` with `h_x(b) ≠ r`. If `(p, b)` is strict, then
`N(p, b)` is even. -/
theorem lemma_6_3 (hDMP : HasDMP T) {I : Set T} {x : T} {r : ℝ} (hI : IsSphericalArc I x r)
    {e₁ e₂ : T} (hIe : IsArcBetween I e₁ e₂) {p : T} (hp : p ∈ I) (hp1 : p ≠ e₁) (hp2 : p ≠ e₂)
    {b : T} (hb : dist x b ≠ r) (h : IsStrictPair p b) : Even (oddCount p b) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  obtain ⟨-, -, -, h4⟩ := cor_5_5 hT hDMP h
  obtain ⟨y₁, t, -, -, ht⟩ := h4 hodd
  have htM : dist t p = dist t b := sgnf_eq_zero_iff.1 ht.2.1
  have hxp : dist x p = r := by rw [dist_comm]; exact hI.2.2 hp
  have htp : t ≠ p := by
    intro e; subst e; exact (sgnf_left_neg h.1).ne ht.2.1
  have htx : t ≠ x := by
    intro e; subst e; exact hb (htM.symm.trans hxp)
  have hloc : IsLocalExtr (dist t) p := (touch_isLocalExtr hT hDMP h hodd ht).1
  obtain ⟨k, hk, hkim, hk0, hk1⟩ := hIe.exists_param
  obtain ⟨s₀, hs₀, rfl⟩ : p ∈ k '' Icc 0 1 := hkim ▸ hp
  have hs₀' : s₀ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs₀.1 (fun e => hp1 (by rw [← e, hk0])),
    lt_of_le_of_ne hs₀.2 (fun e => hp2 (by rw [e, hk1]))⟩
  have hev : ∀ᶠ s in 𝓝 s₀, k s ≠ t := hk.1.continuousAt.eventually_ne (Ne.symm htp)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set δ' := min (δ / 2) (min (s₀ / 2) ((1 - s₀) / 2))
  have hδ' : 0 < δ' := lt_min (by linarith) (lt_min (by linarith [hs₀'.1]) (by linarith [hs₀'.2]))
  have hδ1 : δ' ≤ δ / 2 := min_le_left _ _
  have hδ2 : δ' ≤ s₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ' ≤ (1 - s₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hc : 0 ≤ s₀ - δ' := by linarith
  have hd : s₀ + δ' ≤ 1 := by linarith
  have hcd : s₀ - δ' ≤ s₀ + δ' := by linarith
  have hsph : ∀ s ∈ Icc (s₀ - δ') (s₀ + δ'), dist x (k s) = r := fun s hs => by
    have := hI.2.2 (hkim ▸ ⟨s, ⟨hc.trans hs.1, hs.2.trans hd⟩, rfl⟩ : k s ∈ I)
    rw [mem_sphere, dist_comm] at this; exact this
  have hyI : ∀ s ∈ Icc (s₀ - δ') (s₀ + δ'), k s ≠ t := fun s hs => hball (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hmono := sphere_strictMonoOn h2 hk hc hcd hd hI.2.1 hsph hyI htx
  exact not_isLocalExtr_of_strictMono ⟨by linarith, by linarith⟩ hmono
    (hloc.comp_continuous hk.1.continuousAt)

end Tree

end DoubleMidset
