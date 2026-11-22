module

public import DoubleMidset.Order
public import DoubleMidset.Circle
public import DoubleMidset.Classical.Bump
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Reduction to dendrites (Section 3)

* `boundary_bumping_open`: a component of a proper open subset `U` of a continuum has a closure
  point outside `U` (the form of boundary bumping used in Proposition 3.1).
* **Proposition 3.1** (`prop_3_1`, Loveland–Wayment): a continuum all of whose midsets are finite
  is locally connected.
* **Proposition 3.2** (`prop_3_2`): if `|M(a, b)| ≤ 2` for all distinct `a, b`, a simple closed
  curve in `X` is all of `X`.
* **Corollary 3.4** (`cor_3_4`): a continuum with the DMP is a simple closed curve or a dendrite.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {X : Type u} [MetricSpace X]

theorem sgnf_lipschitz_left (a a' b y : X) : |sgnf a' b y - sgnf a b y| ≤ dist a a' := by
  unfold sgnf
  have h1 := dist_triangle y a a'
  have h2 := dist_triangle y a' a
  rw [abs_le]; constructor <;> linarith [dist_comm a a']

theorem sgnf_lipschitz_right (a b b' y : X) : |sgnf a b' y - sgnf a b y| ≤ dist b b' := by
  unfold sgnf
  have h1 := dist_triangle y b b'
  have h2 := dist_triangle y b' b
  rw [abs_le]; constructor <;> linarith [dist_comm b b']

theorem continuous_sgnf (a b : X) : Continuous (sgnf a b) :=
  (continuous_id.dist continuous_const).sub (continuous_id.dist continuous_const)

theorem sgnf_eq_zero_iff {a b y : X} : sgnf a b y = 0 ↔ y ∈ midset a b := by
  unfold sgnf midset; rw [mem_setOf_eq, sub_eq_zero]

/-- `f` is `2`-Lipschitz in the observer. -/
theorem abs_sgnf_sub_le (a b y z : X) : |sgnf a b y - sgnf a b z| ≤ 2 * dist y z := by
  unfold sgnf
  have h1 := dist_triangle y z a
  have h2 := dist_triangle z y a
  have h3 := dist_triangle y z b
  have h4 := dist_triangle z y b
  rw [abs_le]; constructor <;> linarith [dist_comm y z]

section Bumping

variable [CompactSpace X] [ConnectedSpace X]

/-- **Boundary bumping** for components of open sets: if `U ≠ X` is open and `x ∈ U`, the
closure of the component of `U` containing `x` meets `X \ U`. -/
theorem boundary_bumping_open {U : Set X} (hU : IsOpen U) (hUne : U ≠ univ) {x : X} (hx : x ∈ U) :
    (closure (connectedComponentIn U x) \ U).Nonempty := by
  set D := connectedComponentIn U x
  by_contra h
  have hclU : closure D ⊆ U := fun y hy => by by_contra hyU; exact h ⟨y, hy, hyU⟩
  have hclD : closure D ⊆ D :=
    isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx)) hclU
  have hDc : IsCompact D := (closure_subset_iff_isClosed.1 hclD).isCompact
  obtain ⟨δ, hδ, hδU⟩ := hDc.exists_thickening_subset_open hU
    ((subset_closure).trans hclU)
  set V := thickening (δ / 2) D
  have hVo : IsOpen V := isOpen_thickening
  have hDV : D ⊆ V := self_subset_thickening (by positivity) D
  have hclV : closure V ⊆ U :=
    (closure_thickening_subset_cthickening _ _).trans
      ((cthickening_subset_thickening' hδ (by linarith) D).trans hδU)
  have hVne : V ≠ univ := fun e => hUne (eq_univ_of_univ_subset (e ▸ subset_closure.trans hclV))
  obtain ⟨y, hy1, hy2⟩ := boundary_bumping hVo hVne (subset_closure (hDV
    (mem_connectedComponentIn hx)))
  have : connectedComponentIn (closure V) x ⊆ D :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (subset_closure (hDV (mem_connectedComponentIn hx))))
      ((connectedComponentIn_subset _ _).trans hclV)
  exact hy2.2 (hDV (this hy1))

end Bumping

/-- **Proposition 3.1** (Loveland–Wayment). A continuum in which every midset of distinct points
is finite is locally connected. -/
theorem prop_3_1 [CompactSpace X] [ConnectedSpace X] [Nontrivial X]
    (hfin : ∀ a b : X, a ≠ b → (midset a b).Finite) : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  by_contra hnot
  push_neg at hnot
  obtain ⟨W, hWo, x, hxW, hQ⟩ := hnot
  -- a point `p` of the component `Q` which is not interior to it
  obtain ⟨p, hpQ, hpint⟩ : ∃ p ∈ connectedComponentIn W x,
      connectedComponentIn W x ∉ 𝓝 p := by
    by_contra h; push_neg at h; exact hQ (isOpen_iff_mem_nhds.2 h)
  have hpW : p ∈ W := connectedComponentIn_subset _ _ hpQ
  have hQp : connectedComponentIn W p = connectedComponentIn W x :=
    (connectedComponentIn_eq hpQ).symm
  obtain ⟨y₀, hy₀⟩ := exists_ne p
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hWo p hpW
  set ε := min r (dist p y₀)
  have hε : 0 < ε := lt_min hr (dist_pos.2 hy₀.symm)
  set U := ball p ε
  have hUW : U ⊆ W := (ball_subset_ball (min_le_left _ _)).trans hrW
  have hUne : U ≠ univ := fun e => by
    have : y₀ ∈ U := e ▸ mem_univ y₀
    rw [mem_ball, dist_comm] at this; exact (lt_irrefl _ (this.trans_le (min_le_right _ _)))
  have hpU : p ∈ U := mem_ball_self hε
  set C := connectedComponentIn U p
  have hCQ : C ⊆ connectedComponentIn W x := by
    rw [← hQp]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hpU) ((connectedComponentIn_subset _ _).trans hUW)
  -- components of `U` are closed in `U`
  have hcl : ∀ y ∈ U, ∀ z ∈ closure (connectedComponentIn U y), z ∈ U →
      z ∈ connectedComponentIn U y := by
    intro y hy z hz hzU
    have hpc : IsPreconnected (insert z (connectedComponentIn U y)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset hz subset_closure)
    exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hy))
      (insert_subset hzU (connectedComponentIn_subset _ _)) (mem_insert z _)
  -- the family of other components coming within `ε / 4` of `p` is infinite
  set 𝒟 : Set (Set X) := {D | ∃ y ∈ U, D = connectedComponentIn U y ∧ D ≠ C ∧
    (D ∩ ball p (ε / 4)).Nonempty}
  have h𝒟 : 𝒟.Infinite := by
    intro hfin𝒟
    have hpK : p ∉ ⋃₀ (closure '' 𝒟) := by
      rintro ⟨_, ⟨D, ⟨y, hy, rfl, hne, -⟩, rfl⟩, h⟩
      exact hne (connectedComponentIn_eq (hcl y hy p h hpU))
    have hKc : IsClosed (⋃₀ (closure '' 𝒟)) :=
      (hfin𝒟.image closure).isClosed_sUnion fun _ ⟨D, _, hD⟩ => hD ▸ isClosed_closure
    obtain ⟨s₀, hs₀, hsub⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl p hpK
    have hsD : ∀ D ∈ 𝒟, Disjoint (ball p s₀) D := fun D hD =>
      disjoint_left.2 fun z hz hzD => hsub hz ⟨_, ⟨D, hD, rfl⟩, subset_closure hzD⟩
    have hball : ball p (min s₀ (ε / 4)) ⊆ C := by
      intro z hz
      have hzU : z ∈ U := ball_subset_ball ((min_le_right _ _).trans (by linarith)) hz
      by_contra hzC
      have hD : connectedComponentIn U z ∈ 𝒟 := ⟨z, hzU, rfl, fun e => hzC (e ▸
        mem_connectedComponentIn hzU), z, mem_connectedComponentIn hzU,
          ball_subset_ball (min_le_right _ _) hz⟩
      exact disjoint_left.1 (hsD _ hD) (ball_subset_ball (min_le_left _ _) hz)
        (mem_connectedComponentIn hzU)
    exact hpint (Filter.mem_of_superset (ball_mem_nhds p (lt_min hs₀ (by positivity)))
      (hball.trans hCQ))
  -- an injective sequence of such components, and boundary points `q n`
  set e := h𝒟.natEmbedding
  have hmem : ∀ n, ∃ y ∈ U, (e n : Set X) = connectedComponentIn U y ∧
      ((e n : Set X) ∩ ball p (ε / 4)).Nonempty := by
    intro n
    obtain ⟨y, hy, he, -, hb⟩ := (e n).2
    exact ⟨y, hy, he, hb⟩
  choose y hyU hye hball using hmem
  have hq : ∀ n, ∃ q ∈ closure (e n : Set X), dist p q = ε := by
    intro n
    obtain ⟨q, hqcl, hqU⟩ := boundary_bumping_open isOpen_ball hUne (hyU n)
    refine ⟨q, (hye n).symm ▸ hqcl, ?_⟩
    have h1 : q ∈ closedBall p ε := closure_ball_subset_closedBall
      (closure_mono (connectedComponentIn_subset _ _) hqcl)
    rw [mem_closedBall, dist_comm] at h1
    rw [mem_ball, dist_comm] at hqU
    linarith
  choose q hqcl hqd using hq
  obtain ⟨q₀, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq q
  have hq₀ : dist p q₀ = ε := by
    have : Tendsto (fun n => dist p (q (φ n))) atTop (𝓝 (dist p q₀)) :=
      tendsto_const_nhds.dist hlim
    simp only [hqd] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hpq : p ≠ q₀ := fun h => by rw [← h, dist_self] at hq₀; linarith
  -- for large `n`, the component `e (φ n)` contains a zero of `f_{p,q₀}`
  have hev : ∀ᶠ n in atTop, dist (q (φ n)) q₀ < ε / 4 :=
    (tendsto_iff_dist_tendsto_zero.1 hlim).eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hzero : ∀ n, N ≤ n → ∃ z ∈ (e (φ n) : Set X), z ∈ midset p q₀ := by
    intro n hn
    obtain ⟨a, haD, hap⟩ := hball (φ n)
    obtain ⟨b, hbD, hbq⟩ : ∃ b ∈ (e (φ n) : Set X), dist b q₀ < ε / 2 := by
      obtain ⟨b, hbD, hb⟩ := Metric.mem_closure_iff.1 (hqcl (φ n)) (ε / 4) (by positivity)
      refine ⟨b, hbD, ?_⟩
      have := hN n hn
      linarith [dist_triangle b (q (φ n)) q₀, dist_comm (q (φ n)) b]
    have hpc : IsPreconnected (e (φ n) : Set X) := by
      rw [hye]; exact isPreconnected_connectedComponentIn
    have hfa : sgnf p q₀ a < 0 := by
      have := abs_sgnf_sub_le p q₀ a p
      rw [mem_ball] at hap
      have hfp : sgnf p q₀ p = -ε := by unfold sgnf; rw [dist_self, hq₀]; ring
      rw [abs_le] at this; linarith
    have hfb : 0 < sgnf p q₀ b := by
      have := abs_sgnf_sub_le p q₀ b q₀
      have hfq : sgnf p q₀ q₀ = ε := by unfold sgnf; rw [dist_self, dist_comm, hq₀]; ring
      rw [abs_le] at this; linarith
    obtain ⟨z, hzD, hz⟩ := hpc.intermediate_value haD hbD (continuous_sgnf p q₀).continuousOn
      ⟨hfa.le, hfb.le⟩
    exact ⟨z, hzD, sgnf_eq_zero_iff.1 hz⟩
  choose! z hzD hzM using hzero
  -- the zeros are distinct, as the components are disjoint
  have hinj : InjOn z (Ici N) := by
    intro m hm n hn hmn
    by_contra hne
    have hφne : φ m ≠ φ n := fun h => hne (hφ.injective h)
    have hene : (e (φ m) : Set X) ≠ e (φ n) := fun h =>
      hφne (e.injective (Subtype.ext h))
    have hdisj : Disjoint (e (φ m) : Set X) (e (φ n)) := by
      rw [hye (φ m), hye (φ n)]
      by_contra hd
      obtain ⟨w, hw1, hw2⟩ := not_disjoint_iff.1 hd
      apply hene
      rw [hye (φ m), hye (φ n), connectedComponentIn_eq hw1, connectedComponentIn_eq hw2]
    exact disjoint_left.1 hdisj (hzD m hm) (hmn ▸ hzD n hn)
  have hinf : (z '' Ici N).Infinite := (Set.Ici_infinite N).image hinj
  exact hinf ((hfin p q₀ hpq).subset (by rintro _ ⟨n, hn, rfl⟩; exact hzM n hn))

theorem three_le_encard_midset {a b x y z : X} (hx : x ∈ midset a b) (hy : y ∈ midset a b)
    (hz : z ∈ midset a b) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 ≤ (midset a b).encard := by
  have : ({x, y, z} : Set X).encard = 3 := by
    rw [encard_insert_of_notMem (by simp [hxy, hxz]), encard_pair hyz]; rfl
  rw [← this]
  exact encard_le_encard (by rintro w (rfl | rfl | rfl) <;> assumption)

/-- A continuous function on `[0, 1]` with equal values at the ends takes some value twice
on `[0, 1)`. -/
theorem exists_eq_of_eq_ends {g : ℝ → ℝ} (hg : Continuous g) (h01 : g 0 = g 1) :
    ∃ s t, 0 ≤ s ∧ s < t ∧ t < 1 ∧ g s = g t := by
  by_cases hc : ∀ t ∈ Ioo (0 : ℝ) 1, g t = g 0
  · exact ⟨1 / 3, 2 / 3, by norm_num, by norm_num, by norm_num,
      (hc _ ⟨by norm_num, by norm_num⟩).trans (hc _ ⟨by norm_num, by norm_num⟩).symm⟩
  push_neg at hc
  obtain ⟨t, ht, hne⟩ := hc
  set v := (g 0 + g t) / 2
  have hivt : ∀ a b : ℝ, a ≤ b → (g a < v ∧ v < g b ∨ g b < v ∧ v < g a) →
      ∃ c ∈ Ioo a b, g c = v := by
    intro a b hab h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hab hg.continuousOn ⟨h1.le, h2.le⟩
      exact ⟨c, ⟨lt_of_le_of_ne hc.1 (fun e => by rw [← e] at hcv; linarith),
        lt_of_le_of_ne hc.2 (fun e => by rw [e] at hcv; linarith)⟩, hcv⟩
    · obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc' hab hg.continuousOn ⟨h1.le, h2.le⟩
      exact ⟨c, ⟨lt_of_le_of_ne hc.1 (fun e => by rw [← e] at hcv; linarith),
        lt_of_le_of_ne hc.2 (fun e => by rw [e] at hcv; linarith)⟩, hcv⟩
  have hside : g 0 < v ∧ v < g t ∨ g t < v ∧ v < g 0 := by
    rcases lt_or_gt_of_ne hne with h | h
    · right; constructor <;> simp only [v] <;> linarith
    · left; constructor <;> simp only [v] <;> linarith
  obtain ⟨s₁, hs₁, hs₁v⟩ := hivt 0 t ht.1.le hside
  obtain ⟨s₂, hs₂, hs₂v⟩ := hivt t 1 ht.2.le (by rw [← h01]; tauto)
  exact ⟨s₁, s₂, hs₁.1.le, hs₁.2.trans hs₂.1, hs₂.2, hs₁v.trans hs₂v.symm⟩

/-- **Proposition 3.2.** If `|M(a, b)| ≤ 2` for all distinct `a, b`, every simple closed curve in
`X` is all of `X`. -/
theorem prop_3_2 (h2 : MidsetsAtMostTwo X) {C : Set X} (hC : IsSimpleClosedCurve C) : C = univ := by
  refine eq_univ_of_forall fun z => ?_
  by_contra hz
  obtain ⟨c, hc, hper, hinj, -, hIco⟩ := hC.exists_param
  have hcC : ∀ t, c t ∈ C := by
    intro t
    have : c (t - ⌊t⌋) = c t := by
      have key : ∀ n : ℕ, ∀ s, c (s + n) = c s := by
        intro n; induction n with
        | zero => intro s; simp
        | succ n ih => intro s; rw [Nat.cast_succ, ← add_assoc, hper, ih]
      rcases le_or_gt 0 ⌊t⌋ with h | h
      · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
        have := key n (t - ⌊t⌋); rw [hn] at this ⊢; push_cast at this ⊢
        rw [← this]; ring_nf
      · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat h.le
        have := key n t; rw [hn]; push_cast; rw [← this]; ring_nf
    rw [← this, ← hIco]
    exact ⟨_, ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, rfl⟩
  -- two parameters at the same distance from `z`
  obtain ⟨s, t, hs0, hst, ht1, he⟩ := exists_eq_of_eq_ends
    (show Continuous fun t => dist z (c t) from continuous_const.dist hc)
    (by have h1 := hper 0; rw [zero_add] at h1; show dist z (c 0) = dist z (c 1); rw [h1])
  have hsI : s ∈ Ico (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
  have htI : t ∈ Ico (0 : ℝ) 1 := ⟨hs0.trans hst.le, ht1⟩
  set a := c s
  set b := c t
  have hab : a ≠ b := fun h => hst.ne (hinj hsI htI h)
  have hzM : z ∈ midset a b := by
    exact he
  have hfa : sgnf a b (c s) < 0 := by
    unfold sgnf; rw [dist_self, zero_sub, neg_neg_iff_pos]; exact dist_pos.2 hab
  have hfb : 0 < sgnf a b (c t) := by
    unfold sgnf; rw [dist_self, sub_zero]; exact dist_pos.2 hab.symm
  have hfa' : sgnf a b (c (s + 1)) < 0 := by rw [hper]; exact hfa
  have hcont : Continuous fun u => sgnf a b (c u) := (continuous_sgnf a b).comp hc
  obtain ⟨u₁, hu₁, hu₁0⟩ := intermediate_value_Icc hst.le hcont.continuousOn ⟨hfa.le, hfb.le⟩
  obtain ⟨u₂, hu₂, hu₂0⟩ := intermediate_value_Icc' (show t ≤ s + 1 by linarith)
    hcont.continuousOn ⟨hfa'.le, hfb.le⟩
  have hu₁' : s < u₁ ∧ u₁ < t := ⟨lt_of_le_of_ne hu₁.1 (fun e => by rw [← e] at hu₁0; linarith),
    lt_of_le_of_ne hu₁.2 (fun e => by rw [e] at hu₁0; linarith)⟩
  have hu₂' : t < u₂ ∧ u₂ < s + 1 := ⟨lt_of_le_of_ne hu₂.1 (fun e => by rw [← e] at hu₂0; linarith),
    lt_of_le_of_ne hu₂.2 (fun e => by rw [e] at hu₂0; linarith)⟩
  have hM₁ : c u₁ ∈ midset a b := sgnf_eq_zero_iff.1 hu₁0
  have hM₂ : c u₂ ∈ midset a b := sgnf_eq_zero_iff.1 hu₂0
  have hne : c u₁ ≠ c u₂ := by
    intro h
    rcases lt_or_ge u₂ 1 with h1 | h1
    · exact (hu₁'.2.trans hu₂'.1).ne (hinj ⟨hs0.trans hu₁'.1.le, hu₁'.2.trans ht1⟩
        ⟨(hs0.trans hst.le).trans hu₂'.1.le, h1⟩ h)
    · have : c (u₂ - 1) = c u₂ := by rw [← hper (u₂ - 1)]; ring_nf
      rw [← this] at h
      have := hinj ⟨hs0.trans hu₁'.1.le, hu₁'.2.trans ht1⟩ ⟨by linarith, by linarith⟩ h
      linarith [hu₂'.2]
  have h3 := three_le_encard_midset hzM hM₁ hM₂ (fun e => hz (e ▸ hcC u₁))
    (fun e => hz (e ▸ hcC u₂)) hne
  exact absurd (h3.trans (h2 a b hab)) (by decide)

/-- **Corollary 3.4.** A continuum with the double midset property is a simple closed curve or a
dendrite. -/
theorem cor_3_4 [CompactSpace X] [ConnectedSpace X] [Nontrivial X] (h : HasDMP X) :
    Nonempty (X ≃ₜ Circle) ∨ IsDendrite X := by
  have hlc : LocallyConnectedSpace X := prop_3_1 fun a b hab =>
    finite_of_encard_eq_coe (h a b hab)
  have h2 : MidsetsAtMostTwo X := fun a b hab => (h a b hab).le
  by_cases hC : ∃ C : Set X, IsSimpleClosedCurve C
  · obtain ⟨C, hC⟩ := hC
    have := prop_3_2 h2 hC
    obtain ⟨e⟩ := hC
    left
    exact ⟨(Homeomorph.Set.univ X).symm.trans ((Homeomorph.setCongr this).symm.trans e)⟩
  · push_neg at hC
    exact Or.inr ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hlc, hC⟩

end DoubleMidset
