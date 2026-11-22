module

public import DoubleMidset.Spherical
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Odd boxes lie on a sphere (Lemma 6.6, Proposition 6.5, Corollary 6.7)

The proof follows the paper's five stages.

* (S1) Baire category in the parameter square gives uniform separation `ρ` of the two midset
  points on a smaller square.
* (S2)–(S3) Near a fixed pair the midset has one point near the crossing `y₀` and one near the
  touch `t₀`; the point near `y₀` is protected (opposite signs at two test points) and hence a
  crossing, so the point near `t₀` is the touch. It is the unique zero of a jointly continuous
  function on a compact parameter interval, hence depends continuously on the pair
  (`continuousOn_of_unique_zero`; this replaces the Hausdorff continuity of (S2)).
* (S4) The grid lemma forces the touch to be constant.
* (S5) Off-sphere parity (Lemma 6.3) extends the sphere to the whole box.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

section Generic

/-- Projection along a compact set preserves closedness. -/
theorem isClosed_fst_image_inter {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {Z : Set (X × Y)} (hZ : IsClosed Z) {K : Set Y} (hK : IsCompact K) :
    IsClosed (Prod.fst '' (Z ∩ univ ×ˢ K)) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set Z' : Set (X × K) := (fun p : X × K => (p.1, (p.2 : Y))) ⁻¹' Z
  have hZ' : IsClosed Z' := hZ.preimage (continuous_fst.prodMk (continuous_subtype_val.comp
    continuous_snd))
  have := isClosedMap_fst_of_compactSpace (X := X) (Y := K) Z' hZ'
  convert this using 1
  ext x; constructor
  · rintro ⟨⟨x, y⟩, ⟨hz, -, hy⟩, rfl⟩; exact ⟨(x, ⟨y, hy⟩), hz, rfl⟩
  · rintro ⟨⟨x, ⟨y, hy⟩⟩, hz, rfl⟩; exact ⟨(x, y), ⟨hz, mem_univ _, hy⟩, rfl⟩

/-- The unique zero, in a compact set, of a jointly continuous function depends continuously on
the parameter. -/
theorem continuousOn_of_unique_zero {X : Type*} [TopologicalSpace X] {F : X → ℝ → ℝ}
    (hF : Continuous fun p : X × ℝ => F p.1 p.2) {K : Set ℝ} (hK : IsCompact K) {R : Set X}
    {q : X → ℝ} (hq : ∀ p ∈ R, q p ∈ K ∧ F p (q p) = 0)
    (huniq : ∀ p ∈ R, ∀ x ∈ K, F p x = 0 → x = q p) : ContinuousOn q R := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  set Z : Set (X × ℝ) := {p | F p.1 p.2 = 0}
  have hZ : IsClosed Z := isClosed_eq hF continuous_const
  refine ⟨_, isClosed_fst_image_inter hZ (hK.inter_left ht), ?_⟩
  ext p; constructor
  · rintro ⟨hpt, hpR⟩
    exact ⟨⟨(p, q p), ⟨(hq p hpR).2, mem_univ _, hpt, (hq p hpR).1⟩, rfl⟩, hpR⟩
  · rintro ⟨⟨⟨p', x⟩, ⟨hz, -, hxt, hxK⟩, rfl⟩, hpR⟩
    refine ⟨?_, hpR⟩
    rw [mem_preimage, ← huniq p' hpR x hxK hz]; exact hxt

theorem neg_of_signs {a b c d : ℝ} (h1 : 0 < a * c) (h2 : 0 < b * d) (h3 : c * d < 0) :
    a * b < 0 := by
  by_contra h
  push_neg at h
  have : 0 < (a * c) * (b * d) := mul_pos h1 h2
  rw [show (a * c) * (b * d) = (a * b) * (c * d) by ring] at this
  exact absurd this (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos h h3.le))

end Generic

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem continuous_sgnf_param {X : Type*} [TopologicalSpace X] {A B : X → T} (hA : Continuous A)
    (hB : Continuous B) {Y : X → T} (hY : Continuous Y) :
    Continuous fun x => sgnf (A x) (B x) (Y x) :=
  (hY.dist hA).sub (hY.dist hB)

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem IsStrictPair.symm {a b : T} (h : IsStrictPair a b) : IsStrictPair b a :=
  ⟨h.1.symm, fun u hu e => h.2 u hu (by unfold sgnf at e ⊢; linarith)⟩

/-- **(5.2)**: `N(b, a) ≡ N(a, b) (mod 2)` for a strict pair. -/
theorem odd_oddCount_swap {a b : T} (h : IsStrictPair a b) (hodd : Odd (oddCount a b)) :
    Odd (oddCount b a) := by
  have hfin : (oddVertices T).Finite := hT.vertices_finite.subset fun u hu => hu.1
  have hsplit : oddVertices T = {u | u ∈ oddVertices T ∧ sgnf a b u < 0} ∪
      {u | u ∈ oddVertices T ∧ sgnf b a u < 0} := by
    ext u; constructor
    · intro hu
      rcases lt_or_gt_of_ne (h.2 u hu.1) with hl | hg
      · exact Or.inl ⟨hu, hl⟩
      · exact Or.inr ⟨hu, by unfold sgnf at hg ⊢; linarith⟩
    · rintro (hu | hu) <;> exact hu.1
  have hdisj : Disjoint {u | u ∈ oddVertices T ∧ sgnf a b u < 0}
      {u | u ∈ oddVertices T ∧ sgnf b a u < 0} := by
    rw [Set.disjoint_left]; rintro u ⟨-, h1⟩ ⟨-, h2⟩; unfold sgnf at h1 h2; linarith
  have hcard := ncard_union_eq hdisj (hfin.subset fun u hu => hu.1) (hfin.subset fun u hu => hu.1)
  rw [← hsplit] at hcard
  have hev := even_ncard_oddVertices hT
  unfold oddCount at hodd ⊢
  rw [hcard] at hev
  rcases hodd with ⟨k, hk⟩
  rcases hev with ⟨m, hm⟩
  exact ⟨m - k - 1, by omega⟩

omit hT in
/-- An open edge contains no vertex. -/
theorem IsOpenEdge.notMem_vertices {W : Set T} (hW : IsOpenEdge W) {x : T} (hx : x ∈ W) :
    x ∉ vertices T := by
  obtain ⟨y, -, rfl⟩ := hW; exact connectedComponentIn_subset _ _ hx

/-- A point of an open set of edge points lies in a parameter interval of an edge
parametrization whose image is in the set. -/
theorem exists_param_interval {U : Set T} (hU : IsOpen U) {a : T} (ha : a ∈ U)
    (hav : a ∉ vertices T) : ∃ γ : ℝ → T, IsEdgeParam γ ∧
      γ '' Ioo 0 1 = connectedComponentIn (vertices T)ᶜ a ∧ ∃ α β : ℝ, 0 ≤ α ∧ α < β ∧ β ≤ 1 ∧
      a ∈ γ '' Ioo α β ∧ γ '' Ioo α β ⊆ U := by
  obtain ⟨γ, s, hs, hγ, rfl, hW, -⟩ := exists_edgeParam hT hav
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hγ.arc.1) s ha
  set δ' := min (δ / 2) (min s (1 - s))
  have hδ' : 0 < δ' := lt_min (by linarith) (lt_min hs.1 (by linarith [hs.2]))
  have h1 : δ' ≤ δ / 2 := min_le_left _ _
  have h2 : δ' ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : δ' ≤ 1 - s := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨γ, hγ, hW, s - δ', s + δ', by linarith, by linarith, by linarith,
    ⟨s, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])

/-- **Lemma 6.6 (continuous selection of the touch)**, parametric form: on a parameter square
of an odd box there is a continuous parameter `q` of the touch, ranging in an open parameter
interval of an edge. -/
theorem param_selection (hDMP : HasDMP T) {γ κ : ℝ → T} (hγ : IsEdgeParam γ)
    (hκ : IsEdgeParam κ) {α₁ β₁ α₂ β₂ : ℝ} (hαβ₁ : α₁ < β₁) (hαβ₂ : α₂ < β₂)
    (hodd : ∀ s ∈ Ioo α₁ β₁, ∀ u ∈ Ioo α₂ β₂,
      IsStrictPair (γ s) (κ u) ∧ Odd (oddCount (γ s) (κ u))) :
    ∃ s₁ s₂ u₁ u₂ : ℝ, s₁ < s₂ ∧ u₁ < u₂ ∧ Ioo s₁ s₂ ⊆ Ioo α₁ β₁ ∧ Ioo u₁ u₂ ⊆ Ioo α₂ β₂ ∧
      ∃ ψ : ℝ → T, IsEdgeParam ψ ∧ ∃ j₁ j₂ : ℝ, 0 ≤ j₁ ∧ j₁ < j₂ ∧ j₂ ≤ 1 ∧
      ∃ q : T × T → ℝ, ContinuousOn q ((γ '' Ioo s₁ s₂) ×ˢ (κ '' Ioo u₁ u₂)) ∧
        ∀ s ∈ Ioo s₁ s₂, ∀ u ∈ Ioo u₁ u₂, q (γ s, κ u) ∈ Ioo j₁ j₂ ∧
          IsTouch (sgnf (γ s) (κ u)) (ψ (q (γ s, κ u))) := by
  classical
  ------------------------------------------------------------------
  -- (S1) uniform separation by Baire category in the parameter square
  set B : Set (ℝ × ℝ) := Ioo α₁ β₁ ×ˢ Ioo α₂ β₂
  have hBo : IsOpen B := isOpen_Ioo.prod isOpen_Ioo
  set Φ : ℝ × ℝ → T × T := fun p => (γ p.1, κ p.2)
  have hΦ : Continuous Φ :=
    (hγ.arc.1.comp continuous_fst).prodMk (hκ.arc.1.comp continuous_snd)
  set Z : ℕ → Set ((ℝ × ℝ) × (T × T)) := fun n => {z | sgnf (Φ z.1).1 (Φ z.1).2 z.2.1 = 0 ∧
    sgnf (Φ z.1).1 (Φ z.1).2 z.2.2 = 0 ∧ 1 / ((n : ℝ) + 1) ≤ dist z.2.1 z.2.2}
  have hA1 : Continuous fun z : (ℝ × ℝ) × (T × T) => (Φ z.1).1 := (hΦ.comp continuous_fst).fst
  have hA2 : Continuous fun z : (ℝ × ℝ) × (T × T) => (Φ z.1).2 := (hΦ.comp continuous_fst).snd
  have hZc : ∀ n, IsClosed (Z n) := fun n =>
    (isClosed_eq (continuous_sgnf_param hA1 hA2 continuous_snd.fst) continuous_const).inter
    ((isClosed_eq (continuous_sgnf_param hA1 hA2 continuous_snd.snd) continuous_const).inter
    (isClosed_le continuous_const (continuous_snd.fst.dist continuous_snd.snd)))
  set A : ℕ → Set (ℝ × ℝ) := fun n => Prod.fst '' Z n
  have hAc : ∀ n, IsClosed (A n) := fun n => isClosedMap_fst_of_compactSpace _ (hZc n)
  have htwo : ∀ p ∈ B, ∃ y z, y ≠ z ∧ midset (Φ p).1 (Φ p).2 = {y, z} := fun p hp =>
    encard_eq_two.1 (hDMP _ _ (hodd p.1 hp.1 p.2 hp.2).1.1)
  have hcover : ⋃ n, (A n ∪ Bᶜ) = univ := by
    refine eq_univ_of_forall fun p => ?_
    by_cases hp : p ∈ B
    · obtain ⟨y, z, hyz, hM⟩ := htwo p hp
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.2 hyz)
      have hy : y ∈ midset (Φ p).1 (Φ p).2 := hM ▸ (mem_insert _ _)
      have hz : z ∈ midset (Φ p).1 (Φ p).2 := hM ▸ (mem_insert_of_mem _ rfl)
      exact mem_iUnion.2 ⟨n, Or.inl ⟨(p, y, z),
        ⟨sgnf_eq_zero_iff.2 hy, sgnf_eq_zero_iff.2 hz, hn.le⟩, rfl⟩⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hp⟩
  have hdense := dense_iUnion_interior_of_closed
    (fun n => (hAc n).union hBo.isClosed_compl) hcover
  have hBne : B.Nonempty :=
    ⟨((α₁ + β₁) / 2, (α₂ + β₂) / 2), ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨p0, hp0B, hp0U⟩ := hdense.inter_open_nonempty B hBo hBne
  obtain ⟨n, hn⟩ := mem_iUnion.1 hp0U
  set O := interior (A n ∪ Bᶜ) ∩ B
  have hOo : IsOpen O := isOpen_interior.inter hBo
  have hOA : O ⊆ A n := fun p hp =>
    (interior_subset hp.1 : p ∈ A n ∪ Bᶜ).resolve_right fun h => h hp.2
  set ρ : ℝ := 1 / ((n : ℝ) + 1)
  have hρ : 0 < ρ := by positivity
  have hsep : ∀ p ∈ O, ∃ y z, midset (Φ p).1 (Φ p).2 = {y, z} ∧ ρ ≤ dist y z := by
    intro p hp
    obtain ⟨⟨p', y, z⟩, ⟨hy, hz, hd⟩, hpe⟩ := hOA hp
    simp only at hpe
    subst hpe
    have hyz : y ≠ z := fun e => by rw [e, dist_self] at hd; linarith
    refine ⟨y, z, ?_, hd⟩
    have hsub : ({y, z} : Set T) ⊆ midset (Φ p').1 (Φ p').2 := by
      rintro w (rfl | rfl)
      · exact sgnf_eq_zero_iff.1 hy
      · exact sgnf_eq_zero_iff.1 hz
    refine ((toFinite _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hDMP _ _ (hodd p'.1 hp.2.1 p'.2 hp.2.2).1.1, encard_pair hyz]
  have hp0O : p0 ∈ O := ⟨hn, hp0B⟩
  ------------------------------------------------------------------
  -- the base pair: a crossing `y₀` and a touch `t₀`
  obtain ⟨hstr, hoddp⟩ := hodd p0.1 hp0B.1 p0.2 hp0B.2
  obtain ⟨-, -, -, h4⟩ := cor_5_5 hT hDMP hstr
  obtain ⟨y₀, t₀, hM₀, hy₀, ht₀⟩ := h4 hoddp
  have hρ₀ : ρ ≤ dist y₀ t₀ := by
    obtain ⟨y, z, hM, hd⟩ := hsep p0 hp0O
    change midset (γ p0.1) (κ p0.2) = {y, z} at hM
    rw [hM₀] at hM
    rcases pair_eq_pair_iff.1 hM with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hd
    · rw [h1, h2, dist_comm]; exact hd
  -- protecting the crossing
  obtain ⟨κ', r₀, hr₀, hκ', hκ'r₀, -, -⟩ := exists_edgeParam hT hy₀.1
  obtain ⟨ε₁, hε₁, hside⟩ := hy₀.along hT hκ'.arc hr₀ hκ'r₀
  obtain ⟨δκ, hδκ, hκball⟩ := Metric.continuous_iff.1 hκ'.arc.1 r₀ (ρ / 3) (by positivity)
  set η := min (min (ε₁ / 2) (δκ / 2)) (min (r₀ / 2) ((1 - r₀) / 2)) with hηdef
  have hη : 0 < η := lt_min (lt_min (by linarith) (by linarith))
    (lt_min (by linarith [hr₀.1]) (by linarith [hr₀.2]))
  have hη1 : η ≤ ε₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hη2 : η ≤ δκ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hη3 : η ≤ r₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hη4 : η ≤ (1 - r₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsign₀ : sgnf (γ p0.1) (κ p0.2) (κ' (r₀ - η)) * sgnf (γ p0.1) (κ p0.2) (κ' (r₀ + η)) < 0 :=
    hside _ ⟨by linarith, by linarith⟩ _ ⟨by linarith, by linarith⟩
  have hκIcc : κ' '' Icc (r₀ - η) (r₀ + η) ⊆ ball y₀ (ρ / 3) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← hκ'r₀]
    exact hκball r (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2])
  -- the touch side
  obtain ⟨ψ, q₀, hq₀, hψ, hψq₀, -, -⟩ := exists_edgeParam hT ht₀.1
  obtain ⟨δψ, hδψ, hψball⟩ := Metric.continuous_iff.1 hψ.arc.1 q₀ (ρ / 3) (by positivity)
  set η' := min (δψ / 2) (min (q₀ / 4) ((1 - q₀) / 4)) with hη'def
  have hη' : 0 < η' := lt_min (by linarith) (lt_min (by linarith [hq₀.1]) (by linarith [hq₀.2]))
  have hη'1 : η' ≤ δψ / 2 := min_le_left _ _
  have hη'2 : η' ≤ q₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hη'3 : η' ≤ (1 - q₀) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hψK : ψ '' Icc (q₀ - η') (q₀ + η') ⊆ ball t₀ (ρ / 3) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← hψq₀]
    exact hψball r (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2])
  have hO1 : IsOpen (κ' '' Ioo (r₀ - η) (r₀ + η)) :=
    hκ'.isOpen_image_Ioo hT (by linarith) (by linarith)
  have hO2 : IsOpen (ψ '' Ioo (q₀ - η') (q₀ + η')) :=
    hψ.isOpen_image_Ioo hT (by linarith) (by linarith)
  obtain ⟨e1, he1, hb1⟩ := Metric.isOpen_iff.1 hO1 y₀
    ⟨r₀, ⟨by linarith, by linarith⟩, hκ'r₀⟩
  obtain ⟨e2, he2, hb2⟩ := Metric.isOpen_iff.1 hO2 t₀
    ⟨q₀, ⟨by linarith, by linarith⟩, hψq₀⟩
  set ε := min (min e1 e2) (ρ / 3) with hεdef
  have hε : 0 < ε := lt_min (lt_min he1 he2) (by positivity)
  have hεe1 : ε ≤ e1 := (min_le_left _ _).trans (min_le_left _ _)
  have hεe2 : ε ≤ e2 := (min_le_left _ _).trans (min_le_right _ _)
  have hερ : ε ≤ ρ / 3 := min_le_right _ _
  ------------------------------------------------------------------
  -- (S2) the midset stays near `{y₀, t₀}`; the signs at the test points persist
  set Bad : Set (ℝ × ℝ) := Prod.fst '' {z : (ℝ × ℝ) × T |
    sgnf (Φ z.1).1 (Φ z.1).2 z.2 = 0 ∧ z.2 ∈ (ball y₀ ε ∪ ball t₀ ε)ᶜ}
  have hBadc : IsClosed Bad := isClosedMap_fst_of_compactSpace _
    ((isClosed_eq (continuous_sgnf_param (hΦ.comp continuous_fst).fst
      (hΦ.comp continuous_fst).snd continuous_snd) continuous_const).inter
      ((isOpen_ball.union isOpen_ball).isClosed_compl.preimage continuous_snd))
  have hp0Bad : p0 ∉ Bad := by
    rintro ⟨⟨p, y⟩, ⟨hy, hyb⟩, hpe⟩
    simp only at hpe
    subst hpe
    have hyM : y ∈ midset (γ p.1) (κ p.2) := sgnf_eq_zero_iff.1 hy
    rw [hM₀] at hyM
    rcases hyM with rfl | hyM
    · exact hyb (Or.inl (mem_ball_self hε))
    · rw [mem_singleton_iff] at hyM; subst hyM; exact hyb (Or.inr (mem_ball_self hε))
  have hcs : Continuous fun p : ℝ × ℝ =>
      sgnf (Φ p).1 (Φ p).2 (κ' (r₀ - η)) * sgnf (Φ p).1 (Φ p).2 (κ' (r₀ + η)) :=
    (continuous_sgnf_param hΦ.fst hΦ.snd continuous_const).mul
      (continuous_sgnf_param hΦ.fst hΦ.snd continuous_const)
  have hN : O ∩ Badᶜ ∩ {p | sgnf (Φ p).1 (Φ p).2 (κ' (r₀ - η)) *
      sgnf (Φ p).1 (Φ p).2 (κ' (r₀ + η)) < 0} ∈ 𝓝 p0 :=
    inter_mem (inter_mem (hOo.mem_nhds hp0O) (hBadc.isOpen_compl.mem_nhds hp0Bad))
      ((isOpen_lt hcs continuous_const).mem_nhds hsign₀)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.1 hN
  have hsq : ∀ s ∈ Ioo (p0.1 - δ) (p0.1 + δ), ∀ u ∈ Ioo (p0.2 - δ) (p0.2 + δ),
      (s, u) ∈ ball p0 δ := by
    intro s hs u hu
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  have hdisj : ∀ w, w ∈ ball y₀ (ρ / 3) → w ∈ ball t₀ (ρ / 3) → False := fun w h1 h2 => by
    rw [mem_ball] at h1 h2
    have := dist_triangle_left y₀ t₀ w
    linarith
  have hsame : ∀ c w w' : T, w ∈ ball c ε → w' ∈ ball c ε → dist w w' < ρ := fun c w w' h1 h2 => by
    rw [mem_ball] at h1 h2
    have := dist_triangle_right w w' c
    linarith
  ------------------------------------------------------------------
  -- (S3) the point near `t₀` is the touch, and the unique zero in `ψ [q₀ - η', q₀ + η']`
  have key : ∀ s ∈ Ioo (p0.1 - δ) (p0.1 + δ), ∀ u ∈ Ioo (p0.2 - δ) (p0.2 + δ),
      ∃ x ∈ Ioo (q₀ - η') (q₀ + η'), IsTouch (sgnf (γ s) (κ u)) (ψ x) ∧
        ∀ x' ∈ Icc (q₀ - η') (q₀ + η'), sgnf (γ s) (κ u) (ψ x') = 0 → x' = x := by
    intro s hs u hu
    obtain ⟨⟨hpO, hpBad⟩, hpsign⟩ := hδball (hsq s hs u hu)
    have hpB : (s, u) ∈ B := hpO.2
    obtain ⟨hstr', hodd'⟩ := hodd s hpB.1 u hpB.2
    obtain ⟨y, z, hM, hd⟩ := hsep _ hpO
    change midset (γ s) (κ u) = {y, z} at hM
    have hin : ∀ w ∈ midset (γ s) (κ u), w ∈ ball y₀ ε ∪ ball t₀ ε := fun w hw => by
      by_contra hc; exact hpBad ⟨((s, u), w), ⟨sgnf_eq_zero_iff.2 hw, hc⟩, rfl⟩
    have hy := hin y (hM ▸ mem_insert _ _)
    have hz := hin z (hM ▸ mem_insert_of_mem _ rfl)
    obtain ⟨y', z', hM', hy', hz'⟩ : ∃ y' z', midset (γ s) (κ u) = {y', z'} ∧
        y' ∈ ball y₀ ε ∧ z' ∈ ball t₀ ε := by
      rcases hy with hy | hy <;> rcases hz with hz | hz
      · exact absurd (hsame _ _ _ hy hz) (not_lt.2 hd)
      · exact ⟨y, z, hM, hy, hz⟩
      · exact ⟨z, y, by rw [hM, pair_comm], hz, hy⟩
      · exact absurd (hsame _ _ _ hy hz) (not_lt.2 hd)
    have hεb : ∀ c : T, ball c ε ⊆ ball c (ρ / 3) := fun c => ball_subset_ball hερ
    obtain ⟨r', hr', rfl⟩ := hb1 (ball_subset_ball hεe1 hy')
    set g := sgnf (γ s) (κ u) with hgdef
    have hfin : (g ⁻¹' {0}).Finite := by
      exact midset_finite_of_dmp hDMP hstr'.1
    have hz'K : z' ∉ κ' '' Icc (r₀ - η) (r₀ + η) := fun h => hdisj z' (hκIcc h) (hεb _ hz')
    have hzeros : ∀ r ∈ Icc (r₀ - η) (r₀ + η), g (κ' r) = 0 → r = r' := by
      intro r hr hr0
      have hrM : κ' r ∈ midset (γ s) (κ u) := sgnf_eq_zero_iff.1 hr0
      rw [hM'] at hrM
      rcases hrM with h | h
      · exact hκ'.arc.2 ⟨by linarith [hr.1], by linarith [hr.2]⟩
          ⟨by linarith [hr'.1], by linarith [hr'.2]⟩ h
      · rw [mem_singleton_iff] at h
        exact absurd (h ▸ ⟨r, hr, rfl⟩ : z' ∈ κ' '' Icc (r₀ - η) (r₀ + η)) hz'K
    have hgc : Continuous (g ∘ κ') := (continuous_sgnf _ _).comp hκ'.arc.1
    have hleft : ∀ t ∈ Ico (r₀ - η) r', 0 < (g ∘ κ') t * (g ∘ κ') (r₀ - η) :=
      fun t ht => const_sign isPreconnected_Ico hgc.continuousOn
        (fun x hx e => by
          have := hzeros x ⟨hx.1, by linarith [hx.2, hr'.2]⟩ e; linarith [hx.2])
        t ht (r₀ - η) ⟨le_rfl, hr'.1⟩
    have hright : ∀ t ∈ Ioc r' (r₀ + η), 0 < (g ∘ κ') t * (g ∘ κ') (r₀ + η) :=
      fun t ht => const_sign isPreconnected_Ioc hgc.continuousOn
        (fun x hx e => by
          have := hzeros x ⟨by linarith [hx.1, hr'.1], hx.2⟩ e; linarith [hx.1])
        t ht (r₀ + η) ⟨hr'.2, le_rfl⟩
    have hy'0 : g (κ' r') = 0 := sgnf_eq_zero_iff.2 (hM' ▸ mem_insert _ _)
    have hpc : IsParamCrossing (g ∘ κ') r' := by
      refine ⟨hy'0, min (r' - (r₀ - η)) (r₀ + η - r'),
        lt_min (by linarith [hr'.1]) (by linarith [hr'.2]), fun t ht t' ht' => ?_⟩
      have m1 : min (r' - (r₀ - η)) (r₀ + η - r') ≤ r' - (r₀ - η) := min_le_left _ _
      have m2 : min (r' - (r₀ - η)) (r₀ + η - r') ≤ r₀ + η - r' := min_le_right _ _
      exact neg_of_signs (hleft t ⟨by linarith [ht.1], ht.2⟩)
        (hright t' ⟨ht'.1, by linarith [ht'.2]⟩) hpsign
    have hr'01 : r' ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
    have hcross : IsCrossing g (κ' r') := isCrossing_of_param hT hκ' hfin hr'01 hpc
    obtain ⟨-, -, -, h4'⟩ := cor_5_5 hT hDMP hstr'
    obtain ⟨c₁, t₁, hM₁, -, ht₁⟩ := h4' hodd'
    have hz'touch : IsTouch g z' := by
      rw [hM'] at hM₁
      rcases pair_eq_pair_iff.1 hM₁ with ⟨-, h2⟩ | ⟨h1, -⟩
      · rw [h2]; exact ht₁
      · rw [← h1] at ht₁; exact absurd ht₁ fun ht => not_isCrossing_and_isTouch hT hcross ht
    obtain ⟨x, hx, rfl⟩ := hb2 (ball_subset_ball hεe2 hz')
    refine ⟨x, hx, hz'touch, fun x' hx' hx'0 => ?_⟩
    have hxM : ψ x' ∈ midset (γ s) (κ u) := sgnf_eq_zero_iff.1 hx'0
    rw [hM'] at hxM
    rcases hxM with h | h
    · exfalso
      exact hdisj (ψ x') (by rw [h]; exact hκIcc ⟨r', Ioo_subset_Icc_self hr', rfl⟩)
        (hψK ⟨x', hx', rfl⟩)
    · rw [mem_singleton_iff] at h
      exact hψ.arc.2 ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
        ⟨by linarith [hx.1], by linarith [hx.2]⟩ h
  ------------------------------------------------------------------
  -- the selection and its continuity
  set K := Icc (q₀ - η') (q₀ + η') with hKdef
  let q : T × T → ℝ := fun p =>
    if h : ∃ x ∈ K, sgnf p.1 p.2 (ψ x) = 0 then h.choose else 0
  have hq : ∀ s ∈ Ioo (p0.1 - δ) (p0.1 + δ), ∀ u ∈ Ioo (p0.2 - δ) (p0.2 + δ),
      q (γ s, κ u) ∈ Ioo (q₀ - η') (q₀ + η') ∧
        IsTouch (sgnf (γ s) (κ u)) (ψ (q (γ s, κ u))) ∧
        ∀ x' ∈ K, sgnf (γ s) (κ u) (ψ x') = 0 → x' = q (γ s, κ u) := by
    intro s hs u hu
    obtain ⟨x, hx, htouch, huniq⟩ := key s hs u hu
    have hex : ∃ x ∈ K, sgnf (γ s) (κ u) (ψ x) = 0 := ⟨x, Ioo_subset_Icc_self hx, htouch.2.1⟩
    have hqx : q (γ s, κ u) = x := by
      show (if h : ∃ x ∈ K, sgnf (γ s) (κ u) (ψ x) = 0 then h.choose else 0) = x
      rw [dif_pos hex]
      exact huniq _ hex.choose_spec.1 hex.choose_spec.2
    rw [hqx]; exact ⟨hx, htouch, huniq⟩
  have hcont : ContinuousOn q ((γ '' Ioo (p0.1 - δ) (p0.1 + δ)) ×ˢ
      (κ '' Ioo (p0.2 - δ) (p0.2 + δ))) := by
    refine continuousOn_of_unique_zero (F := fun p x => sgnf p.1 p.2 (ψ x))
      (continuous_sgnf_param continuous_fst.fst continuous_fst.snd
        (hψ.arc.1.comp continuous_snd)) (isCompact_Icc (a := q₀ - η') (b := q₀ + η')) ?_ ?_
    · rintro ⟨a, b⟩ ⟨⟨s, hs, rfl⟩, ⟨u, hu, rfl⟩⟩
      obtain ⟨h1, h2, -⟩ := hq s hs u hu
      exact ⟨Ioo_subset_Icc_self h1, h2.2.1⟩
    · rintro ⟨a, b⟩ ⟨⟨s, hs, rfl⟩, ⟨u, hu, rfl⟩⟩
      exact (hq s hs u hu).2.2
  refine ⟨p0.1 - δ, p0.1 + δ, p0.2 - δ, p0.2 + δ, by linarith, by linarith,
    fun s hs => (hδball (hsq s hs p0.2 ⟨by linarith, by linarith⟩)).1.1.2.1,
    fun u hu => (hδball (hsq p0.1 ⟨by linarith, by linarith⟩ u hu)).1.1.2.2,
    ψ, hψ, q₀ - 2 * η', q₀ + 2 * η', by linarith, by linarith, by linarith, q, hcont,
    fun s hs u hu => ?_⟩
  obtain ⟨h1, h2, -⟩ := hq s hs u hu
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, h2⟩

omit [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
/-- If `h_z` is constant along a nondegenerate parameter interval of an arc, then `z` is the
center of a spherical arc. -/
theorem mem_centers_of_const {k : ℝ → T} (hk : IsArcParam k) {c d : ℝ} (hc : 0 ≤ c)
    (hcd : c < d) (hd : d ≤ 1) {z : T}
    (hconst : ∀ y ∈ Ioo c d, ∀ y' ∈ Ioo c d, dist z (k y) = dist z (k y')) :
    ∃ I r, IsSphericalArc I z r := by
  set c' := (2 * c + d) / 3
  set d' := (c + 2 * d) / 3
  have hc' : c' ∈ Ioo c d := ⟨by simp only [c']; linarith, by simp only [c']; linarith⟩
  have hd' : d' ∈ Ioo c d := ⟨by simp only [d']; linarith, by simp only [d']; linarith⟩
  have hcd' : c' < d' := by simp only [c', d']; linarith
  have h01 : ∀ y ∈ Ioo c d, y ∈ Icc (0 : ℝ) 1 := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  obtain ⟨k', hk', -, -, him⟩ := hk.exists_subarc (h01 c' hc') (h01 d' hd') hcd'.ne
  refine ⟨k' '' Icc 0 1, dist z (k c'), hk'.isArcBetween.isArc, ?_, ?_⟩
  · rcases (dist_nonneg (x := z) (y := k c')).lt_or_eq with h | h
    · exact h
    · exfalso
      have e1 : k c' = z := (dist_eq_zero.1 h.symm).symm
      have e2 : k d' = z := (dist_eq_zero.1 ((hconst d' hd' c' hc').trans h.symm)).symm
      exact hcd'.ne (hk.2 (h01 c' hc') (h01 d' hd') (e1.trans e2.symm))
  · rw [him, uIcc_of_le hcd'.le]
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_sphere, dist_comm]
    exact hconst y ⟨by linarith [hy.1, hc'.1], by linarith [hy.2, hd'.2]⟩ c' hc'

/-- **Proposition 6.5, parametric core (S4).** On a parameter square of an odd box there is a
smaller square whose two sides lie on one sphere `S(c, r)`, `r > 0`. -/
theorem param_box_sphere (hDMP : HasDMP T) {γ κ : ℝ → T} (hγ : IsEdgeParam γ)
    (hκ : IsEdgeParam κ) {α₁ β₁ α₂ β₂ : ℝ} (h0₁ : 0 ≤ α₁) (hαβ₁ : α₁ < β₁) (h1₁ : β₁ ≤ 1)
    (h0₂ : 0 ≤ α₂) (hαβ₂ : α₂ < β₂) (h1₂ : β₂ ≤ 1)
    (hodd : ∀ s ∈ Ioo α₁ β₁, ∀ u ∈ Ioo α₂ β₂,
      IsStrictPair (γ s) (κ u) ∧ Odd (oddCount (γ s) (κ u))) :
    ∃ s₁ s₂ u₁ u₂ : ℝ, s₁ < s₂ ∧ u₁ < u₂ ∧ Ioo s₁ s₂ ⊆ Ioo α₁ β₁ ∧ Ioo u₁ u₂ ⊆ Ioo α₂ β₂ ∧
      ∃ c : T, ∃ r : ℝ, 0 < r ∧ (∀ s ∈ Ioo s₁ s₂, dist c (γ s) = r) ∧
        ∀ u ∈ Ioo u₁ u₂, dist c (κ u) = r := by
  have h2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  obtain ⟨s₁, s₂, u₁, u₂, hs, hu, hsS, huS, ψ, hψ, j₁, j₂, hj₁, hj, hj₂, q, hqc, hq⟩ :=
    param_selection hT hDMP hγ hκ hαβ₁ hαβ₂ hodd
  set Sq := Ioo s₁ s₂ ×ˢ Ioo u₁ u₂
  set g : ℝ × ℝ → ℝ := fun p => q (γ p.1, κ p.2)
  have hgc : ContinuousOn g Sq := hqc.comp
    ((hγ.arc.1.comp continuous_fst).prodMk (hκ.arc.1.comp continuous_snd)).continuousOn
    fun p hp => ⟨⟨p.1, hp.1, rfl⟩, ⟨p.2, hp.2, rfl⟩⟩
  have hs01 : ∀ s ∈ Ioo s₁ s₂, s ∈ Icc (0 : ℝ) 1 := fun s hs' =>
    ⟨by linarith [(hsS hs').1], by linarith [(hsS hs').2]⟩
  have hu01 : ∀ u ∈ Ioo u₁ u₂, u ∈ Icc (0 : ℝ) 1 := fun u hu' =>
    ⟨by linarith [(huS hu').1], by linarith [(huS hu').2]⟩
  have hsb := (Ioo_subset_Ioo_iff hs).1 hsS
  have hub := (Ioo_subset_Ioo_iff hu).1 huS
  -- (S4) the touch is constant
  have main : ∀ p ∈ Sq, ∀ p' ∈ Sq, g p < g p' → False := by
    intro p hp p' hp' hlt
    set Cen := {x : T | ∃ I r, IsSphericalArc I x r}
    have hCen : Cen.Countable := centers_countable hT h2
    set S := {x ∈ Icc (0 : ℝ) 1 | ψ x ∈ Cen}
    have hS : S.Countable := MapsTo.countable_of_injOn (f := ψ) (t := Cen)
      (fun x hx => hx.2) (hψ.arc.2.mono fun x hx => hx.1) hCen
    obtain ⟨q', hq', hq'S⟩ := exists_mem_Ioo_notMem hS hlt
    have hgp := (hq p.1 hp.1 p.2 hp.2).1
    have hgp' := (hq p'.1 hp'.1 p'.2 hp'.2).1
    have hq'01 : q' ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hgp.1, hq'.1], by linarith [hgp'.2, hq'.2]⟩
    set z := ψ q'
    have hzC : z ∉ Cen := fun h => hq'S ⟨hq'01, h⟩
    have hnc : ∀ k : ℝ → T, IsArcParam k → ∀ σ₁ σ₂ : ℝ, 0 ≤ σ₁ → σ₂ ≤ 1 →
        ∀ c d, c < d → Ioo c d ⊆ Ioo σ₁ σ₂ →
          ∃ y ∈ Ioo c d, ∃ y' ∈ Ioo c d, (dist z ∘ k) y ≠ (dist z ∘ k) y' := by
      intro k hk σ₁ σ₂ h0 h1 c d hcd hsub
      by_contra hall
      push_neg at hall
      have hcd' := (Ioo_subset_Ioo_iff hcd).1 hsub
      exact hzC (mem_centers_of_const hk (by linarith [hcd'.1]) hcd (by linarith [hcd'.2])
        fun y hy y' hy' => hall y hy y' hy')
    set E := {s | s ∈ Ioo s₁ s₂ ∧ IsLocalExtr (dist z ∘ γ) s}
    set F := {u | u ∈ Ioo u₁ u₂ ∧ IsLocalExtr (dist z ∘ κ) u}
    have hEm : IsMeagre E := lemma_2_8_ii (continuous_const.dist hγ.arc.1).continuousOn
      (hnc γ hγ.arc s₁ s₂ (by linarith [hsb.1]) (by linarith [hsb.2]))
    have hFm : IsMeagre F := lemma_2_8_ii (continuous_const.dist hκ.arc.1).continuousOn
      (hnc κ hκ.arc u₁ u₂ (by linarith [hub.1]) (by linarith [hub.2]))
    have hgrid := (lemma_2_9 hs hu (E := E) (F := F) (fun s hs' => hs'.1) (fun u hu' => hu'.1)
      hEm hFm).2.2 (fun p => g p - q') (hgc.sub continuousOn_const) (by
        rintro ⟨s, u⟩ hp0 hzero
        have hsq : (s, u) ∈ Sq := by
          rcases hp0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1.1, h2⟩
          · exact ⟨h1, h2.1⟩
        have hgq : g (s, u) = q' := by linarith
        obtain ⟨-, htouch⟩ := hq s hsq.1 u hsq.2
        change IsTouch (sgnf (γ s) (κ u)) (ψ (g (s, u))) at htouch
        rw [hgq] at htouch
        obtain ⟨hstr, hodd'⟩ := hodd s (hsS hsq.1) u (huS hsq.2)
        obtain ⟨hla, hlb⟩ := touch_isLocalExtr hT hDMP hstr hodd' htouch
        have hsE : s ∈ E := ⟨hsq.1, hla.comp_continuous hγ.arc.1.continuousAt⟩
        have huF : u ∈ F := ⟨hsq.2, hlb.comp_continuous hκ.arc.1.continuousAt⟩
        rcases hp0 with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact h1.2 hsE
        · exact h2.2 huF)
    rcases hgrid with h | h
    · have := h p hp; linarith [hq'.1]
    · have := h p' hp'; linarith [hq'.2]
  have hconst : ∀ p ∈ Sq, ∀ p' ∈ Sq, g p = g p' := by
    intro p hp p' hp'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact main p hp p' hp' h
    · exact main p' hp' p hp h
  -- a sphere on the subsquare
  set sm := (s₁ + s₂) / 2
  set um := (u₁ + u₂) / 2
  have hsm : sm ∈ Ioo s₁ s₂ := ⟨by simp only [sm]; linarith, by simp only [sm]; linarith⟩
  have hum : um ∈ Ioo u₁ u₂ := ⟨by simp only [um]; linarith, by simp only [um]; linarith⟩
  set c := ψ (g (sm, um))
  have hmid : ∀ s ∈ Ioo s₁ s₂, ∀ u ∈ Ioo u₁ u₂, dist c (γ s) = dist c (κ u) := by
    intro s hs' u hu'
    have htouch := (hq s hs' u hu').2
    change IsTouch (sgnf (γ s) (κ u)) (ψ (g (s, u))) at htouch
    rw [hconst (s, u) ⟨hs', hu'⟩ (sm, um) ⟨hsm, hum⟩] at htouch
    exact sgnf_eq_zero_iff.1 htouch.2.1
  set r := dist c (κ um)
  have hr : 0 < r := by
    rcases (dist_nonneg (x := c) (y := κ um)).lt_or_eq with h | h
    · exact h
    · exfalso
      set s' := (sm + s₂) / 2
      have hs' : s' ∈ Ioo s₁ s₂ := ⟨by simp only [s', sm]; linarith, by simp only [s', sm]; linarith⟩
      have e1 : γ sm = c := (dist_eq_zero.1 ((hmid sm hsm um hum).trans h.symm)).symm
      have e2 : γ s' = c := (dist_eq_zero.1 ((hmid s' hs' um hum).trans h.symm)).symm
      have : sm = s' := hγ.arc.2 (hs01 sm hsm) (hs01 s' hs') (e1.trans e2.symm)
      simp only [s', sm] at this; linarith
  refine ⟨s₁, s₂, u₁, u₂, hs, hu, hsS, huS, c, r, hr, fun s hs' => hmid s hs' um hum,
    fun u hu' => ?_⟩
  rw [← hmid sm hsm u hu', hmid sm hsm um hum]

omit hT in
theorem IsOpenArc.nonempty {U : Set T} (hU : IsOpenArc U) : U.Nonempty := by
  obtain ⟨e⟩ := hU.2
  exact ⟨(e.symm ⟨1 / 2, by norm_num, by norm_num⟩).1, (e.symm _).2⟩

/-- Parameter intervals inside an odd box. -/
theorem oddBox_params {U V : Set T} (hUV : IsOddBox U V) :
    ∃ γ κ : ℝ → T, IsEdgeParam γ ∧ IsEdgeParam κ ∧ ∃ α₁ β₁ α₂ β₂ : ℝ,
      0 ≤ α₁ ∧ α₁ < β₁ ∧ β₁ ≤ 1 ∧ 0 ≤ α₂ ∧ α₂ < β₂ ∧ β₂ ≤ 1 ∧
      γ '' Ioo α₁ β₁ ⊆ U ∧ κ '' Ioo α₂ β₂ ⊆ V ∧
      ∀ s ∈ Ioo α₁ β₁, ∀ u ∈ Ioo α₂ β₂, IsStrictPair (γ s) (κ u) ∧ Odd (oddCount (γ s) (κ u)) := by
  obtain ⟨⟨hU, hV, -, ⟨W₁, hW₁, hUW⟩, ⟨W₂, hW₂, hVW⟩⟩, hpairs⟩ := hUV
  obtain ⟨a, ha⟩ := hU.nonempty
  obtain ⟨b, hb⟩ := hV.nonempty
  obtain ⟨γ, hγ, -, α₁, β₁, h1, h2, h3, -, hγU⟩ :=
    exists_param_interval hT hU.1 ha (hW₁.notMem_vertices (hUW ha))
  obtain ⟨κ, hκ, -, α₂, β₂, h4, h5, h6, -, hκV⟩ :=
    exists_param_interval hT hV.1 hb (hW₂.notMem_vertices (hVW hb))
  exact ⟨γ, κ, hγ, hκ, α₁, β₁, α₂, β₂, h1, h2, h3, h4, h5, h6, hγU, hκV,
    fun s hs u hu => hpairs _ (hγU ⟨s, hs, rfl⟩) _ (hκV ⟨u, hu, rfl⟩)⟩

/-- The image of an open parameter subinterval of an edge parametrization is an open arc in an
open edge. -/
theorem IsEdgeParam.inOpenEdge {γ : ℝ → T} (hγ : IsEdgeParam γ) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ 1) : ∃ W, IsOpenEdge W ∧ γ '' Ioo a b ⊆ W := by
  have hm : (a + b) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  refine ⟨_, ⟨γ ((a + b) / 2), hγ.interior _ hm, rfl⟩, ?_⟩
  rw [← hγ.image_Ioo_eq hT hm]
  exact image_mono (Ioo_subset_Ioo ha hb)

/-- **Lemma 6.6 (continuous selection of the touch).** Let `U × V` be an odd box. There are a
nonempty box `U₁ × V₁ ⊆ U × V`, an open arc `J` in an open edge, and a map `w`, continuous on
`U₁ × V₁`, such that `w(a, b) ∈ J` is the touch of `M(a, b)` for every `(a, b) ∈ U₁ × V₁`. -/
theorem lemma_6_6 (hDMP : HasDMP T) {U V : Set T} (hUV : IsOddBox U V) :
    ∃ U₁ V₁ : Set T, IsBox U₁ V₁ ∧ U₁ ⊆ U ∧ V₁ ⊆ V ∧
      ∃ J : Set T, IsOpenArc J ∧ (∃ W, IsOpenEdge W ∧ J ⊆ W) ∧
      ∃ w : T × T → T, ContinuousOn w (U₁ ×ˢ V₁) ∧
        ∀ a ∈ U₁, ∀ b ∈ V₁, w (a, b) ∈ J ∧ IsTouch (sgnf a b) (w (a, b)) := by
  obtain ⟨γ, κ, hγ, hκ, α₁, β₁, α₂, β₂, h1, h2, h3, h4, h5, h6, hγU, hκV, hodd⟩ :=
    oddBox_params hT hUV
  obtain ⟨s₁, s₂, u₁, u₂, hs, hu, hsS, huS, ψ, hψ, j₁, j₂, hj₁, hj, hj₂, q, hqc, hq⟩ :=
    param_selection hT hDMP hγ hκ h2 h5 hodd
  have hsb := (Ioo_subset_Ioo_iff hs).1 hsS
  have hub := (Ioo_subset_Ioo_iff hu).1 huS
  have hUsub : γ '' Ioo s₁ s₂ ⊆ U := (image_mono hsS).trans hγU
  have hVsub : κ '' Ioo u₁ u₂ ⊆ V := (image_mono huS).trans hκV
  refine ⟨γ '' Ioo s₁ s₂, κ '' Ioo u₁ u₂,
    ⟨hγ.isOpenArc_image hT (by linarith) hs (by linarith),
      hκ.isOpenArc_image hT (by linarith) hu (by linarith),
      hUV.1.2.2.1.mono hUsub hVsub,
      hγ.inOpenEdge hT (by linarith) hs (by linarith),
      hκ.inOpenEdge hT (by linarith) hu (by linarith)⟩,
    hUsub, hVsub, ψ '' Ioo j₁ j₂, hψ.isOpenArc_image hT hj₁ hj hj₂,
    hψ.inOpenEdge hT hj₁ hj hj₂, fun p => ψ (q p), hψ.arc.1.comp_continuousOn hqc, ?_⟩
  rintro _ ⟨s, hs', rfl⟩ _ ⟨u, hu', rfl⟩
  obtain ⟨h1', h2'⟩ := hq s hs' u hu'
  exact ⟨⟨_, h1', rfl⟩, h2'⟩

omit [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
/-- A spherical parameter interval contains a spherical arc with an interior point. -/
theorem exists_sphericalArc_of_param {k : ℝ → T} (hk : IsArcParam k) {s₁ s₂ : ℝ} (h0 : 0 ≤ s₁)
    (h12 : s₁ < s₂) (h1 : s₂ ≤ 1) {c : T} {r : ℝ} (hr : 0 < r)
    (hsph : ∀ s ∈ Ioo s₁ s₂, dist c (k s) = r) :
    ∃ I e₁ e₂, IsSphericalArc I c r ∧ IsArcBetween I e₁ e₂ ∧ I ⊆ k '' Ioo s₁ s₂ ∧
      k ((s₁ + s₂) / 2) ∈ I ∧ k ((s₁ + s₂) / 2) ≠ e₁ ∧ k ((s₁ + s₂) / 2) ≠ e₂ := by
  set a := (3 * s₁ + s₂) / 4
  set b := (s₁ + 3 * s₂) / 4
  set m := (s₁ + s₂) / 2
  have ha : a ∈ Icc (0 : ℝ) 1 := ⟨by simp only [a]; linarith, by simp only [a]; linarith⟩
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨by simp only [b]; linarith, by simp only [b]; linarith⟩
  have hm : m ∈ Icc (0 : ℝ) 1 := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hab : a < b := by simp only [a, b]; linarith
  obtain ⟨k', hk', hk0, hk1, him⟩ := hk.exists_subarc ha hb hab.ne
  have hI : k' '' Icc 0 1 = k '' Icc a b := by rw [him, uIcc_of_le hab.le]
  have hsub : Icc a b ⊆ Ioo s₁ s₂ := fun y hy =>
    ⟨by simp only [a] at hy; linarith [hy.1], by simp only [b] at hy; linarith [hy.2]⟩
  refine ⟨k '' Icc a b, k a, k b, ⟨?_, hr, ?_⟩, ?_, image_mono hsub,
    ⟨m, ⟨by simp only [a, m]; linarith, by simp only [b, m]; linarith⟩, rfl⟩, ?_, ?_⟩
  · rw [← hI]; exact hk'.isArcBetween.isArc
  · rintro _ ⟨y, hy, rfl⟩; rw [mem_sphere, dist_comm]; exact hsph y (hsub hy)
  · have := hk'.isArcBetween; rwa [hk0, hk1, hI] at this
  · intro e; have := hk.2 hm ha e; simp only [a, m] at this; linarith
  · intro e; have := hk.2 hm hb e; simp only [b, m] at this; linarith

/-- **Proposition 6.5 (odd boxes lie on a sphere).** Let `U × V` be an odd box. Then there are
`c ∈ T` and `r > 0` with `U ∪ V ⊆ S(c, r)`. The point `c` is unique. -/
theorem prop_6_5 (hDMP : HasDMP T) {U V : Set T} (hUV : IsOddBox U V) :
    ∃ c : T, ∃ r : ℝ, 0 < r ∧ U ∪ V ⊆ sphere c r ∧ ∀ c' r', U ∪ V ⊆ sphere c' r' → c' = c := by
  have h2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  obtain ⟨γ, κ, hγ, hκ, α₁, β₁, α₂, β₂, h1, h2', h3, h4, h5, h6, hγU, hκV, hodd⟩ :=
    oddBox_params hT hUV
  obtain ⟨s₁, s₂, u₁, u₂, hs, hu, hsS, huS, c, r, hr, hsU, hsV⟩ :=
    param_box_sphere hT hDMP hγ hκ h1 h2' h3 h4 h5 h6 hodd
  have hsb := (Ioo_subset_Ioo_iff hs).1 hsS
  have hub := (Ioo_subset_Ioo_iff hu).1 huS
  obtain ⟨I, e₁, e₂, hI, hIe, hIsub, hpI, hp1, hp2⟩ :=
    exists_sphericalArc_of_param hγ.arc (by linarith) hs (by linarith) hr hsU
  obtain ⟨I', e₁', e₂', hI', hIe', -, hpI', hp1', hp2'⟩ :=
    exists_sphericalArc_of_param hκ.arc (by linarith) hu (by linarith) hr hsV
  have hpU : γ ((s₁ + s₂) / 2) ∈ U := hγU ⟨_, hsS ⟨by linarith, by linarith⟩, rfl⟩
  have hpV : κ ((u₁ + u₂) / 2) ∈ V := hκV ⟨_, huS ⟨by linarith, by linarith⟩, rfl⟩
  -- (S5) extension to the whole box
  have hVs : V ⊆ sphere c r := by
    intro b hb
    rw [mem_sphere, dist_comm]
    by_contra hne
    obtain ⟨hstr, hoddc⟩ := hUV.2 _ hpU b hb
    exact (Nat.not_even_iff_odd.2 hoddc) (lemma_6_3 hT hDMP hI hIe hpI hp1 hp2 hne hstr)
  have hUs : U ⊆ sphere c r := by
    intro a ha
    rw [mem_sphere, dist_comm]
    by_contra hne
    obtain ⟨hstr, hoddc⟩ := hUV.2 a ha _ hpV
    exact (Nat.not_even_iff_odd.2 (odd_oddCount_swap hT hstr hoddc))
      (lemma_6_3 hT hDMP hI' hIe' hpI' hp1' hp2' hne hstr.symm)
  refine ⟨c, r, hr, union_subset hUs hVs, fun c' r' hc' => ?_⟩
  exact (lemma_6_2 hT h2 hI).2.1.1 c' r'
    ((hIsub.trans ((image_mono hsS).trans hγU)).trans (subset_union_left.trans hc'))

/-- Strictness and `N` are locally constant. -/
theorem strict_nhds {a b : T} (h : IsStrictPair a b) :
    {p : T × T | IsStrictPair p.1 p.2 ∧ oddCount p.1 p.2 = oddCount a b} ∈ 𝓝 (a, b) := by
  have hfin := hT.vertices_finite
  have hev : ∀ᶠ p : T × T in 𝓝 (a, b), p.1 ≠ p.2 ∧
      ∀ u ∈ vertices T, 0 < sgnf p.1 p.2 u * sgnf a b u := by
    have hne : ∀ᶠ p : T × T in 𝓝 (a, b), p.1 ≠ p.2 :=
      (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds h.1
    refine hne.and ?_
    refine (eventually_all_finite hfin).2 fun u hu => ?_
    have hc : Continuous fun p : T × T => sgnf p.1 p.2 u * sgnf a b u :=
      (continuous_sgnf_param continuous_fst continuous_snd continuous_const).mul continuous_const
    exact (isOpen_lt continuous_const hc).mem_nhds (mul_self_pos.2 (h.2 u hu))
  filter_upwards [hev] with p hp
  refine ⟨⟨hp.1, fun u hu e => by have := hp.2 u hu; rw [e, zero_mul] at this; exact lt_irrefl _ this⟩,
    ?_⟩
  unfold oddCount
  congr 1
  ext u
  simp only [mem_setOf_eq]
  refine and_congr_right fun hu => ?_
  have := hp.2 u hu.1
  constructor
  · intro hl; by_contra hn; push_neg at hn; nlinarith
  · intro hl; by_contra hn; push_neg at hn; nlinarith

/-- **Corollary 6.7.** Let `(a, b)` be a strict pair of edge points with `N(a, b)` odd. Then there
are a unique `c ∈ T`, a radius `r > 0`, and open arcs `U ∋ a` and `V ∋ b` in open edges with
`U ∪ V ⊆ S(c, r)`. Moreover `c ∈ M(a', b')` for all `(a', b') ∈ U × V`; in particular `c` is an
edge point. -/
theorem cor_6_7 (hDMP : HasDMP T) {a b : T} (h : IsStrictPair a b) (ha : a ∉ vertices T)
    (hb : b ∉ vertices T) (hodd : Odd (oddCount a b)) :
    ∃ c : T, (∃ r : ℝ, 0 < r ∧ ∃ U V : Set T, IsOpenArc U ∧ IsOpenArc V ∧ a ∈ U ∧ b ∈ V ∧
        (∃ W, IsOpenEdge W ∧ U ⊆ W) ∧ (∃ W, IsOpenEdge W ∧ V ⊆ W) ∧ U ∪ V ⊆ sphere c r ∧
        (∀ a' ∈ U, ∀ b' ∈ V, c ∈ midset a' b')) ∧
      c ∉ vertices T ∧
      ∀ c' : T, ∀ r' : ℝ, ∀ U' V' : Set T, IsOpenArc U' → IsOpenArc V' → a ∈ U' → b ∈ V' →
        U' ∪ V' ⊆ sphere c' r' → c' = c := by
  have h2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  -- an odd box around `(a, b)`
  obtain ⟨N₁, hN₁, N₂, hN₂, hN⟩ := mem_nhds_prod_iff.1 (strict_nhds hT h)
  have hd : 0 < dist a b := dist_pos.2 h.1
  set O₁ := interior N₁ ∩ ball a (dist a b / 2)
  set O₂ := interior N₂ ∩ ball b (dist a b / 2)
  have hO₁ : IsOpen O₁ := isOpen_interior.inter isOpen_ball
  have hO₂ : IsOpen O₂ := isOpen_interior.inter isOpen_ball
  have haO : a ∈ O₁ := ⟨mem_interior_iff_mem_nhds.2 hN₁, mem_ball_self (by linarith)⟩
  have hbO : b ∈ O₂ := ⟨mem_interior_iff_mem_nhds.2 hN₂, mem_ball_self (by linarith)⟩
  obtain ⟨γ, hγ, -, α₁, β₁, h1, h2', h3, haU, hγU⟩ := exists_param_interval hT hO₁ haO ha
  obtain ⟨κ, hκ, -, α₂, β₂, h4, h5, h6, hbV, hκV⟩ := exists_param_interval hT hO₂ hbO hb
  set U := γ '' Ioo α₁ β₁
  set V := κ '' Ioo α₂ β₂
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    have h1 := (hγU hxU).2; have h2 := (hκV hxV).2
    rw [mem_ball] at h1 h2
    have := dist_triangle_left a b x
    linarith
  have hbox : IsOddBox U V := by
    refine ⟨⟨hγ.isOpenArc_image hT h1 h2' h3, hκ.isOpenArc_image hT h4 h5 h6, hdisj,
      hγ.inOpenEdge hT h1 h2' h3, hκ.inOpenEdge hT h4 h5 h6⟩, fun a' ha' b' hb' => ?_⟩
    obtain ⟨hs, hn⟩ := hN (mk_mem_prod (interior_subset (hγU ha').1)
      (interior_subset (hκV hb').1))
    exact ⟨hs, hn ▸ hodd⟩
  obtain ⟨c, r, hr, hsph, -⟩ := prop_6_5 hT hDMP hbox
  have hmid : ∀ a' ∈ U, ∀ b' ∈ V, c ∈ midset a' b' := fun a' ha' b' hb' => by
    have e1 := hsph (Or.inl ha'); have e2 := hsph (Or.inr hb')
    rw [mem_sphere, dist_comm] at e1 e2
    show dist c a' = dist c b'
    rw [e1, e2]
  refine ⟨c, ⟨r, hr, U, V, hbox.1.1, hbox.1.2.1, haU, hbV, hbox.1.2.2.2.1, hbox.1.2.2.2.2,
    hsph, hmid⟩, h.notMem_vertices (hmid a haU b hbV), ?_⟩
  -- uniqueness: a common spherical subarc around `a`
  intro c' r' U' V' hU' _ haU' _ hc'
  obtain ⟨γ', hγ', -, α, β, h7, h8, h9, -, hγ'U⟩ :=
    exists_param_interval hT ((hγ.isOpenArc_image hT h1 h2' h3).1.inter hU'.1) ⟨haU, haU'⟩ ha
  have hsph' : ∀ s ∈ Ioo α β, dist c (γ' s) = r := fun s hs => by
    have := hsph (Or.inl (hγ'U ⟨s, hs, rfl⟩).1); rw [mem_sphere, dist_comm] at this; exact this
  obtain ⟨I, -, -, hI, -, hIsub, -⟩ := exists_sphericalArc_of_param hγ'.arc h7 h8 h9 hr hsph'
  exact (lemma_6_2 hT h2 hI).2.1.1 c' r'
    (fun x hx => hc' (Or.inl (hγ'U (hIsub hx)).2))

end DoubleMidset
