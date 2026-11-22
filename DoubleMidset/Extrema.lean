module

public import DoubleMidset.Reduction
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Instances.Rat

/-!
# Protected signs, local extrema and the grid lemma (Lemmas 2.2, 2.8, 2.9)

* **Lemma 2.2** (`lemma_2_2_a`, `lemma_2_2_b`, `three_le_encard_of_sets`): strict signs of
  `f_{a,b}` survive small moves of the sites; disjointly placed connected sets on which `f_{a,b}`
  changes sign force as many zeros.
* **Lemma 2.8** (`lemma_2_8_i`, `lemma_2_8_ii`, `lemma_2_8_iii`): for a function on an open
  interval, the values at local extrema form a countable set; the local extrema form a meagre set
  if the function is constant on no subinterval; a point that is not a local extremum has larger
  and smaller values arbitrarily close.
* **Lemma 2.9** (`lemma_2_9`, the grid lemma).
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

section Signs

variable {X : Type u} [MetricSpace X]

/-- **Lemma 2.2 (a)**: a strict sign of `f_{a,b}` at a test point `t` survives moving the sites by
less than `|f_{a,b}(t)|` in total. -/
theorem lemma_2_2_a {a b a' b' t : X} (h : dist a a' + dist b b' < |sgnf a b t|) :
    (0 < sgnf a b t → 0 < sgnf a' b' t) ∧ (sgnf a b t < 0 → sgnf a' b' t < 0) := by
  have h1 := sgnf_lipschitz_left a a' b t
  have h2 := sgnf_lipschitz_right a' b b' t
  rw [abs_le] at h1 h2
  constructor
  · intro hp; rw [abs_of_pos hp] at h; linarith [h1.1, h2.1]
  · intro hn; rw [abs_of_neg hn] at h; linarith [h1.2, h2.2]

/-- **Lemma 2.2 (b)**: if `A₁, …, A_k` are connected sets, each containing points where
`f_{a,b} < 0` and where `f_{a,b} > 0`, and no point of `M(a, b)` lies in two of them, then
`|M(a, b)| ≥ k`. -/
theorem lemma_2_2_b {a b : X} {k : ℕ} (A : Fin k → Set X) (hA : ∀ i, IsPreconnected (A i))
    (hneg : ∀ i, ∃ y ∈ A i, sgnf a b y < 0) (hpos : ∀ i, ∃ y ∈ A i, 0 < sgnf a b y)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i ∩ midset a b) (A j ∩ midset a b)) :
    (k : ℕ∞) ≤ (midset a b).encard := by
  have hz : ∀ i, ∃ z ∈ A i, z ∈ midset a b := by
    intro i
    obtain ⟨y, hy, hyn⟩ := hneg i
    obtain ⟨w, hw, hwp⟩ := hpos i
    obtain ⟨z, hz, hz0⟩ := (hA i).intermediate_value hy hw (continuous_sgnf a b).continuousOn
      ⟨hyn.le, hwp.le⟩
    exact ⟨z, hz, sgnf_eq_zero_iff.1 hz0⟩
  choose z hzA hzM using hz
  have hinj : Injective z := fun i j h => by
    by_contra hij
    exact disjoint_left.1 (hdisj i j hij) ⟨hzA i, hzM i⟩ (h ▸ ⟨hzA j, hzM j⟩)
  calc (k : ℕ∞) = (range z).encard := by
        rw [← image_univ, hinj.encard_image, encard_univ, ENat.card_eq_coe_fintype_card,
          Fintype.card_fin]
    _ ≤ _ := encard_le_encard (by rintro _ ⟨i, rfl⟩; exact hzM i)

/-- Three connected sets as in Lemma 2.2 (b) give three zeros. -/
theorem three_le_encard_of_sets {a b : X} {A₁ A₂ A₃ : Set X} (h₁ : IsPreconnected A₁)
    (h₂ : IsPreconnected A₂) (h₃ : IsPreconnected A₃)
    (hn₁ : ∃ y ∈ A₁, sgnf a b y < 0) (hp₁ : ∃ y ∈ A₁, 0 < sgnf a b y)
    (hn₂ : ∃ y ∈ A₂, sgnf a b y < 0) (hp₂ : ∃ y ∈ A₂, 0 < sgnf a b y)
    (hn₃ : ∃ y ∈ A₃, sgnf a b y < 0) (hp₃ : ∃ y ∈ A₃, 0 < sgnf a b y)
    (d₁₂ : Disjoint (A₁ ∩ midset a b) (A₂ ∩ midset a b))
    (d₁₃ : Disjoint (A₁ ∩ midset a b) (A₃ ∩ midset a b))
    (d₂₃ : Disjoint (A₂ ∩ midset a b) (A₃ ∩ midset a b)) : 3 ≤ (midset a b).encard := by
  have := lemma_2_2_b (k := 3) ![A₁, A₂, A₃] (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | assumption |
        exact Disjoint.symm (by assumption))
  exact_mod_cast this

/-- Three zeros contradict `|M| ≤ 2`. -/
theorem false_of_three {a b : X} (hab : a ≠ b) (h2 : MidsetsAtMostTwo X)
    (h : 3 ≤ (midset a b).encard) : False :=
  absurd (h.trans (h2 a b hab)) (by decide)

end Signs

section Extrema

variable {g : ℝ → ℝ} {α β : ℝ}

/-- **Lemma 2.8 (i)**: the values of `g` at its local extrema form a countable set. -/
theorem lemma_2_8_i (g : ℝ → ℝ) : (g '' {s | IsLocalExtr g s}).Countable := by
  have key : g '' {s | IsLocalExtr g s} ⊆
      ⋃ q : ℚ × ℚ, {sSup (g '' Icc (q.1 : ℝ) q.2), sInf (g '' Icc (q.1 : ℝ) q.2)} := by
    rintro _ ⟨s, hs, rfl⟩
    rcases hs with hs | hs
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
      obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show s - ε < s by linarith)
      obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show s < s + ε by linarith)
      refine mem_iUnion.2 ⟨(q₁, q₂), Or.inr ?_⟩
      have hsI : s ∈ Icc (q₁ : ℝ) q₂ := ⟨hq₁.2.le, hq₂.1.le⟩
      have hl : IsLeast (g '' Icc (q₁ : ℝ) q₂) (g s) := by
        refine ⟨⟨s, hsI, rfl⟩, ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        exact hball (show y ∈ ball s ε by
          rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])
      exact hl.csInf_eq.symm
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
      obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show s - ε < s by linarith)
      obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show s < s + ε by linarith)
      refine mem_iUnion.2 ⟨(q₁, q₂), Or.inl ?_⟩
      have hsI : s ∈ Icc (q₁ : ℝ) q₂ := ⟨hq₁.2.le, hq₂.1.le⟩
      have hl : IsGreatest (g '' Icc (q₁ : ℝ) q₂) (g s) := by
        refine ⟨⟨s, hsI, rfl⟩, ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        exact hball (show y ∈ ball s ε by
          rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2])
      exact hl.csSup_eq.symm
  exact (countable_iUnion fun q => (countable_singleton _).insert _).mono key

/-- **Lemma 2.8 (ii)**: if `g` is continuous on the open interval `(α, β)` and constant on no
nondegenerate subinterval, its local extrema in `(α, β)` form a meagre set. -/
theorem lemma_2_8_ii (hg : ContinuousOn g (Ioo α β))
    (hnc : ∀ c d, c < d → Ioo c d ⊆ Ioo α β → ∃ y ∈ Ioo c d, ∃ z ∈ Ioo c d, g y ≠ g z) :
    IsMeagre {s | s ∈ Ioo α β ∧ IsLocalExtr g s} := by
  -- level sets of the maximum and minimum on rational subintervals of `(α, β)`
  classical
  set v : ℚ × ℚ → Bool → ℝ := fun q b => if b then sSup (g '' Icc (q.1 : ℝ) q.2)
    else sInf (g '' Icc (q.1 : ℝ) q.2)
  set L : ℚ × ℚ → Bool → Set ℝ := fun q b => if Icc (q.1 : ℝ) q.2 ⊆ Ioo α β then
    Icc (q.1 : ℝ) q.2 ∩ g ⁻¹' {v q b} else ∅
  have hnd : ∀ q b, IsMeagre (L q b) := by
    intro q b
    simp only [L]
    split_ifs with h
    · have hc : IsClosed (Icc (q.1 : ℝ) q.2 ∩ g ⁻¹' {v q b}) :=
        (hg.mono h).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
      have hint : interior (Icc (q.1 : ℝ) q.2 ∩ g ⁻¹' {v q b}) = ∅ := by
        by_contra hne
        obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
        have hsub : Ioo (y - ε) (y + ε) ⊆ Icc (q.1 : ℝ) q.2 ∩ g ⁻¹' {v q b} := fun z hz =>
          interior_subset (hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;>
            linarith [hz.1, hz.2]))
        obtain ⟨w, hw, w', hw', hne'⟩ := hnc (y - ε) (y + ε) (by linarith)
          (fun z hz => h (hsub hz).1)
        exact hne' ((hsub hw).2.trans (hsub hw').2.symm)
      exact (hc.isNowhereDense_iff.2 hint).isMeagre
    · exact IsMeagre.empty
  refine (isMeagre_iUnion fun q => isMeagre_iUnion fun b => hnd q b).mono ?_
  rintro s ⟨hsJ, hs⟩
  obtain ⟨r, hr, hrJ⟩ := Metric.isOpen_iff.1 isOpen_Ioo s hsJ
  have hext : ∀ {P : ℝ → Prop}, (∀ᶠ y in 𝓝 s, P y) → ∃ q : ℚ × ℚ, Icc (q.1 : ℝ) q.2 ⊆ Ioo α β ∧
      s ∈ Icc (q.1 : ℝ) q.2 ∧ ∀ y ∈ Icc (q.1 : ℝ) q.2, P y := by
    intro P hP
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hP
    set δ := min ε r
    obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show s - δ < s by linarith [lt_min hε hr])
    obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show s < s + δ by linarith [lt_min hε hr])
    have hmem : ∀ y ∈ Icc (q₁ : ℝ) q₂, dist y s < δ := fun y hy => by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
    exact ⟨(q₁, q₂), fun y hy => hrJ (lt_of_lt_of_le (hmem y hy) (min_le_right _ _)),
      ⟨hq₁.2.le, hq₂.1.le⟩, fun y hy => hball (lt_of_lt_of_le (hmem y hy) (min_le_left _ _))⟩
  rcases hs with hs | hs
  · obtain ⟨q, hqJ, hsq, hq⟩ := hext hs
    refine mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨false, ?_⟩⟩
    simp only [L, v, if_pos hqJ]
    have hl : IsLeast (g '' Icc (q.1 : ℝ) q.2) (g s) :=
      ⟨⟨s, hsq, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hq y hy⟩
    exact ⟨hsq, by simp [hl.csInf_eq]⟩
  · obtain ⟨q, hqJ, hsq, hq⟩ := hext hs
    refine mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨true, ?_⟩⟩
    simp only [L, v, if_pos hqJ]
    have hl : IsGreatest (g '' Icc (q.1 : ℝ) q.2) (g s) :=
      ⟨⟨s, hsq, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hq y hy⟩
    exact ⟨hsq, by simp [hl.csSup_eq]⟩

/-- **Lemma 2.8 (iii)**: if `s` is not a local extremum of `g`, every neighbourhood of `s` contains
points with smaller and with larger values. -/
theorem lemma_2_8_iii {s : ℝ} (hs : ¬ IsLocalExtr g s) {N : Set ℝ} (hN : N ∈ 𝓝 s) :
    ∃ s' ∈ N, ∃ s'' ∈ N, g s' < g s ∧ g s < g s'' := by
  rw [IsLocalExtr, IsExtrFilter, not_or] at hs
  obtain ⟨hmin, hmax⟩ := hs
  have h1 : ∃ᶠ y in 𝓝 s, g y < g s := by
    rw [IsMinFilter, Filter.not_eventually] at hmin
    exact hmin.mono fun y hy => not_le.1 hy
  have h2 : ∃ᶠ y in 𝓝 s, g s < g y := by
    rw [IsMaxFilter, Filter.not_eventually] at hmax
    exact hmax.mono fun y hy => not_le.1 hy
  obtain ⟨s', hs', hs'N⟩ := (h1.and_eventually hN).exists
  obtain ⟨s'', hs'', hs''N⟩ := (h2.and_eventually hN).exists
  exact ⟨s', hs'N, s'', hs''N, hs', hs''⟩

/-- A value in a nondegenerate interval avoiding a countable set (used with Lemma 2.8 (i)). -/
theorem exists_mem_Ioo_notMem {S : Set ℝ} (hS : S.Countable) {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, c ∉ S := by
  obtain ⟨c, hc, hac, hcb⟩ := (hS.dense_compl ℝ).exists_between hab
  exact ⟨c, ⟨hac, hcb⟩, hc⟩


/-- **Lemma 2.9 (grid lemma).** Let `U, V` be nonempty open intervals and `E ⊆ U`, `F ⊆ V`
meagre. Then `G = ((U \ E) × V) ∪ (U × (V \ F))` is connected and dense in `U × V`; consequently
a continuous function on `U × V` without zeros on `G` is either `≥ 0` or `≤ 0` on all of
`U × V`. -/
theorem lemma_2_9 {a b c d : ℝ} (hab : a < b) (hcd : c < d) {E F : Set ℝ} (hE : E ⊆ Ioo a b)
    (hF : F ⊆ Ioo c d) (hEm : IsMeagre E) (hFm : IsMeagre F) :
    IsConnected (((Ioo a b \ E) ×ˢ Ioo c d) ∪ (Ioo a b ×ˢ (Ioo c d \ F))) ∧
    Ioo a b ×ˢ Ioo c d ⊆ closure (((Ioo a b \ E) ×ˢ Ioo c d) ∪ (Ioo a b ×ˢ (Ioo c d \ F))) ∧
    ∀ g : ℝ × ℝ → ℝ, ContinuousOn g (Ioo a b ×ˢ Ioo c d) →
      (∀ z ∈ ((Ioo a b \ E) ×ˢ Ioo c d) ∪ (Ioo a b ×ˢ (Ioo c d \ F)), g z ≠ 0) →
      (∀ z ∈ Ioo a b ×ˢ Ioo c d, 0 ≤ g z) ∨ (∀ z ∈ Ioo a b ×ˢ Ioo c d, g z ≤ 0) := by
  set U := Ioo a b
  set V := Ioo c d
  set G := ((U \ E) ×ˢ V) ∪ (U ×ˢ (V \ F))
  have hEd : Dense Eᶜ := dense_of_mem_residual hEm
  have hFd : Dense Fᶜ := dense_of_mem_residual hFm
  have hUE : U ⊆ closure (U \ E) := by
    rw [diff_eq]; exact hEd.open_subset_closure_inter isOpen_Ioo
  have hVF : V ⊆ closure (V \ F) := by
    rw [diff_eq]; exact hFd.open_subset_closure_inter isOpen_Ioo
  obtain ⟨a₀, ha₀⟩ : (U \ E).Nonempty := by
    rw [diff_eq]; exact hEd.inter_open_nonempty U isOpen_Ioo (nonempty_Ioo.2 hab)
  obtain ⟨c₀, hc₀⟩ : (V \ F).Nonempty := by
    rw [diff_eq]; exact hFd.inter_open_nonempty V isOpen_Ioo (nonempty_Ioo.2 hcd)
  have hGpc : IsPreconnected G := by
    refine isPreconnected_of_forall (a₀, c₀) fun z hz => ?_
    rcases hz with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · refine ⟨({z.1} ×ˢ V) ∪ (U ×ˢ {c₀}), ?_, Or.inr ⟨ha₀.1, rfl⟩,
        Or.inl ⟨rfl, hv⟩, ?_⟩
      · rintro w (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
        · exact Or.inl ⟨(mem_singleton_iff.1 hw1) ▸ hu, hw2⟩
        · exact Or.inr ⟨hw1, (mem_singleton_iff.1 hw2) ▸ hc₀⟩
      · exact IsPreconnected.union (z.1, c₀) ⟨rfl, hc₀.1⟩ ⟨hu.1, rfl⟩
          (isPreconnected_singleton.prod isPreconnected_Ioo)
          (isPreconnected_Ioo.prod isPreconnected_singleton)
    · refine ⟨(U ×ˢ {z.2}) ∪ ({a₀} ×ˢ V), ?_, Or.inr ⟨rfl, hc₀.1⟩,
        Or.inl ⟨hu, rfl⟩, ?_⟩
      · rintro w (⟨hw1, hw2⟩ | ⟨hw1, hw2⟩)
        · exact Or.inr ⟨hw1, (mem_singleton_iff.1 hw2) ▸ hv⟩
        · exact Or.inl ⟨(mem_singleton_iff.1 hw1) ▸ ha₀, hw2⟩
      · exact IsPreconnected.union (a₀, z.2) ⟨ha₀.1, rfl⟩ ⟨rfl, hv.1⟩
          (isPreconnected_Ioo.prod isPreconnected_singleton)
          (isPreconnected_singleton.prod isPreconnected_Ioo)
  have hdense : U ×ˢ V ⊆ closure G := by
    intro z hz
    have : z ∈ closure ((U \ E) ×ˢ V) := by
      rw [closure_prod_eq]; exact ⟨hUE hz.1, subset_closure hz.2⟩
    exact closure_mono subset_union_left this
  refine ⟨⟨⟨(a₀, c₀), Or.inl ⟨ha₀, hc₀.1⟩⟩, hGpc⟩, hdense, fun g hg hg0 => ?_⟩
  have hGsub : G ⊆ U ×ˢ V := by
    rintro z (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · exact ⟨hu.1, hv⟩
    · exact ⟨hu, hv.1⟩
  -- constant sign on `G`
  have hsign : (∀ z ∈ G, 0 < g z) ∨ (∀ z ∈ G, g z < 0) := by
    by_contra h
    push_neg at h
    obtain ⟨⟨z₁, hz₁, h₁⟩, ⟨z₂, hz₂, h₂⟩⟩ := h
    obtain ⟨w, hw, hw0⟩ := hGpc.intermediate_value hz₁ hz₂ (hg.mono hGsub)
      ⟨h₁, h₂⟩
    exact hg0 w hw hw0
  have hopen : IsOpen (U ×ˢ V) := isOpen_Ioo.prod isOpen_Ioo
  rcases hsign with h | h
  · left
    intro z hz
    by_contra hneg; push_neg at hneg
    have hca := (hg z hz).continuousAt (hopen.mem_nhds hz)
    have hN : {w | g w < 0} ∈ 𝓝 z := hca.preimage_mem_nhds (Iio_mem_nhds hneg)
    obtain ⟨w, hwN, hwG⟩ := mem_closure_iff_nhds.1 (hdense hz) _ hN
    exact absurd (h w hwG) (not_lt.2 hwN.le)
  · right
    intro z hz
    by_contra hpos; push_neg at hpos
    have hca := (hg z hz).continuousAt (hopen.mem_nhds hz)
    have hN : {w | 0 < g w} ∈ 𝓝 z := hca.preimage_mem_nhds (Ioi_mem_nhds hpos)
    obtain ⟨w, hwN, hwG⟩ := mem_closure_iff_nhds.1 (hdense hz) _ hN
    exact absurd (h w hwG) (not_lt.2 hwN.le)

end Extrema

end DoubleMidset
