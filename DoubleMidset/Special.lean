module

public import DoubleMidset.Main

/-!
# Arcs and simple triods are finite trees

These facts, used implicitly by the paper (Theorem B, "in particular"; Theorems 10.1 and 11.1),
give the statements `theorem_10_1` and `theorem_11_1` for spaces that are a simple triod or an
arc.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {X : Type u} [MetricSpace X]

/-- No simple closed curve lies in an arc. -/
theorem not_scc_subset_arc {A : Set X} (hA : IsArc A) {C : Set X} (hC : IsSimpleClosedCurve C)
    (hCA : C ⊆ A) : False := by
  obtain ⟨e⟩ := hA
  obtain ⟨c, hc, hper, hinj, hCim, -⟩ := hC.exists_param
  have hcA : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ A := fun t ht => hCA (hCim ▸ ⟨t, ht, rfl⟩)
  -- a continuous real function with equal ends, injective on `[0, 1)`
  let φ : ℝ → ℝ := fun t => (e ⟨c (max 0 (min t 1)), hcA _ ⟨le_max_left _ _,
    max_le zero_le_one (min_le_right _ _)⟩⟩ : ℝ)
  have hφc : Continuous φ := continuous_subtype_val.comp (e.continuous.comp
    ((hc.comp (continuous_const.max (continuous_id.min continuous_const))).subtype_mk _))
  have hclamp : ∀ t ∈ Icc (0 : ℝ) 1, max 0 (min t 1) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have h01 : φ 0 = φ 1 := by
    show (e ⟨c (max 0 (min 0 1)), _⟩ : ℝ) = (e ⟨c (max 0 (min 1 1)), _⟩ : ℝ)
    congr 3
    rw [hclamp 0 ⟨le_rfl, zero_le_one⟩, hclamp 1 ⟨zero_le_one, le_rfl⟩]
    have := hper 0; rw [zero_add] at this; exact this.symm
  obtain ⟨s, t, hs0, hst, ht1, he⟩ := exists_eq_of_eq_ends hφc h01
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, by linarith⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht1.le⟩
  have hφs : φ s = (e ⟨c s, hcA s hsI⟩ : ℝ) := by
    show (e ⟨c (max 0 (min s 1)), _⟩ : ℝ) = _; congr 3; rw [hclamp s hsI]
  have hφt : φ t = (e ⟨c t, hcA t htI⟩ : ℝ) := by
    show (e ⟨c (max 0 (min t 1)), _⟩ : ℝ) = _; congr 3; rw [hclamp t htI]
  rw [hφs, hφt] at he
  have := e.injective (Subtype.ext he)
  have hct : c s = c t := congrArg Subtype.val this
  exact hst.ne (hinj ⟨hs0, by linarith⟩ ⟨by linarith, ht1⟩ hct)

/-- A simple closed curve minus a point is connected. -/
theorem IsSimpleClosedCurve.isPreconnected_diff {C : Set X} (hC : IsSimpleClosedCurve C)
    (y : X) : IsPreconnected (C \ {y}) := by
  obtain ⟨c, hc, hper, hinj, hCim, hIco⟩ := hC.exists_param
  by_cases hy : y ∈ C
  · rw [← hIco] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have : C \ {c s} = c '' Ioo s (s + 1) := by
      ext z; constructor
      · rintro ⟨hz, hzs⟩
        rw [← hIco] at hz
        obtain ⟨u, hu, rfl⟩ := hz
        rcases lt_or_gt_of_ne (fun h : u = s => hzs (by rw [h]; rfl)) with h | h
        · exact ⟨u + 1, ⟨by linarith [hu.1, hs.2], by linarith⟩, hper u⟩
        · exact ⟨u, ⟨h, by linarith [hu.2, hs.1]⟩, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        rcases lt_or_ge u 1 with h | h
        · have huI : u ∈ Ico (0 : ℝ) 1 := ⟨by linarith [hu.1, hs.1], h⟩
          refine ⟨hIco ▸ ⟨u, huI, rfl⟩, fun hz => ?_⟩
          have := hinj huI hs hz; linarith [hu.1]
        · have huI : u - 1 ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith [hu.2, hs.2]⟩
          have hcu : c (u - 1) = c u := by
            have := hper (u - 1); rw [sub_add_cancel] at this; exact this.symm
          refine ⟨hIco ▸ ⟨u - 1, huI, hcu⟩, fun hz => ?_⟩
          rw [← hcu] at hz
          have := hinj huI hs hz; linarith [hu.2]
    rw [this]; exact isPreconnected_Ioo.image _ hc.continuousOn
  · rw [diff_singleton_eq_self hy, ← hCim]
    exact isPreconnected_Icc.image _ hc.continuousOn

/-- The image of a parameter window is open in a space parametrized by an arc. -/
theorem open_window {g : ℝ → X} (hg : IsArcParam g) {K : Set X} (hK : IsClosed K)
    (hcov : ∀ z, z ∈ g '' Icc 0 1 ∨ z ∈ K) {a b : ℝ}
    (hdisj : ∀ t ∈ Ioo a b ∩ Icc 0 1, g t ∉ K) : IsOpen (g '' (Ioo a b ∩ Icc 0 1)) := by
  have hcompl : (g '' (Ioo a b ∩ Icc 0 1))ᶜ = g '' (Icc 0 1 \ Ioo a b) ∪ K := by
    ext z; constructor
    · intro hz
      rcases hcov z with ⟨t, ht, rfl⟩ | hzK
      · exact Or.inl ⟨t, ⟨ht, fun h => hz ⟨t, ⟨h, ht⟩, rfl⟩⟩, rfl⟩
      · exact Or.inr hzK
    · rintro (⟨t, ⟨ht, hnt⟩, rfl⟩ | hzK) ⟨s, ⟨hs1, hs2⟩, he⟩
      · exact hnt (hg.2 hs2 ht he ▸ hs1)
      · rw [← he] at hzK
        exact hdisj s ⟨hs1, hs2⟩ hzK
  rw [← isClosed_compl_iff, hcompl]
  exact ((isCompact_Icc.diff isOpen_Ioo).image hg.1).isClosed.union hK

theorem window_isConnected {g : ℝ → X} (hg : IsArcParam g) {a b t : ℝ} (ht : t ∈ Ioo a b)
    (ht' : t ∈ Icc (0 : ℝ) 1) : IsConnected (g '' (Ioo a b ∩ Icc 0 1)) :=
  ⟨⟨g t, t, ⟨ht, ht'⟩, rfl⟩, ((ordConnected_Ioo.inter ordConnected_Icc).isPreconnected).image _
    hg.1.continuousOn⟩

theorem encard_pair_le' (a b : Set X) : ({a, b} : Set (Set X)).encard ≤ 2 := by
  refine (encard_insert_le _ _).trans ?_
  rw [encard_singleton]; rfl

/-- Local connectedness at a point of an arc piece other than its base point. -/
theorem piece_lc {g : ℝ → X} (hg : IsArcParam g) {K : Set X} (hK : IsClosed K)
    (hcov : ∀ z, z ∈ g '' Icc 0 1 ∨ z ∈ K) (hdisj : ∀ t ∈ Ioc (0 : ℝ) 1, g t ∉ K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (ht0 : 0 < t ∨ K = ∅) {U : Set X} (hU : U ∈ 𝓝 (g t)) :
    ∃ V ⊆ U, IsOpen V ∧ g t ∈ V ∧ IsConnected V := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (hg.1.continuousAt.preimage_mem_nhds hU)
  have hδ' : 0 < min δ (if 0 < t then t else 1) := lt_min hδ (by split_ifs with h <;> linarith)
  set δ' := min δ (if 0 < t then t else 1)
  refine ⟨g '' (Ioo (t - δ') (t + δ') ∩ Icc 0 1), ?_, ?_, ⟨t, ⟨⟨by linarith, by linarith⟩, ht⟩,
    rfl⟩, window_isConnected hg ⟨by linarith, by linarith⟩ ht⟩
  · rintro _ ⟨s, ⟨hs, -⟩, rfl⟩
    exact hball (by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2, min_le_left δ (if 0 < t then t else 1)])
  · refine open_window hg hK hcov fun s hs => ?_
    rcases ht0 with h | h
    · have : δ' ≤ t := by simp only [δ', if_pos h]; exact min_le_right _ _
      exact hdisj s ⟨by linarith [hs.1.1], hs.2.2⟩
    · rw [h]; exact notMem_empty _

/-- Order at most two at a point of an arc piece other than its base point. -/
theorem piece_order {g : ℝ → X} (hg : IsArcParam g) {K : Set X} (hKc : IsPreconnected K)
    (hvK : g 0 ∈ K ∨ K = ∅) (hcov : ∀ z, z ∈ g '' Icc 0 1 ∨ z ∈ K)
    (hdisj : ∀ t ∈ Ioc (0 : ℝ) 1, g t ∉ K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht0 : 0 < t ∨ K = ∅) : order (g t) ≤ 2 := by
  have hgtK : g t ∉ K := by
    rcases ht0 with h | h
    · exact hdisj t ⟨h, ht.2⟩
    · rw [h]; exact notMem_empty _
  have hsub : {C : Set X | ∃ y, y ≠ g t ∧ C = connectedComponentIn {g t}ᶜ y} ⊆
      {connectedComponentIn {g t}ᶜ (g 0), connectedComponentIn {g t}ᶜ (g 1)} := by
    rintro _ ⟨y, hy, rfl⟩
    have hP : g '' Ico 0 t ∪ K ⊆ {g t}ᶜ →
        y ∈ g '' Ico 0 t ∪ K → g 0 ∈ g '' Ico 0 t ∪ K →
        connectedComponentIn {g t}ᶜ y = connectedComponentIn {g t}ᶜ (g 0) := by
      intro hsub' hy' h0'
      have hpc : IsPreconnected (g '' Ico 0 t ∪ K) := by
        rcases hvK with hvK | hvK
        · rcases eq_or_lt_of_le ht.1 with h0 | h0
          · have : g '' Ico 0 t = ∅ := by rw [← h0, Ico_self, image_empty]
            rw [this, empty_union]; exact hKc
          · exact hg.isPreconnected_image_Ico.union (g 0) ⟨0, ⟨le_rfl, h0⟩, rfl⟩ hvK hKc
        · rw [hvK, union_empty]; exact hg.isPreconnected_image_Ico
      exact connectedComponentIn_eq (hpc.subset_connectedComponentIn hy' hsub' h0')
    have hsub1 : g '' Ico 0 t ∪ K ⊆ {g t}ᶜ := by
      rintro _ (⟨u, hu, rfl⟩ | hzK) he
      · exact hu.2.ne (hg.2 ⟨hu.1, hu.2.le.trans ht.2⟩ ht he)
      · exact hgtK (mem_singleton_iff.1 he ▸ hzK)
    rcases hcov y with ⟨s, hs, rfl⟩ | hyK
    · have hst : s ≠ t := fun h => hy (h ▸ rfl)
      rcases lt_or_gt_of_ne hst with h | h
      · left
        exact hP hsub1 (Or.inl ⟨s, ⟨hs.1, h⟩, rfl⟩)
          (Or.inl ⟨0, ⟨le_rfl, lt_of_le_of_lt hs.1 h⟩, rfl⟩)
      · right
        have hQ : g '' Ioc t 1 ⊆ {g t}ᶜ := by
          rintro _ ⟨u, hu, rfl⟩ he
          exact hu.1.ne' (hg.2 ⟨ht.1.trans hu.1.le, hu.2⟩ ht he)
        have := hg.isPreconnected_image_Ioc.subset_connectedComponentIn
          (⟨s, ⟨h, hs.2⟩, rfl⟩ : g s ∈ g '' Ioc t 1) hQ
        exact connectedComponentIn_eq (this ⟨1, ⟨lt_of_lt_of_le h hs.2, le_rfl⟩, rfl⟩)
    · left
      rcases hvK with hvK | hvK
      · exact hP hsub1 (Or.inr hyK) (Or.inr hvK)
      · rw [hvK] at hyK; exact absurd hyK (notMem_empty _)
  exact (encard_le_encard hsub).trans (encard_pair_le' _ _)

/-- **An arc is a finite tree.** -/
theorem arc_isFiniteTree (h : IsArc (univ : Set X)) : IsFiniteTree X := by
  obtain ⟨p, q, hpq⟩ := h.exists_isArcBetween
  obtain ⟨g, hg, him, -, -⟩ := hpq.exists_param
  have hcov : ∀ z : X, z ∈ g '' Icc 0 1 ∨ z ∈ (∅ : Set X) := fun z => Or.inl (him ▸ trivial)
  have hc : CompactSpace X := ⟨by rw [← him]; exact isCompact_Icc.image hg.1⟩
  have hconn : ConnectedSpace X := connectedSpace_iff_univ.2
    (by rw [← him]; exact (isConnected_Icc zero_le_one).image _ hg.1.continuousOn)
  have hnt : Nontrivial X := ⟨⟨g 0, g 1, hg.ne⟩⟩
  have hlc : LocallyConnectedSpace X := by
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro x U hU
    obtain ⟨t, ht, rfl⟩ := (hcov x).resolve_right (notMem_empty _)
    exact piece_lc hg isClosed_empty hcov (fun _ _ => notMem_empty _) ht (Or.inr rfl) hU
  have hord : ∀ x : X, order x ≤ 2 := fun x => by
    obtain ⟨t, ht, rfl⟩ := (hcov x).resolve_right (notMem_empty _)
    exact piece_order hg isPreconnected_empty (Or.inr rfl) hcov (fun _ _ => notMem_empty _) ht
      (Or.inr rfl)
  have hnb : ∀ x : X, ¬ IsBranchPoint x := fun x hx => by
    have h3 : 3 ≤ order x := hx
    exact absurd (h3.trans (hord x)) (by decide)
  refine ⟨⟨⟨hc, hconn, hnt, inferInstance⟩, hlc, fun C hC => not_scc_subset_arc h hC
    (subset_univ C)⟩, ?_, fun p hp => absurd hp (hnb p)⟩
  rw [show {p : X | IsBranchPoint p} = ∅ from eq_empty_of_forall_notMem hnb]
  exact finite_empty

/-- **Theorem 11.1.** No compatible metric on an arc has the DMP. -/
theorem theorem_11_1 (h : IsArc (univ : Set X)) : ¬ HasDMP X :=
  theorem_B (arc_isFiniteTree h)

/-- The initial segment of an arc piece, together with the rest of the space, is open. -/
theorem open_start {g : ℝ → X} (hg : IsArcParam g) {K : Set X}
    (hcov : ∀ z, z ∈ g '' Icc 0 1 ∨ z ∈ K) (hdisj : ∀ t ∈ Ioc (0 : ℝ) 1, g t ∉ K) {δ : ℝ}
    (hδ : 0 < δ) : IsOpen (g '' Ico 0 δ ∪ K) := by
  have hcompl : (g '' Ico 0 δ ∪ K)ᶜ = g '' Icc δ 1 := by
    ext z; constructor
    · intro hz
      rcases hcov z with ⟨t, ht, rfl⟩ | hzK
      · refine ⟨t, ⟨not_lt.1 fun h => hz (Or.inl ⟨t, ⟨ht.1, h⟩, rfl⟩), ht.2⟩, rfl⟩
      · exact absurd (Or.inr hzK) hz
    · rintro ⟨t, ht, rfl⟩ (⟨s, hs, he⟩ | hK)
      · have := hg.2 ⟨hs.1, by linarith [hs.2, ht.1, ht.2]⟩ ⟨by linarith [ht.1], ht.2⟩ he
        linarith [hs.2, ht.1]
      · exact hdisj t ⟨by linarith [ht.1], ht.2⟩ hK
  rw [← isClosed_compl_iff, hcompl]
  exact (isCompact_Icc.image hg.1).isClosed

/-- The hypotheses of an arc piece of a simple triod. -/
theorem triod_piece {A B C : Set X} {v q r : X} {g : ℝ → X} (hg : IsArcParam g)
    (him : g '' Icc 0 1 = A) (hg0 : g 0 = v) (hB : IsArcBetween B v q) (hC : IsArcBetween C v r)
    (hAB : A ∩ B = {v}) (hAC : A ∩ C = {v}) (hcov : ∀ z, z ∈ A ∪ B ∪ C) :
    IsClosed (B ∪ C) ∧ IsPreconnected (B ∪ C) ∧ g 0 ∈ B ∪ C ∧
      (∀ z, z ∈ g '' Icc 0 1 ∨ z ∈ B ∪ C) ∧ ∀ t ∈ Ioc (0 : ℝ) 1, g t ∉ B ∪ C := by
  refine ⟨hB.isCompact.isClosed.union hC.isCompact.isClosed,
    hB.isConnected.isPreconnected.union v hB.left_mem hC.left_mem hC.isConnected.isPreconnected,
    Or.inl (hg0 ▸ hB.left_mem), fun z => ?_, fun t ht hK => ?_⟩
  · rw [him]
    rcases hcov z with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · have hA : g t ∈ A := him ▸ ⟨t, Ioc_subset_Icc_self ht, rfl⟩
    have hv : g t = v := by
      rcases hK with h | h
      · have : g t ∈ A ∩ B := ⟨hA, h⟩; rw [hAB] at this; exact this
      · have : g t ∈ A ∩ C := ⟨hA, h⟩; rw [hAC] at this; exact this
    have := hg.2 (Ioc_subset_Icc_self ht) ⟨le_rfl, zero_le_one⟩ (hv.trans hg0.symm)
    linarith [ht.1]

/-- **A simple triod is a finite tree.** -/
theorem triod_isFiniteTree (h : IsSimpleTriod (univ : Set X)) : IsFiniteTree X := by
  obtain ⟨v, p₁, p₂, p₃, A₁, A₂, A₃, h₁, h₂, h₃, h12, h13, h23, hU⟩ := h
  obtain ⟨g₁, hg₁, him₁, hg₁0, hg₁1⟩ := h₁.exists_param
  obtain ⟨g₂, hg₂, him₂, hg₂0, hg₂1⟩ := h₂.exists_param
  obtain ⟨g₃, hg₃, him₃, hg₃0, hg₃1⟩ := h₃.exists_param
  have hcov : ∀ z, z ∈ A₁ ∪ A₂ ∪ A₃ := fun z => hU ▸ trivial
  have hcov₂ : ∀ z, z ∈ A₂ ∪ A₁ ∪ A₃ := fun z => by
    rcases hcov z with (h | h) | h
    exacts [Or.inl (Or.inr h), Or.inl (Or.inl h), Or.inr h]
  have hcov₃ : ∀ z, z ∈ A₃ ∪ A₁ ∪ A₂ := fun z => by
    rcases hcov z with (h | h) | h
    exacts [Or.inl (Or.inr h), Or.inr h, Or.inl (Or.inl h)]
  obtain ⟨hK₁, hKc₁, hvK₁, hc₁, hd₁⟩ := triod_piece hg₁ him₁ hg₁0 h₂ h₃ h12 h13 hcov
  obtain ⟨hK₂, hKc₂, hvK₂, hc₂, hd₂⟩ := triod_piece hg₂ him₂ hg₂0 h₁ h₃
    (by rw [inter_comm]; exact h12) h23 hcov₂
  obtain ⟨hK₃, hKc₃, hvK₃, hc₃, hd₃⟩ := triod_piece hg₃ him₃ hg₃0 h₁ h₂
    (by rw [inter_comm]; exact h13) (by rw [inter_comm]; exact h23) hcov₃
  -- every point other than `v` is a non-base point of one piece
  have hpt : ∀ x : X, x = v ∨ (∃ t ∈ Ioc (0 : ℝ) 1, g₁ t = x) ∨ (∃ t ∈ Ioc (0 : ℝ) 1, g₂ t = x) ∨
      (∃ t ∈ Ioc (0 : ℝ) 1, g₃ t = x) := by
    intro x
    by_cases hxv : x = v
    · exact Or.inl hxv
    have aux : ∀ {g : ℝ → X}, g 0 = v → x ∈ g '' Icc 0 1 → ∃ t ∈ Ioc (0 : ℝ) 1, g t = x := by
      rintro g hg0 ⟨t, ht, rfl⟩
      exact ⟨t, ⟨lt_of_le_of_ne ht.1 fun h => hxv (by rw [← h, hg0]), ht.2⟩, rfl⟩
    rcases hcov x with (h | h) | h
    · exact Or.inr (Or.inl (aux hg₁0 (him₁ ▸ h)))
    · exact Or.inr (Or.inr (Or.inl (aux hg₂0 (him₂ ▸ h))))
    · exact Or.inr (Or.inr (Or.inr (aux hg₃0 (him₃ ▸ h))))
  have hc : CompactSpace X := ⟨by
    rw [hU]; exact (h₁.isCompact.union h₂.isCompact).union h₃.isCompact⟩
  have hconn : ConnectedSpace X := connectedSpace_iff_univ.2 (by
    rw [hU]
    exact ⟨⟨v, Or.inl (Or.inl h₁.left_mem)⟩, (h₁.isConnected.isPreconnected.union v h₁.left_mem
      h₂.left_mem h₂.isConnected.isPreconnected).union v (Or.inl h₁.left_mem) h₃.left_mem
      h₃.isConnected.isPreconnected⟩)
  have hnt : Nontrivial X := ⟨⟨v, p₁, h₁.ne⟩⟩
  -- local connectedness
  have hlc : LocallyConnectedSpace X := by
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro x U hU'
    rcases hpt x with rfl | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · -- the center
      have hδ : ∀ {g : ℝ → X}, IsArcParam g → g 0 = x → ∃ δ > 0, ∀ s, |s| < δ → g s ∈ U :=
        fun {g} hg hg0 => by
          obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1
            (hg.1.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU' : U ∈ 𝓝 (g 0)))
          exact ⟨δ, hδ, fun s hs => hb (by rw [mem_ball, Real.dist_eq, sub_zero]; exact hs)⟩
      obtain ⟨δ₁, hδ₁, hb₁⟩ := hδ hg₁ hg₁0
      obtain ⟨δ₂, hδ₂, hb₂⟩ := hδ hg₂ hg₂0
      obtain ⟨δ₃, hδ₃, hb₃⟩ := hδ hg₃ hg₃0
      set δ := min (min δ₁ δ₂) (min δ₃ 1)
      have hδ0 : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ one_pos)
      have e1 : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
      have e2 : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
      have e3 : δ ≤ δ₃ := (min_le_right _ _).trans (min_le_left _ _)
      have e4 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
      set W₁ := g₁ '' Ico 0 δ
      set W₂ := g₂ '' Ico 0 δ
      set W₃ := g₃ '' Ico 0 δ
      have hO : (W₁ ∪ (A₂ ∪ A₃)) ∩ (W₂ ∪ (A₁ ∪ A₃)) ∩ (W₃ ∪ (A₁ ∪ A₂)) = W₁ ∪ W₂ ∪ W₃ := by
        have hW₁ : W₁ ⊆ A₁ := him₁ ▸ image_mono fun s hs => ⟨hs.1, by linarith [hs.2]⟩
        have hW₂ : W₂ ⊆ A₂ := him₂ ▸ image_mono fun s hs => ⟨hs.1, by linarith [hs.2]⟩
        have hW₃ : W₃ ⊆ A₃ := him₃ ▸ image_mono fun s hs => ⟨hs.1, by linarith [hs.2]⟩
        have hv₁ : x ∈ W₁ := ⟨0, ⟨le_rfl, hδ0⟩, hg₁0⟩
        have m12 : ∀ z, z ∈ A₁ → z ∈ A₂ → z = x := fun z h h' => by
          have : z ∈ A₁ ∩ A₂ := ⟨h, h'⟩; rw [h12] at this; exact this
        have m13 : ∀ z, z ∈ A₁ → z ∈ A₃ → z = x := fun z h h' => by
          have : z ∈ A₁ ∩ A₃ := ⟨h, h'⟩; rw [h13] at this; exact this
        have m23 : ∀ z, z ∈ A₂ → z ∈ A₃ → z = x := fun z h h' => by
          have : z ∈ A₂ ∩ A₃ := ⟨h, h'⟩; rw [h23] at this; exact this
        ext z; constructor
        · rintro ⟨⟨o1, o2⟩, o3⟩
          rcases o1 with h | h | h
          · exact Or.inl (Or.inl h)
          · rcases o2 with h' | (h' | h')
            · exact Or.inl (Or.inr h')
            · rw [m12 z h' h]; exact Or.inl (Or.inl hv₁)
            · rw [m23 z h h']; exact Or.inl (Or.inl hv₁)
          · rcases o3 with h' | (h' | h')
            · exact Or.inr h'
            · rw [m13 z h' h]; exact Or.inl (Or.inl hv₁)
            · rw [m23 z h' h]; exact Or.inl (Or.inl hv₁)
        · rintro ((h | h) | h)
          · exact ⟨⟨Or.inl h, Or.inr (Or.inl (hW₁ h))⟩, Or.inr (Or.inl (hW₁ h))⟩
          · exact ⟨⟨Or.inr (Or.inl (hW₂ h)), Or.inl h⟩, Or.inr (Or.inr (hW₂ h))⟩
          · exact ⟨⟨Or.inr (Or.inr (hW₃ h)), Or.inr (Or.inr (hW₃ h))⟩, Or.inl h⟩
      refine ⟨W₁ ∪ W₂ ∪ W₃, ?_, ?_, Or.inl (Or.inl ⟨0, ⟨le_rfl, hδ0⟩, hg₁0⟩), ?_⟩
      · rintro z ((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
        · exact hb₁ s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
        · exact hb₂ s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
        · exact hb₃ s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
      · rw [← hO]
        refine ((open_start hg₁ hc₁ hd₁ hδ0).inter (open_start hg₂ hc₂ hd₂ hδ0)).inter
          (open_start hg₃ hc₃ hd₃ hδ0)
      · have hcW : ∀ {g : ℝ → X}, IsArcParam g → g 0 = x → IsConnected (g '' Ico 0 δ) ∧
            x ∈ g '' Ico 0 δ := fun {g} hg hg0 =>
          ⟨⟨⟨g 0, 0, ⟨le_rfl, hδ0⟩, rfl⟩, hg.isPreconnected_image_Ico⟩,
            ⟨0, ⟨le_rfl, hδ0⟩, hg0⟩⟩
        obtain ⟨c₁, x₁⟩ := hcW hg₁ hg₁0
        obtain ⟨c₂, x₂⟩ := hcW hg₂ hg₂0
        obtain ⟨c₃, x₃⟩ := hcW hg₃ hg₃0
        exact ⟨⟨x, Or.inl (Or.inl x₁)⟩, (c₁.isPreconnected.union x x₁ x₂ c₂.isPreconnected).union
          x (Or.inl x₁) x₃ c₃.isPreconnected⟩
    · exact piece_lc hg₁ hK₁ hc₁ hd₁ (Ioc_subset_Icc_self ht) (Or.inl ht.1) hU'
    · exact piece_lc hg₂ hK₂ hc₂ hd₂ (Ioc_subset_Icc_self ht) (Or.inl ht.1) hU'
    · exact piece_lc hg₃ hK₃ hc₃ hd₃ (Ioc_subset_Icc_self ht) (Or.inl ht.1) hU'
  -- orders
  have hord : ∀ x : X, x ≠ v → order x ≤ 2 := by
    intro x hxv
    rcases hpt x with h | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact absurd h hxv
    · exact piece_order hg₁ hKc₁ (Or.inl hvK₁) hc₁ hd₁ (Ioc_subset_Icc_self ht) (Or.inl ht.1)
    · exact piece_order hg₂ hKc₂ (Or.inl hvK₂) hc₂ hd₂ (Ioc_subset_Icc_self ht) (Or.inl ht.1)
    · exact piece_order hg₃ hKc₃ (Or.inl hvK₃) hc₃ hd₃ (Ioc_subset_Icc_self ht) (Or.inl ht.1)
  have hordv : order v ≠ ⊤ := by
    have hsub : {C : Set X | ∃ y, y ≠ v ∧ C = connectedComponentIn {v}ᶜ y} ⊆
        {connectedComponentIn {v}ᶜ p₁, connectedComponentIn {v}ᶜ p₂,
          connectedComponentIn {v}ᶜ p₃} := by
      rintro _ ⟨y, hy, rfl⟩
      have aux : ∀ {g : ℝ → X}, IsArcParam g → g 0 = v → ∀ t ∈ Ioc (0 : ℝ) 1,
          connectedComponentIn {v}ᶜ (g t) = connectedComponentIn {v}ᶜ (g 1) := by
        intro g hg hg0 t ht
        have hsub' : g '' Ioc 0 1 ⊆ {v}ᶜ := by
          rintro _ ⟨u, hu, rfl⟩ he
          have := hg.2 (Ioc_subset_Icc_self hu) ⟨le_rfl, zero_le_one⟩ (he.trans hg0.symm)
          linarith [hu.1]
        exact connectedComponentIn_eq (hg.isPreconnected_image_Ioc.subset_connectedComponentIn
          ⟨t, ht, rfl⟩ hsub' ⟨1, ⟨zero_lt_one, le_rfl⟩, rfl⟩)
      rcases hpt y with h | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact absurd h hy
      · left; rw [aux hg₁ hg₁0 t ht, hg₁1]
      · right; left; rw [aux hg₂ hg₂0 t ht, hg₂1]
      · right; right; show _ = _; rw [aux hg₃ hg₃0 t ht, hg₃1]
    have := (encard_le_encard hsub).trans_lt (Set.Finite.encard_lt_top (toFinite _))
    exact this.ne
  have hbr : ∀ x : X, IsBranchPoint x → x = v := fun x hx => by
    by_contra hxv
    have h3 : 3 ≤ order x := hx
    exact absurd (h3.trans (hord x hxv)) (by decide)
  -- no simple closed curve
  have hnoSCC : ∀ C : Set X, ¬ IsSimpleClosedCurve C := by
    intro C hC
    have hS := hC.isPreconnected_diff v
    have hcomp : ∀ z, z ∉ A₂ ∪ A₃ → z ∈ A₁ := fun z hz => by
      rcases hcov z with (h | h) | h
      · exact h
      · exact absurd (Or.inl h) hz
      · exact absurd (Or.inr h) hz
    have hcomp₂ : ∀ z, z ∉ A₁ ∪ A₃ → z ∈ A₂ := fun z hz => by
      rcases hcov z with (h | h) | h
      · exact absurd (Or.inl h) hz
      · exact h
      · exact absurd (Or.inr h) hz
    have hcomp₃ : ∀ z, z ∉ A₁ ∪ A₂ → z ∈ A₃ := fun z hz => by
      rcases hcov z with (h | h) | h
      · exact absurd (Or.inl h) hz
      · exact absurd (Or.inr h) hz
      · exact h
    have hcovS : C \ {v} ⊆ (A₂ ∪ A₃)ᶜ ∪ ((A₁ ∪ A₃)ᶜ ∪ (A₁ ∪ A₂)ᶜ) := by
      rintro z ⟨-, hzv⟩
      have hzv' : z ≠ v := hzv
      rcases hcov z with (h | h) | h
      · left; rintro (h' | h')
        · have : z ∈ A₁ ∩ A₂ := ⟨h, h'⟩; rw [h12] at this; exact hzv' this
        · have : z ∈ A₁ ∩ A₃ := ⟨h, h'⟩; rw [h13] at this; exact hzv' this
      · right; left; rintro (h' | h')
        · have : z ∈ A₁ ∩ A₂ := ⟨h', h⟩; rw [h12] at this; exact hzv' this
        · have : z ∈ A₂ ∩ A₃ := ⟨h, h'⟩; rw [h23] at this; exact hzv' this
      · right; right; rintro (h' | h')
        · have : z ∈ A₁ ∩ A₃ := ⟨h', h⟩; rw [h13] at this; exact hzv' this
        · have : z ∈ A₂ ∩ A₃ := ⟨h', h⟩; rw [h23] at this; exact hzv' this
    have hd12 : Disjoint (A₂ ∪ A₃)ᶜ ((A₁ ∪ A₃)ᶜ ∪ (A₁ ∪ A₂)ᶜ) := by
      rw [Set.disjoint_left]
      rintro z h1 (h2 | h2)
      · exact h2 (Or.inl (hcomp z h1))
      · exact h2 (Or.inl (hcomp z h1))
    have hd23 : Disjoint (A₁ ∪ A₃)ᶜ (A₁ ∪ A₂)ᶜ := by
      rw [Set.disjoint_left]
      intro z h1 h2; exact h2 (Or.inr (hcomp₂ z h1))
    have hfin : ∀ {A : Set X}, IsArc A → v ∈ A → C \ {v} ⊆ A → False := fun {A} hA hvA hsub =>
      not_scc_subset_arc hA hC fun z hz => by
        by_cases hzv : z = v
        · rw [hzv]; exact hvA
        · exact hsub ⟨hz, hzv⟩
    rcases hS.subset_or_subset hK₁.isOpen_compl (hK₂.isOpen_compl.union hK₃.isOpen_compl) hd12
        hcovS with h | h
    · exact hfin h₁.isArc h₁.left_mem fun z hz => hcomp z (h hz)
    · rcases hS.subset_or_subset hK₂.isOpen_compl hK₃.isOpen_compl hd23 h with h' | h'
      · exact hfin h₂.isArc h₂.left_mem fun z hz => hcomp₂ z (h' hz)
      · exact hfin h₃.isArc h₃.left_mem fun z hz => hcomp₃ z (h' hz)
  refine ⟨⟨⟨hc, hconn, hnt, inferInstance⟩, hlc, hnoSCC⟩, ?_, fun p hp => ?_⟩
  · exact (finite_singleton v).subset fun x hx => hbr x hx
  · rw [hbr p hp]; exact hordv

/-- **Theorem 10.1.** No compatible metric on a simple triod has the DMP. -/
theorem theorem_10_1 (h : IsSimpleTriod (univ : Set X)) : ¬ HasDMP X :=
  theorem_B (triod_isFiniteTree h)

/-- **Theorem B**, with its consequence for arcs and simple triods. -/
theorem theorem_B_full :
    (IsFiniteTree X → ¬ HasDMP X) ∧ (IsArc (univ : Set X) → ¬ HasDMP X) ∧
      (IsSimpleTriod (univ : Set X) → ¬ HasDMP X) :=
  ⟨theorem_B, theorem_11_1, theorem_10_1⟩

/-- Unpacking a finite tree into the standing hypotheses of Sections 5–11. -/
theorem IsFiniteTree.unpack (h : IsFiniteTree X) :
    CompactSpace X ∧ ConnectedSpace X ∧ LocallyConnectedSpace X ∧ Nontrivial X ∧ TreeHyp X := by
  obtain ⟨⟨⟨hc, hconn, hnt, -⟩, hlc, hD⟩, hBf, hBo⟩ := h
  exact ⟨hc, hconn, hlc, hnt, ⟨hD, hBf, hBo⟩⟩

/-- Unpacking a dendrite. -/
theorem IsDendrite.unpack (h : IsDendrite X) :
    CompactSpace X ∧ ConnectedSpace X ∧ LocallyConnectedSpace X ∧ Nontrivial X ∧
      ∀ C : Set X, ¬ IsSimpleClosedCurve C := by
  obtain ⟨⟨hc, hconn, hnt, -⟩, hlc, hD⟩ := h
  exact ⟨hc, hconn, hlc, hnt, hD⟩

end DoubleMidset
