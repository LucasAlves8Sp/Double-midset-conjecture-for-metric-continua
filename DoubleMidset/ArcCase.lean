module

public import DoubleMidset.Triod

/-!
# The arc (Section 11)

`not_hasDMP_of_unbranched`: a finite tree without branch points (an arc) carries no DMP metric.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

/-- An unbranched finite tree is a single edge whose two ends are tips. -/
theorem arc_structure (hnb : ∀ v : T, ¬ IsBranchPoint v) :
    ∃ γ : ℝ → T, IsEdgeParam γ ∧ γ '' Icc 0 1 = univ ∧ IsTip (γ 0) ∧ IsTip (γ 1) ∧
      oddVertices T = {γ 0, γ 1} := by
  have hBe : branchSet T = ∅ := eq_empty_of_forall_notMem fun v hv => hnb v hv
  have hform := tips_formula hT
  have hBf : hT.bfin.toFinset = ∅ := by
    rw [Finite.toFinset_eq_empty]; exact hBe
  rw [hBf, Finset.sum_empty, add_zero] at hform
  have hVt : vertices T = {p : T | IsTip p} := by
    ext p; simp only [vertices, mem_setOf_eq]
    exact ⟨fun h => h.resolve_right (hnb p), Or.inl⟩
  have hEcard : {ℓ : Set T | IsEdge ℓ}.ncard = 1 := by
    have := ncard_edges_add_one hT.noSCC hT.bfin hT.bord
    rw [hVt, hform] at this; omega
  obtain ⟨ℓ, hℓ⟩ := ncard_eq_one.1 hEcard
  have hℓe : IsEdge ℓ := by
    have : ℓ ∈ {ℓ : Set T | IsEdge ℓ} := by rw [hℓ]; rfl
    exact this
  obtain ⟨γ, hγ, hγℓ⟩ := exists_param_of_isEdge hT hℓe
  have huniv : γ '' Icc 0 1 = univ := by
    rw [hγℓ, ← sUnion_singleton ℓ, ← hℓ, sUnion_edges hT.noSCC hT.bfin hT.bord]
  have h0 : IsTip (γ 0) := hγ.end0.resolve_right (hnb _)
  have h1 : IsTip (γ 1) := hγ.end1.resolve_right (hnb _)
  refine ⟨γ, hγ, huniv, h0, h1, ?_⟩
  have hV : vertices T = {γ 0, γ 1} := by
    rw [← hγ.inter_vertices hT, huniv, univ_inter]
  rw [← hV]; ext u
  refine ⟨fun h => h.1, fun hu => ⟨hu, 1, ?_, odd_one⟩⟩
  have : IsTip u := hu.resolve_right (hnb u)
  exact_mod_cast this

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
/-- A point of an open subset of a sphere inside a parameter window is interior to a spherical
parameter subarc inside the window. -/
theorem good_of_open {γ : ℝ → T} (hγ : IsArcParam γ) {O : Set T} (hO : IsOpen O) {t lo hi : ℝ}
    (hlo : lo < t) (hhi : t < hi) (ht : γ t ∈ O) :
    ∃ σ σ', lo < σ ∧ σ < t ∧ t < σ' ∧ σ' < hi ∧ γ '' Icc σ σ' ⊆ O := by
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 (hO.preimage hγ.1) t ht
  set η' := min (η / 2) (min ((t - lo) / 2) ((hi - t) / 2))
  have hη' : 0 < η' := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have e1 : η' ≤ η / 2 := min_le_left _ _
  have e2 : η' ≤ (t - lo) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have e3 : η' ≤ (hi - t) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t - η', t + η', by linarith, by linarith, by linarith, by linarith, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])

/-- **Theorem 11.1, in tree form.** An unbranched finite tree admits no DMP metric. -/
theorem not_hasDMP_of_unbranched (hnb : ∀ v : T, ¬ IsBranchPoint v) : ¬ HasDMP T := by
  intro hDMP
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  obtain ⟨γ, hγ, huniv, h0, h1, hOdd⟩ := arc_structure hT hnb
  have hℓ : IsEdge (γ '' Icc 0 1) := hγ.isEdge hT
  have hγne : γ 0 ≠ γ 1 := hγ.arc.ne
  have hI : ∀ t, 0 ≤ t → t ≤ 1 → t ∈ Icc (0 : ℝ) 1 := fun t h h' => ⟨h, h'⟩
  -- a sphere: sites near the two tips
  set D := dist (γ 0) (γ 1)
  have hD : 0 < D := dist_pos.2 hγne
  obtain ⟨ε₀, hε₀, hb0⟩ := Metric.continuous_iff.1 hγ.arc.1 0 (D / 3) (by linarith)
  obtain ⟨ε₁, hε₁, hb1⟩ := Metric.continuous_iff.1 hγ.arc.1 1 (D / 3) (by linarith)
  set ε := min (min ε₀ ε₁) (1 / 2) / 2
  have hε : 0 < ε := by positivity
  have m1 := min_le_left (min ε₀ ε₁) (1 / 2)
  have m2 := min_le_left ε₀ ε₁
  have m3 := min_le_right ε₀ ε₁
  have m4 := min_le_right (min ε₀ ε₁) (1 / 2)
  have hε0 : ε < ε₀ := by simp only [ε]; linarith
  have hε1 : ε < ε₁ := by simp only [ε]; linarith
  have hε2 : ε ≤ 1 / 4 := by simp only [ε]; linarith
  have ha0 : dist (γ ε) (γ 0) < D / 3 := hb0 ε (by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hε0)
  have hb1' : dist (γ (1 - ε)) (γ 1) < D / 3 := hb1 (1 - ε) (by
    rw [Real.dist_eq, show 1 - ε - 1 = -ε by ring, abs_neg, abs_of_pos hε]; exact hε1)
  have hab : γ ε ≠ γ (1 - ε) := fun h => by
    have := hγ.arc.2 (hI ε hε.le (by linarith)) (hI (1 - ε) (by linarith) (by linarith)) h
    linarith
  have hT0 := dist_triangle (γ 0) (γ (1 - ε)) (γ 1)
  have hT1 := dist_triangle (γ 1) (γ ε) (γ 0)
  have hf0 : sgnf (γ ε) (γ (1 - ε)) (γ 0) < 0 := by
    show dist (γ 0) (γ ε) - dist (γ 0) (γ (1 - ε)) < 0
    rw [dist_comm (γ 0) (γ ε)]; rw [dist_comm (γ 1)] at hT1
    linarith [dist_comm (γ (1 - ε)) (γ 1)]
  have hf1 : 0 < sgnf (γ ε) (γ (1 - ε)) (γ 1) := by
    show 0 < dist (γ 1) (γ ε) - dist (γ 1) (γ (1 - ε))
    rw [dist_comm (γ 1) (γ (1 - ε))]
    linarith [dist_comm (γ 0) (γ 1), dist_comm (γ ε) (γ 0), dist_comm (γ 1) (γ 0)]
  have hVall : ∀ u ∈ vertices T, u = γ 0 ∨ u = γ 1 := fun u hu => by
    have : u ∈ γ '' Icc 0 1 ∩ vertices T := ⟨by rw [huniv]; trivial, hu⟩
    rw [hγ.inter_vertices hT] at this; exact this
  have hstr : IsStrictPair (γ ε) (γ (1 - ε)) := ⟨hab, fun u hu h0' => by
    rcases hVall u hu with rfl | rfl
    · linarith
    · linarith⟩
  have hodd : Odd (oddCount (γ ε) (γ (1 - ε))) := by
    have : {u | u ∈ oddVertices T ∧ sgnf (γ ε) (γ (1 - ε)) u < 0} = {γ 0} := by
      rw [hOdd]; ext u; simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · linarith
      · rintro rfl; exact ⟨Or.inl rfl, hf0⟩
    unfold oddCount; rw [this, ncard_singleton]; exact odd_one
  have hεV : γ ε ∉ vertices T := hγ.interior ε ⟨hε, by linarith⟩
  have h1εV : γ (1 - ε) ∉ vertices T := hγ.interior (1 - ε) ⟨by linarith, by linarith⟩
  obtain ⟨x, ⟨r, hr, U, V, hU, hV, haU, hbV, -, -, hsph, -⟩, hxV, -⟩ :=
    cor_6_7 hT hDMP hstr hεV h1εV hodd
  obtain ⟨ξ, hξ, rfl⟩ := hγ.mem_Ioo hT (by rw [huniv]; trivial) hxV
  set Sph := sphere (γ ξ) r
  have hxSph : γ ξ ∉ Sph := fun h => by
    rw [mem_sphere, dist_self] at h; linarith
  -- good points on the two sides of the center
  set GL : ℝ → Prop := fun s => ∃ σ σ', 0 < σ ∧ σ < s ∧ s < σ' ∧ σ' < ξ ∧ γ '' Icc σ σ' ⊆ Sph
  set GR : ℝ → Prop := fun s => ∃ σ' σ, ξ < σ' ∧ σ' < s ∧ s < σ ∧ σ < 1 ∧ γ '' Icc σ' σ ⊆ Sph
  have hγ' : IsEdgeParam fun t => γ (1 - t) := hγ.symm
  have hℓ' : (fun t => γ (1 - t)) '' Icc 0 1 = γ '' Icc 0 1 := by
    rw [image_symm_Icc]; simp
  -- Step 1: matching to the right
  have step1 : ∀ s, GL s → ∃ s', GR s' ∧ dist (γ 1) (γ s') = dist (γ 1) (γ s) ∧
      dist (γ 0) (γ s) < dist (γ 0) (γ s') := by
    rintro s ⟨σ, σ', hσ, hσs, hsσ', hσ'ξ, hIs⟩
    obtain ⟨-, ⟨hZo, hmatch⟩, ⟨hZsub, hMid⟩⟩ :=
      lemma_7_3 hT hDMP hℓ hγ.arc.1 hγ.arc.2 rfl h1 hσ (hσs.trans hsσ') hσ'ξ hξ.2 hr hIs
    obtain ⟨b, hbZ, hbe⟩ := hmatch (γ s) ⟨s, ⟨hσs, hsσ'⟩, rfl⟩
    obtain ⟨hbSph, ⟨sb, hsb, rfl⟩⟩ := hZsub hbZ
    obtain ⟨σ₁, σ₂, h1', h2', h3', h4', hsub⟩ := good_of_open hγ.arc hZo hsb.1 hsb.2 hbZ
    refine ⟨sb, ⟨σ₁, σ₂, h1', h2', h3', h4', fun z hz => (hZsub (hsub hz)).1⟩, hbe, ?_⟩
    have hM := hMid _ hbZ (γ s) ⟨s, ⟨hσs, hsσ'⟩, rfl⟩ hbe.symm
    have hne : γ s ≠ γ sb := fun h => by
      have := hγ.arc.2 (hI s (by linarith) (by linarith)) (hI sb (by linarith [hsb.1])
        hsb.2.le) h
      linarith [hsb.1]
    have hfc : Continuous fun t => sgnf (γ s) (γ sb) (γ t) := (continuous_sgnf _ _).comp hγ.arc.1
    have hnz : ∀ t ∈ Icc (0 : ℝ) s, (fun t => sgnf (γ s) (γ sb) (γ t)) t ≠ 0 := by
      intro t ht h0'
      have : γ t ∈ midset (γ s) (γ sb) := sgnf_eq_zero_iff.1 h0'
      rw [hM] at this
      rcases this with h | h
      · have := hγ.arc.2 (hI t ht.1 (by linarith [ht.2])) ⟨zero_le_one, le_rfl⟩ h
        linarith [ht.2]
      · rw [mem_singleton_iff] at h
        have := hγ.arc.2 (hI t ht.1 (by linarith [ht.2])) (hI ξ hξ.1.le hξ.2.le) h
        linarith [ht.2]
    have hprod : 0 < sgnf (γ s) (γ sb) (γ 0) * sgnf (γ s) (γ sb) (γ s) :=
      const_sign isPreconnected_Icc hfc.continuousOn hnz 0 ⟨le_rfl, by linarith⟩ s
        ⟨by linarith, le_rfl⟩
    have hfs : sgnf (γ s) (γ sb) (γ s) < 0 := sgnf_left_neg hne
    have hf0' : sgnf (γ s) (γ sb) (γ 0) < 0 := by
      by_contra hc; push_neg at hc
      have : sgnf (γ s) (γ sb) (γ 0) * sgnf (γ s) (γ sb) (γ s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc hfs.le
      linarith
    have : dist (γ 0) (γ s) - dist (γ 0) (γ sb) < 0 := hf0'
    linarith
  -- Step 2: matching to the left
  have step2 : ∀ s, GR s → ∃ s', GL s' ∧ dist (γ 0) (γ s') = dist (γ 0) (γ s) := by
    rintro s ⟨σ', σ, hξσ', hσ's, hsσ, hσ1, hIs⟩
    have hIs' : (fun t => γ (1 - t)) '' Icc (1 - σ) (1 - σ') ⊆ sphere ((fun t => γ (1 - t)) (1 - ξ)) r := by
      rw [image_symm_Icc]; simpa using hIs
    obtain ⟨-, ⟨hZo, hmatch⟩, ⟨hZsub, -⟩⟩ :=
      lemma_7_3 hT hDMP (hℓ'.symm ▸ hℓ) hγ'.arc.1 hγ'.arc.2 rfl (by simpa using h0)
        (σ := 1 - σ) (σ' := 1 - σ') (ξ := 1 - ξ) (by linarith) (by linarith) (by linarith)
        (by linarith [hξ.1]) hr hIs'
    obtain ⟨a', ha'Z, ha'e⟩ := hmatch (γ s) ⟨1 - s, ⟨by linarith, by linarith⟩, by simp⟩
    obtain ⟨-, ⟨t', ht', rfl⟩⟩ := hZsub ha'Z
    obtain ⟨σ₁, σ₂, h1', h2', h3', h4', hsub⟩ := good_of_open hγ'.arc hZo ht'.1 ht'.2 ha'Z
    refine ⟨1 - t', ⟨1 - σ₂, 1 - σ₁, by linarith, by linarith, by linarith, by linarith, ?_⟩,
      by simpa using ha'e⟩
    intro z hz
    have hz' : z ∈ (fun t => γ (1 - t)) '' Icc σ₁ σ₂ := by
      rw [image_symm_Icc]; exact hz
    have := (hZsub (hsub hz')).1
    exact mem_sphere.2 (by simpa using this)
  -- a first good point on the left
  have hstart : ∃ s₀, GL s₀ := by
    have hεξ : ε ≠ ξ := fun h => hxSph (by rw [← h]; exact hsph (Or.inl haU))
    rcases lt_or_gt_of_ne hεξ with h | h
    · obtain ⟨σ, σ', h1', h2', h3', h4', hsub⟩ := good_of_open hγ.arc hU.1 hε h haU
      exact ⟨ε, σ, σ', h1', h2', h3', h4', hsub.trans (subset_union_left.trans hsph)⟩
    · obtain ⟨σ', σ, h1', h2', h3', h4', hsub⟩ := good_of_open hγ.arc hV.1
        (show ξ < 1 - ε by linarith) (show 1 - ε < 1 by linarith) hbV
      obtain ⟨s₀, hs₀, -⟩ := step2 (1 - ε)
        ⟨σ', σ, h1', h2', h3', h4', hsub.trans (subset_union_right.trans hsph)⟩
      exact ⟨s₀, hs₀⟩
  obtain ⟨s₀, hs₀⟩ := hstart
  -- the alternating sequences
  choose! gR hgR using step1
  choose! gL hgL using step2
  let seq : ℕ → ℝ := fun n => Nat.rec s₀ (fun _ s => gL (gR s)) n
  have hseqS : ∀ n, seq (n + 1) = gL (gR (seq n)) := fun n => rfl
  have hGL : ∀ n, GL (seq n) := by
    intro n
    induction n with
    | zero => exact hs₀
    | succ n ih => rw [hseqS]; exact (hgL _ (hgR _ ih).1).1
  have hGR : ∀ n, GR (gR (seq n)) := fun n => (hgR _ (hGL n)).1
  have hh1 : ∀ n, dist (γ 1) (γ (gR (seq n))) = dist (γ 1) (γ (seq n)) := fun n =>
    (hgR _ (hGL n)).2.1
  have hlt : ∀ n, dist (γ 0) (γ (seq n)) < dist (γ 0) (γ (gR (seq n))) := fun n =>
    (hgR _ (hGL n)).2.2
  have hstepA : ∀ n, dist (γ 0) (γ (seq (n + 1))) = dist (γ 0) (γ (gR (seq n))) := fun n => by
    rw [hseqS]; exact (hgL _ (hGR n)).2
  -- `A_n = h_0(a_n)` increases to a limit
  set A : ℕ → ℝ := fun n => dist (γ 0) (γ (seq n))
  have hAmono : Monotone A := monotone_nat_of_le_succ fun n => by
    show dist (γ 0) (γ (seq n)) ≤ dist (γ 0) (γ (seq (n + 1)))
    rw [hstepA]; exact (hlt n).le
  have hAbdd : BddAbove (range A) := by
    obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image
      (f := fun z : T => dist (γ 0) z) (continuous_const.dist continuous_id).continuousOn
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM ⟨γ (seq n), trivial, rfl⟩⟩
  have hAconv := tendsto_atTop_ciSup hAmono hAbdd
  have hdiff : Tendsto (fun n => dist (γ 0) (γ (gR (seq n))) - dist (γ 0) (γ (seq n))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n => A (n + 1)) atTop (𝓝 (⨆ n, A n)) :=
      hAconv.comp (tendsto_add_atTop_nat 1)
    have := h1.sub hAconv
    rw [sub_self] at this
    refine this.congr fun n => ?_
    show dist (γ 0) (γ (seq (n + 1))) - dist (γ 0) (γ (seq n)) = _
    rw [hstepA]
  -- a convergent subsequence of pairs
  obtain ⟨⟨a₀, b₀⟩, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq
    (x := fun n => (γ (seq n), γ (gR (seq n)))) (fun n => trivial)
  have hla : Tendsto (fun n => γ (seq (φ n))) atTop (𝓝 a₀) :=
    (continuous_fst.tendsto _).comp hlim
  have hlb : Tendsto (fun n => γ (gR (seq (φ n)))) atTop (𝓝 b₀) :=
    (continuous_snd.tendsto _).comp hlim
  have hSc : IsClosed Sph := isClosed_sphere
  have haS : ∀ n, γ (seq n) ∈ Sph := fun n => by
    obtain ⟨σ, σ', _, h2', h3', _, hsub⟩ := hGL n
    exact hsub ⟨seq n, ⟨h2'.le, h3'.le⟩, rfl⟩
  have hbS : ∀ n, γ (gR (seq n)) ∈ Sph := fun n => by
    obtain ⟨σ', σ, _, h2', h3', _, hsub⟩ := hGR n
    exact hsub ⟨gR (seq n), ⟨h2'.le, h3'.le⟩, rfl⟩
  have haL : ∀ n, γ (seq n) ∈ γ '' Icc 0 ξ := fun n => by
    obtain ⟨σ, σ', h1', h2', h3', h4', _⟩ := hGL n
    exact ⟨seq n, ⟨by linarith, by linarith⟩, rfl⟩
  have hbR : ∀ n, γ (gR (seq n)) ∈ γ '' Icc ξ 1 := fun n => by
    obtain ⟨σ', σ, h1', h2', h3', h4', _⟩ := hGR n
    exact ⟨gR (seq n), ⟨by linarith, by linarith⟩, rfl⟩
  have ha₀S : a₀ ∈ Sph := hSc.mem_of_tendsto hla (Eventually.of_forall fun n => haS _)
  have hb₀S : b₀ ∈ Sph := hSc.mem_of_tendsto hlb (Eventually.of_forall fun n => hbS _)
  have ha₀L : a₀ ∈ γ '' Icc 0 ξ := hγ.arc.isCompact_image.isClosed.mem_of_tendsto hla
    (Eventually.of_forall fun n => haL _)
  have hb₀R : b₀ ∈ γ '' Icc ξ 1 := hγ.arc.isCompact_image.isClosed.mem_of_tendsto hlb
    (Eventually.of_forall fun n => hbR _)
  obtain ⟨ta, hta, rfl⟩ := ha₀L
  obtain ⟨tb, htb, rfl⟩ := hb₀R
  have hta' : ta < ξ := lt_of_le_of_ne hta.2 fun h => hxSph (by rw [← h]; exact ha₀S)
  have htb' : ξ < tb := lt_of_le_of_ne htb.1 fun h => hxSph (by rw [h]; exact hb₀S)
  have hab₀ : γ ta ≠ γ tb := fun h => by
    have := hγ.arc.2 (hI ta hta.1 (by linarith [hξ.2])) (hI tb (by linarith [hξ.1]) htb.2) h
    linarith
  -- the limiting pair is equidistant from `0`, `x` and `1`
  have e1 : dist (γ 1) (γ ta) = dist (γ 1) (γ tb) := by
    have h₁ : Tendsto (fun n => dist (γ 1) (γ (seq (φ n)))) atTop (𝓝 (dist (γ 1) (γ ta))) :=
      tendsto_const_nhds.dist hla
    have h₂ : Tendsto (fun n => dist (γ 1) (γ (seq (φ n)))) atTop (𝓝 (dist (γ 1) (γ tb))) :=
      (tendsto_const_nhds.dist hlb).congr fun n => hh1 _
    exact tendsto_nhds_unique h₁ h₂
  have e0 : dist (γ 0) (γ ta) = dist (γ 0) (γ tb) := by
    have h₁ : Tendsto (fun n => dist (γ 0) (γ (gR (seq (φ n)))) - dist (γ 0) (γ (seq (φ n))))
        atTop (𝓝 (dist (γ 0) (γ tb) - dist (γ 0) (γ ta))) :=
      (tendsto_const_nhds.dist hlb).sub (tendsto_const_nhds.dist hla)
    have h₂ := tendsto_nhds_unique h₁ (hdiff.comp hφ.tendsto_atTop)
    linarith
  have ex : dist (γ ξ) (γ ta) = dist (γ ξ) (γ tb) := by
    rw [mem_sphere, dist_comm] at ha₀S hb₀S; rw [ha₀S, hb₀S]
  have h0ξ : γ 0 ≠ γ ξ := fun h => by
    have := hγ.arc.2 ⟨le_rfl, zero_le_one⟩ (hI ξ hξ.1.le hξ.2.le) h; linarith [hξ.1]
  have h1ξ : γ 1 ≠ γ ξ := fun h => by
    have := hγ.arc.2 ⟨zero_le_one, le_rfl⟩ (hI ξ hξ.1.le hξ.2.le) h; linarith [hξ.2]
  exact false_of_three hab₀ hD2 (three_le_encard_midset (x := γ 0) (y := γ 1) (z := γ ξ) e0 e1 ex
    hγne h0ξ h1ξ)

end DoubleMidset
