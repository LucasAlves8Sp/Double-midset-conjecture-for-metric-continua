module

public import DoubleMidset.Extrema
public import DoubleMidset.TreeStructure
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.IntervalCases

/-!
# Branch points under the upper bound (Section 4, Theorem C)

Convention 4.1: `X` is a dendrite with `|M(a, b)| ≤ 2` for all distinct `a, b`.

* **Lemma 4.2** (`exists_arm`, `lemma_4_2`): arms at a point.
* `three_le_of_arms`: two arms with a sign change and a third connected set give three zeros.
* `core_move`: if `f_{a,b}(c) = 0` for a branch point `c` and `a` can be moved along a path so that
  `d(c, ·)` moves off the level `d(c, b)` in either direction, then some midset has three points.
* **Lemma 4.3** (`lemma_4_3`, radial monotonicity), **Lemma 4.4** (`lemma_4_4`, order at most
  four), **Theorem 4.5** (`theorem_4_5`, few branch points), **Corollary 4.6** (`cor_4_6`).
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

theorem exists_two_same : ∀ σ : Fin 3 → Bool, ∃ i j, i ≠ j ∧ σ i = σ j := by decide

theorem exists_three_same :
    ∀ σ : Fin 5 → Bool, ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ σ i = σ j ∧ σ i = σ k := by decide

variable {X : Type u} [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyConnectedSpace X] (hD : ∀ C : Set X, ¬ IsSimpleClosedCurve C)

omit [MetricSpace X] [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X] in
theorem sign_cases {u v : ℝ} (h : u * v < 0) : (u < 0 ∧ 0 < v) ∨ (0 < u ∧ v < 0) := by
  rcases mul_neg_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right; exact ⟨h1, h2⟩
  · left; exact ⟨h1, h2⟩

section Arms

include hD

/-- An arc minus its first end is `g '' (0, 1]`. -/
theorem seg_diff_left_eq {c p : X} {g : ℝ → X} (hg : IsArcParam g) (hgim : g '' Icc 0 1 = seg c p)
    (hg0 : g 0 = c) : seg c p \ {c} = g '' Ioc 0 1 := by
  rw [← hgim]; ext y; constructor
  · rintro ⟨⟨t, ht, rfl⟩, hy⟩
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 (fun e => hy (by rw [← e, hg0]; rfl)), ht.2⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, Ioc_subset_Icc_self ht, rfl⟩, fun e => ht.1.ne'
      (hg.2 (Ioc_subset_Icc_self ht) ⟨le_rfl, zero_le_one⟩ (e.trans hg0.symm))⟩

/-- **An arm.** For `y ≠ c`, a closed set `K ∌ c`, `δ > 0` and a continuous `f` with finitely many
zeros other than `c`, there is a short arc `[c, p]` with `p` in the component of `X \ {c}`
containing `y`, disjoint from `K`, inside `B(c, δ)`, on which `f` has a constant strict sign
off `c`. -/
theorem exists_arm {c y : X} (hyc : y ≠ c) {K : Set X} (hK : IsClosed K) (hcK : c ∉ K) {δ : ℝ}
    (hδ : 0 < δ) {f : X → ℝ} (hf : Continuous f) (hfin : (f ⁻¹' {0} \ {c}).Finite) :
    ∃ p, p ≠ c ∧ connectedComponentIn {c}ᶜ p = connectedComponentIn {c}ᶜ y ∧
      seg c p ⊆ ball c δ ∧ Disjoint (seg c p) K ∧
      seg c p \ {c} ⊆ connectedComponentIn {c}ᶜ y ∧
      ((∀ z ∈ seg c p \ {c}, 0 < f z) ∨ (∀ z ∈ seg c p \ {c}, f z < 0)) := by
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hyc.symm).exists_param
  set N := ball c δ ∩ Kᶜ ∩ (f ⁻¹' {0} \ {c})ᶜ
  have hNo : IsOpen N := (isOpen_ball.inter hK.isOpen_compl).inter hfin.isClosed.isOpen_compl
  have hcN : c ∈ N := ⟨⟨mem_ball_self hδ, hcK⟩, fun h => h.2 rfl⟩
  have h0N : (0 : ℝ) ∈ g ⁻¹' N := by rw [mem_preimage, hg0]; exact hcN
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hNo.preimage hg.1) 0 h0N
  set t := min (ε / 2) 1
  have ht0 : 0 < t := lt_min (by positivity) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨k, hk, hk0, hk1, hkim⟩ := hg.exists_subarc ⟨le_rfl, zero_le_one⟩ ⟨ht0.le, ht1⟩ ht0.ne
  have hseg : seg c (g t) = g '' Icc 0 t := by
    rw [seg_eq hD (show IsArcBetween (k '' Icc 0 1) c (g t) by
      have := hk.isArcBetween; rwa [hk0, hk1, hg0] at this), hkim, uIcc_of_le ht0.le]
  have hsubN : seg c (g t) ⊆ N := by
    rw [hseg]; rintro _ ⟨s, hs, rfl⟩
    have : s ∈ ball (0 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]; exact hs.2.trans_lt htε
    exact hball this
  have hpc : g t ≠ c := fun e => ht0.ne' (hg.2 ⟨ht0.le, ht1⟩ ⟨le_rfl, zero_le_one⟩ (e.trans hg0.symm))
  -- the punctured arm lies in the component of `y`
  have hbig : seg c y \ {c} ⊆ connectedComponentIn {c}ᶜ y := by
    obtain ⟨g', hg', hg'im, hg'0, hg'1⟩ := (seg_isArcBetween hyc.symm).exists_param
    have hpc' : IsPreconnected (seg c y \ {c}) := by
      rw [seg_diff_left_eq hD hg' hg'im hg'0]; exact hg'.isPreconnected_image_Ioc
    exact hpc'.subset_connectedComponentIn ⟨right_mem_seg hD c y, hyc⟩ (fun z hz => hz.2)
  have harm : seg c (g t) \ {c} ⊆ seg c y \ {c} := by
    rintro z ⟨hz, hzc⟩
    refine ⟨?_, hzc⟩
    rw [hseg] at hz; rw [← hgim]
    exact image_mono (Icc_subset_Icc le_rfl ht1) hz
  have hpcomp : g t ∈ connectedComponentIn {c}ᶜ y := hbig (harm ⟨right_mem_seg hD _ _, hpc⟩)
  refine ⟨g t, hpc, (connectedComponentIn_eq hpcomp).symm, fun z hz => (hsubN hz).1.1,
    disjoint_left.2 fun z hz hzK => (hsubN hz).1.2 hzK, harm.trans hbig, ?_⟩
  -- constant sign on the punctured arm
  have hpcarm : IsPreconnected (seg c (g t) \ {c}) := by
    rw [hseg, show g '' Icc 0 t \ {c} = g '' Ioc 0 t by
      ext z; constructor
      · rintro ⟨⟨s, hs, rfl⟩, hz⟩
        exact ⟨s, ⟨lt_of_le_of_ne hs.1 (fun e => hz (by rw [← e, hg0]; rfl)), hs.2⟩, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨⟨s, Ioc_subset_Icc_self hs, rfl⟩, fun e => hs.1.ne'
          (hg.2 ⟨hs.1.le, hs.2.trans ht1⟩ ⟨le_rfl, zero_le_one⟩ (e.trans hg0.symm))⟩]
    exact isPreconnected_Ioc.image _ hg.1.continuousOn
  have hnz : ∀ z ∈ seg c (g t) \ {c}, f z ≠ 0 := fun z hz h0 =>
    (hsubN hz.1).2 ⟨h0, hz.2⟩
  by_contra hsign
  push_neg at hsign
  obtain ⟨⟨z₁, hz₁, h₁⟩, ⟨z₂, hz₂, h₂⟩⟩ := hsign
  obtain ⟨w, hw, hw0⟩ := hpcarm.intermediate_value hz₁ hz₂ hf.continuousOn ⟨h₁, h₂⟩
  exact hnz w hw hw0

/-- **Lemma 4.2 (Arms).** If `c` has order at least `k`, `K ⊆ X \ {c}` is compact, `δ > 0` and
`f` is continuous with finitely many zeros, there are arcs `[c, p_i]`, `i < k`, of diameter less
than `2δ`, disjoint from `K`, whose punctured arms lie in distinct components of `X \ {c}` (so
the arcs pairwise meet only in `c`), on each of which `f` has a constant strict sign off `c`. -/
theorem lemma_4_2 {c : X} {k : ℕ} (hk : (k : ℕ∞) ≤ order c) {K : Set X} (hK : IsCompact K)
    (hcK : c ∉ K) {δ : ℝ} (hδ : 0 < δ) {f : X → ℝ} (hf : Continuous f)
    (hfin : (f ⁻¹' {0}).Finite) :
    ∃ p : Fin k → X, (∀ i, IsArcBetween (seg c (p i)) c (p i)) ∧
      (∀ i j, i ≠ j → connectedComponentIn {c}ᶜ (p i) ≠ connectedComponentIn {c}ᶜ (p j)) ∧
      (∀ i, seg c (p i) \ {c} ⊆ connectedComponentIn {c}ᶜ (p i)) ∧
      (∀ i j, i ≠ j → seg c (p i) ∩ seg c (p j) = {c}) ∧
      (∀ i, seg c (p i) ⊆ ball c δ) ∧ (∀ i, Disjoint (seg c (p i)) K) ∧
      ∀ i, (∀ z ∈ seg c (p i) \ {c}, 0 < f z) ∨ (∀ z ∈ seg c (p i) \ {c}, f z < 0) := by
  obtain ⟨S, hSc, hSk, hSinj⟩ := exists_points_of_le_order hk
  have hSf : S.Finite := finite_of_encard_eq_coe hSk
  have hcard : hSf.toFinset.card = k := by
    have := hSk; rw [hSf.encard_eq_coe_toFinset_card] at this; exact_mod_cast this
  let e : Fin k ≃ hSf.toFinset := (hSf.toFinset.equivFin.trans (finCongr hcard)).symm
  set y : Fin k → X := fun i => (e i : X)
  have hyS : ∀ i, y i ∈ S := fun i => (hSf.mem_toFinset).1 (e i).2
  have hyinj : ∀ i j, i ≠ j → connectedComponentIn {c}ᶜ (y i) ≠ connectedComponentIn {c}ᶜ (y j) :=
    fun i j hij h => hij (e.injective (Subtype.ext (hSinj (hyS i) (hyS j) h)))
  have harm : ∀ i, ∃ p, p ≠ c ∧ connectedComponentIn {c}ᶜ p = connectedComponentIn {c}ᶜ (y i) ∧
      seg c p ⊆ ball c δ ∧ Disjoint (seg c p) K ∧
      seg c p \ {c} ⊆ connectedComponentIn {c}ᶜ (y i) ∧
      ((∀ z ∈ seg c p \ {c}, 0 < f z) ∨ (∀ z ∈ seg c p \ {c}, f z < 0)) := fun i =>
    exists_arm hD (hSc (hyS i)) hK.isClosed hcK hδ hf (hfin.subset diff_subset)
  choose p hpc hpcomp hpball hpK hpsub hpsign using harm
  refine ⟨p, fun i => seg_isArcBetween (hpc i).symm, fun i j hij h => hyinj i j hij ?_,
    fun i => (hpcomp i).symm ▸ hpsub i, fun i j hij => ?_, hpball, hpK, hpsign⟩
  · rw [← hpcomp i, ← hpcomp j, h]
  · apply Subset.antisymm
    · intro z ⟨hzi, hzj⟩
      by_contra hzc
      have h1 := hpsub i ⟨hzi, hzc⟩
      have h2 := hpsub j ⟨hzj, hzc⟩
      exact hyinj i j hij ((connectedComponentIn_eq h1).trans (connectedComponentIn_eq h2).symm)
    · rintro z rfl; exact ⟨left_mem_seg _ _, left_mem_seg _ _⟩

end Arms

section Core

include hD

theorem arm_signs {a b c p : X} (h : sgnf a b c * sgnf a b p < 0) :
    (∃ y ∈ seg c p, sgnf a b y < 0) ∧ (∃ y ∈ seg c p, 0 < sgnf a b y) := by
  rcases sign_cases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨c, left_mem_seg c p, h1⟩, ⟨p, right_mem_seg hD c p, h2⟩⟩
  · exact ⟨⟨p, right_mem_seg hD c p, h2⟩, ⟨c, left_mem_seg c p, h1⟩⟩

/-- Two arms at `c` on each of which `f_{a,b}` changes sign, meeting only at `c` (not a zero),
and a third connected set disjoint from them on which `f_{a,b}` changes sign, give three
zeros. -/
theorem three_le_of_arms {a b c p₁ p₂ : X} {K : Set X} (hK : IsPreconnected K)
    (hKn : ∃ y ∈ K, sgnf a b y < 0) (hKp : ∃ y ∈ K, 0 < sgnf a b y)
    (h12 : seg c p₁ ∩ seg c p₂ ⊆ {c}) (hK1 : Disjoint (seg c p₁) K)
    (hK2 : Disjoint (seg c p₂) K) (hc : sgnf a b c ≠ 0)
    (hs1 : sgnf a b c * sgnf a b p₁ < 0) (hs2 : sgnf a b c * sgnf a b p₂ < 0) :
    3 ≤ (midset a b).encard := by
  obtain ⟨n₁, p₁'⟩ := arm_signs hD hs1
  obtain ⟨n₂, p₂'⟩ := arm_signs hD hs2
  refine three_le_encard_of_sets (isConnected_seg c p₁).isPreconnected
    (isConnected_seg c p₂).isPreconnected hK n₁ p₁' n₂ p₂' hKn hKp ?_ ?_ ?_
  · refine disjoint_left.2 fun z ⟨hz1, hzM⟩ ⟨hz2, _⟩ => hc ?_
    rw [← mem_singleton_iff.1 (h12 ⟨hz1, hz2⟩)]; exact sgnf_eq_zero_iff.2 hzM
  · exact disjoint_left.2 fun z ⟨hz1, _⟩ ⟨hzK, _⟩ => disjoint_left.1 hK1 hz1 hzK
  · exact disjoint_left.2 fun z ⟨hz1, _⟩ ⟨hzK, _⟩ => disjoint_left.1 hK2 hz1 hzK

/-- Three arms at `c` pairwise meeting only at `c` (not a zero), on each of which `f_{a,b}`
changes sign, give three zeros. -/
theorem three_le_of_three_arms {a b c p₁ p₂ p₃ : X}
    (h12 : seg c p₁ ∩ seg c p₂ ⊆ {c}) (h13 : seg c p₁ ∩ seg c p₃ ⊆ {c})
    (h23 : seg c p₂ ∩ seg c p₃ ⊆ {c}) (hc : sgnf a b c ≠ 0)
    (hs1 : sgnf a b c * sgnf a b p₁ < 0) (hs2 : sgnf a b c * sgnf a b p₂ < 0)
    (hs3 : sgnf a b c * sgnf a b p₃ < 0) : 3 ≤ (midset a b).encard := by
  obtain ⟨n₁, p₁'⟩ := arm_signs hD hs1
  obtain ⟨n₂, p₂'⟩ := arm_signs hD hs2
  obtain ⟨n₃, p₃'⟩ := arm_signs hD hs3
  have key : ∀ {q r : X}, seg c q ∩ seg c r ⊆ {c} →
      Disjoint (seg c q ∩ midset a b) (seg c r ∩ midset a b) := fun h =>
    disjoint_left.2 fun z ⟨hz1, hzM⟩ ⟨hz2, _⟩ => hc (by
      rw [← mem_singleton_iff.1 (h ⟨hz1, hz2⟩)]; exact sgnf_eq_zero_iff.2 hzM)
  exact three_le_encard_of_sets (isConnected_seg c p₁).isPreconnected
    (isConnected_seg c p₂).isPreconnected (isConnected_seg c p₃).isPreconnected n₁ p₁' n₂ p₂'
    n₃ p₃' (key h12) (key h13) (key h23)

omit [CompactSpace X] [ConnectedSpace X] [LocallyConnectedSpace X] hD in
theorem midset_finite (h2 : MidsetsAtMostTwo X) {a b : X} (hab : a ≠ b) :
    (sgnf a b ⁻¹' {0}).Finite := by
  have : sgnf a b ⁻¹' {0} = midset a b := by ext y; exact sgnf_eq_zero_iff
  rw [this]
  exact finite_of_encard_le_coe (h2 a b hab)

variable (h2 : MidsetsAtMostTwo X)
include h2

/-- **The basic perturbation.** Let `c` have order at least three, and let `a = γ(s₀)` and `b`
be sites with `d(c, a) = d(c, b)`, joined by a compact connected set `K ∌ c`. If `s₀` is not a
local extremum of `d(c, γ(·))`, moving `a` along `γ` produces a midset with three points. -/
theorem core_move {c : X} (hc : 3 ≤ order c) {γ : ℝ → X} (hγ : Continuous γ) {s₀ : ℝ}
    (hext : ¬ IsLocalExtr (fun t => dist c (γ t)) s₀) {b : X} (hab : γ s₀ ≠ b)
    (hfc : dist c (γ s₀) = dist c b) {K : Set X} (hK : IsCompact K) (hKpc : IsPreconnected K)
    (ha : γ s₀ ∈ K) (hb : b ∈ K) (hcK : c ∉ K) : False := by
  set a := γ s₀
  obtain ⟨p, harc, -, -, h12, -, hpK, hsign⟩ := lemma_4_2 hD (k := 3) (by exact_mod_cast hc) hK
    hcK one_pos (continuous_sgnf a b) (midset_finite h2 hab)
  have hfp : ∀ i, 0 < sgnf a b (p i) ∨ sgnf a b (p i) < 0 := fun i => by
    have hpi : p i ∈ seg c (p i) \ {c} := ⟨right_mem_seg hD _ _, (harc i).ne.symm⟩
    rcases hsign i with h | h
    · exact Or.inl (h _ hpi)
    · exact Or.inr (h _ hpi)
  obtain ⟨i, j, hij, hσ⟩ := exists_two_same fun i => decide (0 < sgnf a b (p i))
  have hεpos : 0 < min (|sgnf a b (p i)|) (min (|sgnf a b (p j)|) (dist a b)) := by
    refine lt_min ?_ (lt_min ?_ (dist_pos.2 hab))
    · rcases hfp i with h | h
      · exact abs_pos.2 h.ne'
      · exact abs_pos.2 h.ne
    · rcases hfp j with h | h
      · exact abs_pos.2 h.ne'
      · exact abs_pos.2 h.ne
  set ε₀ := min (|sgnf a b (p i)|) (min (|sgnf a b (p j)|) (dist a b))
  obtain ⟨ρ, hρ, hcont⟩ := Metric.continuous_iff.1 hγ s₀ ε₀ hεpos
  obtain ⟨s', hs', s'', hs'', hlt, hgt⟩ := lemma_2_8_iii hext (ball_mem_nhds s₀ hρ)
  -- moving `a` to `a' = γ t`, with `d(a, a') < ε₀`
  have hmove : ∀ t, dist t s₀ < ρ → (dist c (γ t) - dist c b) * sgnf a b (p i) < 0 →
      (dist c (γ t) - dist c b) * sgnf a b (p j) < 0 → False := by
    intro t ht hsi hsj
    set a' := γ t
    have hd : dist a a' < ε₀ := by rw [dist_comm]; exact hcont t ht
    have hdi : dist a a' < |sgnf a b (p i)| := hd.trans_le (min_le_left _ _)
    have hdj : dist a a' < |sgnf a b (p j)| :=
      hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hdab : dist a a' < dist a b :=
      hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have ha'b : a' ≠ b := fun e => by rw [e] at hdab; exact lt_irrefl _ hdab
    have hfc' : sgnf a' b c = dist c (γ t) - dist c b := rfl
    -- the test signs survive
    have hsurv : ∀ q, dist a a' < |sgnf a b q| → 0 < sgnf a' b q * sgnf a b q := by
      intro q hq
      have := lemma_2_2_a (a := a) (b := b) (a' := a') (b' := b) (t := q)
        (by rw [dist_self, add_zero]; exact hq)
      rcases lt_trichotomy (sgnf a b q) 0 with h | h | h
      · exact mul_pos_of_neg_of_neg (this.2 h) h
      · rw [h, abs_zero] at hq; exact absurd hq (not_lt.2 dist_nonneg)
      · exact mul_pos (this.1 h) h
    have hci : sgnf a' b c * sgnf a' b (p i) < 0 := by
      have h1 := hsurv _ hdi
      rw [hfc']
      nlinarith [mul_pos_iff.1 h1, sq_nonneg (sgnf a b (p i))]
    have hcj : sgnf a' b c * sgnf a' b (p j) < 0 := by
      have h1 := hsurv _ hdj
      rw [hfc']
      nlinarith [mul_pos_iff.1 h1, sq_nonneg (sgnf a b (p j))]
    have hcne : sgnf a' b c ≠ 0 := fun h0 => by rw [h0, zero_mul] at hci; exact lt_irrefl _ hci
    have hKn : ∃ y ∈ K, sgnf a' b y < 0 := ⟨a, ha, by
      unfold sgnf; linarith [dist_comm a a']⟩
    have hKp : ∃ y ∈ K, 0 < sgnf a' b y := ⟨b, hb, by
      unfold sgnf; rw [dist_self, sub_zero]; exact dist_pos.2 (Ne.symm ha'b)⟩
    exact false_of_three ha'b h2 (three_le_of_arms hD hKpc hKn hKp (h12 i j hij).le
      (hpK i) (hpK j) hcne hci hcj)
  rcases hfp i with hpos | hneg
  · -- both test signs positive: move `a` down
    have hpos' : 0 < sgnf a b (p j) := by
      by_contra h; push_neg at h
      have : decide (0 < sgnf a b (p i)) = decide (0 < sgnf a b (p j)) := hσ
      rw [decide_eq_true hpos, eq_comm, decide_eq_true_iff] at this; linarith
    refine hmove s' (by rw [← mem_ball]; exact hs') ?_ ?_
    · exact mul_neg_of_neg_of_pos (by linarith) hpos
    · exact mul_neg_of_neg_of_pos (by linarith) hpos'
  · have hneg' : sgnf a b (p j) < 0 := by
      by_contra h; push_neg at h
      have : decide (0 < sgnf a b (p i)) = decide (0 < sgnf a b (p j)) := hσ
      rw [decide_eq_false (not_lt.2 hneg.le)] at this
      rcases eq_or_lt_of_le h with h' | h'
      · have hpj : p j ∈ seg c (p j) \ {c} := ⟨right_mem_seg hD _ _, (harc j).ne.symm⟩
        rcases hsign j with hh | hh
        · exact absurd (hh _ hpj) (by rw [← h']; exact lt_irrefl 0)
        · exact absurd (hh _ hpj) (by rw [← h']; exact lt_irrefl 0)
      · rw [decide_eq_true h'] at this; exact Bool.false_ne_true this
    refine hmove s'' (by rw [← mem_ball]; exact hs'') ?_ ?_
    · exact mul_neg_of_pos_of_neg (by linarith) hneg
    · exact mul_neg_of_pos_of_neg (by linarith) hneg'


/-- **Lemma 4.3 (radial monotonicity).** Distances from a branch point `c` are nondecreasing
along every arc having `c` as an end. -/
theorem lemma_4_3 {c : X} (hc : IsBranchPoint c) {α : ℝ → X} (hα : IsArcParam α)
    (h0 : α 0 = c) : MonotoneOn (fun t => dist c (α t)) (Icc 0 1) := by
  intro σ hσ τ hτ hστ
  by_contra hlt
  push_neg at hlt
  set g := fun t => dist c (α t)
  have hστ' : σ < τ := lt_of_le_of_ne hστ (fun e => by rw [e] at hlt; exact lt_irrefl _ hlt)
  have hτpos : 0 < g τ := by
    simp only [g]
    refine dist_pos.2 fun e => ?_
    have := hα.2 ⟨le_rfl, zero_le_one⟩ hτ (h0.trans e)
    linarith [hσ.1]
  obtain ⟨l, hl, hlS⟩ := exists_mem_Ioo_notMem (lemma_2_8_i g) hlt
  have hg0 : g 0 = 0 := by simp only [g, h0, dist_self]
  have hgc : Continuous g := continuous_const.dist hα.1
  obtain ⟨α₁, hα₁, hgα₁⟩ := intermediate_value_Icc hσ.1 hgc.continuousOn
    ⟨by rw [hg0]; linarith [hl.1], hl.2.le⟩
  obtain ⟨β₁, hβ₁, hgβ₁⟩ := intermediate_value_Icc' hστ hgc.continuousOn ⟨hl.1.le, hl.2.le⟩
  have hα₁0 : 0 < α₁ := lt_of_le_of_ne hα₁.1 (fun e => by
    rw [← e, hg0] at hgα₁; linarith [hl.1])
  have hα₁σ : α₁ < σ := lt_of_le_of_ne hα₁.2 (fun e => by rw [e] at hgα₁; linarith [hl.2])
  have hβ₁σ : σ < β₁ := lt_of_le_of_ne hβ₁.1 (fun e => by rw [← e] at hgβ₁; linarith [hl.2])
  have hext : ¬ IsLocalExtr g α₁ := fun h => hlS ⟨α₁, h, hgα₁⟩
  have hI : ∀ t ∈ Icc α₁ β₁, t ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨hα₁0.le.trans ht.1, ht.2.trans (hβ₁.2.trans hτ.2)⟩
  have hab : α α₁ ≠ α β₁ := fun e => (hα₁σ.trans hβ₁σ).ne
    (hα.2 (hI α₁ ⟨le_rfl, (hα₁σ.trans hβ₁σ).le⟩) (hI β₁ ⟨(hα₁σ.trans hβ₁σ).le, le_rfl⟩) e)
  refine core_move hD h2 hc hα.1 hext hab (by simp only [g] at hgα₁ hgβ₁; rw [hgα₁, hgβ₁])
    hα.isCompact_image hα.isPreconnected_image ⟨α₁, ⟨le_rfl, (hα₁σ.trans hβ₁σ).le⟩, rfl⟩
    ⟨β₁, ⟨(hα₁σ.trans hβ₁σ).le, le_rfl⟩, rfl⟩ ?_
  rintro ⟨t, ht, hte⟩
  have := hα.2 (hI t ht) ⟨le_rfl, zero_le_one⟩ (hte.trans h0.symm)
  linarith [ht.1]


omit hD h2 in
/-- The first parameter at which `d(c, g(·))` reaches the level `ρ`. -/
theorem exists_first_level {c : X} {g : ℝ → X} (hg : Continuous g) (h0 : g 0 = c) {ρ : ℝ}
    (hρ : 0 < ρ) (h1 : ρ ≤ dist c (g 1)) :
    ∃ s ∈ Ioc (0 : ℝ) 1, dist c (g s) = ρ ∧ ∀ t ∈ Ico 0 s, dist c (g t) < ρ := by
  have hcl : IsClosed {x : X | ρ ≤ dist c x} := isClosed_le continuous_const
    (continuous_const.dist continuous_id)
  obtain ⟨s, hs, hsK, hbefore⟩ := exists_first_entry hg hcl
    (by simp only [mem_setOf_eq, h0, dist_self, not_le]; exact hρ) h1
  refine ⟨s, hs, le_antisymm ?_ hsK, fun t ht => not_le.1 (hbefore t ht)⟩
  -- by continuity from the left
  have hle : ∀ t ∈ Ico 0 s, dist c (g t) ≤ ρ := fun t ht => (not_le.1 (hbefore t ht)).le
  have hcont : ContinuousWithinAt (fun t => dist c (g t)) (Ico 0 s) s :=
    (continuous_const.dist hg).continuousWithinAt
  have hmem : s ∈ closure (Ico 0 s) := by
    rw [closure_Ico hs.1.ne]; exact ⟨hs.1.le, le_rfl⟩
  exact hcont.closure_le hmem continuous_const.continuousWithinAt hle |>.trans le_rfl
    |> fun h => by simpa using h

/-- **Lemma 4.4 (order at most four).** -/
theorem lemma_4_4 (c : X) : order c ≤ 4 := by
  by_contra h4
  have h5 : ((5 : ℕ) : ℕ∞) ≤ order c := by
    have := Order.add_one_le_of_lt (not_le.1 h4); exact_mod_cast this
  -- five arms
  have hfin₀ : ((fun y => dist c y) ⁻¹' {0}).Finite :=
    (finite_singleton c).subset fun y hy => by
      simp only [mem_preimage, mem_singleton_iff, dist_eq_zero] at hy; exact hy.symm
  obtain ⟨p, harc, hcomp, hsub, -, -, -, -⟩ := lemma_4_2 hD h5 isCompact_empty (notMem_empty c)
    one_pos (continuous_const.dist continuous_id) hfin₀
  have hdp : ∀ i, 0 < dist c (p i) := fun i => dist_pos.2 (harc i).ne
  set ρ := min (dist c (p 0)) (dist c (p 1)) / 2
  have hρ : 0 < ρ := by have := lt_min (hdp 0) (hdp 1); positivity
  obtain ⟨g₀, hg₀, hg₀im, hg₀0, hg₀1⟩ := (harc 0).exists_param
  obtain ⟨g₁, hg₁, hg₁im, hg₁0, hg₁1⟩ := (harc 1).exists_param
  obtain ⟨s₁, hs₁, ha, hbefore₀⟩ := exists_first_level hg₀.1 hg₀0 hρ
    (by rw [hg₀1]; simp only [ρ]; linarith [min_le_left (dist c (p 0)) (dist c (p 1)), hdp 0])
  obtain ⟨t₁, ht₁, hb, hbefore₁⟩ := exists_first_level hg₁.1 hg₁0 hρ
    (by rw [hg₁1]; simp only [ρ]; linarith [min_le_right (dist c (p 0)) (dist c (p 1)), hdp 1])
  set a := g₀ s₁
  set b := g₁ t₁
  -- points of the two arms off `c` are distinct
  have harm₀ : ∀ s ∈ Ioc (0 : ℝ) 1, g₀ s ∈ connectedComponentIn {c}ᶜ (p 0) := fun s hs =>
    hsub 0 ⟨by rw [← hg₀im]; exact ⟨s, Ioc_subset_Icc_self hs, rfl⟩, fun e => hs.1.ne'
      (hg₀.2 (Ioc_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ (e.trans hg₀0.symm))⟩
  have harm₁ : ∀ s ∈ Ioc (0 : ℝ) 1, g₁ s ∈ connectedComponentIn {c}ᶜ (p 1) := fun s hs =>
    hsub 1 ⟨by rw [← hg₁im]; exact ⟨s, Ioc_subset_Icc_self hs, rfl⟩, fun e => hs.1.ne'
      (hg₁.2 (Ioc_subset_Icc_self hs) ⟨le_rfl, zero_le_one⟩ (e.trans hg₁0.symm))⟩
  have hne01 : ∀ s ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Ioc (0 : ℝ) 1, g₀ s ≠ g₁ t := by
    intro s hs t ht e
    apply hcomp 0 1 (by decide)
    rw [connectedComponentIn_eq (harm₀ s hs), connectedComponentIn_eq (harm₁ t ht), e]
  have hab : a ≠ b := hne01 s₁ hs₁ t₁ ht₁
  -- the shortened arms, with constant signs of `f_{a,b}`
  obtain ⟨q, hqarc, -, -, hq12, -, -, hqsign⟩ := lemma_4_2 hD h5 isCompact_empty (notMem_empty c)
    one_pos (continuous_sgnf a b) (midset_finite h2 hab)
  have hfq : ∀ i, 0 < sgnf a b (q i) ∨ sgnf a b (q i) < 0 := fun i => by
    have hqi : q i ∈ seg c (q i) \ {c} := ⟨right_mem_seg hD _ _, (hqarc i).ne.symm⟩
    rcases hqsign i with h | h
    · exact Or.inl (h _ hqi)
    · exact Or.inr (h _ hqi)
  have hfc : sgnf a b c = 0 := by unfold sgnf; rw [dist_comm c a, dist_comm c b] at *; simp [ha, hb]
  obtain ⟨i, j, k, hij, hik, hjk, hσj, hσk⟩ :=
    exists_three_same fun i => decide (0 < sgnf a b (q i))
  have hsame : ∀ l, decide (0 < sgnf a b (q i)) = decide (0 < sgnf a b (q l)) →
      (0 < sgnf a b (q i) → 0 < sgnf a b (q l)) ∧ (sgnf a b (q i) < 0 → sgnf a b (q l) < 0) := by
    intro l hl
    constructor
    · intro h; rw [decide_eq_true h, eq_comm, decide_eq_true_iff] at hl; exact hl
    · intro h
      rw [decide_eq_false (not_lt.2 h.le), eq_comm, decide_eq_false_iff_not, not_lt] at hl
      rcases hfq l with h' | h'
      · exact absurd h' (not_lt.2 hl)
      · exact h'
  have habs : ∀ l, 0 < |sgnf a b (q l)| := fun l => by
    rcases hfq l with h | h
    · exact abs_pos.2 h.ne'
    · exact abs_pos.2 h.ne
  set ε₀ := min (|sgnf a b (q i)|) (min (|sgnf a b (q j)|) (|sgnf a b (q k)|))
  have hε₀ : 0 < ε₀ := lt_min (habs i) (lt_min (habs j) (habs k))
  have hε₀i : ε₀ ≤ |sgnf a b (q i)| := min_le_left _ _
  have hε₀j : ε₀ ≤ |sgnf a b (q j)| := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀k : ε₀ ≤ |sgnf a b (q k)| := (min_le_right _ _).trans (min_le_right _ _)
  -- surviving signs after a small move of one site
  have hsurv : ∀ a' b' : X, dist a a' + dist b b' < ε₀ → ∀ l ∈ ({i, j, k} : Set (Fin 5)),
      0 < sgnf a' b' (q l) * sgnf a b (q l) := by
    intro a' b' hd l hl
    have hlε : ε₀ ≤ |sgnf a b (q l)| := by
      rcases hl with rfl | rfl | rfl
      · exact hε₀i
      · exact hε₀j
      · exact hε₀k
    have := lemma_2_2_a (a := a) (b := b) (a' := a') (b' := b') (t := q l) (hd.trans_le hlε)
    rcases hfq l with h | h
    · exact mul_pos (this.1 h) h
    · exact mul_pos_of_neg_of_neg (this.2 h) h
  have hclose : ∀ {g : ℝ → X} (hg : Continuous g) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1),
      ∃ s' ∈ Ioo (0 : ℝ) s, dist (g s) (g s') < ε₀ := by
    intro g hg s hs
    obtain ⟨r, hr, hcont⟩ := Metric.continuous_iff.1 hg s ε₀ hε₀
    refine ⟨max (s / 2) (s - r / 2), ⟨lt_max_of_lt_left (by linarith [hs.1]),
      max_lt (by linarith [hs.1]) (by linarith)⟩, ?_⟩
    rw [dist_comm]; apply hcont
    rw [Real.dist_eq, abs_lt]; constructor
    · linarith [le_max_right (s / 2) (s - r / 2)]
    · linarith [max_lt (show s / 2 < s by linarith [hs.1]) (show s - r / 2 < s by linarith)]
  have hmeet : ∀ l l' : Fin 5, l ≠ l' → seg c (q l) ∩ seg c (q l') ⊆ {c} := fun l l' h =>
    (hq12 l l' h).le
  rcases hfq i with hpos | hneg
  · -- move `a` towards `c`
    obtain ⟨s', hs', hd⟩ := hclose hg₀.1 hs₁
    set a' := g₀ s'
    have ha'b : a' ≠ b := hne01 s' ⟨hs'.1, hs'.2.le.trans hs₁.2⟩ t₁ ht₁
    have hc' : sgnf a' b c < 0 := by
      unfold sgnf
      have := hbefore₀ s' ⟨hs'.1.le, hs'.2⟩
      linarith
    have hsv := hsurv a' b (by rw [dist_self, add_zero]; exact hd)
    have hpos_l : ∀ l ∈ ({i, j, k} : Set (Fin 5)), 0 < sgnf a b (q l) := by
      rintro l (rfl | rfl | rfl)
      · exact hpos
      · exact (hsame _ hσj).1 hpos
      · exact (hsame _ hσk).1 hpos
    have hs : ∀ l ∈ ({i, j, k} : Set (Fin 5)), sgnf a' b c * sgnf a' b (q l) < 0 := by
      intro l hl
      have h1 := hsv l hl
      have h2 := hpos_l l hl
      have : 0 < sgnf a' b (q l) := pos_of_mul_pos_left h1 h2.le |> fun h => by
        rcases lt_trichotomy (sgnf a' b (q l)) 0 with h' | h' | h'
        · nlinarith
        · rw [h', zero_mul] at h1; exact absurd h1 (lt_irrefl 0)
        · exact h'
      exact mul_neg_of_neg_of_pos hc' this
    exact false_of_three ha'b h2 (three_le_of_three_arms hD (hmeet i j hij) (hmeet i k hik)
      (hmeet j k hjk) hc'.ne (hs i (Or.inl rfl)) (hs j (Or.inr (Or.inl rfl)))
      (hs k (Or.inr (Or.inr rfl))))
  · -- move `b` towards `c`
    obtain ⟨t', ht', hd⟩ := hclose hg₁.1 ht₁
    set b' := g₁ t'
    have hab' : a ≠ b' := hne01 s₁ hs₁ t' ⟨ht'.1, ht'.2.le.trans ht₁.2⟩
    have hc' : 0 < sgnf a b' c := by
      unfold sgnf
      have := hbefore₁ t' ⟨ht'.1.le, ht'.2⟩
      linarith
    have hsv := hsurv a b' (by rw [dist_self, zero_add]; exact hd)
    have hneg_l : ∀ l ∈ ({i, j, k} : Set (Fin 5)), sgnf a b (q l) < 0 := by
      rintro l (rfl | rfl | rfl)
      · exact hneg
      · exact (hsame _ hσj).2 hneg
      · exact (hsame _ hσk).2 hneg
    have hs : ∀ l ∈ ({i, j, k} : Set (Fin 5)), sgnf a b' c * sgnf a b' (q l) < 0 := by
      intro l hl
      have h1 := hsv l hl
      have h2 := hneg_l l hl
      have : sgnf a b' (q l) < 0 := by
        rcases lt_trichotomy (sgnf a b' (q l)) 0 with h' | h' | h'
        · exact h'
        · rw [h', zero_mul] at h1; exact absurd h1 (lt_irrefl 0)
        · nlinarith
      exact mul_neg_of_pos_of_neg hc' this
    exact false_of_three hab' h2 (three_le_of_three_arms hD (hmeet i j hij) (hmeet i k hik)
      (hmeet j k hjk) hc'.ne' (hs i (Or.inl rfl)) (hs j (Or.inr (Or.inl rfl)))
      (hs k (Or.inr (Or.inr rfl))))


omit hD h2 in
theorem concat_half {g h : ℝ → X} (h1 : g 1 = h 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    concat g h ((1 + s) / 2) = h s := by
  rcases eq_or_lt_of_le hs.1 with e | e
  · subst e; rw [concat_of_le (by norm_num)]; norm_num [h1]
  · rw [concat_of_lt (by linarith)]; congr 1; ring

omit h2 in
/-- An arc minus its second end is connected. -/
theorem isPreconnected_seg_diff_right {c v : X} (hcv : c ≠ v) : IsPreconnected (seg c v \ {v}) := by
  rw [seg_symm hD]; exact isPreconnected_seg_diff_left hcv.symm

omit h2 in
theorem seg_diff_subset_cc {c v : X} (hcv : c ≠ v) :
    seg c v \ {v} ⊆ connectedComponentIn {v}ᶜ c :=
  (isPreconnected_seg_diff_right hD hcv).subset_connectedComponentIn
    ⟨left_mem_seg c v, hcv⟩ fun z hz => hz.2

/-- Along an arc from `v` into a component of `X \ {v}` not containing the branch point `c`, the
distance from `c` is nondecreasing (Lemma 4.3 applied to `[c, v] ∪ I`). -/
theorem monotone_away {c v y : X} (hc : IsBranchPoint c) (hcv : c ≠ v) (hyv : y ≠ v)
    (hcy : connectedComponentIn {v}ᶜ c ≠ connectedComponentIn {v}ᶜ y) {P : ℝ → X}
    (hP : IsArcParam P) (hPim : P '' Icc 0 1 = seg v y) (hP0 : P 0 = v) :
    MonotoneOn (fun t => dist c (P t)) (Icc 0 1) := by
  obtain ⟨g, hg, hgim, hg0, hg1⟩ := (seg_isArcBetween hcv).exists_param
  have hmeet : g '' Icc 0 1 ∩ P '' Icc 0 1 ⊆ {g 1} := by
    rintro z ⟨hz1, hz2⟩
    rw [hg1, mem_singleton_iff]
    by_contra hzv
    rw [hgim] at hz1; rw [hPim] at hz2
    have h1 := seg_diff_subset_cc hD hcv ⟨hz1, hzv⟩
    have h2 : z ∈ connectedComponentIn {v}ᶜ y := by
      have := seg_diff_subset_cc hD hyv ⟨by rw [seg_symm hD]; exact hz2, hzv⟩; exact this
    exact hcy ((connectedComponentIn_eq h1).trans (connectedComponentIn_eq h2).symm)
  have hcat := hg.concat hP (hg1.trans hP0.symm) hmeet
  have hmono := lemma_4_3 hD h2 hc hcat (by rw [concat_zero, hg0])
  intro s hs t ht hst
  have := hmono (show (1 + s) / 2 ∈ Icc (0 : ℝ) 1 from ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    (show (1 + t) / 2 ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (by linarith)
  simp only at this
  rwa [concat_half (hg1.trans hP0.symm) hs, concat_half (hg1.trans hP0.symm) ht] at this

/-- **The claim in Theorem 4.5.** For a branch point `c ≠ v`, the distance from `c` is constant
on all arcs `I_y` into components of `X \ {v}` other than that of `c`, with at most one
exception. -/
theorem not_two_nonconstant {c v y y' : X} (hc : IsBranchPoint c) (hcv : c ≠ v) (hyv : y ≠ v)
    (hy'v : y' ≠ v) (hcy : connectedComponentIn {v}ᶜ c ≠ connectedComponentIn {v}ᶜ y)
    (hcy' : connectedComponentIn {v}ᶜ c ≠ connectedComponentIn {v}ᶜ y')
    (hyy' : connectedComponentIn {v}ᶜ y ≠ connectedComponentIn {v}ᶜ y')
    (hne : ∃ z ∈ seg v y, dist c z ≠ dist c v) (hne' : ∃ z ∈ seg v y', dist c z ≠ dist c v) :
    False := by
  obtain ⟨P, hP, hPim, hP0, hP1⟩ := (seg_isArcBetween hyv.symm).exists_param
  obtain ⟨P', hP', hP'im, hP'0, hP'1⟩ := (seg_isArcBetween hy'v.symm).exists_param
  have hm := monotone_away hD h2 hc hcv hyv hcy hP hPim hP0
  have hm' := monotone_away hD h2 hc hcv hy'v hcy' hP' hP'im hP'0
  set φ := fun t => dist c (P t)
  set φ' := fun t => dist c (P' t)
  -- the far ends are strictly farther than `v`
  have hfar : ∀ {Q : ℝ → X}, IsArcParam Q → Q 0 = v → MonotoneOn (fun t => dist c (Q t)) (Icc 0 1) →
      (∃ z ∈ Q '' Icc 0 1, dist c z ≠ dist c v) → dist c v < dist c (Q 1) := by
    intro Q hQ hQ0 hmQ ⟨z, ⟨t, ht, hzt⟩, hz⟩
    have h1 := hmQ ⟨le_rfl, zero_le_one⟩ ht ht.1
    have h2 := hmQ ht ⟨zero_le_one, le_rfl⟩ ht.2
    simp only at h1 h2; rw [hQ0] at h1; rw [hzt] at h1 h2
    exact lt_of_lt_of_le (lt_of_le_of_ne h1 (Ne.symm hz)) h2
  have hμ := hfar hP hP0 hm (hPim ▸ hne)
  have hμ' := hfar hP' hP'0 hm' (hP'im ▸ hne')
  obtain ⟨l, hl, hlS⟩ := exists_mem_Ioo_notMem ((lemma_2_8_i φ).union (lemma_2_8_i φ'))
    (lt_min hμ hμ')
  have hcont : Continuous φ := continuous_const.dist hP.1
  have hcont' : Continuous φ' := continuous_const.dist hP'.1
  obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn
    ⟨by simp only [φ, hP0]; exact hl.1.le, hl.2.le.trans (min_le_left _ _)⟩
  obtain ⟨s', hs', hφs'⟩ := intermediate_value_Icc zero_le_one hcont'.continuousOn
    ⟨by simp only [φ', hP'0]; exact hl.1.le, hl.2.le.trans (min_le_right _ _)⟩
  have hs0 : 0 < s := lt_of_le_of_ne hs.1 (fun e => by
    rw [← e] at hφs; simp only [φ, hP0] at hφs; linarith [hl.1])
  have hs'0 : 0 < s' := lt_of_le_of_ne hs'.1 (fun e => by
    rw [← e] at hφs'; simp only [φ', hP'0] at hφs'; linarith [hl.1])
  have hext : ¬ IsLocalExtr φ s := fun h => hlS (Or.inl ⟨s, h, hφs⟩)
  -- the two sites lie in different components
  have hPcomp : ∀ {Q : ℝ → X} {w : X}, IsArcParam Q → Q '' Icc 0 1 = seg v w → Q 0 = v → w ≠ v →
      ∀ t ∈ Ioc (0 : ℝ) 1, Q t ∈ connectedComponentIn {v}ᶜ w := by
    intro Q w hQ hQim hQ0 hwv t ht
    have hne : Q t ≠ v := fun e => ht.1.ne' (hQ.2 (Ioc_subset_Icc_self ht) ⟨le_rfl, zero_le_one⟩
      (e.trans hQ0.symm))
    have := seg_diff_subset_cc hD hwv ⟨by rw [seg_symm hD, ← hQim]; exact
      ⟨t, Ioc_subset_Icc_self ht, rfl⟩, hne⟩
    exact this
  have ha := hPcomp hP hPim hP0 hyv s ⟨hs0, hs.2⟩
  have hb := hPcomp hP' hP'im hP'0 hy'v s' ⟨hs'0, hs'.2⟩
  have hab : P s ≠ P' s' := fun e => hyy' ((connectedComponentIn_eq ha).trans
    ((congrArg _ e).trans (connectedComponentIn_eq hb).symm))
  -- the connected set `P[0, s] ∪ P'[0, s']` avoids `c`
  have hK : IsCompact (P '' Icc 0 s ∪ P' '' Icc 0 s') :=
    hP.isCompact_image.union hP'.isCompact_image
  have hKpc : IsPreconnected (P '' Icc 0 s ∪ P' '' Icc 0 s') :=
    IsPreconnected.union v ⟨0, ⟨le_rfl, hs.1⟩, hP0⟩ ⟨0, ⟨le_rfl, hs'.1⟩, hP'0⟩
      hP.isPreconnected_image hP'.isPreconnected_image
  have hcK : c ∉ P '' Icc 0 s ∪ P' '' Icc 0 s' := by
    rintro (⟨t, ht, hte⟩ | ⟨t, ht, hte⟩)
    · rcases eq_or_lt_of_le ht.1 with e | e
      · rw [← e, hP0] at hte; exact hcv hte.symm
      · have := hPcomp hP hPim hP0 hyv t ⟨e, ht.2.trans hs.2⟩
        rw [hte] at this
        exact hcy (connectedComponentIn_eq this).symm
    · rcases eq_or_lt_of_le ht.1 with e | e
      · rw [← e, hP'0] at hte; exact hcv hte.symm
      · have := hPcomp hP' hP'im hP'0 hy'v t ⟨e, ht.2.trans hs'.2⟩
        rw [hte] at this
        exact hcy' (connectedComponentIn_eq this).symm
  exact core_move hD h2 hc hP.1 hext hab (by simp only [φ, φ'] at hφs hφs'; rw [hφs, hφs'])
    hK hKpc (Or.inl ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩) (Or.inr ⟨s', ⟨hs'.1, le_rfl⟩, rfl⟩) hcK

/-- No arc from `v` carries two constant distance functions `d(c, ·)`, `d(c', ·)`. -/
theorem not_two_constant {c c' v y : X} (hcc' : c ≠ c') (hyv : y ≠ v)
    (hc : ∀ z ∈ seg v y, dist c z = dist c v) (hc' : ∀ z ∈ seg v y, dist c' z = dist c' v)
    (hcv : c ≠ v) (hc'v : c' ≠ v) : False := by
  obtain ⟨P, hP, hPim, hP0, hP1⟩ := (seg_isArcBetween hyv.symm).exists_param
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ seg v y := fun t ht => hPim ▸ ⟨t, ht, rfl⟩
  set p := P (1 / 3)
  set q := P (2 / 3)
  have hpq : p ≠ q := fun e => by
    have := hP.2 ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ e; norm_num at this
  have hcp := hc p (hmem _ ⟨by norm_num, by norm_num⟩)
  have hcq := hc q (hmem _ ⟨by norm_num, by norm_num⟩)
  have hc'p := hc' p (hmem _ ⟨by norm_num, by norm_num⟩)
  have hc'q := hc' q (hmem _ ⟨by norm_num, by norm_num⟩)
  have hcM : c ∈ midset p q := by
    show dist c p = dist c q; rw [hcp, hcq]
  have hc'M : c' ∈ midset p q := by
    show dist c' p = dist c' q; rw [hc'p, hc'q]
  -- a zero between `p` and `q` on the arc
  have hpc : IsPreconnected (P '' Icc (1 / 3) (2 / 3)) := hP.isPreconnected_image
  obtain ⟨z, ⟨t, ht, rfl⟩, hz⟩ := hpc.intermediate_value (⟨1 / 3, ⟨le_rfl, by norm_num⟩, rfl⟩ :
    p ∈ P '' Icc (1 / 3) (2 / 3)) (⟨2 / 3, ⟨by norm_num, le_rfl⟩, rfl⟩ :
    q ∈ P '' Icc (1 / 3) (2 / 3)) (continuous_sgnf p q).continuousOn
    ⟨by unfold sgnf; rw [dist_self, zero_sub, neg_nonpos]; exact dist_nonneg,
      by unfold sgnf; rw [dist_self, sub_zero]; exact dist_nonneg⟩
  have hzM : P t ∈ midset p q := sgnf_eq_zero_iff.1 hz
  have hzseg := hmem t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcz : c ≠ P t := fun e => by
    have := hc _ hzseg; rw [← e, dist_self] at this; exact hcv (dist_eq_zero.1 this.symm)
  have hc'z : c' ≠ P t := fun e => by
    have := hc' _ hzseg; rw [← e, dist_self] at this; exact hc'v (dist_eq_zero.1 this.symm)
  exact false_of_three hpq h2 (three_le_encard_midset hcM hc'M hzM hcc' hcz hc'z)

/-- **Theorem 4.5 (few branch points).** If `v` is a branch point of order `m` and `B` is the set
of branch points, then `B` is finite, `(m - 2)(|B| - 1) ≤ m`, and `|B| ≤ 4`. -/
theorem theorem_4_5 {v : X} (hv : IsBranchPoint v) :
    ∃ m : ℕ, order v = m ∧ (branchSet X).Finite ∧
      (m - 2) * ((branchSet X).ncard - 1) ≤ m ∧ (branchSet X).ncard ≤ 4 := by
  classical
  -- the order of `v` is `3` or `4`
  have h4 := lemma_4_4 hD h2 v
  obtain ⟨m, hm⟩ : ∃ m : ℕ, order v = m := ⟨(order v).toNat,
    (ENat.coe_toNat (ne_top_of_le_ne_top (by decide) h4)).symm⟩
  have hm3 : 3 ≤ m := by have := hv; unfold IsBranchPoint at this; rw [hm] at this
                         exact_mod_cast this
  have hm4 : m ≤ 4 := by rw [hm] at h4; exact_mod_cast h4
  -- one point in each component of `X \ {v}`
  obtain ⟨S, hSv, hSm, hSinj⟩ := exists_points_of_le_order (le_of_eq hm.symm)
  have hSf : S.Finite := finite_of_encard_eq_coe hSm
  have hcover : ∀ x, x ≠ v → ∃ y ∈ S, connectedComponentIn {v}ᶜ x = connectedComponentIn {v}ᶜ y := by
    have himg : connectedComponentIn {v}ᶜ '' S = compsAt v := by
      refine (hSf.image _).eq_of_subset_of_encard_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩; exact ⟨y, hSv hy, rfl⟩
      · rw [← order_eq, hm, hSinj.encard_image, hSm]
    intro x hx
    have : connectedComponentIn {v}ᶜ x ∈ compsAt v := ⟨x, hx, rfl⟩
    rw [← himg] at this
    obtain ⟨y, hy, he⟩ := this
    exact ⟨y, hy, he.symm⟩
  set Sf := hSf.toFinset
  have hSfcard : Sf.card = m := by
    have := hSm; rw [hSf.encard_eq_coe_toFinset_card] at this; exact_mod_cast this
  set J : X → Finset X := fun c => Sf.filter fun y => ∀ z ∈ seg v y, dist c z = dist c v
  -- each branch point `c ≠ v` has at least `m - 2` constant arcs
  have hJ : ∀ c, IsBranchPoint c → c ≠ v → m - 2 ≤ (J c).card := by
    intro c hc hcv
    obtain ⟨k, hkS, hck⟩ := hcover c hcv
    have hsub : Sf \ J c ⊆ insert k (Sf.filter fun y => y ≠ k ∧ ¬ ∀ z ∈ seg v y,
        dist c z = dist c v) := by
      intro y hy
      rw [Finset.mem_sdiff, Finset.mem_filter] at hy
      by_cases hyk : y = k
      · exact Finset.mem_insert_self _ _ |> fun h => hyk ▸ h
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hy.1, hyk, fun h => hy.2 ⟨hy.1, h⟩⟩)
    have hle1 : (Sf.filter fun y => y ≠ k ∧ ¬ ∀ z ∈ seg v y, dist c z = dist c v).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro y hy y' hy'
      rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hy hy'
      by_contra hyy
      have hcy : connectedComponentIn {v}ᶜ c ≠ connectedComponentIn {v}ᶜ y := by
        rw [hck]; exact fun e => hy.2.1 (hSinj hkS hy.1 e).symm
      have hcy' : connectedComponentIn {v}ᶜ c ≠ connectedComponentIn {v}ᶜ y' := by
        rw [hck]; exact fun e => hy'.2.1 (hSinj hkS hy'.1 e).symm
      have hyy' : connectedComponentIn {v}ᶜ y ≠ connectedComponentIn {v}ᶜ y' :=
        fun e => hyy (hSinj hy.1 hy'.1 e)
      push_neg at hy hy'
      exact not_two_nonconstant hD h2 hc hcv (hSv hy.1) (hSv hy'.1) hcy hcy' hyy' hy.2.2 hy'.2.2
    have h1 := Finset.card_le_card hsub
    have h2' : (Sf \ J c).card = Sf.card - (J c).card :=
      Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
    have h3 := Finset.card_insert_le k (Sf.filter fun y => y ≠ k ∧ ¬ ∀ z ∈ seg v y,
        dist c z = dist c v)
    have h4' : (J c).card ≤ Sf.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  -- different branch points have disjoint sets of constant arcs
  have hdisj : ∀ c c', IsBranchPoint c → IsBranchPoint c' → c ≠ v → c' ≠ v → c ≠ c' →
      Disjoint (J c) (J c') := by
    intro c c' hc hc' hcv hc'v hcc'
    rw [Finset.disjoint_left]
    intro y hy hy'
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hy hy'
    exact not_two_constant hD h2 hcc' (hSv hy.1) hy.2 hy'.2 hcv hc'v
  -- counting
  have hcount : ∀ F : Finset X, (↑F : Set X) ⊆ branchSet X \ {v} → F.card * (m - 2) ≤ m := by
    intro F hF
    have hpd : (↑F : Set X).PairwiseDisjoint J := by
      intro c hc c' hc' hcc'
      exact hdisj c c' (hF hc).1 (hF hc').1 (hF hc).2 (hF hc').2 hcc'
    have hbu : (F.biUnion J).card = ∑ c ∈ F, (J c).card := Finset.card_biUnion hpd
    have hle : (F.biUnion J).card ≤ Sf.card :=
      Finset.card_le_card (Finset.biUnion_subset.2 fun c _ => Finset.filter_subset _ _)
    have hsum : F.card * (m - 2) ≤ ∑ c ∈ F, (J c).card := by
      have := Finset.card_nsmul_le_sum F (fun c => (J c).card) (m - 2)
        (fun c hc => hJ c (hF hc).1 (hF hc).2)
      rwa [smul_eq_mul] at this
    omega
  have hfin : (branchSet X \ {v}).Finite := by
    by_contra hinf
    obtain ⟨F, hF, hFc⟩ := Set.Infinite.exists_subset_card_eq (show (branchSet X \ {v}).Infinite from hinf) (m + 1)
    have := hcount F hF
    rw [hFc] at this
    interval_cases m <;> omega
  have hBfin : (branchSet X).Finite := (hfin.union (finite_singleton v)).subset fun x hx => by
    by_cases hxv : x = v
    · exact Or.inr hxv
    · exact Or.inl ⟨hx, hxv⟩
  have hBcard : (branchSet X).ncard = (branchSet X \ {v}).ncard + 1 := by
    rw [ncard_diff_singleton_add_one (show v ∈ branchSet X from hv) hBfin]
  have hmain := hcount hfin.toFinset (by simp)
  rw [← ncard_eq_toFinset_card _ hfin] at hmain
  refine ⟨m, hm, hBfin, ?_, ?_⟩
  · rw [hBcard, Nat.add_sub_cancel, mul_comm]; exact hmain
  · rw [hBcard]; interval_cases m <;> omega

end Core

section Statements

variable {Y : Type u} [MetricSpace Y]

/-- **Corollary 4.6.** A dendrite with `|M(a, b)| ≤ 2` for all distinct `a, b` is a finite
tree. -/
theorem cor_4_6 (hY : IsDendrite Y) (h2 : MidsetsAtMostTwo Y) : IsFiniteTree Y := by
  obtain ⟨⟨hc, hconn, hnt, -⟩, hlc, hD⟩ := hY
  refine ⟨⟨⟨hc, hconn, hnt, inferInstance⟩, hlc, hD⟩, ?_, fun p _ =>
    ne_top_of_le_ne_top (by decide) (lemma_4_4 hD h2 p)⟩
  rcases (branchSet Y).eq_empty_or_nonempty with h | ⟨v, hv⟩
  · rw [show {p : Y | IsBranchPoint p} = ∅ from h]; exact finite_empty
  · obtain ⟨m, -, hfin, -⟩ := theorem_4_5 hD h2 hv; exact hfin

/-- **Theorem C.** Let `Y` be a dendrite with a compatible metric such that `|M(a, b)| ≤ 2` for
all distinct `a, b`. Then every point of `Y` has order at most four. If `Y` has a branch point of
order `m`, then the set `B` of branch points satisfies `(m - 2)(|B| - 1) ≤ m`. In particular
`|B| ≤ 4`, and `Y` is a finite tree. -/
theorem theorem_C (hY : IsDendrite Y) (h2 : MidsetsAtMostTwo Y) :
    (∀ p : Y, order p ≤ 4) ∧
    (∀ v : Y, IsBranchPoint v → ∃ m : ℕ, order v = m ∧
      (m - 2) * ({p : Y | IsBranchPoint p}.ncard - 1) ≤ m) ∧
    {p : Y | IsBranchPoint p}.Finite ∧ {p : Y | IsBranchPoint p}.ncard ≤ 4 ∧
    IsFiniteTree Y := by
  have hft := cor_4_6 hY h2
  obtain ⟨⟨hc, hconn, hnt, -⟩, hlc, hD⟩ := hY
  refine ⟨lemma_4_4 hD h2, fun v hv => ?_, hft.2.1, ?_, hft⟩
  · obtain ⟨m, hm, -, h, -⟩ := theorem_4_5 hD h2 hv; exact ⟨m, hm, h⟩
  · rcases (branchSet Y).eq_empty_or_nonempty with h | ⟨v, hv⟩
    · rw [show {p : Y | IsBranchPoint p} = ∅ from h, ncard_empty]; decide
    · obtain ⟨m, -, -, -, h⟩ := theorem_4_5 hD h2 hv; exact h

end Statements

end DoubleMidset
