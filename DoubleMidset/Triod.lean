module

public import DoubleMidset.Count

/-!
# The simple triod (Section 10)

`not_hasDMP_of_branched`: a branched finite tree carries no DMP metric. By Proposition 9.3 it would
be a simple triod; the proof of Theorem 10.1 then fills the `3 × 3` direction table of the tips
along the legs and derives the impossible cycle `r₁ > r₂ > r₃ > r₁`.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

universe u

variable {T : Type u} [MetricSpace T] [CompactSpace T] [ConnectedSpace T]
  [LocallyConnectedSpace T] [Nontrivial T] (hT : TreeHyp T)
include hT

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
theorem vertex_cases {v u : T} (hB : branchSet T = {v}) (hu : u ∈ vertices T) : u = v ∨ IsTip u := by
  rcases hu with h | h
  · exact Or.inr h
  · left; have : u ∈ branchSet T := h; rw [hB] at this; exact this

/-- **Step (ii) of Theorem 10.1**: two edge points `p` before `q` on a leg with `h_v(p) < h_v(q)`
form a strict pair with `N(p, q)` even. -/
theorem column_even (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {v : T}
    (hB : branchSet T = {v}) {κ : ℝ → T} (hκ : IsEdgeParam κ) (hκ0 : κ 0 = v)
    {tp tq : ℝ} (h0 : 0 < tp) (h1 : tp < tq) (h2 : tq < 1)
    (hvpq : dist v (κ tp) < dist v (κ tq)) :
    IsStrictPair (κ tp) (κ tq) ∧ Even (oddCount (κ tp) (κ tq)) := by
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  have hv : IsBranchPoint v := by
    have : v ∈ branchSet T := by rw [hB]; rfl
    exact this
  have hI : ∀ t, 0 < t → t < 1 → t ∈ Icc (0 : ℝ) 1 := fun t ht ht' => ⟨ht.le, ht'.le⟩
  have hne : κ tp ≠ κ tq := fun h => by
    have := hκ.arc.2 (hI tp h0 (by linarith)) (hI tq (by linarith) h2) h; linarith
  have hstr : IsStrictPair (κ tp) (κ tq) := by
    refine ⟨hne, fun u hu h0' => ?_⟩
    rcases vertex_cases hB hu with rfl | hut
    · have : dist u (κ tp) - dist u (κ tq) = 0 := h0'; linarith
    · have hinj := tip_strictMono hT hDMP hbr hut hκ
      have : dist u (κ tp) = dist u (κ tq) := by
        have : dist u (κ tp) - dist u (κ tq) = 0 := h0'; linarith
      have := hinj.elim (fun h => h.injOn) (fun h => h.injOn) (hI tp h0 (by linarith))
        (hI tq (by linarith) h2) this
      linarith
  refine ⟨hstr, ?_⟩
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨c, ⟨ρ, hρ, P, Q, hP, -, hpP, -, -, -, hsph, -⟩, hcV, -⟩ :=
    cor_6_7 hT hDMP hstr (hκ.interior tp ⟨h0, by linarith⟩) (hκ.interior tq ⟨by linarith, h2⟩)
      hodd
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hP.1.preimage hκ.arc.1) tp hpP
  set δ' := min (δ / 2) ((1 - tp) / 2)
  have hδ' : 0 < δ' := lt_min (by linarith) (by linarith)
  have e1 : δ' ≤ δ / 2 := min_le_left _ _
  have e2 : δ' ≤ (1 - tp) / 2 := min_le_right _ _
  have hIs : κ '' Icc tp (tp + δ') ⊆ sphere c ρ := by
    rintro _ ⟨t, ht, rfl⟩
    exact hsph (Or.inl (hball (by
      rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])))
  have hne' : κ tp ≠ κ (tp + δ') := fun h => by
    have := hκ.arc.2 (hI tp h0 (by linarith)) (hI (tp + δ') (by linarith) (by linarith)) h
    linarith
  set K := connectedComponentIn (sphere c ρ) (κ tp)
  have hIK : κ '' Icc tp (tp + δ') ⊆ K :=
    hκ.arc.isPreconnected_image.subset_connectedComponentIn ⟨tp, ⟨le_rfl, by linarith⟩, rfl⟩ hIs
  obtain ⟨-, -, hpairs⟩ := lemma_7_2 hT hDMP hcV hρ ⟨κ tp, hIs ⟨tp, ⟨le_rfl, by linarith⟩, rfl⟩, rfl⟩
    ⟨κ tp, hIK ⟨tp, ⟨le_rfl, by linarith⟩, rfl⟩, κ (tp + δ'), hIK ⟨tp + δ', ⟨by linarith, le_rfl⟩,
      rfl⟩, hne'⟩
  obtain ⟨-, heven, -⟩ := hpairs _ (hIK ⟨tp, ⟨le_rfl, by linarith⟩, rfl⟩) _
    (hIK ⟨tp + δ', ⟨by linarith, le_rfl⟩, rfl⟩) hne'
  -- the vertex signs of `(p, q')` and `(p, q)` agree
  have hvq' : dist v (κ tp) < dist v (κ (tp + δ')) := by
    have hmono := lemma_4_3 hT.noSCC hD2 hv hκ.arc hκ0
    have hle : dist v (κ tp) ≤ dist v (κ (tp + δ')) :=
      hmono (hI tp h0 (by linarith)) (hI (tp + δ') (by linarith) (by linarith)) (by linarith)
    have hsa : IsSphericalArc (κ '' Icc tp (tp + δ')) c ρ :=
      ⟨(hκ.arc.isArcBetween_Icc h0.le (by linarith) (by linarith)).isArc, hρ, hIs⟩
    have hvI : v ∉ κ '' Icc tp (tp + δ') := by
      rintro ⟨t, ht, he⟩
      exact hκ.interior t ⟨by linarith [ht.1], by linarith [ht.2]⟩ (he ▸ Or.inr hv)
    have hvc : v ≠ c := fun h => hcV (h ▸ Or.inr hv)
    have hinj := (lemma_6_2 hT hD2 hsa).1 v hvI hvc
    exact lt_of_le_of_ne hle fun h => hne' (hinj ⟨tp, ⟨le_rfl, by linarith⟩, rfl⟩
      ⟨tp + δ', ⟨by linarith, le_rfl⟩, rfl⟩ h)
  have hsame : oddCount (κ tp) (κ (tp + δ')) = oddCount (κ tp) (κ tq) := by
    unfold oddCount; congr 1; ext u
    simp only [mem_setOf_eq]
    refine and_congr_right fun hu => ?_
    rcases vertex_cases hB hu.1 with rfl | hut
    · constructor
      · intro _; show dist u (κ tp) - dist u (κ tq) < 0; linarith
      · intro _; show dist u (κ tp) - dist u (κ (tp + δ')) < 0; linarith
    · exact sub_neg_iff_of_strictMono (tip_strictMono hT hDMP hbr hut hκ)
        (hI tp h0 (by linarith)) (hI (tp + δ') (by linarith) (by linarith))
        (hI tp h0 (by linarith)) (hI tq (by linarith) h2) (by linarith) (by linarith)
        ⟨fun _ => h1, fun _ => by linarith⟩
  rw [hsame] at heven
  exact (Nat.not_even_iff_odd.2 hodd) heven

/-- Two equal directions give a used pair. -/
theorem uses_of_same (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {e v : T}
    (he : IsTip e) {κ κ' : ℝ → T} (hκ : IsEdgeParam κ) (hκ' : IsEdgeParam κ') (hκ0 : κ 0 = v)
    (hκ'0 : κ' 0 = v)
    (hsame : (dist e (κ 1) < dist e v ↔ dist e (κ' 1) < dist e v)) :
    UsesPair e v (κ '' Icc 0 1) (κ' '' Icc 0 1) := by
  have key : ∀ {k : ℝ → T}, IsEdgeParam k → k 0 = v →
      ((dist e (k 1) < dist e v) ↔ ∀ a ∈ k '' Icc 0 1, a ≠ v → ¬ (dist e v < dist e a)) := by
    intro k hk hk0
    have hpos : ∀ t ∈ Icc (0 : ℝ) 1, k t ≠ v → 0 < t := fun t ht h =>
      lt_of_le_of_ne ht.1 fun h0 => h (by rw [← h0, hk0])
    have h1v : k 1 ≠ v := by rw [← hk0]; exact hk.arc.ne.symm
    rcases tip_strictMono hT hDMP hbr he hk with hm | hm
    · have hlt : dist e v < dist e (k 1) := by
        have : dist e (k 0) < dist e (k 1) := hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
          zero_lt_one
        rwa [hk0] at this
      exact ⟨fun h => absurd h (not_lt.2 hlt.le),
        fun h => absurd hlt (h _ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩ h1v)⟩
    · have hlt : dist e (k 1) < dist e v := by
        have : dist e (k 1) < dist e (k 0) := hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
          zero_lt_one
        rwa [hk0] at this
      refine ⟨fun _ => ?_, fun _ => hlt⟩
      rintro _ ⟨t, ht, rfl⟩ h
      have : dist e (k t) < dist e (k 0) := hm ⟨le_rfl, zero_le_one⟩ ht (hpos t ht h)
      rw [hk0] at this; exact not_lt.2 this.le
  have hk := key hκ hκ0
  have hk' := key hκ' hκ'0
  intro a ha a' ha' hav ha'v
  by_cases h : dist e (κ 1) < dist e v
  · exact ⟨fun h' => absurd h' (hk.1 h a ha hav),
      fun h' => absurd h' (hk'.1 (hsame.1 h) a' ha' ha'v)⟩
  · have h' : ¬ dist e (κ' 1) < dist e v := fun h'' => h (hsame.2 h'')
    -- both increasing
    have inc : ∀ {k : ℝ → T}, IsEdgeParam k → k 0 = v → ¬ dist e (k 1) < dist e v →
        ∀ b ∈ k '' Icc 0 1, b ≠ v → dist e v < dist e b := by
      intro k hk hk0 hn
      rcases tip_strictMono hT hDMP hbr he hk with hm | hm
      · rintro _ ⟨t, ht, rfl⟩ hb
        have hpos : 0 < t := lt_of_le_of_ne ht.1 fun h0 => hb (by rw [← h0, hk0])
        have : dist e (k 0) < dist e (k t) := hm ⟨le_rfl, zero_le_one⟩ ht hpos
        rwa [hk0] at this
      · exfalso; apply hn
        have : dist e (k 1) < dist e (k 0) := hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
          zero_lt_one
        rwa [hk0] at this
    exact ⟨fun _ => inc hκ' hκ'0 h' a' ha' ha'v, fun _ => inc hκ hκ0 h a ha hav⟩

/-- Sign of a tip along a leg, read from its direction. -/
theorem sign_tip_leg (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {a v : T} (ha : IsTip a)
    {κ : ℝ → T} (hκ : IsEdgeParam κ) (hκ0 : κ 0 = v) {tp tq : ℝ} (h0 : 0 ≤ tp) (h1 : tp < tq)
    (h2 : tq ≤ 1) : sgnf (κ tp) (κ tq) a < 0 ↔ ¬ dist a (κ 1) < dist a v := by
  have hI1 : tp ∈ Icc (0 : ℝ) 1 := ⟨h0, by linarith⟩
  have hI2 : tq ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h2⟩
  show dist a (κ tp) - dist a (κ tq) < 0 ↔ _
  rcases tip_strictMono hT hDMP hbr ha hκ with hm | hm
  · have := hm hI1 hI2 h1
    have h01 : dist a (κ 0) < dist a (κ 1) := hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      zero_lt_one
    rw [hκ0] at h01
    exact ⟨fun _ => not_lt.2 h01.le, fun _ => by linarith⟩
  · have := hm hI1 hI2 h1
    have h01 : dist a (κ 1) < dist a (κ 0) := hm ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
      zero_lt_one
    rw [hκ0] at h01
    exact ⟨fun h => by linarith, fun h => absurd h01 h⟩

omit [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T] hT in
/-- Parity of a count over four points. -/
theorem count_four {v c a b : T} (hvc : v ≠ c) (hva : v ≠ a) (hvb : v ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) (hab : a ≠ b) (P : T → Prop) (hv : P v) (hc : ¬ P c)
    (hev : Even {u | u ∈ ({v, c, a, b} : Set T) ∧ P u}.ncard) : (P a ↔ ¬ P b) := by
  by_contra h
  have hcases : (P a ∧ P b) ∨ (¬ P a ∧ ¬ P b) := by tauto
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have : {u | u ∈ ({v, c, a, b} : Set T) ∧ P u} = {v, a, b} := by
      ext u; simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨h1 | h1 | h1 | h1, h2⟩
        · exact Or.inl h1
        · exact absurd (h1 ▸ h2) hc
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
      · rintro (rfl | rfl | rfl)
        · exact ⟨Or.inl rfl, hv⟩
        · exact ⟨Or.inr (Or.inr (Or.inl rfl)), ha⟩
        · exact ⟨Or.inr (Or.inr (Or.inr rfl)), hb⟩
    rw [this, ncard_insert_of_notMem (by simp [hva, hvb]), ncard_pair hab] at hev
    exact (by decide : ¬ Even 3) hev
  · have : {u | u ∈ ({v, c, a, b} : Set T) ∧ P u} = {v} := by
      ext u; simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨h1 | h1 | h1 | h1, h2⟩
        · exact h1
        · exact absurd (h1 ▸ h2) hc
        · exact absurd (h1 ▸ h2) ha
        · exact absurd (h1 ▸ h2) hb
      · rintro rfl; exact ⟨Or.inl rfl, hv⟩
    rw [this, ncard_singleton] at hev
    exact (by decide : ¬ Even 1) hev

/-- **Step (i) of Theorem 10.1**: no tip has three decreasing legs. -/
theorem row_lemma (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) {v : T}
    (hv : IsBranchPoint v) {κ₁ κ₂ κ₃ : ℝ → T} (hκ₁ : IsEdgeParam κ₁) (hκ₂ : IsEdgeParam κ₂)
    (hκ₃ : IsEdgeParam κ₃) (h₁ : κ₁ 0 = v) (h₂ : κ₂ 0 = v) (h₃ : κ₃ 0 = v)
    (h12 : κ₁ '' Icc 0 1 ≠ κ₂ '' Icc 0 1) (h13 : κ₁ '' Icc 0 1 ≠ κ₃ '' Icc 0 1)
    (h23 : κ₂ '' Icc 0 1 ≠ κ₃ '' Icc 0 1) {e e' : T} (he : IsTip e) (he' : IsTip e')
    (hee' : e ≠ e') :
    ¬ (dist e (κ₁ 1) < dist e v ∧ dist e (κ₂ 1) < dist e v ∧ dist e (κ₃ 1) < dist e v) := by
  rintro ⟨d1, d2, d3⟩
  have hmem : ∀ {κ : ℝ → T}, κ 0 = v → v ∈ κ '' Icc 0 1 := fun h =>
    ⟨0, ⟨le_rfl, zero_le_one⟩, h⟩
  have pair : ∀ {k k' : ℝ → T}, IsEdgeParam k → IsEdgeParam k' → k 0 = v → k' 0 = v →
      k '' Icc 0 1 ≠ k' '' Icc 0 1 → dist e (k 1) < dist e v → dist e (k' 1) < dist e v →
      (dist e' (k 1) < dist e' v ↔ dist e' (k' 1) < dist e' v) → False :=
    fun hk hk' hk0 hk'0 hne d d' hsame =>
      lemma_9_2 hT hDMP hbr hv (hk.isEdge hT) (hk'.isEdge hT) (hmem hk0) (hmem hk'0) hne he he'
        hee' ⟨uses_of_same hT hDMP hbr he hk hk' hk0 hk'0 ⟨fun _ => d', fun _ => d⟩,
          uses_of_same hT hDMP hbr he' hk hk' hk0 hk'0 hsame⟩
  by_cases s12 : (dist e' (κ₁ 1) < dist e' v ↔ dist e' (κ₂ 1) < dist e' v)
  · exact pair hκ₁ hκ₂ h₁ h₂ h12 d1 d2 s12
  by_cases s13 : (dist e' (κ₁ 1) < dist e' v ↔ dist e' (κ₃ 1) < dist e' v)
  · exact pair hκ₁ hκ₃ h₁ h₃ h13 d1 d3 s13
  exact pair hκ₂ hκ₃ h₂ h₃ h23 d2 d3 (by tauto)

/-- **Theorem 10.1, in tree form.** A branched finite tree admits no DMP metric. -/
theorem not_hasDMP_of_branched (hbr : ∃ v : T, IsBranchPoint v) : ¬ HasDMP T := by
  intro hDMP
  have hD2 : MidsetsAtMostTwo T := fun p q hpq => (hDMP p q hpq).le
  obtain ⟨v, hv, hB, hdeg, ℓ₁, ℓ₂, ℓ₃, h12, h13, h23, hE, hmem⟩ := triod_structure hT hDMP hbr
  have hvV : v ∈ vertices T := Or.inr hv
  have hleg : ∀ ℓ ∈ ({ℓ₁, ℓ₂, ℓ₃} : Set (Set T)), ∃ (c : T) (κ : ℝ → T), IsTip c ∧ seg v c = ℓ ∧
      ℓ ∩ vertices T = {v, c} ∧ IsEdgeParam κ ∧ κ '' Icc 0 1 = ℓ ∧ κ 0 = v ∧ κ 1 = c := by
    intro ℓ hℓ
    obtain ⟨hℓe, hvℓ⟩ := hmem ℓ hℓ
    obtain ⟨c, hcV, hvc, hseg, hcap⟩ := edge_from_vertex hT hℓe hvℓ hvV
    obtain ⟨κ, hκ, hκℓ, hκ0⟩ := edge_param_from hT hℓe hvℓ hvV
    have hct : IsTip c := (vertex_cases hB hcV).resolve_left (Ne.symm hvc)
    have hκ1 : κ 1 = c := by
      have : κ 1 ∈ ℓ ∩ vertices T := ⟨hκℓ ▸ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, hκ.end1⟩
      rw [hcap] at this
      rcases this with h | h
      · exact absurd (h.trans hκ0.symm) hκ.arc.ne.symm
      · exact h
    exact ⟨c, κ, hct, hseg, hcap, hκ, hκℓ, hκ0, hκ1⟩
  obtain ⟨c₁, κ₁, ht₁, hs₁, hcap₁, hκ₁, hκℓ₁, hκ₁0, hκ₁1⟩ := hleg ℓ₁ (mem_insert _ _)
  obtain ⟨c₂, κ₂, ht₂, hs₂, hcap₂, hκ₂, hκℓ₂, hκ₂0, hκ₂1⟩ :=
    hleg ℓ₂ (mem_insert_of_mem _ (mem_insert _ _))
  obtain ⟨c₃, κ₃, ht₃, hs₃, hcap₃, hκ₃, hκℓ₃, hκ₃0, hκ₃1⟩ :=
    hleg ℓ₃ (mem_insert_of_mem _ (mem_insert_of_mem _ rfl))
  have hc12 : c₁ ≠ c₂ := fun h => h12 (by rw [← hs₁, ← hs₂, h])
  have hc13 : c₁ ≠ c₃ := fun h => h13 (by rw [← hs₁, ← hs₃, h])
  have hc23 : c₂ ≠ c₃ := fun h => h23 (by rw [← hs₂, ← hs₃, h])
  have hvt : ∀ {c : T}, IsTip c → v ≠ c := by
    intro c hc h
    have h3 : 3 ≤ order v := hv
    have h1 : order c = 1 := hc
    rw [h, h1] at h3; exact absurd h3 (by decide)
  -- the odd vertices
  have hV : vertices T = {v, c₁, c₂, c₃} := by
    ext u; constructor
    · intro hu
      obtain ⟨ℓ, hℓ, huℓ⟩ : u ∈ ⋃₀ {ℓ : Set T | IsEdge ℓ} := by
        rw [sUnion_edges hT.noSCC hT.bfin hT.bord]; trivial
      rw [hE] at hℓ
      rcases hℓ with rfl | rfl | rfl
      · have : u ∈ ℓ ∩ vertices T := ⟨huℓ, hu⟩
        rw [hcap₁] at this
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · have : u ∈ ℓ ∩ vertices T := ⟨huℓ, hu⟩
        rw [hcap₂] at this
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      · have : u ∈ ℓ ∩ vertices T := ⟨huℓ, hu⟩
        rw [hcap₃] at this
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
    · rintro (rfl | rfl | rfl | rfl)
      · exact hvV
      · exact Or.inl ht₁
      · exact Or.inl ht₂
      · exact Or.inl ht₃
  have hOdd : oddVertices T = {v, c₁, c₂, c₃} := by
    rw [← hV]; ext u
    refine ⟨fun h => h.1, fun hu => ⟨hu, ?_⟩⟩
    rcases vertex_cases hB hu with rfl | hut
    · exact ⟨3, by rw [order_eq_degree hT hvV, hdeg], by decide⟩
    · exact ⟨1, by exact_mod_cast hut, odd_one⟩
  -- columns: every column has exactly two `↓`
  have hcolumn : ∀ {κ : ℝ → T} {cj a b : T}, IsEdgeParam κ → κ 0 = v → κ 1 = cj → IsTip cj →
      IsTip a → IsTip b → cj ≠ a → cj ≠ b → a ≠ b →
      ({v, c₁, c₂, c₃} : Set T) = {v, cj, a, b} →
      (dist a cj < dist a v ↔ ¬ dist b cj < dist b v) := by
    intro κ cj a b hκ hκ0 hκ1 hcj ha hb hca hcb hab hset
    set φ := fun t => dist v (κ t)
    have hφc : Continuous φ := continuous_const.dist hκ.arc.1
    have hφ0 : φ 0 = 0 := by simp only [φ, hκ0, dist_self]
    have hφ1 : 0 < φ 1 := dist_pos.2 (by rw [← hκ0]; exact hκ.arc.ne)
    obtain ⟨tp, htp, hp⟩ := intermediate_value_Ioo zero_le_one hφc.continuousOn
      (show φ 1 / 3 ∈ Ioo (φ 0) (φ 1) by rw [hφ0]; constructor <;> linarith)
    obtain ⟨tq, htq, hq⟩ := intermediate_value_Ioo zero_le_one hφc.continuousOn
      (show 2 * φ 1 / 3 ∈ Ioo (φ 0) (φ 1) by rw [hφ0]; constructor <;> linarith)
    have hmono : MonotoneOn φ (Icc 0 1) := lemma_4_3 hT.noSCC hD2 hv hκ.arc hκ0
    have hpq : tp < tq := by
      by_contra hc; push_neg at hc
      have := hmono (Ioo_subset_Icc_self htq) (Ioo_subset_Icc_self htp) hc
      simp only [φ] at hp hq this; linarith
    have hvpq : dist v (κ tp) < dist v (κ tq) := by
      have h1 : φ tp = φ 1 / 3 := hp
      have h2 : φ tq = 2 * φ 1 / 3 := hq
      show φ tp < φ tq; rw [h1, h2]; linarith
    obtain ⟨-, heven⟩ := column_even hT hDMP hbr hB hκ hκ0 htp.1 hpq htq.2 hvpq
    unfold oddCount at heven
    rw [hOdd, hset] at heven
    have hP := count_four (hvt hcj) (hvt ha) (hvt hb) hca hcb hab
      (fun u => sgnf (κ tp) (κ tq) u < 0) (by show dist v (κ tp) - dist v (κ tq) < 0; linarith)
      (by
        show ¬ sgnf (κ tp) (κ tq) cj < 0
        rw [sign_tip_leg hT hDMP hbr hcj hκ hκ0 htp.1.le hpq htq.2.le, hκ1, dist_self,
          not_not]
        exact dist_pos.2 (hvt hcj).symm)
      heven
    rw [sign_tip_leg hT hDMP hbr ha hκ hκ0 htp.1.le hpq htq.2.le,
      sign_tip_leg hT hDMP hbr hb hκ hκ0 htp.1.le hpq htq.2.le, hκ1, not_not] at hP
    tauto
  have col1 := hcolumn hκ₁ hκ₁0 hκ₁1 ht₁ ht₂ ht₃ hc12 hc13 hc23 rfl
  have col2 := hcolumn hκ₂ hκ₂0 hκ₂1 ht₂ ht₁ ht₃ hc12.symm hc23 hc13 (by
    ext u; simp only [mem_insert_iff, mem_singleton_iff]; tauto)
  have col3 := hcolumn hκ₃ hκ₃0 hκ₃1 ht₃ ht₁ ht₂ hc13.symm hc23.symm hc12 (by
    ext u; simp only [mem_insert_iff, mem_singleton_iff]; tauto)
  -- rows: no tip has three `↓`
  have hne₁₂ : κ₁ '' Icc 0 1 ≠ κ₂ '' Icc 0 1 := by rw [hκℓ₁, hκℓ₂]; exact h12
  have hne₁₃ : κ₁ '' Icc 0 1 ≠ κ₃ '' Icc 0 1 := by rw [hκℓ₁, hκℓ₃]; exact h13
  have hne₂₃ : κ₂ '' Icc 0 1 ≠ κ₃ '' Icc 0 1 := by rw [hκℓ₂, hκℓ₃]; exact h23
  have row := fun {e e' : T} (he : IsTip e) (he' : IsTip e') (hee' : e ≠ e') =>
    row_lemma hT hDMP hbr hv hκ₁ hκ₂ hκ₃ hκ₁0 hκ₂0 hκ₃0 hne₁₂ hne₁₃ hne₂₃ he he' hee'
  rw [hκ₁1, hκ₂1, hκ₃1] at row
  have row1 := row ht₁ ht₂ hc12
  have row2 := row ht₂ ht₁ hc12.symm
  have row3 := row ht₃ ht₁ hc13.symm
  have diag : ∀ {c : T}, IsTip c → dist c c < dist c v := by
    intro c hc; rw [dist_self]; exact dist_pos.2 (hvt hc).symm
  -- strictness of `↑`
  have strict : ∀ {c c' : T} {κ : ℝ → T}, IsTip c → IsEdgeParam κ → κ 0 = v → κ 1 = c' →
      ¬ dist c c' < dist c v → dist c v < dist c c' := by
    intro c c' κ hc hκ hκ0 hκ1 h
    rcases lt_or_eq_of_le (not_lt.1 h) with h' | h'
    · exact h'
    · exfalso
      have hinj := prop_8_2_a hT hDMP hbr hc (hκ.isEdge hT)
      have := hinj ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
        (by rw [hκ0, hκ1]; exact h')
      exact hκ.arc.ne this
  have s12 := fun h => strict ht₁ hκ₂ hκ₂0 hκ₂1 h
  have s13 := fun h => strict ht₁ hκ₃ hκ₃0 hκ₃1 h
  have s21 := fun h => strict ht₂ hκ₁ hκ₁0 hκ₁1 h
  have s23 := fun h => strict ht₂ hκ₃ hκ₃0 hκ₃1 h
  have s31 := fun h => strict ht₃ hκ₁ hκ₁0 hκ₁1 h
  have s32 := fun h => strict ht₃ hκ₂ hκ₂0 hκ₂1 h
  have d12 := dist_comm c₁ c₂
  have d13 := dist_comm c₁ c₃
  have d23 := dist_comm c₂ c₃
  have dv1 := dist_comm c₁ v
  have dv2 := dist_comm c₂ v
  have dv3 := dist_comm c₃ v
  -- (iii) the cycle
  by_cases D21 : dist c₂ c₁ < dist c₂ v
  · have nD31 : ¬ dist c₃ c₁ < dist c₃ v := col1.1 D21
    have nD23 : ¬ dist c₂ c₃ < dist c₂ v := fun h => row2 ⟨D21, diag ht₂, h⟩
    have D13 : dist c₁ c₃ < dist c₁ v := col3.2 nD23
    have nD12 : ¬ dist c₁ c₂ < dist c₁ v := fun h => row1 ⟨diag ht₁, h, D13⟩
    have D32 : dist c₃ c₂ < dist c₃ v := by
      by_contra h; exact nD12 (col2.2 h)
    linarith [s12 nD12, s31 nD31, s23 nD23]
  · have D31 : dist c₃ c₁ < dist c₃ v := by by_contra h; exact D21 (col1.2 h)
    have nD32 : ¬ dist c₃ c₂ < dist c₃ v := fun h => row3 ⟨D31, h, diag ht₃⟩
    have D12 : dist c₁ c₂ < dist c₁ v := col2.2 nD32
    have nD13 : ¬ dist c₁ c₃ < dist c₁ v := fun h => row1 ⟨diag ht₁, D12, h⟩
    have D23 : dist c₂ c₃ < dist c₂ v := by by_contra h; exact nD13 (col3.2 h)
    linarith [s21 D21, s13 nD13, s32 nD32]

end DoubleMidset
