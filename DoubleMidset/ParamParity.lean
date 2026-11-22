module

public import DoubleMidset.Edges

/-!
# Sign changes of a real function on an interval

`IsParamCrossing h s`: `s` is a zero of `h` at which `h` changes sign; `IsParamTouch h s`: a zero
at which the sign is the same on both sides. The main result (`param_parity`): if `h` is
continuous on `[α, β]` with finitely many zeros there and none at the ends, the number of sign
changes in `(α, β)` has the parity of `[h α < 0] + [h β < 0]`. This is the edge-by-edge count in
the proof of Lemma 5.4.
-/

@[expose] public section

open Set Topology Function Metric Filter

namespace DoubleMidset

/-- `s` is a zero of `h` at which `h` changes sign. -/
def IsParamCrossing (h : ℝ → ℝ) (s : ℝ) : Prop :=
  h s = 0 ∧ ∃ ε > 0, ∀ t ∈ Ioo (s - ε) s, ∀ t' ∈ Ioo s (s + ε), h t * h t' < 0

/-- `s` is a zero of `h` with the same sign of `h` on both sides. -/
def IsParamTouch (h : ℝ → ℝ) (s : ℝ) : Prop :=
  h s = 0 ∧ ∃ ε > 0, ∀ t ∈ Ioo (s - ε) s, ∀ t' ∈ Ioo s (s + ε), 0 < h t * h t'

/-- A continuous function without zeros on a preconnected set has a constant sign there. -/
theorem const_sign {h : ℝ → ℝ} {S : Set ℝ} (hS : IsPreconnected S) (hc : ContinuousOn h S)
    (h0 : ∀ x ∈ S, h x ≠ 0) : ∀ x ∈ S, ∀ y ∈ S, 0 < h x * h y := by
  intro x hx y hy
  by_contra hneg
  push_neg at hneg
  rcases le_total (h x) 0 with hx0 | hx0
  · have hy0 : 0 ≤ h y := by
      by_contra hy0; push_neg at hy0
      have := mul_pos_of_neg_of_neg (lt_of_le_of_ne hx0 (h0 x hx)) hy0; linarith
    obtain ⟨z, hz, hz0⟩ := hS.intermediate_value hx hy hc ⟨hx0, hy0⟩
    exact h0 z hz hz0
  · have hy0 : h y ≤ 0 := by
      by_contra hy0; push_neg at hy0
      have := mul_pos (lt_of_le_of_ne hx0 (Ne.symm (h0 x hx))) hy0; linarith
    obtain ⟨z, hz, hz0⟩ := hS.intermediate_value hy hx hc ⟨hy0, hx0⟩
    exact h0 z hz hz0

theorem mul_pos_iff_same {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < a * b ↔ (a < 0 ↔ b < 0) := by
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · exact ⟨fun _ => ⟨fun _ => hb, fun _ => ha⟩, fun _ => mul_pos_of_neg_of_neg ha hb⟩
  · exact ⟨fun h => absurd h (not_lt.2 (mul_neg_of_neg_of_pos ha hb).le),
      fun h => absurd (h.1 ha) (not_lt.2 hb.le)⟩
  · exact ⟨fun h => absurd h (not_lt.2 (mul_neg_of_pos_of_neg ha hb).le),
      fun h => absurd (h.2 hb) (not_lt.2 ha.le)⟩
  · exact ⟨fun _ => ⟨fun h => absurd h (not_lt.2 ha.le), fun h => absurd h (not_lt.2 hb.le)⟩,
      fun _ => mul_pos ha hb⟩

/-- **Parity of sign changes on an interval.** -/
theorem param_parity {h : ℝ → ℝ} :
    ∀ (n : ℕ) {α β : ℝ}, α < β → ContinuousOn h (Icc α β) →
      {s | s ∈ Icc α β ∧ h s = 0}.Finite → {s | s ∈ Icc α β ∧ h s = 0}.ncard = n →
      h α ≠ 0 → h β ≠ 0 →
      ({s | s ∈ Ioo α β ∧ IsParamCrossing h s}.ncard + (if h α < 0 then 1 else 0) +
        (if h β < 0 then 1 else 0)) % 2 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α β hαβ hc hfin hcard hα hβ
  set Z := {s | s ∈ Icc α β ∧ h s = 0}
  have hcrossZ : ∀ s ∈ Ioo α β, IsParamCrossing h s → s ∈ Z := fun s hs hcr =>
    ⟨Ioo_subset_Icc_self hs, hcr.1⟩
  rcases Z.eq_empty_or_nonempty with hZ | hZne
  · -- constant sign
    have h0 : ∀ x ∈ Icc α β, h x ≠ 0 := fun x hx hx0 => by
      have : x ∈ Z := ⟨hx, hx0⟩; rw [hZ] at this; exact this
    have hcr : {s | s ∈ Ioo α β ∧ IsParamCrossing h s} = ∅ := by
      ext s; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hs hcr; exact h0 s (Ioo_subset_Icc_self hs) hcr.1
    have hsame := (mul_pos_iff_same hα hβ).1 (const_sign isPreconnected_Icc hc h0 α
      ⟨le_rfl, hαβ.le⟩ β ⟨hαβ.le, le_rfl⟩)
    rw [hcr, ncard_empty]
    by_cases h1 : h α < 0
    · rw [if_pos h1, if_pos (hsame.1 h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hsame.2 h2))]
  · -- the largest zero `z`, and a point `w` between the previous zero (or `α`) and `z`
    have hZc : IsCompact Z := hfin.isCompact
    set z := sSup Z
    have hzZ : z ∈ Z := hZc.sSup_mem hZne
    have hzmax : ∀ s ∈ Z, s ≤ z := fun s hs => le_csSup hZc.bddAbove hs
    have hzα : α < z := lt_of_le_of_ne hzZ.1.1 fun e => hα (e ▸ hzZ.2)
    have hzβ : z < β := lt_of_le_of_ne hzZ.1.2 fun e => hβ (e.symm ▸ hzZ.2)
    set Z' := Z \ {z}
    have hZ'f : Z'.Finite := hfin.subset diff_subset
    set m := sSup (insert α Z')
    have hmZ : m ∈ insert α Z' := (hZ'f.insert α).isCompact.sSup_mem (insert_nonempty _ _)
    have hmmax : ∀ s ∈ insert α Z', s ≤ m := fun s hs =>
      le_csSup (hZ'f.insert α).isCompact.bddAbove hs
    have hmz : m < z := by
      rcases hmZ with e | ⟨hm, hmz⟩
      · rw [e]; exact hzα
      · exact lt_of_le_of_ne (hzmax m hm) hmz
    have hαm : α ≤ m := hmmax α (mem_insert _ _)
    set w := (m + z) / 2
    have hmw : m < w := by simp only [w]; linarith
    have hwz : w < z := by simp only [w]; linarith
    -- no zeros in `(m, z)` and `(z, β]`
    have hnoz1 : ∀ x ∈ Ioo m z, h x ≠ 0 := by
      intro x hx hx0
      have hxZ : x ∈ Z := ⟨⟨hαm.trans hx.1.le, hx.2.le.trans hzβ.le⟩, hx0⟩
      have := hmmax x (mem_insert_of_mem _ ⟨hxZ, fun e => hx.2.ne (mem_singleton_iff.1 e)⟩)
      linarith [hx.1]
    have hnoz2 : ∀ x ∈ Ioc z β, h x ≠ 0 := by
      intro x hx hx0
      have := hzmax x ⟨⟨hzα.le.trans hx.1.le, hx.2⟩, hx0⟩; linarith [hx.1]
    have hw0 : h w ≠ 0 := hnoz1 w ⟨hmw, hwz⟩
    -- induction hypothesis on `[α, w]`
    have hZw : {s | s ∈ Icc α w ∧ h s = 0} = Z' := by
      ext s; constructor
      · rintro ⟨hs, hs0⟩
        refine ⟨⟨⟨hs.1, hs.2.trans (hwz.trans hzβ).le⟩, hs0⟩, fun e => ?_⟩
        rw [mem_singleton_iff] at e; linarith [hs.2]
      · rintro ⟨⟨hs, hs0⟩, hsz⟩
        have := hmmax s (mem_insert_of_mem _ ⟨⟨hs, hs0⟩, hsz⟩)
        exact ⟨⟨hs.1, this.trans hmw.le⟩, hs0⟩
    have hcardZ' : Z'.ncard < n := by
      rw [← hcard]; exact ncard_lt_ncard (diff_singleton_ssubset.2 hzZ) hfin
    have hIH := ih _ hcardZ' (hαm.trans_lt hmw) (hc.mono (Icc_subset_Icc le_rfl
      (hwz.trans hzβ).le)) (hZw ▸ hZ'f) (by rw [hZw]) hα hw0
    -- the crossings in `(α, β)` are those in `(α, w)`, plus `z` if it is one
    have hz_iff : IsParamCrossing h z ↔ h w * h β < 0 := by
      have hs1 := const_sign isPreconnected_Ioo (hc.mono fun x hx =>
        ⟨hαm.trans hx.1.le, hx.2.le.trans hzβ.le⟩) hnoz1
      have hs2 := const_sign isPreconnected_Ioc (hc.mono fun x hx =>
        ⟨hzα.le.trans hx.1.le, hx.2⟩) hnoz2
      constructor
      · rintro ⟨-, ε, hε, hside⟩
        set t := max w (z - ε / 2)
        set t' := min β (z + ε / 2)
        have ht : t ∈ Ioo (z - ε) z := ⟨lt_max_of_lt_right (by linarith), max_lt hwz (by linarith)⟩
        have ht' : t' ∈ Ioo z (z + ε) := ⟨lt_min hzβ (by linarith), min_lt_of_right_lt
          (by linarith)⟩
        have h1 := hside t ht t' ht'
        have h2 := hs1 w ⟨hmw, hwz⟩ t ⟨hmw.trans_le (le_max_left _ _), ht.2⟩
        have h3 := hs2 t' ⟨ht'.1, min_le_left _ _⟩ β ⟨hzβ, le_rfl⟩
        nlinarith [sq_nonneg (h t), sq_nonneg (h t'), mul_pos h2 h3]
      · intro hneg
        refine ⟨hzZ.2, min (z - m) (β - z), lt_min (by linarith) (by linarith), ?_⟩
        intro t ht t' ht'
        have h2 := hs1 w ⟨hmw, hwz⟩ t ⟨by linarith [ht.1, min_le_left (z - m) (β - z)], ht.2⟩
        have h3 := hs2 t' ⟨ht'.1, by linarith [ht'.2, min_le_right (z - m) (β - z)]⟩ β
          ⟨hzβ, le_rfl⟩
        nlinarith [sq_nonneg (h w), sq_nonneg (h β), mul_pos h2 h3]
    have hcrossings : {s | s ∈ Ioo α β ∧ IsParamCrossing h s} =
        {s | s ∈ Ioo α w ∧ IsParamCrossing h s} ∪
          (if h w * h β < 0 then {z} else ∅) := by
      ext s; constructor
      · rintro ⟨hs, hcr⟩
        by_cases hsz : s = z
        · subst hsz; right; rw [if_pos (hz_iff.1 hcr)]; rfl
        · left
          have hsZ' : s ∈ Z' := ⟨hcrossZ s hs hcr, hsz⟩
          have := hmmax s (mem_insert_of_mem _ hsZ')
          exact ⟨⟨hs.1, this.trans_lt hmw⟩, hcr⟩
      · rintro (⟨hs, hcr⟩ | hs)
        · exact ⟨⟨hs.1, hs.2.trans (hwz.trans hzβ)⟩, hcr⟩
        · split_ifs at hs with hneg
          · rw [mem_singleton_iff.1 hs]; exact ⟨⟨hzα, hzβ⟩, hz_iff.2 hneg⟩
          · exact hs.elim
    have hdisj : Disjoint {s | s ∈ Ioo α w ∧ IsParamCrossing h s}
        (if h w * h β < 0 then ({z} : Set ℝ) else ∅) := by
      split_ifs
      · rw [disjoint_singleton_right]; rintro ⟨hz, -⟩; exact (lt_asymm hz.2 hwz).elim
      · exact disjoint_empty _
    have hZwf : {s | s ∈ Icc α w ∧ h s = 0}.Finite := by rw [hZw]; exact hZ'f
    have hfinw : {s | s ∈ Ioo α w ∧ IsParamCrossing h s}.Finite :=
      hZwf.subset fun s ⟨hs, hcr⟩ => ⟨Ioo_subset_Icc_self hs, hcr.1⟩
    rw [hcrossings, ncard_union_eq hdisj hfinw (by split_ifs <;> simp)]
    have hsame : 0 < h w * h β ∨ h w * h β < 0 := by
      rcases lt_trichotomy (h w * h β) 0 with h' | h' | h'
      · exact Or.inr h'
      · exact absurd h' (mul_ne_zero hw0 hβ)
      · exact Or.inl h'
    rcases hsame with hpos | hneg
    · rw [if_neg (not_lt.2 hpos.le), ncard_empty, add_zero]
      have := (mul_pos_iff_same hw0 hβ).1 hpos
      by_cases hw' : h w < 0
      · rw [if_pos hw'] at hIH; rw [if_pos (this.1 hw')]; omega
      · rw [if_neg hw'] at hIH; rw [if_neg (fun h' => hw' (this.2 h'))]; omega
    · rw [if_pos hneg, ncard_singleton]
      have : ¬ (h w < 0 ↔ h β < 0) := fun hh =>
        absurd hneg (not_lt.2 ((mul_pos_iff_same hw0 hβ).2 hh).le)
      by_cases hw' : h w < 0
      · rw [if_pos hw'] at hIH; rw [if_neg (fun h' => this ⟨fun _ => h', fun _ => hw'⟩)]; omega
      · rw [if_neg hw'] at hIH
        rw [if_pos (show h β < 0 by by_contra h'; exact this ⟨fun h'' => (hw' h'').elim,
          fun h'' => (h' h'').elim⟩)]
        omega

end DoubleMidset
