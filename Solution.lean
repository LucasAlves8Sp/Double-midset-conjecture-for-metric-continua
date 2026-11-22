module

public import DoubleMidset

public section

/-!
# Proved solution

Every theorem below has the same name and statement as its counterpart in `Challenge.lean`;
the proofs are in the library `DoubleMidset`. The definitions used in the statements are those
of `DoubleMidset/Defs.lean`, which `Challenge.lean` copies verbatim.
-/

open Set Topology Metric Filter

namespace DoubleMidset

universe u

namespace Paper

/-! ## Section 2. Preliminaries -/

section Prelim

variable {X : Type u} [MetricSpace X]

/-- **Lemma 2.2 (a)** (protected signs). -/
theorem lemma_2_2_a {a b a' b' t : X} (h : dist a a' + dist b b' < |sgnf a b t|) :
    (0 < sgnf a b t → 0 < sgnf a' b' t) ∧ (sgnf a b t < 0 → sgnf a' b' t < 0) := by
  exact _root_.DoubleMidset.lemma_2_2_a h

/-- **Lemma 2.2 (b)** (counting zeros). -/
theorem lemma_2_2_b {a b : X} {k : ℕ} (A : Fin k → Set X) (hA : ∀ i, IsPreconnected (A i))
    (hneg : ∀ i, ∃ y ∈ A i, sgnf a b y < 0) (hpos : ∀ i, ∃ y ∈ A i, 0 < sgnf a b y)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i ∩ midset a b) (A j ∩ midset a b)) :
    (k : ℕ∞) ≤ (midset a b).encard := by
  exact _root_.DoubleMidset.lemma_2_2_b A hA hneg hpos hdisj

/-- **Fact 2.3 (D1)**: in a dendrite, any two distinct points of a connected set are joined by an
arc inside it. -/
theorem fact_2_3_D1 (hX : IsDendrite X) {Y : Set X} (hY : IsPreconnected Y) {p q : X}
    (hp : p ∈ Y) (hq : q ∈ Y) (hpq : p ≠ q) : ∃ A, IsArcBetween A p q ∧ A ⊆ Y := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact exists_arc_in hD hY hp hq hpq

/-- **Fact 2.3 (D2)**: in a dendrite, the intersection of two connected sets is connected, and
arcs are unique. -/
theorem fact_2_3_D2 (hX : IsDendrite X) :
    (∀ Y Z : Set X, IsPreconnected Y → IsPreconnected Z → IsPreconnected (Y ∩ Z)) ∧
    ∀ (A B : Set X) (p q : X), IsArcBetween A p q → IsArcBetween B p q → A = B := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact ⟨fun Y Z hY hZ => IsPreconnected.inter_of_dendrite hD hY hZ,
    fun A B p q hA hB => arc_unique hD hA hB⟩

/-- **Fact 2.3 (D3)**: every subcontinuum of a dendrite is a dendrite. -/
theorem fact_2_3_D3 (hX : IsDendrite X) {K : Set X} (hKc : IsClosed K) (hK : IsPreconnected K)
    (hnt : K.Nontrivial) : IsDendrite K := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact isDendrite_of_subcontinuum hD hKc hK hnt

/-- **Fact 2.3 (D4)**: components of open subsets of a dendrite are open. -/
theorem fact_2_3_D4 (hX : IsDendrite X) {U : Set X} (hU : IsOpen U) (x : X) :
    IsOpen (connectedComponentIn U x) := by
  obtain ⟨_, _, _, _, -⟩ := hX.unpack
  exact hU.connectedComponentIn

/-- **Lemma 2.4 (interior points of arcs separate).** -/
theorem lemma_2_4 (hX : IsDendrite X) :
    (∀ {A : Set X} {p q y : X}, IsArcBetween A p q → y ∈ A → y ≠ p → y ≠ q →
      ∀ {y₁ y₂ : X}, y₁ ∈ A \ {y} → y₂ ∈ A \ {y} →
        connectedComponentIn (A \ {y}) y₁ ≠ connectedComponentIn (A \ {y}) y₂ →
        connectedComponentIn {y}ᶜ y₁ ≠ connectedComponentIn {y}ᶜ y₂) ∧
    (∀ {A : Set X} {p q y : X}, IsArcBetween A p q → y ∈ A → y ≠ p → y ≠ q → 2 ≤ order y) ∧
    (∀ {v p₁ p₂ p₃ : X} {A₁ A₂ A₃ : Set X}, IsArcBetween A₁ v p₁ → IsArcBetween A₂ v p₂ →
      IsArcBetween A₃ v p₃ → A₁ ∩ A₂ = {v} → A₁ ∩ A₃ = {v} → A₂ ∩ A₃ = {v} → 3 ≤ order v) := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact ⟨fun hA hy hyp hyq _ _ h₁ h₂ h => lemma_2_4_sides hD hA hy hyp hyq h₁ h₂ h,
    fun hA hy hyp hyq => two_le_order_of_mem_arc hD hA hy hyp hyq,
    fun h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ => three_le_order_of_triod hD h₁ h₂ h₃ h₁₂ h₁₃ h₂₃⟩

/-- **Fact 2.5**, the consequence used in the paper: a dendrite without branch points is an
arc. (R. L. Moore's characterization of the arc and the circle is not formalized in general.) -/
theorem fact_2_5 (hX : IsDendrite X) (hnb : ∀ p : X, ¬ IsBranchPoint p) :
    Nonempty (X ≃ₜ unitInterval) := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact nonempty_homeomorph_of_noBranch hD hnb

/-- **Lemma 2.7 (structure of finite trees).** The vertex set is finite and `T` is the union of
finitely many edges; each edge is an arc joining two vertices and containing no other vertex;
two edges meet at most in a common end; there are `|V| - 1` edges; the degree of a vertex is the
number of edges containing it. -/
theorem lemma_2_7 (hT : IsFiniteTree X) :
    (vertices X).Finite ∧ {ℓ : Set X | IsEdge ℓ}.Finite ∧ ⋃₀ {ℓ : Set X | IsEdge ℓ} = univ ∧
    (∀ ℓ : Set X, IsEdge ℓ → ∃ a b : X, a ≠ b ∧ IsArcBetween ℓ a b ∧ ℓ ∩ vertices X = {a, b}) ∧
    (∀ ℓ ℓ' : Set X, IsEdge ℓ → IsEdge ℓ' → ℓ ≠ ℓ' →
      ℓ ∩ ℓ' ⊆ vertices X ∧ (ℓ ∩ ℓ').Subsingleton) ∧
    {ℓ : Set X | IsEdge ℓ}.ncard + 1 = (vertices X).ncard ∧
    ∀ u ∈ vertices X, order u = {ℓ : Set X | IsEdge ℓ ∧ u ∈ ℓ}.encard := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  refine ⟨hT'.vertices_finite, hT'.edges_finite, sUnion_edges hT'.noSCC hT'.bfin hT'.bord,
    fun ℓ hℓ => ?_, fun ℓ ℓ' hℓ hℓ' hne => ⟨edge_inter_subset hT'.noSCC hT'.bfin hℓ hℓ' hne,
      edge_inter_subsingleton hT'.noSCC hT'.bfin hℓ hℓ' hne⟩,
    ncard_edges_add_one hT'.noSCC hT'.bfin hT'.bord,
    fun u hu => order_eq_encard_edges hT'.noSCC hT'.bfin hT'.bord hu⟩
  obtain ⟨a, b, hab, hseg, hV⟩ := edge_isArc hT'.noSCC hT'.bfin hℓ
  exact ⟨a, b, hab, hseg ▸ seg_isArcBetween hab, hV⟩

/-- **The paragraph after Lemma 2.7**: open edges are open; every edge point has order two;
`|Odd|` is even; in a branched tree every edge contains a branch point (necessarily one of its ends); and the tip
formula (3) `t = 2 + ∑_{branch points} (deg u - 2)`. -/
theorem tree_facts (hT : IsFiniteTree X) :
    (∀ W : Set X, IsOpenEdge W → IsOpen W) ∧ (∀ x : X, x ∉ vertices X → order x = 2) ∧
    Even (oddVertices X).ncard ∧
    ((∃ v : X, IsBranchPoint v) → ∀ ℓ : Set X, IsEdge ℓ → ∃ a ∈ ℓ, IsBranchPoint a) ∧
    {p : X | IsTip p}.ncard = 2 + ∑ᶠ u ∈ {p : X | IsBranchPoint p}, ((order u).toNat - 2) := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  refine ⟨fun W hW => ?_, fun x hx => order_eq_two_of_notMem hT' hx, even_ncard_oddVertices hT',
    fun ⟨v, hv⟩ ℓ hℓ => ?_, ?_⟩
  · obtain ⟨x, -, rfl⟩ := hW; exact isOpen_openEdge hT' x
  · obtain ⟨a, b, -, hseg, -, ha⟩ := edge_has_branch_end hT' ⟨v, hv⟩ hℓ
    exact ⟨a, hseg ▸ left_mem_seg a b, ha⟩
  · rw [tips_formula hT', finsum_mem_eq_finite_toFinset_sum (fun u : X => (order u).toNat - 2)
      (show {p : X | IsBranchPoint p}.Finite from hT'.bfin)]
    rfl

/-- **Lemma 2.8 (i)**: a real function has countably many local extremum values. -/
theorem lemma_2_8_i (g : ℝ → ℝ) : (g '' {s | IsLocalExtr g s}).Countable := by
  exact _root_.DoubleMidset.lemma_2_8_i g

/-- **Lemma 2.8 (ii)**: if `g` is continuous on `(α, β)` and constant on no nondegenerate
subinterval, its local extrema in `(α, β)` form a meagre set. -/
theorem lemma_2_8_ii {g : ℝ → ℝ} {α β : ℝ} (hg : ContinuousOn g (Ioo α β))
    (hnc : ∀ c d, c < d → Ioo c d ⊆ Ioo α β → ∃ y ∈ Ioo c d, ∃ z ∈ Ioo c d, g y ≠ g z) :
    IsMeagre {s | s ∈ Ioo α β ∧ IsLocalExtr g s} := by
  exact _root_.DoubleMidset.lemma_2_8_ii hg hnc

/-- **Lemma 2.8 (iii)**: near a point which is not a local extremum there are smaller and larger
values. -/
theorem lemma_2_8_iii {g : ℝ → ℝ} {s : ℝ} (hs : ¬ IsLocalExtr g s) {N : Set ℝ} (hN : N ∈ 𝓝 s) :
    ∃ s' ∈ N, ∃ s'' ∈ N, g s' < g s ∧ g s < g s'' := by
  exact _root_.DoubleMidset.lemma_2_8_iii hs hN

/-- **Lemma 2.9 (grid lemma).** -/
theorem lemma_2_9 {a b c d : ℝ} (hab : a < b) (hcd : c < d) {E F : Set ℝ} (hE : E ⊆ Ioo a b)
    (hF : F ⊆ Ioo c d) (hEm : IsMeagre E) (hFm : IsMeagre F) :
    IsConnected (((Ioo a b \ E) ×ˢ Ioo c d) ∪ (Ioo a b ×ˢ (Ioo c d \ F))) ∧
    Ioo a b ×ˢ Ioo c d ⊆ closure (((Ioo a b \ E) ×ˢ Ioo c d) ∪ (Ioo a b ×ˢ (Ioo c d \ F))) ∧
    ∀ g : ℝ × ℝ → ℝ, ContinuousOn g (Ioo a b ×ˢ Ioo c d) →
      (∀ z ∈ ((Ioo a b \ E) ×ˢ Ioo c d) ∪ (Ioo a b ×ˢ (Ioo c d \ F)), g z ≠ 0) →
      (∀ z ∈ Ioo a b ×ˢ Ioo c d, 0 ≤ g z) ∨ (∀ z ∈ Ioo a b ×ˢ Ioo c d, g z ≤ 0) := by
  exact _root_.DoubleMidset.lemma_2_9 hab hcd hE hF hEm hFm

end Prelim

/-! ## Section 3. Reduction to dendrites -/

section Reduction

variable {X : Type u} [MetricSpace X]

/-- **Proposition 3.1 (finite midsets force local connectedness).** -/
theorem prop_3_1 [CompactSpace X] [ConnectedSpace X] [Nontrivial X]
    (hfin : ∀ a b : X, a ≠ b → (midset a b).Finite) : LocallyConnectedSpace X := by
  exact _root_.DoubleMidset.prop_3_1 hfin

/-- **Proposition 3.2 (simple closed curves).** Under the upper bound, a simple closed curve in
`X` is all of `X`. -/
theorem prop_3_2 (h2 : MidsetsAtMostTwo X) {C : Set X} (hC : IsSimpleClosedCurve C) :
    C = univ := by
  exact _root_.DoubleMidset.prop_3_2 h2 hC

/-- **Corollary 3.4.** A nondegenerate compact connected metric space with the DMP is a simple
closed curve or a dendrite. -/
theorem cor_3_4 [CompactSpace X] [ConnectedSpace X] [Nontrivial X] (h : HasDMP X) :
    Nonempty (X ≃ₜ Circle) ∨ IsDendrite X := by
  exact _root_.DoubleMidset.cor_3_4 h

end Reduction

/-! ## Section 4. Branch points under the upper bound -/

section Branch

variable {X : Type u} [MetricSpace X]

/-- **Lemma 4.2 (arms).** -/
theorem lemma_4_2 (hX : IsDendrite X) {c : X} {k : ℕ} (hk : (k : ℕ∞) ≤ order c) {K : Set X}
    (hK : IsCompact K) (hcK : c ∉ K) {δ : ℝ} (hδ : 0 < δ) {f : X → ℝ} (hf : Continuous f)
    (hfin : (f ⁻¹' {0}).Finite) :
    ∃ p : Fin k → X, ∃ A : Fin k → Set X, (∀ i, IsArcBetween (A i) c (p i)) ∧
      (∀ i j, i ≠ j → connectedComponentIn {c}ᶜ (p i) ≠ connectedComponentIn {c}ᶜ (p j)) ∧
      (∀ i, A i \ {c} ⊆ connectedComponentIn {c}ᶜ (p i)) ∧
      (∀ i j, i ≠ j → A i ∩ A j = {c}) ∧
      (∀ i, A i ⊆ ball c δ) ∧ (∀ i, Disjoint (A i) K) ∧
      ∀ i, (∀ z ∈ A i \ {c}, 0 < f z) ∨ (∀ z ∈ A i \ {c}, f z < 0) := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  obtain ⟨p, h1, h2, h3, h4, h5, h6, h7⟩ := _root_.DoubleMidset.lemma_4_2 hD hk hK hcK hδ hf hfin
  exact ⟨p, fun i => seg c (p i), h1, h2, h3, h4, h5, h6, h7⟩

/-- **Lemma 4.3 (radial monotonicity).** Along an arc issuing from a branch point `c`, the
distance from `c` is nondecreasing. -/
theorem lemma_4_3 (hX : IsDendrite X) (h2 : MidsetsAtMostTwo X) {c : X} (hc : IsBranchPoint c)
    {α : ℝ → X} (hαc : Continuous α) (hαi : InjOn α (Icc 0 1)) (h0 : α 0 = c) :
    MonotoneOn (fun t => dist c (α t)) (Icc 0 1) := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact _root_.DoubleMidset.lemma_4_3 hD h2 hc ⟨hαc, hαi⟩ h0

/-- **Lemma 4.4 (order at most four).** -/
theorem lemma_4_4 (hX : IsDendrite X) (h2 : MidsetsAtMostTwo X) (c : X) : order c ≤ 4 := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact _root_.DoubleMidset.lemma_4_4 hD h2 c

/-- **Theorem 4.5 (few branch points).** -/
theorem theorem_4_5 (hX : IsDendrite X) (h2 : MidsetsAtMostTwo X) {v : X}
    (hv : IsBranchPoint v) :
    ∃ m : ℕ, order v = m ∧ {p : X | IsBranchPoint p}.Finite ∧
      (m - 2) * ({p : X | IsBranchPoint p}.ncard - 1) ≤ m ∧
      {p : X | IsBranchPoint p}.ncard ≤ 4 := by
  obtain ⟨_, _, _, _, hD⟩ := hX.unpack
  exact _root_.DoubleMidset.theorem_4_5 hD h2 hv

/-- **Corollary 4.6.** A dendrite with `|M(a, b)| ≤ 2` for all distinct `a, b` is a finite
tree. -/
theorem cor_4_6 (hX : IsDendrite X) (h2 : MidsetsAtMostTwo X) : IsFiniteTree X := by
  exact _root_.DoubleMidset.cor_4_6 hX h2

end Branch

/-! ## Section 5. Signs on a finite tree -/

section Signs

variable {T : Type u} [MetricSpace T]

/-- **Equation (5)**: for a strict pair, `N(a, b) ≡ N(b, a) (mod 2)`. -/
theorem eq_5_2 (hT : IsFiniteTree T) {a b : T} (h : IsStrictPair a b) :
    Odd (oddCount a b) ↔ Odd (oddCount b a) := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact ⟨odd_oddCount_swap hT' h, odd_oddCount_swap hT' h.symm⟩

/-- **Lemma 5.4 (parity).** -/
theorem lemma_5_4 (hT : IsFiniteTree T) {g : T → ℝ} (hg : Continuous g)
    (hfin : (g ⁻¹' {0}).Finite) (hV : ∀ u ∈ vertices T, g u ≠ 0) :
    {y | IsCrossing g y}.ncard % 2 = {u | u ∈ oddVertices T ∧ g u < 0}.ncard % 2 := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_5_4 hT' hg hfin hV

/-- **Corollary 5.5 (two types of strict pairs).** -/
theorem cor_5_5 (hT : IsFiniteTree T) (hDMP : HasDMP T) {a b : T} (h : IsStrictPair a b) :
    (∃ y₁ y₂, y₁ ≠ y₂ ∧ midset a b = {y₁, y₂} ∧ y₁ ∉ vertices T ∧ y₂ ∉ vertices T) ∧
    (∀ A, IsArcBetween A a b → Odd {y | y ∈ A ∧ IsCrossing (sgnf a b) y}.ncard) ∧
    (Even (oddCount a b) → ∀ y ∈ midset a b, IsCrossing (sgnf a b) y) ∧
    (Odd (oddCount a b) → ∃ y₁ y₂, midset a b = {y₁, y₂} ∧
      IsCrossing (sgnf a b) y₁ ∧ IsTouch (sgnf a b) y₂) := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.cor_5_5 hT' hDMP h

/-- **Lemma 5.6 (stability of a touch).** -/
theorem lemma_5_6 (hT : IsFiniteTree T) (hDMP : HasDMP T) {a b t : T} (h : IsStrictPair a b)
    (hodd : Odd (oddCount a b)) (ht : IsTouch (sgnf a b) t) :
    (a ∉ vertices T → IsLocalExtrOn (dist t) (connectedComponentIn (vertices T)ᶜ a) a) ∧
    (b ∉ vertices T → IsLocalExtrOn (dist t) (connectedComponentIn (vertices T)ᶜ b) b) := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_5_6 hT' hDMP h hodd ht

/-! ## Section 6. Spherical arcs and odd boxes -/

/-- **Lemma 6.2 (spherical arcs).** -/
theorem lemma_6_2 (hT : IsFiniteTree T) (h2 : MidsetsAtMostTwo T) {I : Set T} {x : T} {r : ℝ}
    (hI : IsSphericalArc I x r) :
    (∀ y, y ∉ I → y ≠ x → InjOn (dist y) I) ∧
    ((∀ x' r', I ⊆ sphere x' r' → x' = x) ∧ ∀ J ⊆ I, IsArc J → IsSphericalArc J x r) ∧
    ((∀ p q, IsArcBetween I p q → ∀ z ∈ I, z ≠ p → z ≠ q → z ∉ vertices T) ∧
      ∃ ℓ, IsEdge ℓ ∧ I ⊆ ℓ) ∧
    {x : T | ∃ I r, IsSphericalArc I x r}.Countable := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_6_2 hT' h2 hI

/-- **Lemma 6.3 (off-sphere parity).** -/
theorem lemma_6_3 (hT : IsFiniteTree T) (hDMP : HasDMP T) {I : Set T} {x : T} {r : ℝ}
    (hI : IsSphericalArc I x r) {e₁ e₂ : T} (hIe : IsArcBetween I e₁ e₂) {p : T} (hp : p ∈ I)
    (hp1 : p ≠ e₁) (hp2 : p ≠ e₂) {b : T} (hb : dist x b ≠ r) (h : IsStrictPair p b) :
    Even (oddCount p b) := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_6_3 hT' hDMP hI hIe hp hp1 hp2 hb h

/-- **Proposition 6.5 (odd boxes lie on a sphere).** -/
theorem prop_6_5 (hT : IsFiniteTree T) (hDMP : HasDMP T) {U V : Set T} (hUV : IsOddBox U V) :
    ∃ c : T, ∃ r : ℝ, 0 < r ∧ U ∪ V ⊆ sphere c r ∧ ∀ c' r', U ∪ V ⊆ sphere c' r' → c' = c := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.prop_6_5 hT' hDMP hUV

/-- **Lemma 6.6 (continuous selection of the touch).** -/
theorem lemma_6_6 (hT : IsFiniteTree T) (hDMP : HasDMP T) {U V : Set T} (hUV : IsOddBox U V) :
    ∃ U₁ V₁ : Set T, IsBox U₁ V₁ ∧ U₁ ⊆ U ∧ V₁ ⊆ V ∧
      ∃ J : Set T, IsOpenArc J ∧ (∃ W, IsOpenEdge W ∧ J ⊆ W) ∧
      ∃ w : T × T → T, ContinuousOn w (U₁ ×ˢ V₁) ∧
        ∀ a ∈ U₁, ∀ b ∈ V₁, w (a, b) ∈ J ∧ IsTouch (sgnf a b) (w (a, b)) := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_6_6 hT' hDMP hUV

/-- **Corollary 6.7.** -/
theorem cor_6_7 (hT : IsFiniteTree T) (hDMP : HasDMP T) {a b : T} (h : IsStrictPair a b)
    (ha : a ∉ vertices T) (hb : b ∉ vertices T) (hodd : Odd (oddCount a b)) :
    ∃ c : T, (∃ r : ℝ, 0 < r ∧ ∃ U V : Set T, IsOpenArc U ∧ IsOpenArc V ∧ a ∈ U ∧ b ∈ V ∧
        (∃ W, IsOpenEdge W ∧ U ⊆ W) ∧ (∃ W, IsOpenEdge W ∧ V ⊆ W) ∧ U ∪ V ⊆ sphere c r ∧
        (∀ a' ∈ U, ∀ b' ∈ V, c ∈ midset a' b')) ∧
      c ∉ vertices T ∧
      ∀ c' : T, ∀ r' : ℝ, ∀ U' V' : Set T, IsOpenArc U' → IsOpenArc V' → a ∈ U' → b ∈ V' →
        U' ∪ V' ⊆ sphere c' r' → c' = c := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.cor_6_7 hT' hDMP h ha hb hodd

/-! ## Section 7. Where the center of a spherical arc can lie -/

/-- **Lemma 7.1 (tips are not centers).** -/
theorem lemma_7_1 (hT : IsFiniteTree T) (hDMP : HasDMP T) {x : T} (hx : IsTip x) {I : Set T}
    {r : ℝ} : ¬ IsSphericalArc I x r := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_7_1 hT' hDMP hx

/-- **Lemma 7.2 (the center is a crossing).** -/
theorem lemma_7_2 (hT : IsFiniteTree T) (hDMP : HasDMP T) {x : T} (hx : x ∉ vertices T) {r : ℝ}
    (hr : 0 < r) {K : Set T} (hKdef : ∃ z ∈ sphere x r, K = connectedComponentIn (sphere x r) z)
    (hKnt : K.Nontrivial) :
    IsArc K ∧ (∃ ℓ, IsEdge ℓ ∧ K ⊆ ℓ) ∧
    ∀ p ∈ K, ∀ q ∈ K, p ≠ q → IsStrictPair p q ∧ Even (oddCount p q) ∧
      ∃ y, midset p q = {x, y} ∧ (∀ A, IsArcBetween A p q → y ∈ A ∧ y ≠ p ∧ y ≠ q) ∧
        IsCrossing (sgnf p q) x ∧ IsCrossing (sgnf p q) y := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_7_2 hT' hDMP hx hr hKdef hKnt

/-- **Lemma 7.3 (matching beyond the center).** -/
theorem lemma_7_3 (hT : IsFiniteTree T) (hDMP : HasDMP T) {ℓ : Set T} (hℓ : IsEdge ℓ)
    {k : ℝ → T} (hkc : Continuous k) (hki : InjOn k (Icc 0 1)) (hkℓ : k '' Icc 0 1 = ℓ)
    (he : IsTip (k 1)) {σ σ' ξ : ℝ} (h0 : 0 < σ) (h1 : σ < σ') (h2 : σ' < ξ) (h3 : ξ < 1)
    {r : ℝ} (hr : 0 < r) (hI : k '' Icc σ σ' ⊆ sphere (k ξ) r) :
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
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_7_3 hT' hDMP hℓ hkc hki hkℓ he h0 h1 h2 h3 hr hI

/-- **Lemma 7.4 (no center in the arc's own edge).** -/
theorem lemma_7_4 (hT : IsFiniteTree T) (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v)
    {I : Set T} {x : T} {r : ℝ} (hI : IsSphericalArc I x r) {W : Set T} (hW : IsOpenEdge W)
    (hIW : I ⊆ W) : x ∉ W := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_7_4 hT' hDMP hbr hI hW hIW

/-! ## Section 8. Distances to the tips -/

/-- **Lemma 8.1 (no flip at a tip).** -/
theorem lemma_8_1 (hT : IsFiniteTree T) (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v)
    {e : T} (he : IsTip e) {a b : T} (hab : a ≠ b) (ha : a ∉ vertices T) (hb : b ∉ vertices T)
    (hpos : (∃ W, IsOpenEdge W ∧ a ∈ W ∧ b ∈ W) ∨
      ∃ v ∈ vertices T, v ∈ closure (connectedComponentIn (vertices T)ᶜ a) ∧
        v ∈ closure (connectedComponentIn (vertices T)ᶜ b))
    (htie : dist e a = dist e b) (hsign : ∀ u ∈ vertices T, u ≠ e → sgnf a b u ≠ 0) :
    IsLocalExtrOn (dist e) (connectedComponentIn (vertices T)ᶜ a) a := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_8_1 hT' hDMP hbr he hab ha hb hpos htie hsign

/-- **Proposition 8.2 (a)**: the distance from a tip is injective (equivalently, strictly
monotone) on every edge. -/
theorem prop_8_2_a (hT : IsFiniteTree T) (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v)
    {e : T} (he : IsTip e) {ℓ : Set T} (hℓ : IsEdge ℓ) : InjOn (dist e) ℓ := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.prop_8_2_a hT' hDMP hbr he hℓ

/-- **Proposition 8.2 (b).** -/
theorem prop_8_2_b (hT : IsFiniteTree T) (hDMP : HasDMP T) {e : T} (he : IsTip e) {v : T}
    (hv : IsBranchPoint v) {a b : T} (ha : a ∉ vertices T) (hb : b ∉ vertices T)
    (hab : connectedComponentIn (vertices T)ᶜ a ≠ connectedComponentIn (vertices T)ᶜ b)
    (hva : v ∈ closure (connectedComponentIn (vertices T)ᶜ a))
    (hvb : v ∈ closure (connectedComponentIn (vertices T)ᶜ b))
    (htie : dist e a = dist e b) : dist v a = dist v b := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.prop_8_2_b hT' hDMP ⟨v, hv⟩ he hv ha hb hab hva hvb htie

/-! ## Section 9. Counting tips -/

/-- **Lemma 9.2 (distinct tips use disjoint pairs).** -/
theorem lemma_9_2 (hT : IsFiniteTree T) (hDMP : HasDMP T) {v : T} (hv : IsBranchPoint v)
    {ℓ ℓ' : Set T} (hℓ : IsEdge ℓ) (hℓ' : IsEdge ℓ') (hvℓ : v ∈ ℓ) (hvℓ' : v ∈ ℓ')
    (hne : ℓ ≠ ℓ') {e e' : T} (he : IsTip e) (he' : IsTip e') (hee' : e ≠ e') :
    ¬ (UsesPair e v ℓ ℓ' ∧ UsesPair e' v ℓ ℓ') := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.lemma_9_2 hT' hDMP ⟨v, hv⟩ hv hℓ hℓ' hvℓ hvℓ' hne he he' hee'

/-- **Proposition 9.3 (reduction to the triod).** -/
theorem prop_9_3 (hT : IsFiniteTree T) (hDMP : HasDMP T) (hbr : ∃ v : T, IsBranchPoint v) :
    IsSimpleTriod (univ : Set T) := by
  obtain ⟨_, _, _, _, hT'⟩ := hT.unpack
  exact _root_.DoubleMidset.prop_9_3 hT' hDMP hbr

end Signs

/-! ## Sections 10–12. The triod, the arc, and the main theorems -/

section MainResults

variable {X : Type u} [MetricSpace X]

/-- **Theorem 10.1.** No compatible metric on a simple triod has the DMP. -/
theorem theorem_10_1 (h : IsSimpleTriod (univ : Set X)) : ¬ HasDMP X := by
  exact _root_.DoubleMidset.theorem_10_1 h

/-- **Theorem 11.1.** No compatible metric on an arc has the DMP. -/
theorem theorem_11_1 (h : IsArc (univ : Set X)) : ¬ HasDMP X := by
  exact _root_.DoubleMidset.theorem_11_1 h

/-- **Theorem A.** A nondegenerate compact connected metric space with `|M(a, b)| = 2` for all
distinct `a, b` is homeomorphic to `S¹`. -/
theorem theorem_A [CompactSpace X] [ConnectedSpace X] [Nontrivial X] (h : HasDMP X) :
    Nonempty (X ≃ₜ Circle) := by
  exact _root_.DoubleMidset.theorem_A h

/-- **Theorem A, converse.** The unit circle with the Euclidean metric has the DMP. -/
theorem circle_hasDMP : HasDMP Circle := by
  exact _root_.DoubleMidset.circle_hasDMP

/-- **Theorem A, characterization.** A nondegenerate metrizable continuum admits a compatible
metric with the DMP if and only if it is a simple closed curve. -/
theorem theorem_A_iff {Y : Type u} [t : TopologicalSpace Y] (hY : IsContinuum Y) :
    (∃ m : MetricSpace Y, m.toUniformSpace.toTopologicalSpace = t ∧ @HasDMP Y m) ↔
      Nonempty (Y ≃ₜ Circle) := by
  exact _root_.DoubleMidset.theorem_A_iff hY

/-- **Theorem B.** No finite tree admits a compatible metric with the DMP. In particular,
neither an arc nor a simple triod does. -/
theorem theorem_B :
    (IsFiniteTree X → ¬ HasDMP X) ∧ (IsArc (univ : Set X) → ¬ HasDMP X) ∧
      (IsSimpleTriod (univ : Set X) → ¬ HasDMP X) := by
  exact _root_.DoubleMidset.theorem_B_full

/-- **Theorem C.** A dendrite with `|M(a, b)| ≤ 2` for all distinct `a, b`: every point has
order at most four; for a branch point of order `m`, `(m - 2)(|B| - 1) ≤ m`; there are at most
four branch points; and it is a finite tree. -/
theorem theorem_C (hX : IsDendrite X) (h2 : MidsetsAtMostTwo X) :
    (∀ p : X, order p ≤ 4) ∧
    (∀ v : X, IsBranchPoint v → ∃ m : ℕ, order v = m ∧
      (m - 2) * ({p : X | IsBranchPoint p}.ncard - 1) ≤ m) ∧
    {p : X | IsBranchPoint p}.Finite ∧ {p : X | IsBranchPoint p}.ncard ≤ 4 ∧
    IsFiniteTree X := by
  exact _root_.DoubleMidset.theorem_C hX h2

end MainResults

end Paper

end DoubleMidset
