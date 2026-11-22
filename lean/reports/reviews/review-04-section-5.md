# Review 04 — paragraph after Lemma 2.7 and Section 5

Reviewer: independent, no prior context. No `.lean` file was modified.

Files reviewed line by line: `DoubleMidset/Edges.lean`, `DoubleMidset/ParamParity.lean`,
`DoubleMidset/Crossing.lean`, `DoubleMidset/Parity.lean`, `DoubleMidset/Types.lean`, plus the
relevant parts of `DoubleMidset/Defs.lean` (lines 83–152). Paper: paragraph after Lemma 2.7
(tex l. 255–258) and Section 5 (tex l. 473–586); Lemma 7.1 (tex l. 700–726) for the `T'` question.

## Mechanical checks

* **Build.** `/home/claude/dmp/b.sh DoubleMidset` prints `Build completed successfully (2180 jobs)`.
  The whole project has 149 warnings. 60 are in the five reviewed files, and all are
  deprecations (`push_neg`, `if_pos`/`if_neg`, `Set.mem_setOf_eq`, `ENat.coe_toNat`) or
  "automatically included section variable(s) unused" linter warnings. None affects correctness.
* **Forbidden constructs.** `grep` over all of `DoubleMidset/` and `DoubleMidset.lean` for
  `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `@[extern]`
  finds nothing.
* **Axioms.** `#print axioms` (scratch file `/tmp/ax04.lean`, `import DoubleMidset`) gives
  `[propext, Classical.choice, Quot.sound]` for every one of `lemma_5_4`, `cor_5_5`, `lemma_5_6`,
  `tips_formula`, `even_ncard_oddVertices`, `edge_has_branch_end`, `sum_degree'`,
  `order_eq_two_of_notMem`, `param_parity`, `isCrossing_or_isTouch`,
  `not_isCrossing_and_isTouch`, `IsEdgeParam.isOpen_image_Ioo` and `odd_crossings_on_arc`.

## Definition 5.3 (`IsCrossing` / `IsTouch`, Defs.lean l. 123–139): verdict FAITHFUL

The Lean definition reads: `y ∉ vertices`, `g y = 0`, and there is `J` with `IsOpenArc J` (open in
`T` and `≃ₜ (0,1)`), `y ∈ J`, `J ⊆ W` for an open edge `W`, `J ∩ g⁻¹(0) = {y}`, and for all
`z₁, z₂ ∈ J \ {y}` lying in different components of `J \ {y}`, `g z₁ * g z₂ < 0` (crossing) or
`> 0` (touch).

1. **The sides.** `J ≃ₜ (0,1)` and `y ∈ J`, so `J \ {y}` has exactly two components.
   `connectedComponentIn (J \ {y})` uses the subspace topology, which is the topology of
   `J \ {y} ≃ₜ (0,1) \ {c}`. So "different components of `J \ {y}`" means exactly "on the two
   different sides of `y`". This is never vacuous: it cannot happen that both predicates hold
   because there is only one side, and `not_isCrossing_and_isTouch` confirms this.
2. **"Opposite/same signs on the two sides" vs. the product condition over pairs.** The paper
   defines crossings and touches only for continuous `g` with finitely many zeros. In that case
   `g ≠ 0` on each (connected) side because `J ∩ g⁻¹(0) = {y}`, so `g` has a constant sign on each
   side by the IVT. Then "opposite signs" ⇔ `∀ z₁, z₂` on different sides, `g z₁ g z₂ < 0`, and
   likewise for touches. For discontinuous `g` the Lean predicate is still meaningful but
   stronger. That case is outside the paper's definition and is never used.
3. **The existential over `J`.** The paper says "take a small open arc `J`", which tacitly
   claims that the answer does not depend on `J`. The Lean development proves exactly this:
   * `isCrossing_or_isTouch` (Crossing.lean l. 289): for continuous `g` with finitely many zeros
     and an edge-point zero, a suitable `J` exists and the point is one of the two types;
   * `not_isCrossing_and_isTouch` (l. 317), for arbitrary `g`: no `y` has one `J` that witnesses
     a crossing and another `J'` that witnesses a touch.

   So "∃ J that witnesses a crossing" ⇔ "every admissible `J` witnesses a crossing": if `J'` is
   admissible, it witnesses one of the two types by item 2, and a touch would contradict the
   lemma. The existential is therefore harmless and is equivalent to the paper's reading.
4. **`IsOpen J` and "J in its open edge".** The paper's open arc is a subset homeomorphic to an
   open interval inside the open edge. By 1-dimensional invariance of domain such a set is open
   in the open edge, hence open in `T`, so requiring `IsOpen` loses nothing. `J ⊆ W` with
   `y ∈ J` forces `W` to be the open edge of `y`.
5. Crossings are also characterised along *any* arc through `y` (`IsCrossing.along`,
   `IsTouch.along`), via Lemma 2.4 (`sides_separate`). This is the paper's remark in the proof
   of Cor. 5.5 that "`[a,b]` coincides near `y` with the open edge of `y`".

No BLOCKER or MAJOR issue with the definitions.

## 1. `DoubleMidset/Edges.lean`

* l. 29–32 `TreeHyp`: `noSCC`, `bfin : (branchSet T).Finite`, `bord`. `branchSet T` is
  `{p | IsBranchPoint p}` (TreeStructure.lean l. 36), the same set as in `IsFiniteTree`. With the
  instances `[MetricSpace] [CompactSpace] [ConnectedSpace] [LocallyConnectedSpace] [Nontrivial]`,
  this is exactly `IsFiniteTree` (Defs l. 103) with `MetrizableSpace` replaced by a chosen
  compatible metric, i.e. exactly "finite tree with compatible metric" (Convention 5.1). **OK.**
  - MINOR: no lemma connects `IsFiniteTree T` (the Prop in Defs) to `TreeHyp T` plus the
    instances. One will be needed when the main theorem feeds the output of Section 4
    (Cor. 4.5) into Sections 5 and later. It is a one-liner but should exist so the chain is
    visibly closed.
* l. 36–40 `IsEdgeParam`: `IsArcParam γ` (continuous on all of `ℝ`, injective on `[0,1]`), with
  vertex ends and no vertex in `(0,1)`. Requiring continuity on all of `ℝ` is harmless because
  `exists_edgeParam` produces such a `γ`. **OK.**
* l. 55 `order_eq_two_of_notMem`: "edge points have order two". **Faithful.**
* l. 64 `exists_edgeParam`: every edge point is `γ s` with `s ∈ (0,1)`, `γ(0,1)` its open edge,
  `γ[0,1]` the closure. **OK.**
* l. 84 `IsEdgeParam.image_Ioo_eq`, l. 127 `IsEdgeParam.isEdge`: the open arc of any edge
  parametrisation is the open edge of each of its points, and its closed arc is an edge. **OK.**
* l. 156 `IsEdgeParam.isOpen_image_Ioo`: for `0 ≤ c`, `d ≤ 1`, `γ(c,d)` is open in `T`. Together
  with `IsEdgeParam.isOpenArc_image` (Crossing.lean l. 57), this is the paper's "a small open arc
  around it in its open edge is a neighborhood of it in `T`". **OK.**
* l. 166 `degree := (order x).toNat`: junk value only for infinite order. Vertices have finite
  order by `bord`/`order_eq_degree`. **OK.**
* l. 203 `sum_degree` (Σ deg = 2|E|) and l. 230 `sum_degree'` (= 2(|V| − 1), truncated
  subtraction harmless since |V| = |E| + 1). **Faithful.**
* l. 236 `even_ncard_oddVertices`: `Even (oddVertices T).ncard`. `ncard` is meaningful because
  `oddVertices ⊆ vertices`, which is finite. **Faithful.**
* l. 252 `edge_has_branch_end`: branched ⇒ every edge `ℓ` is `seg a b` with
  `ℓ ∩ V = {a, b}`, `a ≠ b`, `a` a branch point. **Faithful.**
  - MINOR: the statement uses the internal choice-based `seg` (Dendrite.lean l. 52). The
    content the paper needs, `ℓ ∩ V = {a,b}` with `a` a branch point, is already there. Stating
    `IsArcBetween ℓ a b` instead of `seg a b = ℓ` would keep the statement in the vocabulary of
    `Defs.lean`.
  - MINOR: l. 260–261 (`h1`, `e`) are dead `have`s. The two branches l. 258–275 and
    l. 276–290 are near-duplicates.
* l. 308 `tips_formula`: `#tips = 2 + Σ_{u ∈ B} (deg u − 2)`. The natural subtraction is safe
  because the proof shows `deg u ≥ 3` (l. 333). It holds for the arc too (empty sum), as in the
  paper. **Faithful.**
  - MINOR: l. 350 `hne` is unused.
* l. 138 `IsArcParam.image_Ioo_eq_diff`: linter warning about unused section instances. Style
  only.

## 2. `DoubleMidset/ParamParity.lean`

* l. 22–27 `IsParamCrossing` / `IsParamTouch`: a zero with a sign change (no sign change) on
  `(s−ε, s)` × `(s, s+ε)`. **OK.**
* l. 30 `const_sign`, l. 47 `mul_pos_iff_same`: auxiliary, correct.
* l. 59 `param_parity`: `h` continuous on `[α,β]`, finitely many zeros there, none at the ends ⇒
  `#{sign changes in (α,β)} + [h α < 0] + [h β < 0] ≡ 0 (mod 2)`. This is exactly the
  edge-by-edge step of the proof of Lemma 5.4. **Faithful.**
  - MINOR: the leading `∀ n, … ncard = n →` is an artefact of strong induction exposed in the
    statement. A wrapper without `n` would be cleaner. Harmless.
* The proof (induction on the largest zero `z` and a point `w` before it) is sound and
  kernel-checked.

## 3. `DoubleMidset/Crossing.lean`

* l. 27 `nonempty_homeomorph_Ioo`: auxiliary, fine.
* l. 57 `IsEdgeParam.isOpenArc_image`: `γ(a,b)` is an open arc. **OK.**
* l. 76 `IsCrossing.along` / l. 108 `IsTouch.along`: along any arc parametrisation `k` with
  `k s₀ = y`, `s₀ ∈ (0,1)`, the sign changes (is kept) at `s₀`. The proof correctly uses only
  that `J` is open and that `k t`, `k t'` lie in different components of `T \ {y}`
  (`sides_separate`), hence of `J \ {y}`. **OK.**
  - MINOR: the two proofs are verbatim duplicates (l. 75–105 vs. l. 107–137), and so are
    `isCrossing_of_param` / `isTouch_of_param` (l. 159–221 vs. l. 223–285). They could be
    factored through a single lemma parametrised by the sign relation. Style only.
* l. 141 `exists_isolated`: zeros of a function with finitely many zeros are isolated along an
  arc. **OK.**
* l. 160 `isCrossing_of_param`, l. 224 `isTouch_of_param`: a parameter sign change (or no sign
  change) at an interior parameter of an edge parametrisation gives a crossing (touch), with
  `J = γ(s−ε, s+ε)`. They need finitely many zeros but not continuity. **OK.**
* l. 289 `isCrossing_or_isTouch`: continuous, finitely many zeros, edge-point zero ⇒ crossing
  ∨ touch. **OK.**
* l. 317 `not_isCrossing_and_isTouch`: holds for *arbitrary* `g`. As argued above, this lemma
  is what makes the `∃ J` in the definition faithful. **OK.**

## 4. `DoubleMidset/Parity.lean`

* l. 27–63: auxiliary edge lemmas (`exists_param_of_isEdge`, `inter_vertices`, `mem_Ioo`,
  `isEdge_closure_cc`, `finite_paramZeros`). These are fine.
  - MINOR: several of them carry `hT` or instances they do not use (linter warnings at l. 34,
    48, 55, 60).
* l. 66 `lemma_5_4`: hypotheses `TreeHyp T` plus instances, `g` continuous, `g⁻¹(0)` finite, no
  vertex is a zero. Conclusion
  `{y | IsCrossing g y}.ncard % 2 = {u | u ∈ oddVertices T ∧ g u < 0}.ncard % 2`. The crossing
  set is shown to be finite in the proof (`hcross`, as a finite biUnion), so `ncard` is not a
  junk value. **Faithful** to Lemma 5.4 with `T' = T`, and it has no hypotheses beyond the
  paper's (no DMP).
  - The proof follows the paper's argument: chosen edge parametrisations, crossings counted edge
    by edge (disjoint since open edges are disjoint, `edge_inter_subset`), `param_parity` per
    edge, regrouping of the end terms by `degree_eq_card`, and `sum_mod_two`.
* **On applying it to the cut tree `T'` of Lemma 7.1 (MINOR / observation, not a defect of this
  file).** The lemma is stated for an arbitrary type, so it could be applied to
  `T' = {z // z ∈ T \ (x', x]}`. But that would require
  - building `CompactSpace`, `ConnectedSpace`, `LocallyConnectedSpace` (non-trivial for a closed
    subset), `Nontrivial` and `TreeHyp` on the subtype;
  - proving `V(T') = (V \ {x}) ∪ {x'}` with orders preserved (transfer of `order` through the
    subtype);
  - relating `IsCrossing` on `T'` to `T`.

  That is a lot of work. A much cheaper route keeps the current statement and avoids `T'`
  entirely: apply `lemma_5_4` on `T` itself to `g' := f_{p,q}` on `T'` and `g' := f_{p,q}(x')`
  on `[x', x]`. This is continuous by the pasting lemma for the closed cover `T' ∪ [x',x]`, and
  `T' ∩ [x',x] = {x'}`. Its only zero is `y`, which is a crossing of `g'` in `T`. Every vertex has
  the same sign as in the paper's `T'` computation, with `g'(x) = f(x') > 0` standing in for the
  new tip `x'`. The lemma then gives directly that `#{u ∈ Odd \ {x} : f_{p,q}(u) < 0}` is odd,
  which is what Lemma 7.1 uses. So **no combinatorial or subtype version of Lemma 5.4 is
  needed**. The formaliser of Section 7 should be pointed to this trick (or should otherwise
  budget for the subtype route).

## 5. `DoubleMidset/Types.lean`

* l. 24–42: `sgnf_preimage_zero`, `midset_finite_of_dmp`, `IsStrictPair.notMem_vertices`,
  `sgnf_left_neg`, `sgnf_right_pos`. Correct auxiliary lemmas.
* l. 46 `crossings_on_arc`: crossings of `f_{a,b}` on `k[0,1]` = images of parameter crossings.
  `HasDMP` is used only for finiteness of the midset. **OK.**
* l. 77 `odd_crossings_on_arc`: every arc `A` from `a` to `b` contains an odd number of
  crossings. **OK.**
* l. 93 `cor_5_5`: four conjuncts:
  1. `M(a,b) = {y₁,y₂}`, `y₁ ≠ y₂`, both edge points;
  2. `∀ A, IsArcBetween A a b → Odd #(crossings in A)`;
  3. `N` even ⇒ every point of `M` is a crossing;
  4. `N` odd ⇒ `M = {y₁,y₂}` with `y₁` a crossing and `y₂` a touch.

  On the rendering of "`[a,b]` contains an odd number of crossings" as "every arc `A` from `a`
  to `b`": in a dendrite the arc is unique, and an arc exists (`exists_arc`, which is used at
  l. 110 for `hpos`). So the ∀-form is equivalent to the paper's statement and is not vacuous.
  "Hence at least one" follows from `Odd`. In (4), `y₁ ≠ y₂` is implied (a point is not both
  types, and also `encard M = 2`). **Faithful.**
* l. 150 `signs_of_sigma`: auxiliary.
* l. 162 `touch_stable_core`: the content of the paper's proof. It gives `σ = ±1` and `ε` with
  `σ(h_t(a') − h_t(a)) ≥ 0` for `d(a,a') < ε`, and `σ(h_t(b) − h_t(b')) ≥ 0` for `d(b,b') < ε`.
  It uses only `MidsetsAtMostTwo` (derived from DMP at l. 167). The three pieces `[t_−,t]`,
  `[t,t_+]`, `[y_−,y_+]` and Lemma 2.2(b) (`three_le_encard_of_sets` + `false_of_three`) match
  the paper. **OK.**
* l. 315 `lemma_5_6`: hypotheses DMP, strict pair, `N(a,b)` odd, `IsTouch (sgnf a b) t` (which
  forces `t ∈ M(a,b)`, so `t` is "the touch"). Conclusion for `a` and for `b`:
  `x ∉ V → IsLocalExtrOn (dist t) (connectedComponentIn Vᶜ x) x`. Here `dist t = h_t`, and
  `connectedComponentIn Vᶜ a` is the open edge of `a`. `IsLocalExtrOn` (non-strict, w.r.t.
  `𝓝[s] a`) is the paper's "local extremum restricted to the open edge". **Faithful.**
  - Observation: the proof actually establishes the stronger `IsLocalExtr (dist t) a` on all of
    `T`, and does not use `a ∉ V` (`fun _ =>` at l. 332). A stronger companion statement would
    be free.
  - Observation: the min/max coupling (`a` is a local min iff `b` is a local max, signs `σ` and
    `−σ`) is lost in `lemma_5_6`. It is kept in `touch_stable_core`. The paper's statement does
    not include it either, so this is fine. If Section 6 (Prop. 6.5 / Lemma 6.6) needs the
    coupling, it should use `touch_stable_core`.
  - The hypothesis `Odd (oddCount a b)` is derivable from the existence of a touch (otherwise
    Cor. 5.5(3) would make `t` a crossing). It is the paper's hypothesis, so keeping it is
    correct.
  - MINOR: l. 321 `htM` is unused.
* Hypothesis strength: `HasDMP` appears in `crossings_on_arc`, `odd_crossings_on_arc`,
  `cor_5_5`, `touch_stable_core` and `lemma_5_6`, and this is Convention 5.1. No statement has a
  hypothesis the paper lacks.

## Summary table

| Paper result | Lean declaration | Faithful? |
|---|---|---|
| Convention 5.1 (finite tree with compatible metric) | instances + `TreeHyp` (Edges l. 29), `HasDMP` | Yes (bridge lemma from `IsFiniteTree` missing, MINOR) |
| §2 after L. 2.7: edge points have order two | `order_eq_two_of_notMem` (Edges l. 55) | Yes |
| §2: open edges = components of `T \ V`; small open arc is a neighbourhood | `exists_edgeParam`, `IsEdgeParam.image_Ioo_eq`, `IsEdgeParam.isEdge`, `IsEdgeParam.isOpen_image_Ioo`, `IsEdgeParam.isOpenArc_image` | Yes |
| §2: handshake, Σ deg = 2(\|V\|−1) | `sum_degree`, `sum_degree'` (Edges l. 203, 230) | Yes |
| §2: \|Odd\| even | `even_ncard_oddVertices` (Edges l. 236) | Yes |
| §2: branched ⇒ each edge has a branch-point end | `edge_has_branch_end` (Edges l. 252) | Yes (uses internal `seg`, MINOR) |
| (2.1) tip formula | `tips_formula` (Edges l. 308) | Yes |
| Def. 5.2 strict pair, `N(a,b)` | `IsStrictPair`, `oddCount` (Defs l. 149, 152) | Yes |
| Def. 5.3 crossing / touch | `IsCrossing`, `IsTouch` (Defs l. 126, 135) + `isCrossing_or_isTouch`, `not_isCrossing_and_isTouch` | Yes (∃ J harmless, shown by the two lemmas) |
| proof of L. 5.4, edge step | `param_parity` (ParamParity l. 59) | Yes |
| Lemma 5.4 (parity) | `lemma_5_4` (Parity l. 66) | Yes, for `T' = T`. Usable for Lemma 7.1 via the pasting trick, no subtype needed |
| Corollary 5.5 | `cor_5_5` (Types l. 93), `odd_crossings_on_arc` | Yes ("every arc `A`" ⇔ "`[a,b]`") |
| Lemma 5.6 | `lemma_5_6` (Types l. 315), core `touch_stable_core` (l. 162) | Yes (proof gives the stronger unrestricted local extremum) |

## Findings by severity

* **BLOCKER:** none.
* **MAJOR:** none.
* **MINOR:**
  - Edges.lean: no `IsFiniteTree → TreeHyp` bridge lemma.
  - Edges l. 253: `seg` in a public statement.
  - Dead `have`s: Edges l. 260–261 and l. 350, Types l. 321.
  - Duplicated proofs: Edges l. 258–290; Crossing l. 75–137 and l. 159–285.
  - `n`-parameter exposed in `param_parity`.
  - Unused section-variable linter warnings: Edges l. 138; Crossing l. 76, 108, 141; Parity
    l. 34, 48, 55, 60.
  - Deprecation warnings throughout.
  - Lemma 7.1's `T'`: use the pasting-lemma modification of `f_{p,q}` on `T` rather than a
    subtype tree.

## Overall verdict

**ACCEPT.** All five files compile, use no `sorry` and no forbidden constructs, and the target
theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. Every statement matches
the paper: the paragraph after Lemma 2.7 (order two, open edges, |Odd| even, branch-point ends,
handshake, tip formula), Definitions 5.2/5.3, Lemma 5.4, Corollary 5.5 and Lemma 5.6. The
revised `IsCrossing`/`IsTouch` match Definition 5.3: the two components of `J \ {y}` are exactly
the two sides, the product condition is equivalent to opposite/same signs for continuous `g`,
and the `∃ J` is shown to be independent of `J` by `isCrossing_or_isTouch` together with
`not_isCrossing_and_isTouch`. The only forward-looking point is Lemma 7.1. The current
`lemma_5_4` suffices there if it is applied on `T` to `f_{p,q}` flattened on the cut-off
terminal segment, so no combinatorial or subtype version is needed.
