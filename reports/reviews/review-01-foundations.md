# Review 01: Foundations (Defs, Arc, Circle, Dendrite, Order, NoBranch, Classical)

Reviewer: independent; no .lean file was modified. Paper read: Sections 1-2 (the whole of
Section 2), Sections 3-4, and Definitions 5.2, 5.3, 6.1, 6.4 with the material around them.

## 0. Global checks

* **Compilation.** Every file in scope was checked on its own with
  `lake env lean DoubleMidset/<F>.lean` (Defs, Arc, Circle, Dendrite, Order, NoBranch,
  Classical/{ArcMinimal, ArcParam, Bump, PeanoChain, PeanoPath, PeanoLPC}): **0 errors** in
  each, warnings only (deprecations, unused section variables, "Try this"). `b.sh DoubleMidset`:
  `Build completed successfully`. `Classical/Bump.lean` is not imported by `DoubleMidset.lean`
  and was built separately (`b.sh DoubleMidset.Classical.Bump`): OK.
* **Forbidden constructs.** I grepped all in-scope files for `sorry`, `admit`, `axiom`,
  `native_decide`, `unsafe`, `opaque`, `implemented_by`, `extern`, `set_option`, `macro`, `elab`,
  `syntax`, `initialize`, `run_cmd`, `#eval`, `ofReduceBool`: **no matches**.
* **Axioms** (`/tmp/axchk/ax.lean`, a plain non-module file with `import DoubleMidset`; the
  plain form worked). Every one of the following depends only on
  `[propext, Classical.choice, Quot.sound]`:
  `isArcBetween_univ_of_noBranch`, `nonempty_homeomorph_of_noBranch`, `exists_seg_eq`,
  `exists_larger_seg`, `arc_unique`, `lemma_2_4_sides`, `two_le_order_of_mem_arc`,
  `three_le_order_of_triod`, `isDendrite_of_subcontinuum`, `IsPreconnected.inter_of_dendrite`,
  `seg_subset`, `exists_arc_in`, `isSimpleClosedCurve_union`, `IsSimpleClosedCurve.exists_param`,
  `Arc.exists_arc`, `Peano.ulc_of_compact`, `Peano.locallyPathConnectedSpace_of_compact_metric`,
  `Peano.locallyPathConnectedSpace_of_compact`, `encard_le_order`, `exists_points_of_le_order`,
  and (separate file) `boundary_bumping`.
* **Satisfiability probes** (`/tmp/axchk/probe.lean`, compiles): `IsArcChart id 0` holds in `ℝ`,
  `IsSimpleClosedCurve (univ : Set Circle)` and `IsArc (univ : Set unitInterval)` hold, and
  `sgnf a b a < 0 ↔ a ≠ b`. So the chart, curve and arc predicates can be satisfied, and the sign
  convention is the paper's.
* **Concurrency note.** `NoBranch.lean` changed twice while I was reviewing it (mtimes 20:43:43
  and 20:43:52). It now has `NoRelBranch`, `exists_seg_eq`, and a relative form of
  `exists_larger_seg`. Everything here refers to the final version (252 lines,
  md5 `3034ba72...`). The final compile and axiom check (20:47) ran after the last change, and
  the md5s of all in-scope files were the same before and after that run. A new file
  `DoubleMidset/TreeStructure.lean` appeared at 20:45. It is outside this review's scope and I did
  not review it.

## 1. DoubleMidset/Defs.lean

For each definition: one sentence on faithfulness, then findings.

| Line | Definition | Verdict |
|---|---|---|
| 47 | `midset a b = {x | dist x a = dist x b}` | Faithful: this is the paper's M(a,b) = {x : d(x,a) = d(x,b)} word for word. |
| 50 | `HasDMP`: `∀ a ≠ b, (midset a b).encard = 2` | Faithful. It uses `encard` (`⊤` for infinite sets), so an infinite midset does **not** count as 2. The `ncard` pitfall is avoided. |
| 54 | `MidsetsAtMostTwo`: `encard ≤ 2` | Faithful. With `encard`, an infinite midset correctly violates the bound (with `ncard` it would satisfy it, since `ncard = 0`). |
| 58 | `sgnf a b y = dist y a - dist y b` | Faithful to Definition 2.1, f_{a,b}(y) = d(y,a) - d(y,b). The probe confirms `sgnf a b a = -d(a,b) < 0`. |
| 67 | `IsArc A := Nonempty (A ≃ₜ unitInterval)` | Faithful: A, with the subspace topology, is homeomorphic to [0,1]. Nondegenerate automatically. |
| 71 | `IsArcBetween A p q`: embedding `f : I → X`, `range f = A`, `f 0 = p`, `f 1 = q` | Faithful: an arc with ends p, q. Injectivity forces p ≠ q, so there is no degenerate "arc from p to p". It agrees with `IsArc` (`IsArcBetween.isArc`, `IsArc.exists_isArcBetween` in Arc.lean). |
| 75 | `IsSimpleClosedCurve C := Nonempty (C ≃ₜ Circle)` | Faithful: Mathlib's `Circle` is the unit circle in ℂ, i.e. S¹. |
| 79 | `IsSimpleTriod Y`: three `IsArcBetween Aᵢ v pᵢ` with pairwise intersections `{v}`, and `Y` their union | Faithful to "the union of three arcs that pairwise meet only in a common end". `v` is an end of each arc by construction, and the `pᵢ` are automatically distinct and different from `v`. |
| 84 | `order p := encard {connectedComponentIn {p}ᶜ x | x ≠ p}` | Faithful to "the number of components of X \ {p}", with values in `ℕ∞` (`⊤` = infinitely many). The components are taken in X \ {p}, as subsets of X, which is right. |
| 88 | `IsTip p := order p = 1` | Faithful. |
| 91 | `IsBranchPoint p := 3 ≤ order p` | Faithful. Order `⊤` counts as a branch point, as it should. |
| 94 | `IsContinuum`: `CompactSpace ∧ ConnectedSpace ∧ Nontrivial ∧ MetrizableSpace` | Faithful to "nondegenerate compact connected metric(-izable) space". `Nontrivial` means at least two points. For a subtype of a metric space, `MetrizableSpace` is inferred, so (D3) is meaningful. |
| 98 | `IsDendrite`: continuum, locally connected, and `∀ C, ¬ IsSimpleClosedCurve C` | Faithful to the definition in §2.2. |
| 103 | `IsFiniteTree`: dendrite, finitely many branch points, each of order `≠ ⊤` | Faithful to Definition 2.6 ("finitely many branch points, each of finite order"). |
| 107 | `vertices X := {p | IsTip p ∨ IsBranchPoint p}` | Faithful ("its vertices are its tips and its branch points"). |
| 110 | `oddVertices`: vertices with `order p = n`, `n : ℕ` odd | Faithful. Tips (order 1) count as odd, and order `⊤` is excluded, which is correct since such points don't exist in a finite tree anyway. |
| 114 | `IsOpenEdge W`: `W` is the component of `(vertices X)ᶜ` containing some non-vertex `x` | Faithful to the paper's remark after Lemma 2.7, "the open edges are the components of T \ Ver". |
| 118 | `IsEdge ℓ := ∃ W, IsOpenEdge W ∧ ℓ = closure W` | Agrees with the paper's edges, **given Lemma 2.7**. A paper edge ℓ is an arc whose interior ℓ° is an open edge; ℓ is closed and ℓ° is dense in it, so cl(ℓ°) = ℓ. For a finite tree with no branch point (an arc), Ver is the two ends, T \ Ver is one open arc, and its closure is T, again matching. The definition itself does not say "arc between two vertices". That part depends on the not-yet-present `lemma_2_7` (see finding D-1). |
| 121 | `IsOpenArc U`: open, and `U ≃ₜ Ioo 0 1` | Faithful for its use in boxes. Inside an open edge, any subset homeomorphic to (0,1) is an open subinterval, so the extra `IsOpen` costs nothing. Nonempty automatically, which the Grid lemma needs. |
| 125 | `IsArcChart γ y`: `γ` restricted to `(-1,1)` is an embedding with open image, `γ 0 = y` | A sound formalization of "a small open arc J ∋ y". It does not say "J lies in the open edge of y", but in a dendrite that follows. If a chart image U contained a tip v, then by D1/D2 the two sides of v in U would lie in different components of X \ {v}, contradicting order 1. If U contained a branch point v, then a third component C of X \ {v} accumulates at v, so it meets U \ {v} and hence one of the two sides; but each side lies in a component of X \ {v} different from C. So U contains no vertex, and being connected it lies in the open edge of y. |
| 130 | `IsCrossing g y`: `y ∉ vertices`, `g y = 0`, some chart with no other zero, and `g(γ s) g(γ t) < 0` for s < 0 < t | Faithful to Definition 5.3 (opposite signs on the two sides of J \ {y}). The product condition over all s, t is the same as constant, opposite signs on each side. The definition is existential over charts, but that is harmless. Two charts at y overlap in an interval around y, and the overlap map is monotone and fixes y, so the two charts have the same sides, possibly swapped, and the crossing/touch verdict does not depend on the chart. Continuity of g and finiteness of the zero set are not built in. That is acceptable: the paper's hypotheses only guarantee that a chart exists, and the lemmas that use the definition have to assume them. |
| 137 | `IsTouch g y`: same, with `0 < g(γ s) g(γ t)` | Faithful (same signs on both sides). It cannot hold together with `IsCrossing`, by the chart-compatibility argument above. |
| 150 | `IsStrictPair a b := a ≠ b ∧ ∀ u ∈ vertices X, sgnf a b u ≠ 0` | Faithful to Definition 5.2 (distinct sites, no vertex in M(a,b)). |
| 153 | `oddCount a b := {u ∈ oddVertices X | sgnf a b u < 0}.ncard` | The sign convention is faithful: `sgnf a b u < 0 ↔ d(u,a) < d(u,b)`, i.e. "closer to a", as in (5.1). The paper defines N only for strict pairs; Lean defines it for all pairs, which is harmless. Uses `ncard`; see finding D-2. |
| 157 | `IsSphericalArc I x r := IsArc I ∧ 0 < r ∧ I ⊆ sphere x r` | Faithful to Definition 6.1. `Metric.sphere x r = {y | dist y x = r}` is S(x,r), and "nondegenerate" is automatic for `IsArc`. |
| 162 | `IsBox U V`: open arcs, disjoint, each contained in some open edge | Faithful to Definition 6.4, which allows "possibly the same open edge": the two `∃ W` are independent. The pair `(U, V)` stands for the product U × V. |
| 167 | `IsOddBox U V := IsBox U V ∧ ∀ a ∈ U, ∀ b ∈ V, IsStrictPair a b ∧ Odd (oddCount a b)` | Faithful to Definition 6.4. |

Findings:

* **D-1 (MAJOR, docstring, l. 27-30).** The module docstring says "Lemma 2.7 (`lemma_2_7`) shows
  that these edges have the properties the paper lists." No declaration `lemma_2_7` exists in
  the reviewed files; a grep of the whole project finds only this docstring. `Challenge.lean`
  copies Defs verbatim, so this sentence would be an unverified claim in the challenge file.
  The definitions of `IsOpenEdge`/`IsEdge` are correct, but that they match the paper's arc-edges
  still has to be proved. It should be resolved once `lemma_2_7` lands (TreeStructure.lean is
  apparently in progress); re-check its statement then. It should include: each edge is
  `IsArcBetween ℓ u u'` with `u ≠ u'` vertices and no other vertex, two edges meet at most in a
  common end, the number of edges is |Ver| - 1, and deg u equals the number of edges containing u.
* **D-2 (MINOR, l. 153).** `oddCount` uses `Set.ncard`, which returns 0 on infinite sets. This
  is correct whenever `vertices X` is finite, which holds for finite trees by Lemma 2.7, the only
  setting where N is used. If the set were infinite, the result would be `0` (even), and
  `IsOddBox` would become false. That failure is "safe" for hypotheses but makes conclusions of
  the form `IsOddBox …` unprovable. Recommendation: keep it, but make sure every challenge
  statement that uses `oddCount`/`IsOddBox` assumes `IsFiniteTree X`, or switch to `encard`
  (with `Odd` on `ℕ∞` replaced by `∃ n, … = n ∧ Odd n`).
* **D-3 (MINOR, l. 126).** `Set.restrict` is deprecated in this Mathlib (warning: use
  `Set.domRestrict`). Defs is copied verbatim into the Challenge file, so it is better to write
  `IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => γ t)` and avoid a deprecated name in the statement
  file.
* **D-4 (MINOR, l. 125-140).** It would help to say in the docstring of `IsCrossing`/`IsTouch`
  that the chart is not required to lie in the open edge of `y`, because in a dendrite this is
  automatic (argument above). Also that the definitions are existential over charts and do not
  depend on the chart chosen. Neither fact is proved yet. Whoever proves Lemma 5.4 (parity) will
  need the "independent of the chart" fact.
* **D-5 (MINOR, l. 14).** The docstring names the author and a date ("Lucas Alves de Almeida,
  21 November 2026"). Fine if intended for the public challenge file; otherwise remove it.
* No BLOCKER in Defs.lean.

## 2. DoubleMidset/Arc.lean (compiles, clean)

* l. 30 `IsArcParam`: continuous `ℝ → X`, injective on [0,1]. A convenience notion, and
  `isArcBetween_iff` (l. 140, with `T2Space`) shows it is equivalent to `IsArcBetween`. Correct.
* l. 70, 80, 93, 126, 144-177: the statements match their docstrings (arc of a parametrization,
  reversal, affine subarc, existence of a parametrization, `isArc`, `symm`, `ne`, membership of
  the ends, compactness, connectedness, `IsArc → ∃ p q, IsArcBetween`).
* l. 218 / 256 `IsArcParam.concat`, `IsArcBetween.union`: two arcs `p→q`, `q→r` with
  `A ∩ B ⊆ {q}` form an arc `p→r`. Correct and as stated. (`A ∩ B ⊆ {q}` with `q` in both is the
  same as `= {q}`.)
* l. 265 `exists_isArcBetween_of_joinedIn`: a direct wrapper of `Arc.exists_arc`. Correct.
* **MINOR**: unused `[TopologicalSpace X]` in `symm_image`, `sub_image`, `concat_of_le`,
  `concat_of_lt`; deprecated `if_pos`/`if_neg`; an unused `congr 1` (l. 119).

## 3. DoubleMidset/Circle.lean (compiles, clean)

* l. 27 `IsSimpleClosedCurve.exists_param`: `c` continuous, 1-periodic, injective on [0,1),
  with `c '' [0,1] = c '' [0,1) = C`. Matches the docstring and needs no T2.
* l. 126 `isSimpleClosedCurve_union`: two arc parametrizations with the same ends that meet only
  in `{a 0, a 1}` give a simple closed curve. Correct. The hypothesis is the natural one, and the
  ends are distinct automatically.
* **MINOR**: deprecated `if_pos`/`if_neg`.

## 4. DoubleMidset/Dendrite.lean (compiles, clean)

* l. 52 `seg p q`: a chosen arc, or `{p}` if there is none. `seg_self` (l. 59) is correct. In a
  dendrite `seg_eq` (l. 170) shows it is *the* unique arc. Correct.
* l. 66 global instance `locallyPathConnected_of_compact_lc` (compact + locally connected metric
  ⇒ locally path connected), priority 100. It is mathematically correct (Peano). **MINOR**: as a
  global instance it is triggered by every `LocallyPathConnectedSpace` search on a metric space.
  Harmless here, but worth knowing about.
* l. 70 `exists_arc_in_open`, l. 78 `exists_arc`: correct.
* l. 94 `arc_subset_of_noSCC`, l. 158 `arc_unique`: two arcs with the same ends in a metric
  space without simple closed curves are equal. This is **stronger** than the paper's
  uniqueness in (D2): it needs neither compactness nor local connectedness. The proof (first
  exit and first return give a simple closed curve) is the standard one and is checked.
* l. 201 `sides_separate` / l. 224 `ends_separate`: the core of Lemma 2.4, stated correctly
  (`0 ≤ s < t < s' ≤ 1`, so `g s`, `g s'` lie in different components of `X \ {g t}`).
* **Fact 2.3:**
  * (D1) l. 233 `seg_subset`: the arc between two points of a preconnected `Y` lies in `Y`.
    l. 246 `exists_arc_in`: connected sets are arcwise connected. Faithful, and in fact stronger,
    since the canonical arc lies in Y.
  * (D2) l. 260 `IsPreconnected.inter_of_dendrite`: preconnected ∩ preconnected is
    preconnected. Faithful. "Preconnected" is the right reading of the paper's "connected",
    because the intersection may be empty. The "consequently unique arc" part is `arc_unique` +
    `seg_isArcBetween`.
  * (D3) l. 282 `isDendrite_of_subcontinuum`: a closed, preconnected, nontrivial `K` is a
    dendrite (as a subtype). Faithful: "subcontinuum" means nondegenerate by the paper's
    definition, and all four parts of `IsDendrite`, including metrizability and "no simple closed
    curve in `K`" (via `IsSimpleClosedCurve.image_val`), are proved.
  * (D4) is taken from Mathlib (`IsOpen.connectedComponentIn`), as the header says.
* Hypotheses: the dendrite is encoded as `[MetricSpace X] [CompactSpace X] [ConnectedSpace X]
  [LocallyConnectedSpace X] (hD : no SCC)`, without `Nontrivial`. That is weaker than
  `IsDendrite X`, so the results are at least as strong as the paper's. Consistent.
* **MINOR (l. 20)**: the header names "(D2) `IsPreconnected.inter`", but the declaration is
  `IsPreconnected.inter_of_dendrite`.
* **MINOR**: `sides_separate` has an unused `[ConnectedSpace X]`, and `image_val` has unused
  `[CompactSpace] [ConnectedSpace] [LocallyConnectedSpace]` (both via section variables). These
  are harmless extra hypotheses, always available where the lemmas are used. Also deprecated
  `dif_pos`/`dif_neg`/`mem_setOf_eq`.

## 5. DoubleMidset/Order.lean (compiles, clean)

* l. 29-52 `compsAt`, `order_eq` (rfl), `encard_le_order`, `exists_points_of_le_order`:
  correct, and these are the right interface to `order` (k points in pairwise different
  components ⟺ k ≤ order, in `ℕ∞`). Both directions are given.
* l. 54, 66 `two_le_order`, `three_le_order`: correct.
* l. 88 **`lemma_2_4_sides`**: for `IsArcBetween A p q`, `y ∈ A \ {p,q}`, and `y₁, y₂ ∈ A \ {y}`
  in different components of `A \ {y}`, it concludes that they lie in different components of
  `X \ {y}`. This is **faithful** to Lemma 2.4, first sentence ("the two components of A \ {y}
  lie in different components of X \ {y}"). It does not prove separately that `A \ {y}` has
  exactly two components, but the lemma only presupposes that, and the internal `same` step
  shows that points on one side are in one component.
* l. 136 `two_le_order_of_mem_arc`: faithful to "y has order at least two".
* l. 141 `three_le_order_of_triod`: stated with the unpacked data of `IsSimpleTriod` (three
  `IsArcBetween Aᵢ v pᵢ`, pairwise `∩ = {v}`) and concludes `3 ≤ order v`. Faithful to "the center
  of a simple triod has order at least three". **MINOR**: a one-line corollary taking
  `IsSimpleTriod Y` and the witnesses would make the link to the Defs predicate explicit.
* No hypothesis is unused or contradictory. The setting is a dendrite (minus `Nontrivial`, which
  is not needed).

## 6. DoubleMidset/NoBranch.lean (final version, compiles, clean)

* l. 37 `NoRelBranch K`: no `w ∈ K` has three points of `K \ {w}` in pairwise different
  components of **X** \ {w}. The docstring matches the definition. Using components of X rather
  than of K makes the hypothesis weaker (easier to satisfy), so `exists_seg_eq` is stronger.
* l. 44 `noRelBranch_univ`: no branch points implies `NoRelBranch univ`. Correct, via
  `three_le_order`.
* l. 49 `exists_larger_seg`: in a preconnected `K` with `NoRelBranch K`, an arc `seg p q ⊆ K`
  and a point `z ∈ K \ seg p q` lie in some larger `seg p' q'` with `p', q' ∈ K`. Correct. The
  proof takes the first point `w` where `[z,p]` meets `[p,q]`. If `w` is an interior point, the
  three points `z, p, q` lie in different components of `X \ {w}` (`ends_separate` three times),
  which contradicts `NoRelBranch`.
* l. 111 `seg_subset_ball`: arcs between close points are small (from ULC + D1). Correct.
* l. 129-180 `phi`, `phi_summable`, `phi_lt_of_ssubset` (strict decrease for a strict superset
  with a closed nonempty smaller set, using a dense sequence), `phi_le_add_of_forall`: correct.
* l. 183 `lowerSemicontinuous_phi_seg`: correct. It uses
  `seg p' q' ⊆ seg p' p ∪ seg p q ∪ seg q q'` and smallness.
* l. 210 `exists_seg_eq`: a closed, preconnected, nontrivial `K` with `NoRelBranch K` equals
  `seg p q` for some `p ≠ q` in `K`. This relative version of "no triod ⇒ arc" is stronger than
  what the paper needs and will be useful for Lemma 2.7.
* l. 239 **`isArcBetween_univ_of_noBranch`**: `[MetricSpace X] [CompactSpace X]
  [ConnectedSpace X] [LocallyConnectedSpace X] [Nontrivial X]`, no simple closed curve, no
  branch point ⇒ `∃ p q, IsArcBetween univ p q`. This is **faithful** to the consequence of
  Fact 2.5 that the paper uses ("a dendrite without branch points is an arc"), and it is proved
  from scratch, so Moore's theorem is not needed. l. 246 `nonempty_homeomorph_of_noBranch` gives
  `X ≃ₜ [0,1]`. The hypotheses are exactly "dendrite" with the metric given. None is unused; for
  example, `Nontrivial` is needed because a point has no arc.
* **MINOR (l. 14-20)**: the module docstring still describes only the `univ` version. It should
  mention `NoRelBranch`/`exists_seg_eq`.
* **MINOR**: `noRelBranch_univ`, `phi_summable`, `infDist_le_add_of_forall` carry unused
  section instances. Deprecated `mem_setOf_eq`.

## 7. DoubleMidset/Classical/*.lean (compiled; no forbidden constructs; standard axioms)

* `ArcParam.lean` l. 366 **`Arc.exists_arc`**: `[T2Space X]`, `γ : Path x y`, `x ≠ y` ⇒ there
  is an embedding `f : I → X` with `f 0 = x`, `f 1 = y`, `range f ⊆ range γ`. This is the arc
  theorem as claimed, including "inside the image of the path", which `exists_arc_in_open` needs.
* `PeanoChain.lean` l. 68 **`Peano.ulc_of_compact`**: compact, locally connected metric ⇒ for
  every `ε > 0` there is `δ > 0` such that `dist a b < δ` gives a preconnected `C ∋ a, b` with
  `C ⊆ ball a ε`. This is uniform local connectedness, as claimed.
* `PeanoLPC.lean` l. 39 **`Peano.locallyPathConnectedSpace_of_compact_metric`**: compact,
  locally connected metric ⇒ `LocallyPathConnectedSpace`. As claimed (l. 56 gives the
  metrizable version). **MINOR**: the module docstring (l. 10-14) mentions
  `IsQuasiPeano.locallyPathConnectedSpace` and "the article … Hahn–Mazurkiewicz", which are
  leftovers from the earlier project; no such declaration exists here.
* `Bump.lean` l. 21 **`boundary_bumping`**: `K` compact, connected, T2; `U` open with
  `U ≠ univ`; `x ∈ cl U` ⇒ the component of `cl U` containing `x` meets `cl U \ U`. This is
  correct, and it is the "closure of an open set" form (Nadler Thm 5.4). **MINOR, but relevant
  for Prop 3.1**: (i) the docstring calls it "Lemma 5.2", the numbering of the earlier article,
  while this paper cites [Nad92, Thm 5.6] in a different form (for a component C of X \ E,
  cl C ∩ ∂E ≠ ∅). (ii) In the paper's proof the components `C_n` of the open ball `U = B(p,ε)`
  have to reach the sphere, and the 5.4 form gives that only after a small adaptation. Apply it
  to `U' = B(p,ε')` with `ε' < ε`: the component of `cl U'` containing `p_n` is a connected
  subset of `U`, so it lies in `C_n`; these are pairwise disjoint and each meets
  `∂U' ⊆ S(p,ε')`. Whoever formalizes Prop 3.1 should use this adaptation. (iii) `Bump.lean` is
  not imported by `DoubleMidset.lean`, so `b.sh DoubleMidset` does not build it.
* `ArcMinimal.lean`, `PeanoPath.lean`: supporting lemmas only. They compile, and the statements
  used downstream (`exists_minimal_adm`, `Minimal.gap_of_eq`, `exists_path_near`) are consistent
  with how they are used. **MINOR**: unused-section-variable and deprecation warnings.

## 8. Project hygiene (MINOR)

* `lakefile.toml` lists `defaultTargets = ["DoubleMidset", "Challenge", "Solution"]`, but
  `Challenge.lean` and `Solution.lean` do not exist yet, so `lake build Challenge` fails
  (checked). A plain `lake build` will fail until they are added.
* `DoubleMidset/Test.lean` is a stray scratch file (imports only, not imported by anything).
  Remove it before release.

## Overall verdict

**No BLOCKER.** All in-scope files compile without errors and contain no forbidden constructs.
Every main theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

Every definition in `Defs.lean` matches the paper. In particular:
* the cardinalities use `encard`, so infinite midsets are handled correctly;
* the sign convention for `sgnf`/`oddCount` is the paper's;
* `order` counts components of X \ {p} in `ℕ∞`;
* crossings and touches through arc charts are equivalent to Definition 5.3 in a dendrite.

The library statements (Lemma 2.4, Fact 2.3 (D1)-(D3), the arc-uniqueness theorem, and the
no-branch-point ⇒ arc replacement for Fact 2.5) say what their docstrings claim, and several are
stronger than the paper's.

There is one MAJOR item: Defs' docstring (D-1) refers to a `lemma_2_7` that does not exist yet.
The edge definitions are correct, but until Lemma 2.7 is proved nothing checks that they match the
paper's arc-edges. The fix is to complete TreeStructure.lean, or to soften the docstring before
Defs is copied into the Challenge file.

Recommended before freezing the Challenge file:
* fix D-1;
* replace the deprecated `Set.restrict` (D-3);
* decide whether `oddCount` should use `encard`, or make sure every statement that uses it
  assumes `IsFiniteTree` (D-2).
