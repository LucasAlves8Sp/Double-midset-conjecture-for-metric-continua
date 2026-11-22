# Review 02: TreeStructure.lean (Lemma 2.7) and the NoBranch.lean refactor

Reviewer: independent, with no prior context. I did not modify any .lean file. Scratch files are in
`/tmp/ax.lean`, `/tmp/ax2.lean` and `/tmp/rev02/wrap.lean`.
Paper read: Section 2 (Fact 2.3, Lemma 2.4, Fact 2.5, Definition 2.6, Lemma 2.7 with its proof, and
the paragraph after it) and Convention 5.1.

Files reviewed (md5 at the time of the final check):
* `DoubleMidset/TreeStructure.lean`: 887 lines, md5 `f946df80...`
* `DoubleMidset/NoBranch.lean`: 252 lines, md5 `3034ba72...`. This is the same file that review-01
  saw as its final version.

**Concurrency note.** While I was reviewing, someone else added `DoubleMidset/Reduction.lean`
(20:57) and an import of it in `DoubleMidset.lean`. That file is outside this review. For that
reason my axiom probe at the end imports `DoubleMidset.TreeStructure` directly. Neither in-scope
file changed during the review.

## 0. Global checks

* **(a) Compilation.** My first `b.sh DoubleMidset` ran before `Reduction` was added, and it
  printed `Build completed successfully (2139 jobs)`. After that I ran
  `b.sh DoubleMidset.TreeStructure` (`Build completed successfully (2137 jobs)`). I also compiled
  `lake env lean DoubleMidset/TreeStructure.lean` and `.../NoBranch.lean` directly. Result: 0 errors.
  The only warnings are deprecations, unused section variables and a `push_neg` deprecation.
* **(b) Forbidden constructs.** I grepped both files (and the rest of `DoubleMidset/`) for `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `extern`,
  `set_option`, `macro`, `elab` and `run_cmd`. **No matches.** `decide` appears only as plain
  `by decide` on small `ℕ∞` facts (TreeStructure l. 378, 380, 431, 432, 472, 488, 489).
* **(e) Axioms.** Each of the following depends only on `[propext, Classical.choice, Quot.sound]`:
  `vertices_finite`, `edges_finite`, `edge_isArc`, `edge_inter_subset`, `edge_inter_subsingleton`,
  `sUnion_edges`, `order_eq_encard_edges`, `ncard_edges_add_one`, `cc_vertices_eq`, `isEdge_iff`,
  `exists_ends`, `order_eq_two_of_ne_ends`, `exists_seg_eq`, `exists_larger_seg`,
  `isArcBetween_univ_of_noBranch` and `nonempty_homeomorph_of_noBranch`. The same holds for the
  bundled probe `lemma_2_7_probe` below.
* **(c) Hypotheses.** I printed every main signature with `#check`. Each one assumes at most
  `[MetricSpace T] [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T]`,
  `hD : ∀ C, ¬ IsSimpleClosedCurve C`, `hBf : (branchSet T).Finite` (where
  `branchSet T = {p | IsBranchPoint p}`, the same set as in `IsFiniteTree`), and in some cases
  `hBo : ∀ p, IsBranchPoint p → order p ≠ ⊤`. These are exactly the fields of `IsFiniteTree`,
  with a metric in place of "metrizable", which matches the paper's convention that a continuum is
  a metric space. Nothing stronger is assumed. Several results need less: `edge_isArc`,
  `edge_inter_*`, `cc_vertices_eq` and `isEdge_iff` do not take `hBo`. None of the ten main results
  triggers the unused-section-variable linter, so every hypothesis they carry is actually used.
  `Nontrivial` is needed: for a one-point space, `ncard_edges_add_one` would read `0 + 1 = 0`.
* **Hypothesis-faithfulness probe.** `/tmp/rev02/wrap.lean` compiles, with standard axioms. It
  proves the following from `IsFiniteTree T` alone, for `[MetricSpace T]`:
  - `V` is finite and the set of edges is finite;
  - the union of the edges is `univ`;
  - every edge is `IsArcBetween ℓ a b` with `a ≠ b` and `ℓ ∩ V = {a, b}`;
  - two distinct edges meet in `∅` or in a single vertex `{v}`;
  - `#E + 1 = #V`;
  - `order u = #{ℓ | u ∈ ℓ}` for every vertex `u`;
  - every `y ∉ V` has order 2;
  - for every edge `ℓ` with ends `a, b`, `ℓ \ {a, b}` is an `IsOpenEdge`.

  So the API really does yield all of Lemma 2.7, under exactly the paper's hypotheses. Each step
  takes only a few lines.

## 1. DoubleMidset/TreeStructure.lean

The approach (components of `T \ B`, their closures are arcs, an injection into pairs for
finiteness, a bijection for degrees, Mathlib's tree edge count) is mathematically sound. I checked
every proof step by step.

* l. 36-39, 283 `branchSet`, `bcomp`, `bcomps`: these are the intended objects. `bcomp` only needs
  `[MetricSpace T]` (I confirmed this with `#check`).
* l. 46-106 (component lemmas): correct.
  - `mem_bcomp_of_mem_closure`: a non-branch point of `cl W` lies in `W`, because
    `insert y W` is preconnected.
  - `bcomp_nontrivial`: a singleton component would be clopen in a connected nontrivial space.
  - `cc_eq_of_mem_closure_bcomp`: `cl W \ {w}` lies in a single component of `T \ {w}` when `w` is
    a branch point.
* l. 111 `enat_eq_two`, l. 122 `exists_first_entry`: correct.
* l. 140 `noRelBranch_closure_bcomp`: correct. If `w ∈ cl W` is a branch point of `T`, then all
  points of `cl W \ {w}` share one component of `T \ {w}`, so `h1` fails. Otherwise
  `three_le_order` would make `w` a branch point. This is exactly where the relative notion is
  needed, because the ends of `cl W` are branch points of `T`.
* l. 149 `exists_ends`: `cl W` is closed, preconnected and nontrivial and satisfies `NoRelBranch`,
  so `exists_seg_eq` makes it an arc `seg a b`. Correct.
* l. 164 `mem_bcomp_of_ne_ends`: correct. An interior point `y ∉ W` would be a branch point, and
  then both ends would lie in one component of `T \ {y}`, which contradicts `ends_separate`.
* l. 174 `order_eq_two_of_ne_ends`: `2 ≤ order` (Lemma 2.4) together with "not a branch point"
  (since `y ∈ W`) gives order 2. Correct.
* l. 180 `isTip_of_end_mem`: correct. I checked both cases:
  - `y ∈ cl W`: the subarc from `y` to `b` avoids `a`.
  - `y ∉ cl W`: the arc from `y` to `a` first enters `cl W` at a point that is not in `W` (`W` is
    open). That point must be `b`, and the initial piece of the arc avoids `a`.
* l. 235-244 (ends are vertices), l. 247 `seg_to_end_subset` (`b ∉ [y, a]` unless `b = y`):
  correct.
* l. 277 `treeGraph`: the adjacency is "distinct and on a common edge". This is a faithful vertex
  graph.
* l. 293 `bcomp_eq_of_cc_eq`: correct. Two different components sharing a boundary point `w`
  produce an arc `[x₁, w] ∪ [w, x₂]` with `w` in its interior, so `w` separates `x₁` from `x₂`.
* l. 328 `bcomps_finite`: correct. A component with empty boundary is `univ`. Every other
  component `W` maps to `(w, cc_{T\{w}}(x))` for a boundary branch point `w`, the map is injective
  by the previous lemma, and the target is finite by `hBf` and `hBo`.
* l. 365 `vertices_finite`: correct. Tips lie in `⋃_W {y ∈ cl W | order y ≠ 2} ⊆ ⋃_W {a_W, b_W}`.
* l. 389-416 (open-arc helpers), l. 420 `cc_vertices_eq`, l. 449 `isEdge_iff`: correct.
  `cc_vertices_eq` identifies the component of `T \ V` at `x` with `seg a b \ {a, b}`, using
  `cl(bcomp x) = seg a b`.
* l. 478 `edge_isArc`, l. 495 `edge_inter_subset`, l. 507 `edge_inter_subsingleton`,
  l. 539 `edges_finite`, l. 566 `sUnion_edges`: correct. For `sUnion_edges`, `T \ B` is dense, and
  the closure of a finite union is the union of the closures.
* l. 617 `order_eq_encard_edges`: correct.
  - Injectivity: two edges at `u` form an arc through `u`, so they land in different components.
  - Surjectivity: every component `C` of `T \ {u}` has `u` in its closure. The open set
    `N = (⋃ edges not containing u)ᶜ ∩ (V \ {u})ᶜ` contains a point `z ∈ C`, and the edge through
    `z` contains `u`.
* l. 708 `treeGraph_preconnected`: correct. It uses the clopen union of the edges that meet the
  reachable set.
* l. 745 `treeGraph_isAcyclic`: correct. Each edge is a bridge, because a walk avoiding `vw`
  produces a connected set that misses the open edge `(v, w)` yet contains `[v, w]`.
* l. 819 `ncard_edges_add_one`: `isTree_iff_connected_and_card` plus a bijection from edges to
  `edgeSet` (`ψ`, injective since `seg_symm`). Correct.

Findings:

* **BLOCKER**: none.
* **MAJOR**: none on correctness. For the coverage gaps in the paragraph after Lemma 2.7, see §3.
  They are labelled MAJOR there only if this file is meant to cover that paragraph in full.
* **MINOR (no bundled statement; Defs.lean l. 29).** The `Defs.lean` docstring promises a
  declaration `lemma_2_7`, but no such declaration exists anywhere. CHECKPOINT.md already tracks
  this. My probe `/tmp/rev02/wrap.lean` (`lemma_2_7_probe`, about 50 lines) shows that it can be
  added directly from `IsFiniteTree T`. I suggest adding it, both so the docstring is true and so
  the hypotheses visibly match Definition 2.6.
* **MINOR (l. 478).** `edge_isArc` states `seg a b = ℓ` rather than `IsArcBetween ℓ a b`. These are
  equivalent through `seg_isArcBetween`, but the second form is self-contained.
* **MINOR (l. 495/507).** "Two edges meet at most in a common end" is only available by combining
  `edge_inter_subsingleton`, `edge_inter_subset` and `edge_isArc`. A single lemma
  `ℓ ∩ ℓ' = ∅ ∨ ∃ v, ℓ ∩ ℓ' = {v} ∧ v ∈ V` would make this direct (see the probe).
* **MINOR (l. 174/420).** Two facts are not stated globally:
  - "every edge point has order 2" (`∀ y ∉ V, order y = 2`);
  - "the interior of every edge is an open edge" (`IsEdge ℓ → IsArcBetween ℓ a b →
    IsOpenEdge (ℓ \ {a, b})`).

  Both can be derived (the probe proves them) but have to be assembled by hand.
  `cc_vertices_eq` is awkward to use downstream, because it is phrased with
  `seg a b = closure (bcomp x)`.
* **MINOR (l. 547, 569).** `dense_compl_finite` carries the unused hypotheses `hD`, `hBf`,
  `[CompactSpace]` and `[LocallyConnectedSpace]`. At l. 569 it is called as
  `dense_compl_finite hD hBf hBf`, passing `hBf` twice. This is harmless but confusing.
* **MINOR (unused section variables).** The following carry extra hypotheses they do not use
  (linter warnings):
  - `noRelBranch_closure_bcomp` (l. 140): `hD`, `hBf`;
  - `end_mem_closure_left`/`_right` (l. 159/161): `hBf`, `hx`, `hab`;
  - `isOpen_bcomp`, `bcomp_subset`, `mem_bcomp`, `isPreconnected_bcomp`, `bcomp_eq` (l. 46-71):
    instances;
  - `branchSet_subset_vertices`, `seg_diff_ends_eq`, `isPreconnected_seg_diff_left`: instances.

  None of these is a main result.
* **MINOR (l. 122 vs NoBranch l. 57-66).** `exists_first_entry` duplicates the first-entry argument
  inside `exists_larger_seg`. The latter could reuse it.
* **MINOR (deprecations).** `Set.mem_diff`, `Set.diff_subset` and `push_neg` (l. 215) are
  deprecated.

## 2. DoubleMidset/NoBranch.lean (refactor re-check)

* l. 37 **`NoRelBranch K`** means: no `w ∈ K` has three points `z, p, q ∈ K \ {w}` in pairwise
  different components of `X \ {w}`. **This is a sensible notion.**
  - Being in different components of `K \ {w}` is a weaker condition than being in different
    components of `X \ {w}`. So in general `NoRelBranch K` is a weaker hypothesis than "the subspace
    `K` has no branch point", which makes `exists_seg_eq` stronger.
  - For `K` connected in a dendrite the two notions coincide. If `z, p ∈ K` lie in one component
    `C` of `X \ {w}`, then the unique arc `[z, p]` lies in `C` (C is open, by D1 and D2) and in `K`
    (`seg_subset`). So `z, p` lie in one component of `K \ {w}`.
  - So in our setting `NoRelBranch K` is exactly "`K`, a subdendrite by D3, has no branch points
    of its own". That is the hypothesis the paper uses when it applies Fact 2.5 to the pieces
    `P_j`.
  - It is strictly weaker than "no point of `K` is a branch point of `X`", and that is what the
    tree argument needs (see TreeStructure l. 140).
  - The definition carries only `[MetricSpace X]`, and `hD` is not baked in (checked with `#check`).
* l. 44 `noRelBranch_univ`: correct (`three_le_order`).
* l. 49 `exists_larger_seg` (relative form): correct. I re-checked each step.
  - `w` is the first point where `[z, p]` meets `A = [p, q]`.
  - If `w = p` or `w = q`, then `seg z q` (resp. `seg z p`) equals `P ∪ A`, and `z ∈ K` gives
    `p' = z ∈ K`.
  - Otherwise, `w ∈ K` by `seg_subset` (since `A ⊆ K`), and `z, p, q ∈ K \ {w}` are pairwise
    separated by `w` (`ends_separate` on `[z, p]`, on `P ∪ [w, q]`, and on `A`). This contradicts
    `NoRelBranch K`.
* l. 210 `exists_seg_eq`: correct. `φ ∘ seg` is lower semicontinuous on the compact set `K × K`
  (`K` is closed in compact `X`). A minimizer has distinct ends (otherwise `φ({z}) > φ(seg z q)`).
  If its arc missed a point of `K`, the relative `exists_larger_seg` would give a strictly smaller
  `φ`.
* l. 239 `isArcBetween_univ_of_noBranch` is now derived from `exists_seg_eq` with `K = univ` and
  `noRelBranch_univ`. Its hypotheses are unchanged (dendrite plus no branch points). l. 246 is as
  before. Correct.
* **MINOR (l. 8-21, still open from review-01).** The module docstring still describes the old
  global version. It says "unless `w` is a branch point" where it should say "a branch point
  relative to `K`", and "hence is all of `X`" where it should say "all of `K`". It does not mention
  `NoRelBranch` or `exists_seg_eq`.
* **MINOR (l. 89).** The comment "otherwise `w` is a branch point" should say a relative branch
  point.
* **MINOR.** There are 10 linter warnings (unused section instances, deprecations), as noted in
  review-01.

No BLOCKER or MAJOR findings for NoBranch.lean.

## 3. Coverage table

### Lemma 2.7

| Assertion | Lean declaration(s) | Status |
|---|---|---|
| `V` is finite | `vertices_finite` | covered |
| `T` is a union of edges | `sUnion_edges` | covered |
| ... finitely many edges | `edges_finite` | covered |
| ... each edge an arc | `edge_isArc` (+ `seg_isArcBetween`) | covered |
| Each edge joins two (distinct) vertices | `edge_isArc` (`a ≠ b`, `{a, b} ⊆ V`) | covered |
| ... and contains no other vertex | `edge_isArc` (`ℓ ∩ V = {a, b}`) | covered |
| Two edges meet at most in a common end | `edge_inter_subsingleton` + `edge_inter_subset` + `edge_isArc` | covered (not bundled) |
| Number of edges `= |V| - 1` | `ncard_edges_add_one` (+ `vertices_finite`, `edges_finite`, so the `ncard`s are meaningful) | covered |
| Degree (order) of each vertex `=` number of edges containing it | `order_eq_encard_edges` | covered |
| Edges are the closures of open edges (Defs.lean definition) vs. the paper's edges | `isEdge_iff` (edges = closures of components of `T \ B`) | covered |

**Every assertion of Lemma 2.7 is covered.** The bundled form compiles from `IsFiniteTree` alone
(`lemma_2_7_probe`). It is not yet in the project.

### Paragraph after Lemma 2.7

| Assertion | Lean declaration(s) | Status |
|---|---|---|
| The interior `ℓ \ {ends}` of an edge is an open edge | derivable from `isEdge_iff`, `exists_ends`, `mem_bcomp_of_ne_ends`, `cc_vertices_eq` (done in the probe) | covered, not stated (MINOR) |
| Open edges are exactly the components of `T \ V` | definition `IsOpenEdge` (Defs.lean) + `cc_vertices_eq` (each such component is `seg a b \ {a, b}` for its edge) | covered |
| Every edge point (`y ∉ V`) has order 2 | `order_eq_two_of_ne_ends` + `exists_ends` + `end_mem_vertices_*` (done in the probe) | covered, not stated (MINOR) |
| A small open arc around an edge point, inside its open edge, is a neighbourhood in `T` (open edges are open and are open arcs) | none. The ingredients are `seg_diff_ends_eq` (open edge = `g '' Ioo 0 1`) and openness of components of the open set `Vᶜ` | **missing** |
| `|Odd|` is even (handshake) | none | **missing** |
| If `T` has a branch point, every edge has an end that is a branch point | none | **missing** |
| `∑_{u ∈ V} deg u = 2(|V| - 1)` | none. Follows from `order_eq_encard_edges`, the fact that each edge has exactly two vertices (`edge_isArc`), double counting, and `ncard_edges_add_one` | **missing** |
| Tip formula (2.1): `t = 2 + ∑_{branch} (deg u - 2)` | none | **missing** |

The two items singled out in the task ("open edges are the components of `T \ V`" and "edge
points have order two") are covered, though not as standalone lemmas. The other assertions of the
paragraph (the neighbourhood claim, handshake, branch end, degree sum and tip formula) are not
formalized yet. They are needed downstream: Sections 5 and later use `IsArcChart`/`IsCrossing` and
the parity of `|Odd|`. **MAJOR** if this file is meant to cover the whole paragraph; otherwise they
are tracked future work.

## 4. Overall verdict

**TreeStructure.lean: ACCEPT (no blockers).**
* It compiles, with no forbidden constructs and only the standard axioms.
* The hypotheses of all ten main results are exactly those of a finite tree in the paper's sense
  (metric, compact, connected, nontrivial, locally connected, no simple closed curve, finitely
  many branch points, each of finite order), and nothing stronger. Some results use fewer.
* Together they prove every assertion of Lemma 2.7. I confirmed this by deriving a bundled
  statement from `IsFiniteTree` in a scratch file.

Recommended before freezing:
1. Add a bundled `lemma_2_7` from `IsFiniteTree T`. The Defs.lean docstring already refers to it.
2. Add the global corollaries `∀ y ∉ V, order y = 2` and "edge interior is an open edge".
3. Formalize the rest of the paragraph after Lemma 2.7: open edges are open arcs and neighbourhoods,
   the degree sum, `|Odd|` even, branch ends, and the tip formula.

**NoBranch.lean refactor: ACCEPT.** The relative `exists_larger_seg` and `exists_seg_eq` are
correct, `isArcBetween_univ_of_noBranch` is correctly derived, and `NoRelBranch` is a sensible
notion. In a dendrite it is equivalent to "the subcontinuum has no branch points of its own". That
is exactly what is needed to make closures of components of `T \ B` into arcs. Only the
docstrings and comments need updating.
