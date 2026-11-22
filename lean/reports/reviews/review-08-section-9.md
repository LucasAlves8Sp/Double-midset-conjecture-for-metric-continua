# Review 08 — Section 9 "Counting tips" (Definition 9.1, Lemma 9.2, Proposition 9.3)

Reviewer: independent, no prior context. No `.lean` file was modified.

Files reviewed:
- `/home/claude/dmp/lean/DoubleMidset/Defs.lean` (end: `UsesPair`, lines 170–174)
- `/home/claude/dmp/lean/DoubleMidset/Count.lean` (all 421 lines)
- Paper `/mnt/user-data/uploads/727504a7-dmp_paper_2.tex`, lines 916–939. Standing Convention 5.x (line 475) puts the DMP in force for Sections 5–11, so the `HasDMP T` hypothesis in Lean matches the paper.

## Verdict: ACCEPT WITH MINOR

No blockers and no major issues. The definition is faithful, the proofs are sound, and they follow the paper's argument closely (in two places the Lean version is slightly more direct). All remaining items are cosmetic.

## 3. Mechanical checks

| Check | Result |
|---|---|
| `/home/claude/dmp/b.sh DoubleMidset` | `Build completed successfully (2186 jobs)`, 0 errors (226 warnings project-wide) |
| Warnings in `Count.lean` | 2, both deprecations: `push_neg` (l.149) and `Set.mem_setOf_eq` (l.370) |
| `grep -rnwE "sorry\|admit\|axiom\|native_decide\|unsafe\|implemented_by\|opaque\|extern"` over `DoubleMidset/` (incl. `Classical/`) and `DoubleMidset.lean` | no hits |
| `set_option` anywhere in `DoubleMidset/` | none |
| `#print axioms DoubleMidset.lemma_9_2` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms DoubleMidset.prop_9_3` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms DoubleMidset.triod_structure` | `[propext, Classical.choice, Quot.sound]` |

## 1. Definition 9.1 — `UsesPair` (Defs.lean:173–174)

```lean
def UsesPair (e v : X) (ℓ ℓ' : Set X) : Prop :=
  ∀ a ∈ ℓ, ∀ a' ∈ ℓ', a ≠ v → a' ≠ v → (dist e v < dist e a ↔ dist e v < dist e a')
```

**Agreement with the paper.** Take `ℓ` to be an edge at `v`. By Prop 8.2(a), `h_e` is strictly monotone on `ℓ`, so for every `a ∈ ℓ \ {v}` we have `h_e(a) ≠ h_e(v)`, and the direction "increasing away from `v`" holds iff `h_e(v) < h_e(a)`, for any one such `a` and so for all of them. In Lean this dichotomy is `tip_direction` (Count.lean:211). So, given 8.2(a), `UsesPair e v ℓ ℓ'` says exactly that `h_e` is increasing on both edges or decreasing on both, which is the paper's "same direction on ℓ and ℓ′". Both directions of that equivalence are actually used in the development:
- The paper's notion implies `UsesPair`: Count.lean:299–316, where pairs of increasing edges and pairs of decreasing edges are shown to be used.
- `UsesPair` gives the paper's matching hypothesis: Count.lean:142–160, where `hside` is applied to the far end `u'` of `ℓ'`.

**Reasonableness as a Challenge-level definition.** It is reasonable.
- It is stated intrinsically, with no parametrization and no orientation data. That avoids hiding the choice of direction in a parametrization.
- It is symmetric in `ℓ, ℓ'` (because of the `↔`), which matches "unordered pair". In `triod_structure`, unordered pairs are 2-element `Finset`s, and the filter quantifies over both orderings (Count.lean:267).
- It does not itself require `ℓ ≠ ℓ'`, that `ℓ, ℓ'` are edges at `v`, that `v` is a branch point, or that `e` is a tip. All of these appear as hypotheses wherever the definition is used (Lemma 9.2 and the `Ev`/`P` construction), which is acceptable.
- Outside the DMP setting the intrinsic predicate is weaker than or incomparable with "same direction". That cannot matter here: every use sits under `HasDMP`, and since Lemma 9.2 is a negative statement, a weaker `UsesPair` would only make it stronger.
- The docstring states the reliance on Prop 8.2(a) explicitly. Good.

## 2. Count.lean, line by line

**`edge_param_from` (25–33).** Takes an edge parametrization from `exists_param_of_isEdge`. Since `γ''[0,1] ∩ V = {γ 0, γ 1}` and `v` is a vertex in `ℓ`, either `γ 0 = v` or `γ 1 = v`; in the second case the proof reverses with `hγ.symm` and `image_symm_Icc`. Correct.

**`tip_strictMono` (36–42).** Prop 8.2(a) gives `InjOn (dist e) ℓ`. Composing with the injective `κ` on `[0,1]` gives a continuous injective function on `Icc 0 1`, which `strictMonoOn_of_injOn_Icc'` turns into a strict-mono-or-anti statement. Correct.

**`lemma_9_2` (46–203).** The statement is checked against the paper in the faithfulness table below. The proof:

- *Radial monotonicity* (59–64). With `κ, κ'` starting at `v`, `φ = h_v∘κ` and `ψ = h_v∘κ'` are monotone on `[0,1]` by `lemma_4_3` (Lemma 4.3). Also `φ 0 = ψ 0 = 0` and `φ 1, ψ 1 > 0` (the far ends differ from `v`). This matches the paper's `R = min{h_v(u), h_v(u')} > 0`.
- *Avoiding flat levels* (66–84). `C` is the set of local-extremum values of `φ` and of `ψ`, as functions `ℝ → ℝ`. It is countable by `lemma_2_8_i`, which holds for an arbitrary `g : ℝ → ℝ` (Extrema.lean:97). The key fact is `huniq`: if `f` is monotone on `[0,1]` and `f t = f t' = ρ` with `t < t'` in `[0,1]`, then `f ≡ ρ` on `[t,t']`. The midpoint then has the neighbourhood `Ioo t t'` in `ℝ` on which `f` is constant, so it is an `IsLocalMin` on `ℝ`, and `ρ ∈ C`. Hence any `ρ ∉ C` has at most one preimage in `[0,1]`.
  - This is sound. It replaces the paper's "nondegenerate levels are disjoint arcs, hence countably many" with "nondegenerate levels have local-extremum values". The avoided set is a superset of the paper's, still countable, and the conclusion is the same. The argument correctly takes `IsLocalExtr` on all of `ℝ`, which works because the witness is an interior point of `[t,t']`.
- *Choosing ρₙ* (86–103). `ρ n ∈ (0, min(min(φ1,ψ1), 1/(n+1))) \ C`, obtained from `exists_mem_Ioo_notMem` (a countable set misses every nonempty open interval). The IVT on `Ioo` gives `t n, s n ∈ (0,1)` with `φ(t n) = ψ(s n) = ρ n`, so the points lie in the open edges, as in the paper.
- *aₙ → v* (104–108). `dist (κ(t n)) v = φ(t n) = ρ n ≤ 1/(n+1)`, followed by a squeeze. This is exactly "h_v(a_k) = ρ_k → 0 ⇒ a_k → v": `h_v` *is* the distance to `v`, so no compactness or limit-point argument is needed. It is more direct than the paper and correct. (`bₙ → v` is never needed and is not proved.)
- *Open-edge bookkeeping* (110–117). `κ t ∉ V` for `t ∈ (0,1)`, and `ℓ = closure (cc(κ t))` by `edge_eq_closure_cc`, and likewise for `ℓ'`. These supply exactly the hypotheses of `prop_8_2_b`.
- *e-matching* (`hmatch`, 119–187). For a tip `e` that uses the pair:
  - `h_e(u') ≠ h_e(v)` follows from injectivity (124–128), and `h_e(aₙ) ≠ h_e(v)` from `t n > 0` (136–139).
  - Continuity gives `h_e(aₙ) → h_e(v)`, so eventually `|h_e(aₙ) − h_e(v)| < |h_e(u') − h_e(v)|`.
  - Applying `UsesPair` to `(aₙ, u')` puts `h_e(aₙ)` on the same side of `h_e(v)` as `h_e(u')`, hence strictly between `h_e(κ' 0)` and `h_e(κ' 1)` (144–160). Both cases are checked and correct.
  - The IVT then gives `σ ∈ [0,1]` with `h_e(κ' σ) = h_e(aₙ)`. Strictness excludes `σ ∈ {0,1}` (161–177).
  - This is the paper's "for a close enough to v, h_e(a) lies strictly between h_e(v) and h_e(u′)". The paper's uniqueness of `μ_e(a)` is not needed and is not used. That is fine.
- *Use of Prop 8.2(b)* (179–183). The hypotheses are discharged as follows:
  - `aₙ, κ'σ ∉ V`.
  - Distinct components: equal components would give `ℓ = ℓ'` through the closures.
  - `v` lies in both closures, since they equal `ℓ` and `ℓ'`.
  - `htie` holds.
  
  The conclusion `h_v(aₙ) = h_v(κ'σ)` matches the paper's "μ_e preserves the radial level". The statement of `prop_8_2_b` (Tips.lean:450–456) is exactly the paper's 8.2(b).
- *Forcing μ_e(aₙ) = bₙ* (184–187). `ψ σ = ρ n = ψ(s n)`, and `ρ n ∉ C`, so `σ = s n` by `huniq`. Hence `h_e(aₙ) = h_e(bₙ)`.
- *Contradiction* (188–203). The two eventual statements for `e` and `e'` have a common `n`. Then:
  - `aₙ ≠ bₙ`, because `ℓ ∩ ℓ' ⊆ V` (`edge_inter_subset`) and `aₙ ∉ V`.
  - `v, e, e'` all lie in `M(aₙ,bₙ)`.
  - The three points are pairwise distinct: `v ≠ e, e'` by order (≥3 vs 1), and `e ≠ e'` by hypothesis.
  
  So `|M| ≥ 3`, contradicting `|M| ≤ 2` (`false_of_three`, `three_le_encard_midset`). This is the paper's final line.

**`choose_bound` (206–208).** For `m ∈ {3,4}` and `k ≤ m`, `m−2 ≤ C(k,2)+C(m−k,2)`. Checked by exhaustive `decide`. Hand check: m=3 gives values 3,1,1,3 (all ≥ 1); m=4 gives 6,3,2,3,6 (all ≥ 2).

**`tip_direction` (211–223).** On every edge at the vertex `v`, either `h_e(v) < h_e(a)` for all `a ≠ v`, or `h_e(a) < h_e(v)` for all `a ≠ v`. This follows from `tip_strictMono` after parametrizing from `v`. Correct, and it is the Lean form of the sentence "By Prop 8.2(a) ... strictly increasing or strictly decreasing" in Def 9.1.

**`edge_from_vertex` (226–238).** From `edge_isArc`, `ℓ = seg a b` with `ℓ ∩ V = {a,b}`. The proof reorients so that `ℓ = seg v c` with `c ≠ v`, using `seg_symm`. Correct.

**`triod_structure` (242–398).**
- *Per branch point* (`htips`, 251–341):
  - `3 ≤ deg v ≤ 4` comes from `IsBranchPoint` and `lemma_4_4` (paper Lemma "Order at most four", `lem:order`), via `order_eq_degree`.
  - `Ev` is the Finset of edges at `v`, with `|Ev| = deg v` (`degree_eq_card`). `P` is its set of 2-subsets, and `used e ⊆ P` is the set of pairs that `e` uses.
  - `hdisj`: the `used e` are pairwise disjoint over the tips, by `lemma_9_2` (the paper cites Lemma 9.2).
  - `hlb`: split `Ev = I ⊔ D` into increasing and non-increasing edges. Non-increasing means decreasing, by `tip_direction`. Every 2-subset of `I` and every 2-subset of `D` is used, and the two families are disjoint. So `|used e| ≥ C(k,2)+C(m−k,2) ≥ m−2`, which is the paper's count.
  - `hsum`: `Σ |used e| ≤ |P| = C(m,2)` (card of the `biUnion` of disjoint sets).
  - Hence `t·(m−2) ≤ C(m,2)`: for m=3, `t ≤ 3`; for m=4, `2t ≤ 6`. So `t ≤ 3`, as in the paper.
- *Tip formula* (345–358). `tips_formula` (Edges.lean:308) is exactly (2.1): `t = 2 + Σ_{u∈B}(deg u − 2)`. Splitting off `v` and bounding each other term by ≥1 gives `(deg v − 2) + (|B|−1) ≤ t − 2 ≤ 1`, with `deg v ≥ 3`, so `deg v = 3`, `|B| = 1` and `t = 3`. The paper instead says "t ≥ m, so m = 3, then t = 2 + |B| ≤ 3". That argument is equivalent; the Lean one combines both steps in a single `omega`. Natural-number subtraction is safe because `deg u ≥ 3` for all `u ∈ B`.
- *Edges* (360–398). `branchSet = {v}`. The vertices are tips ⊔ branch points, so `|V| = 3 + 1 = 4`, and `ncard_edges_add_one` gives `|E| = 3`. The edges at `v` number `order v = 3` (`order_eq_encard_edges`) and form a subset of `E`, so they are all of `E`. That yields three distinct edges, each containing `v`. Correct. This content goes beyond the paper's sentence "that is, T is a simple triod", and it is needed.

**`prop_9_3` (402–419).** The construction checks out:
- Each `ℓᵢ = seg v cᵢ` with `cᵢ ≠ v`, so `IsArcBetween ℓᵢ v cᵢ` by `seg_isArcBetween`.
- Pairwise, `ℓᵢ ∩ ℓⱼ` is a subsingleton (`edge_inter_subsingleton`) containing `v`, so it is `{v}`.
- `univ = ⋃₀ E = ℓ₁ ∪ ℓ₂ ∪ ℓ₃` by `sUnion_edges` (with reassociation).

This matches `IsSimpleTriod` (Defs.lean:79–81): three arcs with common end `v`, pairwise meeting only in `v`, whose union is the set. That is the paper's definition at line 186. The ends `pᵢ` are automatically distinct from `v` and from each other (embedding injectivity plus the `{v}` intersections), so the definition is not degenerate.

## Blockers

None.

## Major

None.

## Minor

1. **Redundant hypothesis.** `lemma_9_2` takes `hbr : ∃ v, IsBranchPoint v` alongside `hv : IsBranchPoint v` (Count.lean:46). `hbr` follows from `hv`. It is harmless and mirrors the "Let T be branched" in the paper and the signature of `prop_8_2_*`.
2. **No packaged equivalence lemma.** There is no lemma of the form `UsesPair e v ℓ ℓ' ↔ (inc ℓ ∧ inc ℓ') ∨ (dec ℓ ∧ dec ℓ')` (under DMP, a tip, and edges at `v`). Both directions are proved inline (Count.lean:142–160 and 299–316), so this is only a transparency suggestion for readers comparing against Def 9.1.
3. **Dead code.** In `triod_structure`, `hm1`, `hm2`, `hm3'` (Count.lean:395–397) are never used, since `hmem` is returned directly.
4. **Fragile rewrite.** `rw [Finset.card_powersetCard, hEv, smul_eq_mul] at *` (Count.lean:335) rewrites across the whole context. It works, but it could break easily under Mathlib changes.
5. **Deprecations.** `push_neg` (l.149) should become `push Not`, and `Set.mem_setOf_eq` (l.370) should become `Set.mem_ofPred_eq`.
6. **Docstring nit.** The paper's Lemma 9.2 leaves the DMP implicit through the standing convention (tex l.475); the Lean statement makes it explicit with `HasDMP T`. That is correct, but the docstring could mention it.

## Faithfulness table

| Paper item | Lean | Location | Faithful? |
|---|---|---|---|
| Def 9.1: e uses {ℓ,ℓ′} at v iff h_e has the same direction on ℓ and ℓ′ away from v | `UsesPair e v ℓ ℓ'` (intrinsic iff on `h_e(v) < h_e(·)`) | Defs.lean:173–174 | Yes, given Prop 8.2(a) (`tip_direction`, Count.lean:211) |
| Def 9.1 preamble: on each edge at v, h_e is strictly increasing or decreasing | `tip_direction`, `tip_strictMono` | Count.lean:211, 36 | Yes |
| Lemma 9.2 hypotheses: T branched (with the DMP), v a branch point, ℓ ≠ ℓ′ edges at v, e ≠ e′ tips | `hDMP`, `hbr`, `hv`, `hℓ hℓ' hvℓ hvℓ' hne`, `he he' hee'` | Count.lean:46–48 | Yes (hbr redundant) |
| Lemma 9.2 conclusion: the pair is not used by both | `¬ (UsesPair e v ℓ ℓ' ∧ UsesPair e' v ℓ ℓ')` | Count.lean:49 | Yes |
| Lemma 4.3 radial monotonicity | `lemma_4_3` | Count.lean:59–60 | Yes |
| Countably many flat levels; ρₖ → 0 avoiding them | `C` of local-extremum values via `lemma_2_8_i`; `huniq`; `ρ n < 1/(n+1)` | Count.lean:66–89 | Yes (superset of the paper's set, still countable) |
| a_k → v | squeeze on `dist = ρ n` | Count.lean:104–108 | Yes |
| e-matching, Prop 8.2(b) | `hmatch` using `prop_8_2_b` | Count.lean:119–187 | Yes |
| M(a_k,b_k) ⊇ {v,e,e′} gives a contradiction | `false_of_three` / `three_le_encard_midset` | Count.lean:188–203 | Yes |
| Prop 9.3: m ∈ {3,4} | `lemma_4_4`, `IsBranchPoint` | Count.lean:255–258 | Yes |
| Each tip uses C(k,2)+C(m−k,2) ≥ m−2 pairs | `hlb`, `choose_bound` | Count.lean:286–330, 206 | Yes |
| Pairs used disjointly, ≤ C(m,2), so t ≤ 3 | `hdisj`, `hsum`, case split | Count.lean:269–341 | Yes |
| (2.1) gives m = 3 and \|B\| = 1, t = 3 | `tips_formula`, `omega` | Count.lean:345–358 | Yes (equivalent arithmetic) |
| "that is, T is a simple triod" | `triod_structure` (3 edges, all at v) + `prop_9_3` construction | Count.lean:242–398, 402–419 | Yes |
| Prop 9.3 statement: a branched finite tree with the DMP is a simple triod | `prop_9_3 (hDMP) (hbr) : IsSimpleTriod (univ : Set T)` under `TreeHyp T` + instances | Count.lean:402–403 | Yes |
| Simple triod (tex l.186) | `IsSimpleTriod` | Defs.lean:79–81 | Yes |
