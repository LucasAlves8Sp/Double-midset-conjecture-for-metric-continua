# Review 09: Sections 10 (simple triod) and 11 (arc)

Reviewer: independent, no prior context. No `.lean` file was modified.

Files: `DoubleMidset/Triod.lean` (396 lines) and `DoubleMidset/ArcCase.lean` (298 lines), read line by line.
Paper: `dmp_paper_2.tex`, Theorem 10.1 (lines ~940-984) and Theorem 11.1 (lines ~985-1032).

## Verdict: ACCEPT WITH MINOR

There are no blockers and no major issues. Both theorems are proved in full. The Lean proofs follow the paper's proofs closely, and in a few places they are slightly tighter. The minor items below are about presentation, plus one note on assembly that belongs to a later stage.

## Mechanical checks

- **Build.** `b.sh DoubleMidset` reports `Build completed successfully (2188 jobs)`. There are no errors. There are 234 warnings in total. The ones in these two files are deprecations only (`Set.mem_setOf_eq`, `push_neg`) plus one unused-section-variable warning at `Triod.lean:180`.
- **Forbidden keywords.** `grep -rnwE "sorry|admit|axiom|native_decide|unsafe|implemented_by|opaque|extern"` over `DoubleMidset/` and `DoubleMidset.lean` finds nothing.
- **Axioms.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:
  - `not_hasDMP_of_branched`
  - `not_hasDMP_of_unbranched`
  - `column_even`
  - `row_lemma`
- **Statements:**
  - `not_hasDMP_of_branched : TreeHyp T → (∃ v, IsBranchPoint v) → ¬ HasDMP T`
  - `not_hasDMP_of_unbranched : TreeHyp T → (∀ v, ¬ IsBranchPoint v) → ¬ HasDMP T`
  - Both carry the standing instances `[MetricSpace T] [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T]`.
  - `HasDMP T` means `∀ a ≠ b, (midset a b).encard = 2`, with `midset a b = {x | dist x a = dist x b}`.

## Faithfulness of the statements

- **10.1 in tree form.** The paper states 10.1 for "a compatible metric on a simple triod". Lean instead states it for any branched finite tree. The proof first calls `triod_structure` (Prop 9.3's content: a unique branch point `v` of degree 3, and exactly three edges ℓ₁, ℓ₂, ℓ₃, all containing `v`) and then runs the 10.1 argument. So the Lean theorem is Prop 9.3 and Theorem 10.1 combined. That combination is exactly how the paper uses them in the proof of Theorem B (line ~1035: "If T has a branch point, it is a simple triod by Prop 9.3, which is impossible by Theorem 10.1"). A simple triod with a compatible metric is a branched finite tree, so the paper's 10.1 follows from the Lean statement. Nothing in the paper's proof is lost.
- **11.1 in tree form.** The paper states 11.1 for "a compatible metric on an arc". Lean states it for an unbranched finite tree. `arc_structure` (ArcCase.lean:24-53) shows that such a tree is a single edge `γ''[0,1] = univ` whose two ends are tips, with `oddVertices = {γ 0, γ 1}`. It uses `tips_formula` (no branch points gives 2 tips) and `ncard_edges_add_one` (2 vertices gives 1 edge). This matches the "Otherwise T is an arc" branch of Theorem B.
- **Hypotheses of the cited lemmas.** The paper notes that the lemmas used in 11.1 need no branch point. This is reflected in Lean: `cor_6_7` and `lemma_7_3` take no `∃ v, IsBranchPoint v` hypothesis. In 10.1, `hbr` is needed only for `tip_strictMono`, `prop_8_2_a` and `lemma_9_2` (Prop 8.2 and Lemma 9.2), as in the paper.
- **Assembly note (informational, not a defect here).** Theorem B (`¬ HasDMP` for every `TreeHyp T`) is not yet put together anywhere. Nothing imports `ArcCase` except the root `DoubleMidset.lean`, and `CHECKPOINT.md:46,50` lists a planned `Main.lean`. It is a one-line `by_cases` on `∃ v, IsBranchPoint v` combining the two theorems reviewed here. It should be checked in the review of `Main.lean`.

## Theorem 10.1 (`Triod.lean`)

**The direction table.** The table entry (i, j) is ↓ exactly when D(i, j) holds, where D(i, j) := `dist cᵢ cⱼ < dist cᵢ v` ("h_{eᵢ}(eⱼ) < h_{eᵢ}(v)"). By `tip_strictMono` (from Prop 8.2(a)), each h_{eᵢ} is strictly monotone or strictly antitone along the leg parametrisation κⱼ, with κⱼ 0 = v and κⱼ 1 = cⱼ. So comparing the two endpoints determines the direction. This equivalence is made explicit in:
- `sign_tip_leg` (L160-176): the sign of f_{κ tp, κ tq} at a tip is negative iff ¬D.
- `uses_of_same` (L111-157): same D-value on two legs implies `UsesPair`.

`strict` (L358-367) upgrades ¬D to a strict reverse inequality. It does this by injectivity of h_e on an edge (`prop_8_2_a`): equality would force κ 0 = κ 1. The diagonal entries are ↓ by `diag` (L355). The encoding is faithful.

**Leg setup** (L240-302):
- `hleg` builds, for each leg, a tip `c`, an edge parametrisation from `v` to `c`, and `ℓ ∩ vertices = {v, c}`.
- `hV` shows `vertices T = {v, c₁, c₂, c₃}`, because every point lies on one of the three edges (`sUnion_edges`, `hE`).
- `hOdd` shows all four vertices are odd, using `degree v = 3` and `order = 1` at the tips. This is what makes "v is counted" in step (ii) correct.
- The tips are distinct because `seg v cᵢ = ℓᵢ` and the legs are distinct.
- `hvt` gives `v ≠` any tip, since the orders differ.

**Step (i), `row_lemma` (L213-234).** Suppose tip `e` has three ↓. The proof takes any other tip `e'`. By pigeonhole (two `by_cases` and a final `tauto`), `e'` has the same direction on some pair of legs. `e` uses every pair, so both tips use that pair, which contradicts `lemma_9_2` (Lemma 9.2). The paper phrases this as "e uses all three pairs, so nothing is left for the other two tips". Lean uses only one other tip. The argument is equivalent and slightly more economical.

**Step (ii), `column_even` (L33-108) and `hcolumn` (L304-339):**
- The points p = κ tp and q = κ tq are interior points of the leg. `hcolumn` picks them by the intermediate value theorem at levels h_v = φ(1)/3 and 2φ(1)/3. Monotonicity of h_v (`lemma_4_3`, Lemma 4.3 radial) gives tp < tq. This realises the paper's "there are edge points p before q with h_v(p) < h_v(q)".
- **Strictness** (L45-54). For v, it follows from h_v(p) < h_v(q). For a tip, it follows from injectivity of `tip_strictMono` on [0,1]. All vertices are covered: `vertex_cases` uses `branchSet = {v}`.
- **Odd case** (L56-108):
  - `cor_6_7` (Cor 6.7) gives a centre c ∉ vertices, ρ > 0, and an open arc P ∋ p with P ⊆ S(c, ρ).
  - A small parameter interval [tp, tp+δ'] with tp+δ' < 1 maps into P, hence into the connected component K of the sphere through p.
  - `lemma_7_2` (Lemma 7.2, the crossing lemma) applied to K gives N(p, q') even, where q' = κ(tp+δ').
  - **v-sign.** Monotonicity (`lemma_4_3`) gives h_v(p) ≤ h_v(q'). Lemma 6.2(a) (`lemma_6_2 ... .1`, injectivity of `dist v` on the spherical arc κ''[tp, tp+δ']) makes the inequality strict. Its side conditions are discharged correctly: v ∉ arc because the arc sits in the open edge, and v ≠ c because c ∉ vertices.
  - **Tip signs.** These agree with those of (p, q) by `sub_neg_iff_of_strictMono`.
  - So `oddCount p q' = oddCount p q`, which is odd and even at once: contradiction.
  - This is exactly the paper's argument, with p' = p and q' close to p.
- **Column conclusion.** `count_four` (L180-210) shows: in an even count over {v, cⱼ, a, b}, if v is counted and cⱼ is not, then exactly one of a, b is counted. `cⱼ` is not counted because κ 1 = cⱼ, so D(j, j) holds, and `sign_tip_leg` turns that into "not counted". The result is `D(a, j) ↔ ¬D(b, j)`, as in the paper.
- The three instances `col1`-`col3` (L340-344) use the correct permutations of {c₁, c₂, c₃}.

**Step (iii), the cycle (L381-394).** Instead of building the permutation, the proof splits on D(2,1):
- **Case D21.** col1 gives ¬D31. row2 gives ¬D23. col3 gives D13. row1 gives ¬D12. col2 gives D32. This is the cycle 2→1→3→2.
- **Case ¬D21.** The proof gets D31, ¬D32, D12, ¬D13, D23. This is the cycle 1→2→3→1.

In each case `linarith` closes a chain of six strict inequalities. For case 1:
r₂ > d(c₂,c₁) > r₁ > d(c₁,c₃) > r₃ > d(c₃,c₂) > r₂.
The `strict` facts and `dist_comm` are in context. I checked every step of both branches by hand against the col/row/diag lemmas. They are correct and they are exactly the paper's "i→j implies rᵢ > d(eᵢ,eⱼ) > rⱼ" argument.

## Theorem 11.1 (`ArcCase.lean`)

**Initial sites** (L80-128). Let D = d(γ0, γ1) > 0. The proof chooses ε ≤ 1/4 by continuity at 0 and at 1 with tolerance D/3, so that d(γε, γ0) < D/3 and d(γ(1-ε), γ1) < D/3. The triangle inequality then gives f(γ0) < 0 < f(γ1) for the pair (a, b) = (γε, γ(1-ε)). So the pair is strict (all vertices are γ0 or γ1) and N = 1. This is the paper's "a near 0, b near 1".

`cor_6_7` gives:
- a centre x ∉ vertices, written x = γξ with ξ ∈ (0,1) via `mem_Ioo`;
- a radius r > 0;
- open arcs U ∋ a and V ∋ b with U ∪ V ⊆ Σ.

γξ ∉ Σ because r > 0.

**Good points** (L134-135).
- GL s: ∃ σ < s < σ' with 0 < σ, σ' < ξ, and γ''[σ, σ'] ⊆ Σ.
- GR s: the same on (ξ, 1).

These are exactly "s is interior to a nondegenerate arc in Σ ∩ (0,x)", resp. (x,1). `good_of_open` (L58-69) is a correct helper: a point of an open set, inside a parameter window, is interior to a small parameter interval mapped into the set.

**Step 1** (L140-175). It applies `lemma_7_3` (Lemma 7.3, e = 1) with σ < σ' < ξ < 1. Then:
- (b) gives b ∈ Z with h₁(b) = h₁(a).
- (c) gives Z ⊆ Σ ∩ γ(ξ,1), and Z is open, so `good_of_open` yields GR.
- (c) also gives M(a,b) = {γ1, γξ}. So f_{a,b} has no zero on γ[0, s]: injectivity with s < ξ < 1.
- `const_sign` together with f(a) = -d(a,b) < 0 gives h₀(a) < h₀(b).

This matches the paper.

**Step 2** (L177-194). It applies `lemma_7_3` to the reversed parametrisation t ↦ γ(1-t). Its tip `k 1 = γ 0` is discharged with `simpa using h0`. The parameters σ ↦ 1-σ, σ' ↦ 1-σ', ξ ↦ 1-ξ satisfy the order constraints. The sphere centre `k(1-ξ) = γξ` is handled through `image_symm_Icc`. The point a' = γ(1-t') with t' ∈ (1-ξ, 1) gives 1-t' ∈ (0, ξ). The interval is transported back correctly, and the inequalities 0 < 1-σ₂ < 1-t' < 1-σ₁ < ξ are checked. The conclusion h₀(a') = h₀(b) is correct.

**Start** (L196-205). ε ≠ ξ because γε ∈ Σ and γξ ∉ Σ.
- If ε < ξ, U gives GL ε directly.
- Otherwise ξ < ε < 1-ε, so V gives GR(1-ε), and Step 2 gives GL.

This is the paper's "either a < x, or x < a < b".

**Iteration** (L208-223). `choose!` turns Steps 1 and 2 into functions gR and gL, and `seq` is defined by `Nat.rec`. The GL and GR invariants are proved by induction. The relations are:
- h₁(b_n) = h₁(a_n);
- A_n < B_n;
- A_{n+1} = B_n.

**Limit** (L225-296):
- A is monotone (`monotone_nat_of_le_succ`) and bounded above (compactness of T). By `tendsto_atTop_ciSup`, B_n - A_n = A_{n+1} - A_n → 0.
- `isCompact_univ.tendsto_subseq` on T × T gives a subsequence φ with (a_{φn}, b_{φn}) → (a₀, b₀).
- Closedness of Σ, γ''[0,ξ] and γ''[ξ,1] places a₀ = γta and b₀ = γtb. Since γξ ∉ Σ, ta < ξ < tb, so a₀ ≠ b₀.
- Continuity gives h₁(a₀) = h₁(b₀) and h₀(a₀) = h₀(b₀), the latter by uniqueness of limits applied to B - A. Both points are on Σ, so h_x(a₀) = h_x(b₀).
- γ0, γ1 and γξ are pairwise distinct. `three_le_encard_midset` and `false_of_three` give the contradiction.
- The paper's side remark "a_* ≠ 0, b_* ≠ 1" is correctly not needed. Membership in the midset needs only a₀ ≠ b₀ and the three distance equalities. Lean omits that step, which is harmless.

## Blockers

None.

## Major

None.

## Minor

1. **Undocumented inequality chain** (`Triod.lean:381-394`). Step (iii) is done as a direct case split with `linarith`. The "fixed-point-free permutation, hence a 3-cycle" reasoning of the paper is not spelled out. It is mathematically equivalent, but a comment naming the two cycles (2→1→3→2 and 1→2→3→1) would help readers.
2. **Redundant hypothesis** (`Triod.lean:33`). `column_even` takes both `hbr` and `hB : branchSet T = {v}`. The first follows from the second. This is harmless, since `hbr` is just passed on to `tip_strictMono`.
3. **Missing docstring** (`Triod.lean:26`). `vertex_cases` has no docstring.
4. **Unused-variable warning** (`Triod.lean:180`). `count_four` triggers the "automatically included section variable(s) unused" warning. The `omit ... in` at L178 does not remove `[MetricSpace T]`, which is used, so this is only noise.
5. **Deprecation warnings** (`Triod.lean:97,187,201,319`; `ArcCase.lean:33,118,170`): `Set.mem_setOf_eq` and `push_neg`. Cosmetic.
6. **Theorem B not yet assembled** (informational). See the faithfulness notes above. The combination of the two theorems is not in the code base yet (`CHECKPOINT.md` plans `Main.lean`).

## Faithfulness summary (paper to Lean)

| Paper | Lean |
|---|---|
| Prop 9.3 (reduction to the triod) | `triod_structure` (Count.lean), used at `Triod.lean:240` |
| Prop 8.2(a) (tip distances strictly monotone) | `tip_strictMono`, `prop_8_2_a` (`Triod.lean:49,103,122,148,166,364`) |
| Lemma 4.3 (radial monotonicity) | `lemma_4_3` (`Triod.lean:83,317`) |
| Cor 6.7 (`cor:oddpair`) | `cor_6_7` (`Triod.lean:59`, `ArcCase.lean:128`) |
| Lemma 6.2(a) | `lemma_6_2 … .1` (`Triod.lean:92`) |
| Lemma 7.2 (crossing) | `lemma_7_2` (`Triod.lean:76`) |
| Lemma 7.3 (matching) | `lemma_7_3` (`ArcCase.lean:144`, reversed at `ArcCase.lean:182`) |
| Lemma 9.2 (pairs) | `lemma_9_2` (`Triod.lean:227`) |
| 10.1 step (i) | `row_lemma` (`Triod.lean:213`) |
| 10.1 step (ii) | `column_even`, `hcolumn`, `count_four` (`Triod.lean:33,304,180`) |
| 10.1 step (iii) | `Triod.lean:381-394` |
| 11.1 "A sphere" paragraph | `ArcCase.lean:80-132` |
| 11.1 Steps 1 and 2 | `ArcCase.lean:140-194` |
| 11.1 Iteration | `ArcCase.lean:196-223` |
| 11.1 Limit | `ArcCase.lean:225-296` |
