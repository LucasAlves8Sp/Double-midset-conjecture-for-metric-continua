# Final independent comparison: paper vs. `Challenge.lean`

Paper: `/mnt/user-data/uploads/727504a7-dmp_paper_2.tex`, "Continua with the double midset property are simple closed curves" (1124 lines, read in full).
Formal surface: `/home/claude/dmp/lean/Challenge.lean`: 21 definitions and 47 theorems.

Checks made by the auditor:
* Every `def` block in `Challenge.lean` occurs verbatim in `DoubleMidset/Defs.lean` (checked by script).
* `comparator.json` lists exactly the 47 theorem names. The permitted axioms are `propext`, `Quot.sound` and `Classical.choice`, and nanoda is enabled.
* `Solution.lean` has 47 theorems, and `DoubleMidset/` and `Solution.lean` contain no `sorry`.
* Mathlib's `Circle` is `Submonoid.unitSphere ℂ` with the subtype metric from `ℂ`, so it is the Euclidean unit circle.
* amsart does not number equations within sections here, so the paper's displayed equations are numbered (1)–(7) throughout.

## 1. Summary verdict

**The formalization is faithful.** Theorems A, B and C are each stated faithfully or slightly more strongly:
* Theorem A in both its directions and its "if and only if" form (`theorem_A`, `circle_hasDMP`, `theorem_A_iff`).
* Theorem B, including "in particular, neither an arc nor a simple triod".
* Theorem C, including the bound `|B| ≤ 4` and the finite-tree conclusion.

`theorem_A` is the main statement. It uses only Mathlib notions plus `midset`/`HasDMP`, which are transparent one-liners, so its meaning does not depend on any of the custom tree definitions.

The 47 statements break down as:
* 34 faithful;
* 12 stronger: they drop hypotheses or give a stronger uniqueness or openness claim;
* 1 weaker: `eq_5_2` gives only the parity form of the displayed identity (5).

No statement is "different", and I found no vacuity defect in the definitions. Coverage of the in-scope numbered results is complete. Only some trivial displayed facts and remarks made in passing have no standalone counterpart (Section 5). The issues I found are minor or cosmetic (Section 6).

## 2. Definitions

| Lean definition | Paper definition | Verdict / notes |
|---|---|---|
| `midset a b` | M(a,b) = {x : d(x,a)=d(x,b)} (l. 62–65, Def 2.1) | Faithful. |
| `HasDMP` | DMP: \|M(a,b)\|=2 for all a≠b (l. 66) | Faithful. `encard = 2` in `ℕ∞` means exactly two points, so finiteness is included. |
| `MidsetsAtMostTwo` | "≤2" hypothesis (l. 150, Conv 4.1) | Faithful (`encard ≤ 2`). |
| `sgnf a b y` | f_{a,b}(y)=d(y,a)−d(y,b) (Def 2.1, l. 191) | Faithful. h_x is written `dist x`. S(x,r) and B(x,r) are Mathlib's `sphere` and `ball`. |
| `IsArc` | homeomorphic to [0,1] (l. 186) | Faithful. |
| `IsArcBetween A p q` | arc with ends p,q; notation [p,q] (D2) | Faithful. An embedding of [0,1] forces p≠q. |
| `IsSimpleClosedCurve` | homeomorphic to S¹ (l. 186) | Faithful (`Circle`, the unit circle in ℂ). |
| `IsSimpleTriod` | union of three arcs that pairwise meet only in a common end (l. 186) | Faithful. |
| `order p` | number of components of X∖{p} (l. 221) | Faithful, with one deviation: values are in `ℕ∞` (`encard`), so all infinite orders become `⊤`. This is harmless because the paper only distinguishes finite orders. It is defined for every space, not only dendrites. |
| `IsTip`, `IsBranchPoint` | order 1; order ≥3 (l. 221) | Faithful. |
| `IsContinuum` | nondegenerate compact connected metric(izable) space (l. 186) | Faithful. Topological version: `MetrizableSpace`. |
| `IsDendrite` | locally connected continuum containing no simple closed curve (l. 221) | Faithful. |
| `IsFiniteTree` | Def 2.6 (l. 244): dendrite, finitely many branch points, each of finite order | Faithful. |
| `vertices` | V = tips ∪ branch points (Def 2.6) | Faithful. |
| `oddVertices` | O = vertices of odd degree (Def 2.6) | Faithful (requires a finite odd order). |
| `IsOpenEdge` | open edge ℓ° (l. 255) | Deviation (intrinsic): defined as a component of T∖V. The paper states that "the open edges are the components of T∖V" (l. 255), so this is faithful for finite trees. `lemma_2_7` and `tree_facts` then prove the expected properties. |
| `IsEdge` | edge (Lemma 2.7) | Deviation (intrinsic): defined as the closure of an open edge, where the paper takes the arcs produced by an induction. `lemma_2_7` proves that each such closure is an arc between two distinct vertices containing no other vertex. This matches the paper's edges. |
| `IsOpenArc` | "open arc" (Lemma 2.8, Def 5.3, Def 6.4) | Faithful. It adds `IsOpen` in X, which is automatic for open arcs inside open edges (open edges are open). |
| `IsCrossing g y`, `IsTouch g y` | Def 5.3 (l. 517) | Faithful. Deviation: existential over an isolating open arc J inside an open edge, and it does not presuppose that g has finitely many zeros. The paper's "take a small J" gives the same answer for every isolating J, because the sides have constant sign. `J∖{y}` always has exactly two components, so neither condition is vacuous, and the two are mutually exclusive. |
| `IsStrictPair` | Def 5.2 (l. 500) | Faithful. |
| `oddCount a b` | N(a,b) (Def 5.2, l. 502) | Faithful under `IsFiniteTree`, where V is finite so `ncard` is the true count. It is defined for every pair, but used only for strict pairs. |
| `IsSphericalArc I x r` | Def 6.1 (l. 591) | Faithful: `IsArc` gives nondegeneracy and r>0. |
| `IsBox U V` | Def 6.4 (l. 630) | Faithful. Uses the pair (U,V) rather than the product U×V. |
| `IsOddBox` | Def 6.4 (l. 631) | Faithful. |
| `UsesPair e v ℓ ℓ'` | Def 9.1 (l. 918) | Deviation: "same direction" is encoded as "for all a∈ℓ∖{v}, a'∈ℓ'∖{v}: h_e(v)<h_e(a) ↔ h_e(v)<h_e(a')". "Distinct edges at v" goes into the hypotheses of `lemma_9_2`. Prop 8.2(a) makes h_e strictly monotone on each edge, and it holds under `lemma_9_2`'s hypotheses. Under that monotonicity this condition is equivalent to the paper's definition. |

## 3. Theorems

Verdicts: F = faithful, S = stronger, W = weaker, D = different.

| Lean name | Paper ref (line) | Verdict | Notes |
|---|---|---|---|
| `lemma_2_2_a` | Lemma 2.2(a) (l. 209) | S | Drops a≠b and a'≠b'. f_{a,b}(t)≠0 follows from the strict inequality. |
| `lemma_2_2_b` | Lemma 2.2(b) (l. 210) | F | Uses preconnected sets. "No midset point in two of the sets" is pairwise disjointness of `A i ∩ M`. Conclusion: `k ≤ encard M`. |
| `fact_2_3_D1` | Fact 2.3 (D1) (l. 226) | F | Arcwise connectedness of connected subsets, stated for distinct points. |
| `fact_2_3_D2` | (D2) (l. 227) | F | Intersections are preconnected (the paper's "connected" implicitly allows the empty set), and arcs with given ends are unique. Proved, not assumed. |
| `fact_2_3_D3` | (D3) (l. 228) | F | Subcontinuum means closed, preconnected and nontrivial. |
| `fact_2_3_D4` | (D4) (l. 229) | F | |
| `lemma_2_4` | Lemma 2.4 (l. 233) | F | All three claims: sides separate, order ≥2, triod centre has order ≥3. |
| `fact_2_5` | Fact 2.5 (l. 240) | F (consequence form) | Only "dendrite without branch points is an arc" is formalized. Moore's theorem is intentionally omitted. |
| `lemma_2_7` | Lemma 2.7 (l. 248) | F | Proved for the intrinsic edges: V finite; finitely many edges covering T; each edge is an arc between two distinct vertices whose vertex set is exactly its two ends; two edges meet in at most one point, which is a vertex (hence a common end); #edges + 1 = \|V\|; degree = #edges containing the vertex. |
| `tree_facts` | Paragraph after Lemma 2.7 and eq. (3) (l. 255–258) | F (partial coverage) | Covered: open edges are open; edge points have order 2; \|O\| is even; in a branched tree each edge contains a branch point (an end, by `lemma_2_7`); tip formula t = 2 + Σ(deg−2) (ℕ subtraction is safe since deg ≥ 3). Not stated: see Section 5. |
| `lemma_2_8_i` | Lemma 2.8(i) (l. 266) | S | Stated for an arbitrary g : ℝ → ℝ, with no continuity, and is still true. Applies to any open arc J by restriction, since local extrema at interior points are local. |
| `lemma_2_8_ii` | Lemma 2.8(ii) (l. 267) | F | Stated on (α,β) ⊂ ℝ. Meagre in ℝ is equivalent to meagre in the open interval. |
| `lemma_2_8_iii` | Lemma 2.8(iii) (l. 268) | F | |
| `lemma_2_9` | Lemma 2.9 (l. 278) | F | U and V are bounded open real intervals; the paper only says "nonempty open intervals". This is equivalent up to homeomorphism and is the case used. Connectedness, density and the sign dichotomy are all included. |
| `prop_3_1` | Prop 3.1 (l. 326) | F | |
| `prop_3_2` | Prop 3.2 (l. 359) | S | Drops "X is a continuum". This is still true: the proof uses no compactness or connectedness of X. |
| `cor_3_4` | Cor 3.4 (l. 370) | F | "Simple closed curve" here means X ≃ₜ Circle. |
| `lemma_4_2` | Lemma 4.2 (l. 386) | S | Needs only `IsDendrite`; Convention 4.1's ≤2 is dropped. Drops f(c)=0. The small diameter is given as `A i ⊆ ball c δ`. Also states that the arms pairwise meet in {c}. |
| `lemma_4_3` | Lemma 4.3 (l. 395) | F | α : ℝ → X is continuous and injective on [0,1]; this is equivalent to a parametrisation of an arc from c (extend by `projIcc`). Hypotheses: dendrite and ≤2. |
| `lemma_4_4` | Lemma 4.4 (l. 438) | F | |
| `theorem_4_5` | Thm 4.5 (l. 447) | F | Gives order v = m ∈ ℕ, B finite, (m−2)(\|B\|−1) ≤ m and \|B\| ≤ 4. The ℕ subtractions are safe because m ≥ 3 and v ∈ B. |
| `cor_4_6` | Cor 4.6 (l. 465) | F | |
| `eq_5_2` | eq. (5) (l. 513) | W | Only `Odd N(a,b) ↔ Odd N(b,a)`. The exact identity N(b,a) = \|O\| − N(a,b) is not stated. Only the parity is used later. |
| `lemma_5_4` | Lemma 5.4 (l. 544) | F | Holds for any finite tree, so it also applies to the subspace T' used in Lemma 7.1. Needs no DMP. |
| `cor_5_5` | Cor 5.5 (l. 561) | F | Gives: two edge-point zeros; an odd number of crossings on every arc from a to b (so at least one); N even ⇒ both zeros are crossings; N odd ⇒ one crossing and one touch. |
| `lemma_5_6` | Lemma 5.6 (l. 574) | F | "The touch" is any `t` with `IsTouch` (this forces t ∈ M). "Local extremum on the open edge" is `IsLocalExtrOn` on `connectedComponentIn Vᶜ a`. |
| `lemma_6_2` | Lemma 6.2 (l. 597) | S | Hypothesis is ≤2, not the DMP of Convention 5.1; this matches the dependency table (l. 163). (a): strictly monotone is stated as injective, which is equivalent for continuous functions on an arc. (b) uniqueness (constant h_{x'} ⇔ I ⊆ sphere x' r') and subarcs. (c) interior points are not vertices, and I lies in an edge. (d) countably many centres. |
| `lemma_6_3` | Lemma 6.3 (l. 618) | F | |
| `prop_6_5` | Prop 6.5 (l. 637) | F | Existence with r>0, plus uniqueness of c. |
| `lemma_6_6` | Lemma 6.6 (l. 655) | F | U₁ × V₁ is a (nonempty) box inside U × V. J is an open arc in an open edge. w is continuous on U₁ × V₁ with values in J that are touches. |
| `cor_6_7` | Cor 6.7 (l. 685) | S | All the paper's conclusions. Uniqueness of c is stronger: it holds for any open arcs U' ∋ a, V' ∋ b and any r'. |
| `lemma_7_1` | Lemma 7.1 (l. 700) | F | No branch hypothesis, as in the paper (it also applies to the arc). |
| `lemma_7_2` | Lemma 7.2 (l. 748) | F | K is a nontrivial component of S(x,r), x an edge point, r>0. "y ∈ (p,q)" is stated as y in every arc from p to q and y ≠ p, q. |
| `lemma_7_3` | Lemma 7.3 (l. 766) | F/S | The edge is parametrised by k with k(1) = e a tip. The order s<s'<x<e becomes 0<σ<σ'<ξ<1. (a) strict monotonicity, (b) Z open (in T, slightly stronger) and the matching property, (c) Z ⊆ S(x,r) ∩ (x,e) and M(p_z,z) = {e,x}. "Z need not be connected" is a caveat, not a claim. |
| `lemma_7_4` | Lemma 7.4 (l. 823) | F | |
| `lemma_8_1` | Lemma 8.1 (l. 844) | F | "Two open edges with a common end v" is encoded as v ∈ V lying in both closures, which is exactly a common end by `lemma_2_7`. |
| `prop_8_2_a` | Prop 8.2(a) (l. 900) | F | Strict monotonicity on each edge is stated as injectivity (equivalent). |
| `prop_8_2_b` | Prop 8.2(b) (l. 901) | F | "Branched" is supplied by `hv`. |
| `lemma_9_2` | Lemma 9.2 (l. 922) | F | Distinct edges ℓ ≠ ℓ' at v, tips e ≠ e'. See the `UsesPair` row in Section 2. |
| `prop_9_3` | Prop 9.3 (l. 932) | F | `IsSimpleTriod univ`. |
| `theorem_10_1` | Thm 10.1 (l. 942) | F | X is any metric space whose whole space is a simple triod, so the metric is automatically compatible. |
| `theorem_11_1` | Thm 11.1 (l. 987) | F | |
| `theorem_A` | Thm A, first sentence (l. 80); Conjecture 1.1 (l. 68) | F | Compact, connected, nontrivial metric space with the DMP ⇒ `Nonempty (X ≃ₜ Circle)`. The hypotheses are plain Mathlib plus `HasDMP`. |
| `circle_hasDMP` | Converse in the proof of Thm A (l. 1046) | F | Euclidean unit circle (Mathlib `Circle`, subtype metric of ℂ). |
| `theorem_A_iff` | Thm A, second sentence (l. 80) | F | For a topological continuum Y: some metric inducing `t` has the DMP ⇔ Y ≃ₜ Circle. |
| `theorem_B` | Thm B (l. 86) | F | Has all three conjuncts: finite tree, arc, simple triod. Quantifying over metric spaces whose topology is the given one is the same as "admits a compatible metric". |
| `theorem_C` | Thm C (l. 92) | F | Gives: order ≤ 4 everywhere; (m−2)(\|B\|−1) ≤ m for each branch point of order m; B finite; \|B\| ≤ 4 (unconditional, which is trivially true when B = ∅); finite tree. |

Standing conventions:
* **Convention 4.1** (dendrite with ≤2) is the pair `hX : IsDendrite X` and `h2 : MidsetsAtMostTwo X` in `lemma_4_3` through `cor_4_6` and `theorem_C`. `lemma_4_2` correctly uses only `IsDendrite`.
* **Convention 5.1** (finite tree with the DMP) is the pair `hT : IsFiniteTree T` and `hDMP : HasDMP T` in Sections 5–9. There are three justified relaxations:
  * `eq_5_2` and `lemma_5_4` use only `IsFiniteTree`; the paper's Lemma 5.4 is purely topological.
  * `lemma_6_2` uses ≤2, as in the dependency table.
* "Branched" appears as `hbr` or `hv` exactly where the paper requires it (7.4, 8.1, 8.2, 9.2, 9.3). It is absent from 7.1–7.3, which the paper says also apply to the arc.

## 4. Vacuity analysis

* **Main theorems are not vacuous.**
  * `theorem_A`: the hypotheses are satisfiable (`circle_hasDMP`), and the conclusion is a concrete homeomorphism to Mathlib's `Circle`.
  * `theorem_A_iff`: the right-hand side is satisfiable.
  * `theorem_B`: the arc and triod conjuncts use only `IsArc`/`IsSimpleTriod`. The finite-tree conjunct needs `IsFiniteTree` to be satisfiable, and it is: [0,1] with the usual metric is a dendrite with no branch points.
  * `theorem_C` and Section 4: the hypotheses are satisfiable. The paper's Section 13 example, a Euclidean four-armed star, has ≤2 and a branch point of order 4, so even the branch-point lemmas are non-vacuous.
* **The definitions do not make conclusions trivial.**
  * `order` counts the components of `{p}ᶜ` correctly.
  * `IsCrossing`/`IsTouch` each require `g y = 0`, an isolating open arc inside an open edge, and a sign condition across the two (always exactly two) components of `J∖{y}`.
  * `oddCount` uses `ncard`, which would read 0 on an infinite set, but V is finite under `IsFiniteTree`.
  * `UsesPair` could only become degenerate if there were ties h_e(a) = h_e(v), and these are excluded under the hypotheses of `lemma_9_2`.
* **Inherent vacuity (not a defect).** Every statement that assumes both `IsFiniteTree` and `HasDMP` has jointly unsatisfiable hypotheses, by `theorem_B` itself. This is unavoidable in a proof by contradiction and is equally true of the paper's Sections 5–11. Those lemmas therefore give structural, not semantic, assurance. The assurance that matters comes from `theorem_A`/`theorem_B`/`theorem_C`, which are non-vacuous as shown above.
* **No witness lemma.** The library does not contain an explicit non-vacuity witness such as "unitInterval is a finite tree". Adding one would document the third bullet of the first point formally (optional).

## 5. Coverage: paper items without a standalone formal counterpart

All numbered results and definitions in Sections 2–12 have counterparts. Out of scope by instruction: examples, figures, Remark 3.3, the Section 13 star example and Question 13.1. Conjecture 1.1 is covered by `theorem_A`. Fact 2.5 is formalized in consequence form only.

Items not stated as standalone formal statements:
1. Eq. (1) (l. 199): f_{a,b}(a) = −d(a,b) < 0 < f_{a,b}(b) and f_{b,a} = −f_{a,b}. Trivial.
2. Eq. (2) (l. 200): the Lipschitz bounds. Only their consequence, `lemma_2_2_a`, is stated.
3. The intermediate value principle (l. 202). Only used inside `lemma_2_2_b`.
4. Paragraph after Lemma 2.7 (l. 255):
   * "a small open arc around an edge point in its open edge is a neighbourhood of it in T". Only "open edges are open" is stated.
   * "ℓ° is the edge minus its two ends". Derivable from `lemma_2_7`, but not stated.
   * The degree sum Σ deg u = 2(\|V\|−1). An intermediate step; its consequence, eq. (3), is stated.
   * "Open edges are the components of T∖V" is definitional here.
5. Eq. (4) (l. 509), the sign convention. Definitional.
6. The claim at l. 512: "strictness is an open condition and N is locally constant on strict pairs". Not stated; it is used inside proofs.
7. The exact identity in eq. (5), N(b,a) = \|O\| − N(a,b). Only the parity form is stated.
8. The claim after Def 6.4 (l. 635): every strict odd pair of edge points lies in an odd box. Not standalone; its content is subsumed by `cor_6_7`.
9. Eqs. (6) and (7) (l. 864, 869), the proof stages S1–S5, and Steps 1–2 of Thm 11.1. These are proof-internal.

## 6. Issues, ranked by severity

No critical, major or moderate issues were found.

**Minor**
1. `eq_5_2` is weaker than the displayed eq. (5): only the parity equivalence is stated, not N(b,a) = \|O\| − N(a,b). This is acceptable because only the parity is used later.
2. `tree_facts`, branched-edge claim: it says "ℓ contains a branch point" rather than "an end of ℓ is a branch point". These are equivalent via `lemma_2_7` (ℓ ∩ V = ends), but the paper's wording is not mirrored literally.
3. Small coverage gaps in the paragraph after Lemma 2.7: the neighbourhood property of edge points and ℓ° = ℓ ∖ ends are not stated as standalone facts (Section 5, item 4).

**Cosmetic**
4. Two docstrings misnumber displayed equations. amsart numbers equations globally here (checked: no `\numberwithin`).
   * `tree_facts` calls the tip formula "(2.1)"; it is (3).
   * `eq_5_2` is called "Equation (5.2)"; it is (5). The name collides visually with Definition 5.2.
5. Several statements are stronger than the paper because they drop hypotheses the proof doesn't need, or strengthen uniqueness or openness:
   * hypotheses dropped: `prop_3_2` (no continuum hypothesis), `lemma_4_2` (no ≤2, no f(c)=0), `lemma_2_8_i` (no continuity), `lemma_2_2_a` (no a≠b), `lemma_6_2` (≤2 instead of DMP);
   * stronger conclusions: `cor_6_7` (uniqueness), `lemma_7_3` (Z open in T).
   These are all mathematically correct strengthenings and not defects, but a reader comparing text line by line should know about them.
6. Inherent vacuity of the Convention 5.1 lemmas (Section 4). Expected for a proof by contradiction; the main theorems are not vacuous.
