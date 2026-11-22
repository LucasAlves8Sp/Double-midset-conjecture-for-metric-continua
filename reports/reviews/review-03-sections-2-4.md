# Review 03: Reduction.lean, Extrema.lean, Branch.lean (Sections 2.1-2.4, 3, 4)

Reviewer: independent; no .lean file was modified. Paper read: Sections 1-4 of
`dmp_paper_2.tex` (lines 76-470), including all proofs in Sections 2.1-2.4, 3 and 4.

Result numbering (shared counter per section): Def 2.1 sign function, Lemma 2.2 protected signs,
Fact 2.3 dendrites, Lemma 2.4 separation, Fact 2.5 Moore, Def 2.6 finite tree, Lemma 2.7 tree
structure, Lemma 2.8 local extrema, Lemma 2.9 grid; Prop 3.1, Prop 3.2, Remark 3.3, Cor 3.4;
Convention 4.1, Lemmas 4.2-4.4, Theorem 4.5, Cor 4.6; Theorem C (Section 1).

## 0. Global checks

* **Build.** `/home/claude/dmp/b.sh DoubleMidset`: `Build completed successfully (2175 jobs)`,
  0 errors. The warnings in the three files are only deprecations (`push_neg`, `Set.diff_eq`,
  `if_pos`, `ENat.coe_toNat`, ...), unused section variables, and two unused hypotheses
  (`hE`, `hF` in `lemma_2_9`; see E-3).
* **Forbidden constructs.** I grepped `DoubleMidset/**` and `DoubleMidset.lean` for `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`, `opaque`, `implemented_by`, `extern`,
  `decide := true` and suspicious `set_option`s. **No matches.**
* **Axioms.** `/tmp/rv03/ax.lean` is a plain file with `import DoubleMidset`. Each of
  `boundary_bumping_open`, `prop_3_1`, `prop_3_2`, `cor_3_4`, `lemma_2_2_a`, `lemma_2_2_b`,
  `lemma_2_8_i/ii/iii`, `lemma_2_9`, `lemma_4_2`, `lemma_4_3`, `lemma_4_4`, `theorem_4_5`,
  `cor_4_6` and `theorem_C` depends only on **`[propext, Classical.choice, Quot.sound]`**.
* **Elaborated signatures.** I printed all of them with `#check` in the same file, so the
  auto-included section variables are visible. They are quoted where relevant below.
* **Probes** (`/tmp/rv03/probe.lean`, compiles with no errors):
  1. From `theorem_C` one derives `3 ≤ m` and the **integer** inequality
     `((m:ℤ) - 2) * ((ncard B : ℤ) - 1) ≤ m`. So the ℕ-subtraction loses nothing.
  2. The f-free form of Lemma 4.2 (arcs only, no sign condition) follows from `lemma_4_2` with
     `f := fun _ => 1`.

## 1. DoubleMidset/Reduction.lean

Findings:

* **R-1 MINOR (l. 63-66, `boundary_bumping_open`).** This is the open-set special case of Nadler
  Thm 5.6, not the general form ("for an arbitrary nonempty proper subset") listed in the paper's
  table of quoted results. The statement reads: `IsOpen U`, `U ≠ univ`, `x ∈ U`, then
  `(closure (connectedComponentIn U x) \ U).Nonempty`. Take `E = X \ U` as in the paper. Since
  `closure C ⊆ closure U`, a point of `closure C \ U` lies in `closure U \ U = ∂U = ∂E`, which is
  exactly what Prop 3.1 uses. So the form is adequate, and nothing external is assumed. It is
  *proved* from `Classical/Bump.lean`'s `boundary_bumping` (components of `cl U` meet
  `cl U \ U`), which is itself proved. The proof here: if `cl D ⊆ U` then `D` is closed, hence
  compact. A thickening `V` of `D` has `cl V ⊆ U`. The component of `cl V` at `x` must then lie in
  `D ⊆ V`, which contradicts `boundary_bumping` for `V`. Correct.
* **R-2 MINOR (Classical/Bump.lean l. 7, 20; outside the three files but imported here).** The
  docstrings call boundary bumping "Lemma 5.2" and mention "the article". In this paper 5.2 is
  Definition 5.2 (strict pairs), and boundary bumping is Nadler Thm 5.6. The labels are stale and
  only cosmetic.
* **R-3 info (l. 95-223, `prop_3_1` proof).** This is a valid variant of the paper's proof. The
  paper picks `p_n → p` outside `C` and passes to distinct components. The Lean proof instead
  shows (l. 133-155) that the family 𝒟 of components `≠ C` of `U = B(p, ε)` meeting `B(p, ε/4)`
  is infinite. If 𝒟 were finite, the union of their closures would be closed and would miss `p`,
  because components are relatively closed (l. 124-131). Then a ball around `p` would lie in
  `C ⊆ Q`, which contradicts the choice of `p`. The rest follows the paper: an injective
  enumeration, a boundary point `q_n` with `d(p, q_n) = ε`, a convergent subsequence, and the
  2-Lipschitz estimate. The estimate gives `f < 0` at a point within `ε/4` of `p` and `f > 0` at a
  point within `ε/2` of `q₀`, so each component has a zero, and disjointness gives infinitely many
  zeros. `ε = min r (d(p, y₀))` makes `U ≠ X`, as in the paper. Correct.
* **R-4 MINOR, harmless strengthening (l. 263, `prop_3_2`).** The signature is
  `[MetricSpace X] → MidsetsAtMostTwo X → IsSimpleClosedCurve C → C = univ`. There is no
  compactness or connectedness hypothesis, so the statement is stronger than the paper's (which
  assumes a continuum). The proof uses `exists_param` (a 1-periodic `c : ℝ → X`, injective on
  `[0,1)`) and `exists_eq_of_eq_ends` for two parameters `s < t` in `[0,1)` with
  `h_z(c s) = h_z(c t)`. IVT on `[s,t]` and on `[t,s+1]` then gives two zeros, distinct by
  injectivity (the case `u₂ ≥ 1` is handled at l. 313-316). These zeros and `z ∉ C` are three
  points of the midset. This is the paper's proof.
* **R-5 info (l. 323-335, `cor_3_4`).** `[CompactSpace] [ConnectedSpace] [Nontrivial]` plus
  `HasDMP` gives `Nonempty (X ≃ₜ Circle) ∨ IsDendrite X`. `IsDendrite` needs metrizability,
  which the instance supplies. Faithful.

No BLOCKER or MAJOR findings.

## 2. DoubleMidset/Extrema.lean

* **E-1 info (l. 37-44, `lemma_2_2_a`).** The hypothesis `dist a a' + dist b b' < |f_{a,b}(t)|`
  already forces `f_{a,b}(t) ≠ 0`, so the paper's "if `f(t) ≠ 0`" is implicit. The conclusion is
  stated separately for both signs. Faithful.
* **E-2 info (l. 49-67, `lemma_2_2_b`).** The sets are `A : Fin k → Set X`. The hypothesis is
  `IsPreconnected`, which is weaker than "connected" (nonemptiness follows anyway from the
  sign points). "No point of `M(a,b)` lies in two of them" is rendered as
  `Disjoint (A i ∩ M) (A j ∩ M)` for `i ≠ j`. The conclusion is `(k : ℕ∞) ≤ encard M`. Faithful,
  and marginally stronger.
* **Lemma 2.8, "local extremum".** Mathlib's `IsLocalExtr g s` is
  `IsMinFilter g (𝓝 s) s ∨ IsMaxFilter g (𝓝 s) s`, that is, `∀ᶠ y in 𝓝 s, g s ≤ g y` or
  `∀ᶠ y in 𝓝 s, g y ≤ g s`. This is non-strict, which **matches the paper's definition**
  ("non-strict extrema are included"). The neighbourhoods are taken in ℝ. Every use is at a point
  of an open interval, where this agrees with "local extremum in `J`".
* **E-3 info, stronger (l. 97, `lemma_2_8_i`).** It is stated for an arbitrary `g : ℝ → ℝ`, with
  no continuity and over all of ℝ. It implies the paper's (i): extend a function on `J` in any
  way; local extrema at points of the open set `J` do not change, and the value set for `J` is a
  subset. The proof does not need continuity: at a local min (max) `s`, `g s` is the `sInf`
  (`sSup`) of `g` over a rational interval around `s`, and that inf (sup) is attained. Correct.
* **E-4 info (l. 128-130, `lemma_2_8_ii`).** The hypotheses are `ContinuousOn g (Ioo α β)` and
  `∀ c < d, Ioo c d ⊆ Ioo α β → ∃ y z ∈ Ioo c d, g y ≠ g z`. This **is** "constant on no
  nondegenerate subinterval". Every nondegenerate subinterval contains a nondegenerate open
  subinterval, and the converse direction is trivial. The conclusion is
  `IsMeagre {s ∈ Ioo α β | IsLocalExtr g s}` in ℝ. For a subset of an open `J ⊆ ℝ`, meagre in ℝ
  is the same as meagre in `J`. The proof is the paper's: the level sets of the max or min on
  rational `[q₁,q₂] ⊆ J` are closed with empty interior. Faithful.
* **E-5 info (l. 185-197, `lemma_2_8_iii`).** Every neighbourhood `N` contains `s'` and `s''`
  with `g s' < g s < g s''`. Faithful.
* **E-6 MINOR, weaker in form (l. 210-216, `lemma_2_9`).** `U = Ioo a b` and `V = Ioo c d` with
  `a < b` and `c < d`, so the formal statement covers only **bounded** nonempty open intervals.
  The paper says "nonempty open intervals", which includes `(0,∞)` and ℝ. This is harmless in
  substance: every nonempty open interval is order-homeomorphic to a bounded one, the statement
  is invariant under such maps, and the paper applies the lemma to open arcs identified with
  `(0,1)`. Formally, though, the Lean statement does not literally cover unbounded intervals.
  * `E`, `F` meagre: Mathlib `IsMeagre` in ℝ, which is equivalent to meagre in `U` (`V`) for open
    `U` (`V`).
  * The conclusions are all present:
    * `IsConnected G` (which includes nonempty);
    * `U ×ˢ V ⊆ closure G`, which is density in `U × V` since `G ⊆ U × V`;
    * the sign dichotomy for `g` `ContinuousOn (U ×ˢ V)` with `g ≠ 0` on `G`.
  * The hypotheses `hE : E ⊆ U` and `hF : F ⊆ V` are never used (compiler warning). The result
    holds for any meagre `E`, `F`, so they are redundant but harmless.
  * The proof is the paper's grid argument: every point of `G` is joined to `(a₀, c₀)` by a
    cross of one retained vertical and one retained horizontal line. Density comes from Baire
    (`dense_of_mem_residual`), and the weak sign extends to `U × V` by continuity and density.
    Correct.
* **E-7 info.** `lemma_2_8_ii` and `lemma_2_9` have no downstream users in the project: they are
  needed only in Section 6, which is not formalized here. So their exact shapes are not checked
  by any use. Both are faithful as stand-alone statements; see E-6 for the bounded-interval point.

No BLOCKER or MAJOR findings.

## 3. DoubleMidset/Branch.lean

Section hypotheses (l. 34-35, 213): `[MetricSpace X] [CompactSpace X] [ConnectedSpace X]
[LocallyConnectedSpace X]`, `hD : ∀ C, ¬ IsSimpleClosedCurve C`, and, from l. 213,
`h2 : MidsetsAtMostTwo X`. This is Convention 4.1 without `Nontrivial`, which is a harmless
generalization. `lemma_4_2` does not take `h2`, correctly, since arms do not need it.

* **B-1 info (l. 61-117, `exists_arm`).** This builds a single arm. It takes `seg c y`
  parametrized from `c` and the open set `N = B(c, δ) ∩ Kᶜ ∩ (f⁻¹{0} \ {c})ᶜ` containing `c`. A
  short initial subarc `g[0,t] ⊆ N` is identified with `seg c (g t)` by uniqueness of arcs
  (`seg_eq hD`). The punctured arm is connected (`g '' Ioc 0 t`) and lies in the component of `y`,
  and since it carries no zero of `f`, `f` has constant sign on it. This is exactly the paper's
  proof. It only needs zeros *other than `c`* to be finite.
* **B-2 MINOR, harmless generalization (l. 119-131, `lemma_4_2`).**
  * The hypothesis is `(f ⁻¹' {0}).Finite`, with the paper's `f(c) = 0` dropped. This is
    harmless: the hypothesis is implied by the paper's, and if `f(c) ≠ 0` the conclusion is
    still true and still proved. The f-part is mandatory in Lean, but `f := 1` recovers the
    f-free first half of the lemma (probe 2).
  * "Arbitrarily small diameter" is `seg c (p i) ⊆ ball c δ` for arbitrary `δ > 0`, so the
    diameter is at most `2δ`. That is adequate.
  * `K` is compact with `c ∉ K`, the order hypothesis is `(k : ℕ∞) ≤ order c` with `k` finite,
    and each `seg c (p i)` is shown to be an arc with ends `c` and `p i` (`IsArcBetween`).
  * Punctured arms lie in pairwise distinct components (two conjuncts), pairwise intersections
    are exactly `{c}`, the arms are disjoint from `K`, and `f` has a constant strict sign on each
    punctured arm.

  This is everything the paper states.
* **B-3 info (l. 173-186, `three_le_of_arms`; l. 190-204, `three_le_of_three_arms`).** These are
  Lemma 2.2(b) specialised to the following situation:
  * two (or three) arms meeting only at `c`, where `f(c) ≠ 0`;
  * opposite signs at `c` and at the far end of each arm;
  * plus, for `three_le_of_arms`, a preconnected `K` disjoint from both arms that carries both
    signs.

  Correct.
* **B-4 info (l. 219-301, `core_move`).** This abstracts the perturbation step shared by Lemma
  4.3 and the claim in Theorem 4.5. Suppose `c` has order ≥ 3, `a = γ(s₀)` with `γ : ℝ → X`
  continuous, `d(c,a) = d(c,b)`, `a ≠ b`, and `s₀` is not a local extremum of `d(c, γ(·))`, with
  `K` compact and preconnected, `a, b ∈ K` and `c ∉ K`. Then we get a contradiction.
  * The proof takes three arms disjoint from `K` (Lemma 4.2 with `f = f_{a,b}`, `δ = 1`) and two
    of them with the same end sign `η`.
  * It then moves `a` along `γ` within `ε₀ = min(|f(p_i)|, |f(p_j)|, d(a,b))` so that
    `η · f_{a',b}(c) < 0` (Lemma 2.8(iii)). The test signs survive (Lemma 2.2(a)).
  * Finally `f_{a',b}(a) < 0 < f_{a',b}(b)` on `K`, and three zeros follow.

  This is the paper's sign table. The abstraction is sound:
  * `a'` need not lie on `K`. Only `a, b ∈ K` is used for the sign change on `K`.
  * Non-extremality is taken over ℝ, which is what makes `a'` exist. Every caller applies it at
    an interior parameter, or uses a non-extremal value over ℝ obtained from `lemma_2_8_i`.
* **B-5 info (l. 306-338, `lemma_4_3`).**
  * The arc is given as `IsArcParam α` (`Continuous α` on ℝ, `InjOn α (Icc 0 1)`) with
    `α 0 = c`. This is equivalent to the paper's `α : [0,1] → A`, because every such map extends
    via `projIcc`.
  * The conclusion is `MonotoneOn (dist c ∘ α) (Icc 0 1)`, which is "nondecreasing".
  * The proof is the paper's. From `σ < τ` and `g σ > g τ`, it picks a level `λ ∈ (g τ, g σ)`
    that is not a local-extremum value (Lemma 2.8(i) and countability). It then finds
    `α₁ ∈ (0, σ)` and `β₁ ∈ (σ, τ)` at level `λ`, sets `K = α[α₁, β₁] ∌ c`, and calls
    `core_move`.

  Faithful.
* **B-6 info (l. 361-503, `lemma_4_4`).** The statement is `order c ≤ 4` in ℕ∞ for every `c`, so
  infinite order is excluded too. The proof follows the paper:
  * five arms;
  * `ρ = min(d(c,p₀), d(c,p₁))/2`;
  * first hits `a`, `b` at level `ρ` (`exists_first_level`);
  * five fresh arms with constant signs of `f_{a,b}` (`f(c) = 0` at l. 402), three of them with
    the same sign;
  * move `a` (or `b`) slightly inward, so that `f_{a',b}(c) < 0` (or `f_{a,b'}(c) > 0`);
  * `three_le_of_three_arms`.

  The paper requires the shortened `B₁`, `B₂` to end before `a`, `b`. The Lean proof does not
  need this, and it is not needed: the three arms meet only at `c`, which is not a zero after the
  move. So the paper's condition is unnecessary, and the Lean proof is a valid simplification.
* **B-7 info (l. 526-547, `monotone_away`).** This is Lemma 4.3 applied to `[c,v] ∪ I` with
  `I = seg v y` in another component. The two arcs meet only at `v`, so their concatenation is an
  arc (`IsArcParam.concat`), and the monotonicity on the second half is read off via
  `concat_half`. This is the first paragraph of the proof of Theorem 4.5. Correct.
* **B-8 info (l. 552-619, `not_two_nonconstant`).** This is the claim in Theorem 4.5. It picks a
  level `λ ∈ (h_c(v), min(μ, μ'))` that is not a local-extremum value of either function. The
  points `P s` and `P' s'` lie in different components, and `K = P[0,s] ∪ P'[0,s'] ∌ c` is
  connected through `v`. Then `core_move`. Faithful.
* **B-9 info (l. 622-652, `not_two_constant`).** No arc `seg v y` carries two constant `h_c`,
  `h_{c'}` with `c ≠ c'`, `c, c' ≠ v`. The points are `p = P(1/3)` and `q = P(2/3)`, with a zero
  of `f_{p,q}` on `P[1/3, 2/3]`. That zero is distinct from `c` and `c'` because `h_c` is constant
  at `d(c,v) > 0`. This is the paper's argument. Unused section variables trigger a warning,
  which is harmless.
* **B-10 info, stronger (l. 656-753, `theorem_4_5`).** The statement is: `IsBranchPoint v` gives
  `∃ m : ℕ, order v = m ∧ (branchSet X).Finite ∧ (m - 2) * (ncard B - 1) ≤ m ∧ ncard B ≤ 4`,
  where `branchSet X = {p | IsBranchPoint p}` (TreeStructure.lean l. 36).
  * **There is no truncation issue.** `m ≥ 3` (l. 664, from `IsBranchPoint v`), so `m - 2` is
    exact. `B` is finite and contains `v`, so `ncard B ≥ 1` (l. 747-748) and `ncard B - 1` is
    exact.
  * **There is no `ncard` vacuity.** For infinite `B`, `ncard = 0` would make the inequality
    trivial, but finiteness is a separate conjunct, so it is excluded.
  * Probe 1 derives the ℤ-valued inequality.
  * The counting follows the paper:
    * One representative `y` per component of `X \ {v}`. `J c` is the set of representatives
      whose arc `seg v y` carries constant `h_c`.
    * `|J c| ≥ m − 2` from the claim (B-8). The `J c` are pairwise disjoint (B-9).
    * `|F|(m−2) ≤ m` for every finite `F ⊆ B \ {v}`. This gives finiteness, by taking `m+1`
      points, and the bound.
    * `ncard B ≤ 4` by `interval_cases m`.
* **B-11 info (l. 763-769, `cor_4_6`).** `IsDendrite Y → MidsetsAtMostTwo Y → IsFiniteTree Y`.
  Finite order comes from `lemma_4_4`, and finiteness of branch points from `theorem_4_5`. The
  case with no branch point is trivial, because `IsFiniteTree` only needs finitely many branch
  points. This is consistent with the paper: Fact 2.5 is used in the paper only to describe the
  structure. Faithful.
* **B-12 info (l. 775-787, `theorem_C`).** The hypotheses are `IsDendrite Y` (a nondegenerate
  compact connected metrizable LC space with no SCC; for a metric space the metric is
  compatible) and `MidsetsAtMostTwo Y`. The conclusions are:
  * all orders `≤ 4`;
  * for each branch point `v`, `∃ m, order v = m ∧ (m-2)(ncard B - 1) ≤ m`;
  * `B` finite;
  * `ncard B ≤ 4`;
  * `IsFiniteTree Y`.

  `m ≥ 3` is not restated, but it follows from `IsBranchPoint v` and `order v = m`. With the
  finiteness conjunct, the second conjunct is not vacuous (probe 1). Faithful.

No BLOCKER or MAJOR findings.

## 4. Faithfulness table

| Paper result | Lean declaration | Faithful? | Justification |
|---|---|---|---|
| Def 2.1 (`f_{a,b}`) | `sgnf` (Defs.lean l. 58) | yes | `dist y a - dist y b`, and its zero set is `midset a b` (`sgnf_eq_zero_iff`). |
| Lemma 2.2 (a) | `lemma_2_2_a` | yes | The same strict-sign survival under `d(a,a') + d(b,b') < |f(t)|`, and `f(t) ≠ 0` is implicit in that hypothesis. |
| Lemma 2.2 (b) | `lemma_2_2_b` (+ `three_le_encard_of_sets`) | stronger | Preconnected instead of connected, with the same disjointness-of-zeros hypothesis and `k ≤ encard M`. |
| Fact 2.3, Lemma 2.4, Fact 2.5, Def 2.6, Lemma 2.7 | Dendrite/Order/NoBranch/Defs/TreeStructure | n/a here | Outside these three files; see reviews 01 and 02. |
| Lemma 2.8 (i) | `lemma_2_8_i` | stronger | Countability of extremum values for *any* `g : ℝ → ℝ` (no continuity needed), which restricts to any open `J`. |
| Lemma 2.8 (ii) | `lemma_2_8_ii` | yes | "Not constant on any nondegenerate open subinterval of `(α, β)`" is the paper's hypothesis, and meagre in ℝ equals meagre in `J`. |
| Lemma 2.8 (iii) | `lemma_2_8_iii` | yes | Non-extremum (Mathlib's non-strict `IsLocalExtr`, as in the paper) gives smaller and larger values in every neighbourhood. |
| Lemma 2.9 (grid) | `lemma_2_9` | weaker (formally) | All three conclusions are present, but `U, V` are bounded intervals `Ioo a b`, `Ioo c d`; unbounded intervals are covered only after an order-homeomorphism, so the difference is harmless. |
| Nadler 5.6 (as used) | `boundary_bumping_open` | yes (special case) | The open-set form is exactly what Prop 3.1 uses, and it is proved, not assumed. |
| Prop 3.1 | `prop_3_1` | yes | A compact connected nontrivial metric space whose midsets of distinct points are `Finite` is `LocallyConnectedSpace`. |
| Prop 3.2 | `prop_3_2` | stronger | `C = univ` for every SCC under `≤ 2`, with no continuum hypothesis needed. |
| Cor 3.4 | `cor_3_4` | yes | DMP continuum gives `Nonempty (X ≃ₜ Circle) ∨ IsDendrite X`. |
| Lemma 4.2 | `lemma_4_2` (+ `exists_arm`) | yes / stronger | The same arms (ends `c`, distinct components, meeting only in `c`, inside `B(c,δ)`, disjoint from `K`). The sign clause needs only finitely many zeros, not `f(c) = 0`. |
| Lemma 4.3 | `lemma_4_3` | yes | For an arc parametrized from a branch point `c`, `h_c ∘ α` is `MonotoneOn` `[0,1]`. |
| Lemma 4.4 | `lemma_4_4` | yes | `order c ≤ 4` (in ℕ∞) for every point, under Convention 4.1. |
| Thm 4.5 | `theorem_4_5` | stronger | It adds `B` finite and `order v = m : ℕ`. The ℕ-subtraction is exact (`m ≥ 3`, `v ∈ B`), and `|B| ≤ 4` is included. |
| Cor 4.6 | `cor_4_6` | yes | Dendrite with `≤ 2` gives `IsFiniteTree`. |
| Theorem C | `theorem_C` | yes | Every clause (order ≤ 4, `(m-2)(|B|-1) ≤ m`, `|B| ≤ 4`, finite tree) plus `B` finite. |

## 5. Overall verdict

**ACCEPT: no BLOCKER and no MAJOR findings.**

* All three files compile and contain no forbidden constructs. Every main result depends only on
  `propext`, `Classical.choice` and `Quot.sound`.
* Every numbered result of Sections 2.1-2.4 (in scope), 3 and 4 is stated faithfully or in a
  harmlessly stronger form.
* The only formal weakening is Lemma 2.9, which is restricted to bounded open intervals (E-6). It
  is harmless and could be removed by stating it for arbitrary `IsOpen`/`OrdConnected`
  nonempty `U, V`, or by noting the order-homeomorphism.
* The proofs follow the paper. Where they differ (Prop 3.1's counting of components, the
  factoring through `core_move`, and Lemma 4.4 without the "arms end before `a, b`" condition),
  the variant is valid. In Lemma 4.4 the paper's condition is in fact unnecessary.
* Minor clean-ups:
  * stale "Lemma 5.2" docstrings in `Classical/Bump.lean` (R-2);
  * unused hypotheses `hE`, `hF` in `lemma_2_9`;
  * deprecation warnings.
