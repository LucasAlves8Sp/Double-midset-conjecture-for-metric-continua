# Review 10: main theorems (Main.lean, Special.lean, `theorem_C` in Branch.lean)

Reviewer: independent, no prior context. No `.lean` file was modified.

## Verdict: ACCEPT WITH MINOR

The statements of Theorems A, B and C, the "Consequently" part of Theorem A, and the "in particular"
part of Theorem B match the paper. The definitions they use are faithful. Everything builds, and the
axiom footprint is clean. The only issues are packaging and cosmetic ones. None affects correctness.

## Checks performed

| Check | Result |
|---|---|
| `b.sh DoubleMidset` | `Build completed successfully (2190 jobs)`, 0 errors |
| `sorry` / `admit` / `axiom` / `native_decide` / `unsafe` / `implemented_by` / `opaque` / `extern` / `macro` / `elab` / `set_option` in `DoubleMidset/`, `DoubleMidset.lean` | none |
| `sorry` in the build log (full `lake build` output) | none (249 warnings: deprecations such as `push_neg`, `if_pos` and `Set.mem_setOf_eq`; unused section variables; linter hints) |
| `#print axioms` for `theorem_A`, `theorem_A_iff`, `theorem_B`, `theorem_B_full`, `theorem_C`, `circle_hasDMP`, `theorem_10_1`, `theorem_11_1` (also `arc_isFiniteTree`, `triod_isFiniteTree`) | each gives exactly `[propext, Classical.choice, Quot.sound]` |
| Non-vacuity (scratch file `/tmp/rev10_sanity*.lean`) | `IsArc (univ : Set unitInterval)`, `IsFiniteTree unitInterval`, `IsDendrite unitInterval`, `¬ HasDMP unitInterval`, `HasDMP Circle`, `IsContinuum Circle`, `theorem_A circle_hasDMP`, and the backward direction of `theorem_A_iff` on `Circle` all elaborate. So the hypotheses `IsFiniteTree` / `IsDendrite` / `IsContinuum` / `HasDMP` can be satisfied, and the theorems are not vacuous. `theorem_A` also elaborates at an arbitrary universe. |
| Circularity | None. `Special.lean` imports `Main.lean`. `theorem_B` (Main.lean:26) uses `not_hasDMP_of_branched` (Triod.lean:237) and `not_hasDMP_of_unbranched` (ArcCase.lean:72), which do not depend on Special.lean. |

## Blockers

None.

## Major

None.

## Minor

1. **Packaging.** `lakefile.toml` lists `defaultTargets = ["DoubleMidset", "Challenge", "Solution"]` with `Challenge` and `Solution` libraries, but `/home/claude/dmp/lean` contains no `Challenge.lean` or `Solution.lean`. A plain `lake build` (or `lake build Challenge`) therefore fails with `build failed`. Also, the module docstring at Defs.lean:14–15 says "`Challenge.lean` copies this file verbatim", and that file does not exist here. Either add the files or remove the targets and the remark.
2. **Organization differs from the paper.** The paper proves Theorems 10.1 and 11.1 (triod, arc) and then derives Theorem B from them. The Lean code instead proves general branched and unbranched finite-tree results, which give `theorem_B`. It then gets `theorem_10_1` and `theorem_11_1` (Special.lean:443, 203) back from `theorem_B` through `triod_isFiniteTree` and `arc_isFiniteTree`. This is legitimate and not circular. It only means the named Lean `theorem_10_1` / `theorem_11_1` are corollaries, not the paper's standalone proofs.
3. **`theorem_C` uses ℕ truncated subtraction and `ncard`** (Branch.lean:777–779): `(m - 2) * (ncard B - 1) ≤ m`. This is harmless. A branch point has `m ≥ 3`, and the same theorem proves `B` finite and nonempty (it contains `v`), so `ncard B ≥ 1` and nothing is truncated. The value `ncard = 0` for an infinite set is also excluded by the `Finite` conjunct. A remark in the docstring would help readers.
4. **Encoding choices** (equivalent to the paper, listed for transparency):
   - `theorem_B` / `theorem_10_1` / `theorem_11_1` are stated for a type carrying a `MetricSpace` instance, with `IsFiniteTree X` read in the metric topology. This is equivalent to "a topological finite tree admits no compatible DMP metric". `theorem_A_iff` shows how the explicit-compatibility form is encoded.
   - The "simple closed curve" in `theorem_A_iff` is `Nonempty (X ≃ₜ Circle)`, not `IsSimpleClosedCurve univ`. These are trivially equivalent.
   - The `IsContinuum` hypothesis of `theorem_A_iff` is only needed in the forward direction (compactness, connectedness, nontriviality). Its metrizability field is redundant there, since a compatible metric is assumed.
5. **Cosmetic.**
   - There are 249 warnings, mostly deprecations and "automatically included section variable(s) unused".
   - `DoubleMidset/Test.lean` is not imported by anything (dead file).
   - `encard_pair_le'` (Special.lean:105) has no docstring.

## Faithfulness table

### Definitions (DoubleMidset/Defs.lean)

| Lean (file:line) | Paper | Assessment |
|---|---|---|
| `midset` Defs.lean:47 | §1: `M(a,b) = {x : d(x,a)=d(x,b)}` | exact |
| `HasDMP` Defs.lean:50 | §1: `|M(a,b)| = 2` for all distinct `a,b` | exact (`encard = 2`, so an infinite midset is excluded) |
| `MidsetsAtMostTwo` Defs.lean:54 | Thm C hypothesis `|M| ≤ 2` | exact |
| `IsArc` Defs.lean:67 | homeomorphic to `[0,1]` | exact |
| `IsArcBetween` Defs.lean:71 | arc with ends `p`, `q` | exact (embedding of `[0,1]`; `p ≠ q` follows) |
| `IsSimpleClosedCurve` Defs.lean:75 | homeomorphic to `S¹` (Mathlib `Circle ⊆ ℂ`) | exact |
| `IsSimpleTriod` Defs.lean:79 | three arcs pairwise meeting only in a common end | exact |
| `order` Defs.lean:84 | number of components of `X \ {p}` (§2.2) | exact (set of `connectedComponentIn {p}ᶜ x`, `x ≠ p`, counted by `encard ∈ ℕ∞`) |
| `IsTip` Defs.lean:88, `IsBranchPoint` Defs.lean:91 | order one; order at least three | exact (`IsBranchPoint` includes order `⊤`, as in the paper) |
| `IsContinuum` Defs.lean:94 | nondegenerate compact connected metrizable | exact (`Nontrivial` = nondegenerate) |
| `IsDendrite` Defs.lean:98 | locally connected continuum with no simple closed curve | exact |
| `IsFiniteTree` Defs.lean:103 | Def 2.6: dendrite, finitely many branch points, each of finite order | exact |

### Main statements

| Lean (file:line) | Paper | Assessment |
|---|---|---|
| `theorem_A` Main.lean:36 | Thm A, first sentence: nondegenerate compact connected metric space with `|M(a,b)|=2` is homeomorphic to `S¹` | faithful. Hypotheses: `[MetricSpace X] [CompactSpace X] [ConnectedSpace X] [Nontrivial X] (HasDMP X)`. Conclusion: `Nonempty (X ≃ₜ Circle)`. Proof: `cor_3_4`, then the dendrite case is a finite tree by `cor_4_6`, excluded by `theorem_B`, as in §12. |
| `theorem_A_iff` Main.lean:156 | Thm A, "Consequently ...": a nondegenerate metrizable continuum admits a compatible DMP metric iff it is a simple closed curve | faithful. `[t : TopologicalSpace X] (IsContinuum X)`. "Compatible" is `m.toUniformSpace.toTopologicalSpace = t`. Converse: pull back the circle metric along `e` with `MetricSpace.induced`; the topology equals `t` by `e.isInducing.eq_induced`; the midset is moved by `e` (`encard` preserved by injectivity). |
| `circle_hasDMP` Main.lean:65 | §12: Euclidean unit circle has the DMP | faithful. `Circle`'s metric is the chordal one from ℂ (`circle_dist`, Main.lean:45). The midset is computed explicitly as `{P, -P}` with `P = (-w₂, w₁)/n`, `P ≠ -P`. Helpers `norm_sq_eq_re_im`:42, `circle_unit`:48 and `circle_dist_eq_iff`:51 (chord equidistance as the linear equation `z·(a−b)=0`, via `nlinarith` with `|z|=|a|=|b|=1`) are correct. |
| `theorem_B` Main.lean:26 | Thm B: no finite tree admits a compatible DMP metric | faithful. `[MetricSpace X] (IsFiniteTree X) : ¬ HasDMP X`. The proof splits on branched / unbranched, like §12. |
| `theorem_B_full` Special.lean:447 | Thm B including "in particular, neither an arc nor a simple triod does" | faithful. The three conjuncts are for `IsFiniteTree X`, `IsArc univ` and `IsSimpleTriod univ`. |
| `theorem_11_1` Special.lean:203 | Thm 11.1: no compatible metric on an arc has the DMP | faithful (derived from `theorem_B` and `arc_isFiniteTree`) |
| `theorem_10_1` Special.lean:443 | Thm 10.1: no compatible metric on a simple triod has the DMP | faithful (derived from `theorem_B` and `triod_isFiniteTree`) |
| `theorem_C` Branch.lean:775 | Thm C: dendrite with `|M| ≤ 2`: order ≤ 4 everywhere; a branch point of order `m` gives `(m−2)(|B|−1) ≤ m`; `|B| ≤ 4`; finite tree | faithful. All four conclusions are present, with `B` finite stated as well. See minor item 3 about ℕ subtraction. |

### Arc and triod are finite trees (Special.lean): proof soundness

| Lean (file:line) | Content | Assessment |
|---|---|---|
| `not_scc_subset_arc` :24 | no simple closed curve lies in an arc | sound. It composes the periodic parametrization `c` of the curve with `e : A ≃ₜ [0,1]`, giving a continuous real `φ` with `φ 0 = φ 1`. `exists_eq_of_eq_ends` (Reduction.lean:235) gives `s < t` in `[0,1)` with `φ s = φ t`. That contradicts injectivity of `e` and of `c` on `[0,1)`. |
| `IsSimpleClosedCurve.isPreconnected_diff` :54 | a curve minus a point is preconnected | sound. The punctured curve is `c '' (s, s+1)`, the image of an interval; the case `y ∉ C` is trivial. |
| `open_window` :84, `window_isConnected` :100 | an image of a parameter window missing the closed rest `K` is open; windows are connected | sound. The complement is a compact image union `K`. |
| `piece_lc` :110 | local connectedness at non-base points of a piece | sound. Small windows `g '' ((t−δ',t+δ') ∩ [0,1])` with `δ' ≤ t` avoid `K`. |
| `piece_order` :130 | order ≤ 2 at non-base points | sound. Every component of `X \ {g t}` equals the component of `g 0` (through `g''[0,t) ∪ K`, preconnected because `g 0 ∈ K` or `K = ∅`) or of `g 1` (through `g''(t,1]`). |
| `arc_isFiniteTree` :177 | an arc is a finite tree | sound. Compactness and connectedness come from `g '' [0,1] = univ`; nontrivial because `g 0 ≠ g 1`; locally connected and order ≤ 2 by `piece_lc` / `piece_order` with `K = ∅`; no simple closed curve by `not_scc_subset_arc`; no branch points, so both finiteness conditions hold trivially. Metrizability is the instance. |
| `open_start` :207, `triod_piece` :224 | the initial segment of a leg plus the other two legs is open; piece hypotheses for each leg | sound |
| `triod_isFiniteTree` :246 | a simple triod is a finite tree | sound. Compact: union of three arcs. Connected: union through `v`. Locally connected: at `v`, the open set `W₁ ∪ W₂ ∪ W₃` (shown open as an intersection of three `open_start` sets, identity `hO`), connected through `v`, inside `U`; elsewhere `piece_lc`. Orders: ≤ 2 away from `v`, so the branch points are contained in `{v}`. `order v ≤ 3 < ⊤`: every component is that of some `p_i`. No simple closed curve: `C \ {v}` is preconnected and covered by the three pairwise disjoint open sets `(A_j ∪ A_k)ᶜ`, so it lies in one leg and `C ⊆ A_i`, which contradicts `not_scc_subset_arc`. |

All of these are kernel-checked with the standard axioms only. The hand reading above found no gap,
and no trivialization of the hypotheses (see the non-vacuity checks).
