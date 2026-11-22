# Review 05: Section 6 (spherical arcs and odd boxes)

Reviewer: independent, no prior context. No `.lean` file was modified. Scratch files are in
`/tmp/rev05/`.

Files reviewed line by line:
* `DoubleMidset/Spherical.lean` (405 lines)
* `DoubleMidset/OddBox.lean` (744 lines)
* `DoubleMidset/Types.lean`, l. 312–341 (`touch_isLocalExtr`, `lemma_5_6`)

Paper sections: Section 6 (tex l. 589–695), plus Section 5 (l. 473–588) for the definitions it uses.

## Verdict: ACCEPT WITH MINOR

There are no blockers and no major issues. Every Section 6 statement is at least as strong as the
paper's and uses no stronger hypotheses. All the proofs are sound. Where a proof departs from the
paper (S2/S3, S4, Lemma 6.2(c), Lemma 6.3), the new argument is correct and is often simpler. The
minor items are documentation and hygiene only.

## Mechanical checks

* **Build.** `/home/claude/dmp/b.sh DoubleMidset` reports `Build completed successfully (2182 jobs)`,
  with 162 warnings across the project. I also compiled each file from source
  (`lake env lean DoubleMidset/{Spherical,OddBox,Types}.lean`): there are no errors. The only
  warnings are deprecations (`push_neg`, `dif_pos`, `if_pos/if_neg`, `Set.mem_setOf_eq`,
  `IsLocalExtr.on`), one `haveI`→`have` hint, and "automatically included section variable(s)
  unused" (listed under Minor issues).
* **Forbidden constructs.** `grep -rnE '\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|opaque)\b'`
  over `DoubleMidset/` and `DoubleMidset.lean` finds nothing. The root `DoubleMidset.lean`
  imports `DoubleMidset.OddBox`, so the reviewed files are part of the build target.
* **Axioms** (`/tmp/rev05/ax.lean`). The following all depend on exactly
  `[propext, Classical.choice, Quot.sound]`: `lemma_6_2`, `lemma_6_3`, `lemma_6_6`, `prop_6_5`,
  `cor_6_7`, `centers_countable`, and the helpers `touch_isLocalExtr`, `lemma_5_6`,
  `param_selection`, `strict_nhds` and `odd_oddCount_swap`.
* **6.2(a) equivalence check** (`/tmp/rev05/eq.lean`, compiles). From
  `IsArcBetween I p q` and `InjOn (dist y) I` it derives a parametrization `k` of `I` with
  `t ↦ dist y (k t)` `StrictMonoOn ∨ StrictAntiOn` on `[0,1]`. The proof uses Mathlib's
  `ContinuousOn.strictMonoOn_of_injOn_Icc'`. The converse is trivial. So `InjOn` on an arc is
  exactly the paper's "strictly monotone on `I`".

## Blockers

None.

## Major issues

None.

## Faithfulness, statement by statement

Standing hypotheses: `TreeHyp T` together with
`[MetricSpace T] [CompactSpace T] [ConnectedSpace T] [LocallyConnectedSpace T] [Nontrivial T]`.
Earlier reviews accepted this as "finite tree with compatible metric".

| Paper | Lean (file:line) | Hypotheses vs paper | Conclusion vs paper | Verdict |
|---|---|---|---|---|
| Def 6.1 spherical arc | `IsSphericalArc` (Defs.lean:157) | — | `IsArc I ∧ 0 < r ∧ I ⊆ sphere x r`. `IsArc` is a homeomorphism with `[0,1]`, so the arc is nondegenerate. | Faithful |
| Lemma 6.2(a) | `lemma_6_2` (Spherical.lean:317), 1st conjunct; parametric `sphere_strictMonoOn` (l. 33) | `MidsetsAtMostTwo` (weaker than DMP) | `∀ y ∉ I, y ≠ x → InjOn (dist y) I`. Equivalent to strict monotonicity along the arc (see above). The parametric version states `StrictMonoOn ∨ StrictAntiOn` directly. | Faithful |
| Lemma 6.2(b) | 2nd conjunct; `sphere_center_unique` (l. 67) | same | `∀ x' r', I ⊆ sphere x' r' → x' = x`. This means "h_{x'} constant on I ⇒ x' = x" and allows any `r'`, including `r' ≤ 0`, which is handled at l. 343–349. Also: every arc `J ⊆ I` is spherical with the same `x, r`. | Faithful (slightly stronger) |
| Lemma 6.2(c) | 3rd conjunct; `no_vertex_inside` (l. 101), `sphere_in_edge` (l. 199) | same | For every presentation `IsArcBetween I p q`, no `z ∈ I \ {p,q}` is a vertex; and `∃ ℓ, IsEdge ℓ ∧ I ⊆ ℓ`. `IsEdge` is the closure of an open edge, which is the paper's "edge". | Faithful |
| Lemma 6.2(d) | 4th conjunct; `centers_countable` (l. 240) | same | `{x \| ∃ I r, IsSphericalArc I x r}.Countable` | Faithful |
| Lemma 6.3 | `lemma_6_3` (Spherical.lean:365) | `HasDMP` (standing). "p interior point of I" is encoded as `IsArcBetween I e₁ e₂`, `p ∈ I`, `p ≠ e₁`, `p ≠ e₂`. Since the ends of an arc are intrinsic, this is exactly "interior point". `b ≠ p` is not stated separately because `IsStrictPair p b` contains it. `h_x(b) ≠ r` is `dist x b ≠ r`. | `Even (oddCount p b)` | Faithful |
| (5.2) parity of swap | `odd_oddCount_swap` (OddBox.lean:89) | strict pair | Only `Odd N(a,b) → Odd N(b,a)`. Applying it to both orders gives the full `≡ mod 2`. The identity `N(b,a) = \|Odd\| − N(a,b)` is not stated. | Sufficient (see Minor 3) |
| Def 6.4 box / odd box | `IsBox`, `IsOddBox` (Defs.lean:163,168) | — | matches | Faithful |
| Lemma 6.6 | `lemma_6_6` (OddBox.lean:575) | `HasDMP`, `IsOddBox U V` | `∃ U₁ V₁, IsBox U₁ V₁ ∧ U₁ ⊆ U ∧ V₁ ⊆ V` (nonempty, because an open arc is nonempty: `IsOpenArc.nonempty`, l. 543); `∃ J`, an open arc inside an open edge; `∃ w : T×T → T`, `ContinuousOn w (U₁ ×ˢ V₁)` with `w(a,b) ∈ J ∧ IsTouch (sgnf a b) (w(a,b))` on `U₁ × V₁`. This is the same as a continuous map `U₁ × V₁ → J`, because the subspace `U₁ ×ˢ V₁` of `T × T` carries the product topology and `ContinuousOn` is continuity of the restriction. "the touch" equals "a touch", because a strict pair with odd `N` has exactly one touch (Cor 5.5 together with `not_isCrossing_and_isTouch`). | Faithful |
| Prop 6.5 | `prop_6_5` (OddBox.lean:628) | `HasDMP`, `IsOddBox U V` | `∃ c r, 0 < r ∧ U ∪ V ⊆ sphere c r ∧ ∀ c' r', U ∪ V ⊆ sphere c' r' → c' = c`. The uniqueness quantifies over every `r'` and is not tied to `r` or to `r' > 0`, so it is at least as strong as "the point `c` is unique". | Faithful (slightly stronger) |
| Cor 6.7 | `cor_6_7` (OddBox.lean:691) | `HasDMP`, strict pair, `a, b ∉ vertices`, `N(a,b)` odd: exactly the paper's | Existence: `r > 0`, open arcs `U ∋ a` and `V ∋ b`, each inside an open edge, `U ∪ V ⊆ S(c,r)`, and `c ∈ M(a',b')` on `U × V`. Edge point: `c ∉ vertices T`. Uniqueness: any `c'` with some `r'` (any sign) and some open arcs `U' ∋ a`, `V' ∋ b` (no open-edge condition) and `U' ∪ V' ⊆ S(c',r')` equals `c`. This is stronger than the paper's uniqueness among triples of the same shape. | Faithful (stronger uniqueness) |
| Lemma 5.6 (refactor) | `lemma_5_6` (Types.lean:336) via `touch_isLocalExtr` (l. 314) | unchanged from review 04 | Statement unchanged: `a ∉ V → IsLocalExtrOn (dist t) (open edge of a) a`, and the same for `b`. `touch_isLocalExtr` gives the stronger `IsLocalExtr (dist t) a ∧ IsLocalExtr (dist t) b` on all of `T`, with no edge-point hypothesis. Its proof is the paper's: `touch_stable_core` works for every `a'` near `a`. | Faithful |

**Vacuity.** No statement adds hypotheses beyond the paper's.
* `lemma_6_2` needs only `MidsetsAtMostTwo`, which is satisfiable on finite trees (e.g. `[0,1]`).
* The DMP-based statements (6.3, 6.6, 6.5, 6.7) assume `TreeHyp ∧ HasDMP`. By the paper's main
  theorem these assumptions are ultimately inconsistent, but that is the intended reductio of
  Sections 5–9 and not a defect of the formalization.
* The conclusions contain no trivially satisfiable disjuncts. Every existential is witnessed by
  substantive objects (open arcs in open edges, `r > 0`, a touch), so the conclusions cannot be
  met trivially.

## Soundness of the proofs, and the deviations from the paper

* **6.2(a)** (`sphere_strictMonoOn`). This is the paper's argument. If `h_y(k u) = h_y(k v)`, then
  `x`, `y` and a zero of `f_{p,q}` on `k[u,v]` are three distinct points of `M(p,q)`. The zero
  comes from the IVT, it is not `x` because `r > 0`, and it is not `y` because `y ∉ I`.
  Injectivity on `Icc` then gives strict monotonicity.
* **6.2(c)** (`no_vertex_inside`), deviation.
  - Tip case: `two_le_order_of_mem_arc`.
  - Branch case: the proof replaces the paper's sequence-and-limit argument with one point. It
    takes a component `w` of `T∖{y}` other than the components of `k c` and `k d` (pigeonhole
    from `order y ≥ 3`). Then `y ∈ closure` of that component (`mem_closure_cc`), which gives `z`
    with `d(z,y) < min(m/2, d(y,x))`, where `m = min(d(y,k c), d(y,k d))`.
  - `z ∉ I`: each half `k[c,t)` and `k(t,d]` of the arc is preconnected and avoids `y`
    (`hhalf`).
  - Strict monotonicity of `h_z` then gives either `h_z(k c) < h_z(y) < m/2` or the same with
    `k d`, and the triangle inequality gives `h_z(k c) ≥ m − m/2`, a contradiction. Correct.
* **6.2(c) "one edge"** (`sphere_in_edge`). `k(Ioo c d)` is preconnected and has no vertices, so it
  lies in the component of `(vertices)ᶜ` at the midpoint. The closure of that component is an
  edge (`isEdge_closure_cc`). Correct.
* **6.2(d)** (`centers_countable`). The index set is (edge, rational, rational), with a chosen
  parametrization per edge (`choose!`). `exists_rational_subarc` puts a rational spherical subarc
  inside the edge (via `seg_eq`/`seg_subset`), and `sphere_center_unique` makes each fibre a
  subsingleton. This is the paper's argument. Correct.
* **6.3** (`lemma_6_3`), deviation. It uses the global `touch_isLocalExtr`, so it does not need
  6.2(c) to know that `p` is an edge point. Pulling `IsLocalExtr` back along the
  parametrization, `not_isLocalExtr_of_strictMono` on a small `[s₀−δ', s₀+δ']` avoiding `t`
  closes the argument. `t ≠ p` follows from `f_{p,b}(p) < 0`, and `t ≠ x` from `h_x(b) ≠ r`.
  Correct.
* **S1** (`param_selection`, l. 151–203). Baire in `ℝ²` is used with closed sets `A n ∪ Bᶜ`,
  where `A n` is a projection along the compact `T × T` and so closed in all of `ℝ²`. This
  avoids "relatively closed in `U×V`". `dense_iUnion_interior_of_closed` gives `p0 ∈ B ∩ int(A n ∪ Bᶜ)`,
  and on `O = int(A n ∪ Bᶜ) ∩ B ⊆ A n` the two midset points are `ρ`-separated (DMP pins down the
  pair, l. 197–202). Correct.
* **S2/S3**, deviation, replacing Hausdorff continuity.
  1. *Upper semicontinuity.* `Bad` (l. 260) is the projection, along compact `T`, of the closed
     set of (pair, zero outside `B(y₀,ε) ∪ B(t₀,ε)`), so `Bad` is closed and `p0 ∉ Bad`. Nearby
     pairs therefore have all midset points in the two `ε`-balls.
  2. *Separation.* Since `2ε < ρ`, one midset point lies in each ball (l. 312–318).
  3. *Protected crossing.* The point near `y₀` is `κ' r'`, the only zero on `κ'[r₀±η]`.
     Persistence of the opposite signs at `κ'(r₀±η)` (open condition in `hN`) together with
     `const_sign` on each side gives `IsParamCrossing`, then `isCrossing_of_param`. By Cor 5.5 the
     other point is the touch.
  4. *Unique zero.* It is the unique zero of `f_{a,b} ∘ ψ` on the compact `K = ψ`-interval
     (l. 363–372; `hdisj` excludes the crossing).
  5. *Continuity.* `continuousOn_of_unique_zero` (l. 48) is the standard closed-graph /
     proper-projection argument: for closed `t`,
     `q⁻¹(t) ∩ R = fst''(Z ∩ univ ×ˢ (K∩t)) ∩ R`, and the projection is closed because `K ∩ t`
     is compact (`isClosed_fst_image_inter`, l. 33). Correct.

  The deviation is sound and needs only upper semicontinuity plus separation, which is less than
  the paper's two-sided Hausdorff continuity.
* **S4** (`param_box_sphere`). The paper picks `z` interior to the image interval. The proof
  instead picks, for any `g p < g p'`, a `q'` strictly between them with `ψ q'` not a center
  (countability via `MapsTo.countable_of_injOn` and `exists_mem_Ioo_notMem`). The steps:
  - `mem_centers_of_const` (constant `h_z` on a parameter interval ⇒ `z` is a center, with
    `r > 0` from injectivity) and `lemma_2_8_ii` make `E` and `F` meagre.
  - A zero of `g − q'` gives a touch at `z`, and `touch_isLocalExtr` composed with the
    parametrizations puts `s ∈ E` and `u ∈ F`. So there are no zeros on the grid.
  - `lemma_2_9` then gives one sign on the whole square, which contradicts `g p < q' < g p'`.

  This is equivalent to the paper's argument and cleaner. The subbox sphere and `r > 0`
  (l. 520–540) are correct.
* **S5 and uniqueness** (`prop_6_5`). `exists_sphericalArc_of_param` produces a spherical arc with
  an explicit interior point in each subbox side. `lemma_6_3` then forces `V ⊆ S(c,r)`, and
  with `odd_oddCount_swap` and `IsStrictPair.symm` it forces `U ⊆ S(c,r)`. Uniqueness comes from
  `lemma_6_2` (b) applied to the arc `I ⊆ U`. This is exactly the paper's argument.
* **`strict_nhds`** (l. 662). The sign of `f_{p}(u)·f_{a,b}(u)` is positive near `(a,b)` for the
  finitely many vertices (`eventually_all_finite`), so strictness and the counted set are
  preserved. Correct.
* **`cor_6_7`**.
  - Odd box: built from a product neighbourhood inside `strict_nhds`, cut by balls of radius
    `d(a,b)/2` (which gives disjointness), with edge-parameter intervals around `a` and `b`
    (`exists_param_interval`).
  - Edge point: `c ∉ vertices` because `(a,b)` is strict and `c ∈ M(a,b)`.
  - Uniqueness: a spherical arc inside `U ∩ U'` around `a`, then 6.2(b). Correct.
* **`touch_isLocalExtr`** (Types.lean:314). `σ = ±1` from `touch_stable_core` gives `IsMinFilter`
  or `IsMaxFilter` at `a`, and the sign `−σ` does the same at `b`. Correct.

## Minor issues

1. **Spherical.lean:14.** The module docstring lists `offsphere_even` as Lemma 6.3, but no such
   declaration exists. The theorem is `lemma_6_3` (l. 365). The list also omits
   `sphere_center_unique`, `sphere_in_edge` and the intrinsic `lemma_6_2`.
2. **Unused auto-included section variables** (linter warnings):
   - Spherical.lean:215 `exists_rational_subarc`: `h2` and `[Nontrivial T]` are unused, so
     callers must pass a superfluous `h2` (l. 258).
   - OddBox.lean:114 `IsOpenEdge.notMem_vertices`: `[CompactSpace] [ConnectedSpace]
     [LocallyConnectedSpace]` are unused.
   - OddBox.lean:411 `mem_centers_of_const`: `[CompactSpace]` is unused.
   - OddBox.lean:543 `IsOpenArc.nonempty`: `[CompactSpace] [ConnectedSpace]
     [LocallyConnectedSpace]` are unused.
   - OddBox.lean:602 `exists_sphericalArc_of_param`: `[CompactSpace]` is unused.

   None of these affects any main statement, because these instances are standing hypotheses
   anyway.
3. **OddBox.lean:88.** The docstring "(5.2): `N(b,a) ≡ N(a,b) (mod 2)`" overstates the statement,
   which proves only `Odd → Odd`. That direction is all that is used, and it implies the
   congruence by symmetry. The identity `N(b,a) = |Odd| − N(a,b)` is not formalized.
4. **Types.lean:336–341.** In `lemma_5_6`, the edge-point hypotheses are ignored (`fun _ =>`).
   This is deliberate, to match the paper's statement, and is harmless. It uses the deprecated
   `IsLocalExtr.on` (rename to `IsLocalExtr.isLocalExtrOn`).
5. **OddBox.lean:697.** In `cor_6_7`, `V'` and `IsOpenArc V'` in the uniqueness clause are unused
   by the proof (`_` at l. 735). The clause is therefore stronger than necessary, which is fine.
   It could be simplified, or kept for symmetry with the paper.
6. **Cor 6.7 does not export the odd box.** It does not say that `U × V` is an odd box, or even
   that `U` and `V` are disjoint. The paper's statement does not say this either, but the
   paragraph before Prop 6.5 ("every strict pair of edge points with `N` odd is contained in an
   odd box") is used later. Exporting the `hbox` construction (l. 701–725) as a standalone lemma
   would avoid re-deriving it in Sections 7–8.
7. **Placement.** `IsStrictPair.symm` (OddBox.lean:85) and `IsOpenArc.nonempty` (l. 543) are
   generic and belong in Types/Defs-level files.
8. **Duplicated code.** The idiom "`hIs (hkim ▸ ⟨t, ht, rfl⟩)`; `rw [mem_sphere, dist_comm]`" is
   repeated about 7 times (Spherical l. 254, 261, 326, 339, 352, 394; OddBox l. 739). The
   `min`-of-several-`ε` bookkeeping is also repeated. A small helper would shorten these.
9. **Size of `param_selection`.** At about 270 lines (OddBox.lean:139–406) it is long. S1 and the
   "near `y₀`/`t₀`" step could be split out, which would make the stage labels S1–S3 clearer.
   The proof itself is correct.
10. **OddBox.lean:36.** `haveI` → `have` (linter hint). There are also assorted `push_neg`,
    `dif_pos`, `if_pos`/`if_neg` and `Set.mem_setOf_eq` deprecations.
