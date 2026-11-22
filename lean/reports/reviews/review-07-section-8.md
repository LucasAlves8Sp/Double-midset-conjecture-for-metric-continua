# Review 07 — Section 8 "Distances to the tips" (`DoubleMidset/Tips.lean`)

Paper: `dmp_paper_2.tex` ll. 840–915 (Lemma 8.1 `lem:boundary`, Proposition 8.2 `prop:tipdistance`).
File: `/home/claude/dmp/lean/DoubleMidset/Tips.lean` (514 lines), read line by line.

## Verdict: **ACCEPT WITH MINOR**

No blockers, no major issues. The three paper statements are faithfully encoded (one is
slightly more general in a harmless way), the proofs follow the paper closely, and the
replacement argument in 8.2(a) is valid. The minor points are cosmetic.

## Build / hygiene

* `/home/claude/dmp/b.sh DoubleMidset` reports `Build completed successfully (2185 jobs)`, with 0 errors.
  I also compiled `lake env lean DoubleMidset/Tips.lean` from source myself: rc=0, 19 warnings, all of them
  deprecation warnings (`push_neg`, `if_pos/if_neg`, `IsLocalMin.on`, `Set.Finite.diff`, ...).
* `grep -rn` over `DoubleMidset/` (including `Classical/`) for `sorry`, `admit`, `axiom `,
  `native_decide`, `implemented_by`, `@[extern`, `unsafe`, `set_option`, `macro`/`elab`, `opaque` finds nothing.
* `#print axioms` (scratch file `/tmp/r07_ax.lean`):
  * `lemma_8_1`: `[propext, Classical.choice, Quot.sound]`
  * `prop_8_2_a`: `[propext, Classical.choice, Quot.sound]`
  * `prop_8_2_b`: `[propext, Classical.choice, Quot.sound]`
  * (`noflip_core`: same)

## Blockers

None.

## Major

None.

## Minor

1. **`prop_8_2_b` has a redundant hypothesis.** `hbr : ∃ v, IsBranchPoint v` (Tips.lean:450) follows from
   `hv : IsBranchPoint v`. It does no harm (callers can pass `⟨v, hv⟩`), but it could be dropped.
2. **8.2(a) only states `InjOn`.** `prop_8_2_a` (l. 352) concludes `InjOn (dist e) ℓ`. This is equivalent to
   the paper's "strictly monotone on every edge", because a continuous injective function on an arc is strictly
   monotone along any parametrization, and the proof derives exactly this at ll. 419–422. It is also the natural
   way to state it without an orientation. Still, the strict-monotone form along an edge parametrization
   (`StrictMonoOn ∨ StrictAntiOn (dist e ∘ γ) (Icc 0 1)`) is never exported as a lemma. Its consumers
   (`prop_8_2_b` l. 507, and presumably Section 9) have to re-derive it with `strictMonoOn_of_injOn_Icc'`. A small
   corollary would help readability.
3. **Deprecation warnings.** There are 19 in Tips.lean. They are cosmetic only.
4. **Unnecessary generality in Lemma 8.1's second disjunct.** The disjunct (l. 218) does not require
   `cc a ≠ cc b` or `v ≠ e`. That is harmless: if `cc a = cc b`, it is the first case, and a tip is the end of only
   one edge. So the hypothesis set is exactly the paper's "one open edge, or two open edges with a common end
   `v`". Noted only for the record.

## Assessment of the specific encoding choices

* **Lemma 8.1 hypotheses and conclusion.** These are faithful.
  * `a, b ∉ vertices T` and `a ≠ b` encode "distinct edge points".
  * In a finite tree, `v ∈ vertices T ∧ v ∈ closure (cc a)` says exactly that `v` is an end of the edge of `a`.
    The edge closures meet the vertices only in the two ends, γ 0 and γ 1 (`IsEdgeParam`, `inter_vertices`).
  * The conclusion `IsLocalExtrOn (dist e) (cc a) a` includes non-strict extrema, matching the paper's definition
    in Lemma 2.8. Because `cc a` is open, it is the same as a local extremum of `h_e` at `a`. This is also exactly
    what 8.2(a) consumes, via `IsLocalExtrOn.param`.
* **8.2(a) as `InjOn`.** This is fine; see minor 2.
* **8.2(b).** The encoding is faithful:
  * `a, b ∉ vertices`, `cc a ≠ cc b` encode "two distinct open edges".
  * `v ∈ closure (cc a) ∩ closure (cc b)` encodes "at v", with `IsBranchPoint v`.
  * The tie is `dist e a = dist e b` and the conclusion is `dist v a = dist v b`.
* **Lemma 8.1, Step 2 in parameters (`noflip_core`).**
  * `Ties = {t ∈ [ta,t₁] : h_e(γ t) = h_e(b)}` is compact and nonempty, and `τ₀ = sSup Ties` is the tie nearest
    `s₁ = γ t₁`, as in the paper.
  * `τ₀ < t₁` because `sgnf (γ t₁) b e ≠ 0`.
  * On `(τ₀, t₁]` the function `σ0·f_{γ t,b}(e)` has no zero, so it is positive there (`const_sign`).
  * Orientation: when `t₁ < ta`, `lemma_8_1` calls `noflip_core` on the reversed parametrization `γ(1-·)`
    (ll. 310–316). The reversal correctly maps `[t₁,ta]` to `[1-ta,1-t₁]` (`image_symm_Icc`) and
    `γ '' Icc 0 1` to itself. Correct.
  * **Step 1.** The proof freezes signs only in the first site, `(s, b)` with `b` fixed. This is enough, because
    the paper's argument only ever uses pairs `(s, b)`.
  * `η` and `N₀` match the paper. `σ0 = -1` iff `N₀` is even. `count_of_frozen` gives
    `N(s,b) = N₀ + [f_{s,b}(e) < 0]` and strictness.
  * `a₀ ≠ b` follows from the radius bound `dist(γ t, a) < d(a,b)/2`. This plays the role of the paper's
    `U ∩ V = ∅`.
* **Step 3 via `center_eq_of_nhds`.**
  * For each `t ∈ L`, `cor_6_7` gives an open arc `V' ∋ b` on a sphere centred at `c'`. The reference pair
    `t₁` gives `V₁ ∋ b` centred at `c`.
  * `center_eq_of_nhds` (l. 36) takes a spherical arc inside the open set `V₁ ∩ V'` (`exists_sphericalArc_in`).
    Then `lemma_6_2(b)` uniqueness gives `c' = c`. This is literally the paper's `Q_s ∩ Q_{s'}` argument, an
    equality rather than a limit.
  * The invariant `d(c, γ t) = d(c, b)` on `L` then passes to `τ₀` by closedness (`closure_Ioc`), which is Step 4.
* **Step 5.**
  * The second zero `y₀ = m ρ` comes from the IVT on `seg(a₀,b)`. It is an interior point of the arc, so its order
    is at least 2, and therefore `y₀ ≠ e` because `e` is a tip. It is not a vertex, by the frozen signs.
  * `M(a₀,b) = {e, y₀}` follows from DMP and `encard_pair`. Since `c ∉ vertices`, `c ≠ e`, hence `c = y₀`.
  * `seg(a₀,b) ⊆ γ[0,1] ∪ closure(cc b)` is established in `lemma_8_1` (ll. 258–273, via `seg_subset` on a
    connected union).
  * Hence `y₀` lies in the open edge of `a` (`= W₁ ⊇ U₁`) or of `b` (`= W₂ ⊇ V₁`, via
    `IsOpenEdge.mem_of_mem_closure`). A spherical arc inside `U₁` or `V₁` with centre `c` in the same open edge
    contradicts `lemma_7_4`, the paper's Lemma 7.4 (`lem:ownedge`, "x ∉ ℓ°"). This matches the paper exactly,
    using the "c is an edge point" route rather than Lemma 7.1.
* **8.2(a) replacement of μ.** The replacement is valid.
  * Given `t₁ < t₂` in `(0,1)` with `φ t₁ = φ t₂`, non-constancy on `(t₁,t₂)` follows from `mem_centers_of_const`
    plus `lemma_7_1`, which is the paper's appeal to Lemma 7.1.
  * Pick `t ∈ (t₁,t₂)` with `φ t ≠ φ t₁`. Pick `λ` strictly between `φ t₁` and `φ t` and outside the countable set
    of local-extremum values of `φ : ℝ → ℝ` (`lemma_2_8_i`, `exists_mem_Ioo_notMem`).
  * The IVT on `[t₁,t]` and on `[t,t₂]` (using `φ t₂ = φ t₁`) gives `a ∈ (t₁,t)` and `b ∈ (t,t₂)` with
    `φ a = φ b = λ`. Strictness of the inclusions holds because `λ ≠ φ t₁, φ t`.
  * This needs no maximum point. Splitting at `t` gives the two sides, and it handles the "exceeds" and "falls
    below" cases at once. Everything the paper then uses holds:
    * `a ≠ b`;
    * both lie in the same open edge;
    * `M(γ a, γ b) = {e, γ ρ}` with `ρ ∈ (a,b)`, so no vertex `u ≠ e` is a zero;
    * Lemma 8.1 makes `a` a local extremum of `φ`, so `λ` is a local-extremum value, which is a contradiction.
  * Using local-extremum values of `φ` on all of `ℝ` rather than on `(0,1)` is harmless: at an interior `a`, an
    extremum on the open edge transfers to `φ` (`IsLocalExtrOn.param`).
  * The extension from `Ioo` to `Icc` (`strictMonoOn_Icc_of_Ioo`/`Anti`, which uses continuity) and from there to
    `InjOn` on `ℓ = γ[0,1]` is correct.
* **8.2(b).**
  * The midset is `{e, y}` with `y` interior to `seg a b ⊆ seg a v ∪ seg b v`.
  * `y ≠ v` because `h_v(a) ≠ h_v(b)`.
  * `y` is not a vertex, by `vertex_on_seg_to_end`: the only vertex on `seg(δ s, v)` for an end `v` is `v`.
  * `lemma_8_1` (second disjunct) then gives a local extremum of `h_e`, which contradicts the strict monotonicity
    from `prop_8_2_a` (`not_isLocalExtr_of_strictMono`). This is the paper's proof.

## Per-statement faithfulness table (Tips.lean)

| Line | Lean name | Paper | Assessment |
|---|---|---|---|
| 26 | `exists_sphericalArc_in` | auxiliary (used in Step 3/5) | Correct: an open set of edge points on `S(c,r)`, `r>0`, contains a spherical arc. |
| 36 | `center_eq_of_nhds` | Step 3 (`Q_s ∩ Q_{s'}` + Lemma 6.2(b)) | Correct, and it is the paper's argument. |
| 44 | `IsOpenEdge.mem_of_mem_closure` | auxiliary (Step 5) | Correct: a non-vertex in the closure of an open edge lies in it. |
| 54 | `IsLocalExtrOn.param` | auxiliary | Correct: an extremum on an open set pulls back along a continuous param. |
| 62 | `noflip_core` | Lemma 8.1 Steps 2–5 | Faithful parametric version. The hypotheses are discharged by `lemma_8_1`. |
| 172 | `count_of_frozen` | Step 1 (`N = N₀ + [f(e)<0]`) | Correct. |
| 215 | `lemma_8_1` | Lemma 8.1 | **Faithful.** The hypotheses are exactly the paper's (the second disjunct is harmlessly general). The conclusion is a local extremum, non-strict allowed, on the open edge of `a`. |
| 319 / 342 | `strictMonoOn_Icc_of_Ioo` / `strictAntiOn_Icc_of_Ioo` | auxiliary ("by continuity, on each edge") | Correct. |
| 352 | `prop_8_2_a` | Prop 8.2(a) | **Faithful** (`InjOn` ⇔ strictly monotone for a continuous function on an arc). The proof is a valid variant of the paper's. |
| 429 | `vertex_on_seg_to_end` | auxiliary (8.2(b): `y ≠ v` ⇒ `y` not a vertex) | Correct. |
| 450 | `prop_8_2_b` | Prop 8.2(b) | **Faithful.** `hbr` is redundant (minor 1). |
