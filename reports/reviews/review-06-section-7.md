# Review 06: Section 7 ("Where the center of a spherical arc can lie")

Files reviewed line by line:
- `DoubleMidset/EdgeTools.lean` (419 lines)
- `DoubleMidset/Centers.lean` (945 lines)

Paper: `dmp_paper_2.tex`, Section 7 (lines ~696-838): Lemmas 7.1-7.4.

## Verdict: ACCEPT WITH MINOR

No blockers and no major issues. All four statements match the paper. Every hypothesis is the
paper's or a harmless way of writing it down, and every conclusion is at least as strong as the
paper's. There is one small exception: Lemma 7.3(b)/(c) does not export that `p_z` exists and is
unique (see m1). The two proof deviations (in Lemma 7.1 and Lemma 7.4 Case 2) are sound, and in
Lemma 7.1 the parity statement obtained is exactly the paper's.

## Mechanical checks

| Check | Result |
|---|---|
| `lake build DoubleMidset` | `Build completed successfully (2184 jobs)`, 0 errors |
| `sorry/admit/axiom/native_decide/unsafe/implemented_by/opaque` in `DoubleMidset/` (including `Classical/`) | none found |
| `set_option`, `instance`, `attribute`, `@[simp]` in the two files | none |
| `#print axioms lemma_7_1` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms lemma_7_2` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms lemma_7_3` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms lemma_7_4` | `[propext, Classical.choice, Quot.sound]` |
| Warnings in the two files | only deprecations (`push_neg`, `if_pos/if_neg`, `Set.Finite.diff`, `Set.mem_setOf_eq`, `Set.diff_subset_iff`, `Set.Infinite.diff`) and 3 "automatically included section variable(s) unused" (EdgeTools:71, Centers:521, Centers:806) |

## Blockers

None.

## Major

None.

## Minor

- **m1 (Lemma 7.3(b)/(c), Centers.lean:552-554).** The paper's part (c) refers to "the point
  `p_z` of `(s,s')` with `h_e(p_z)=h_e(z)`". The paper's proof of (b) says this point exists and
  is unique. The Lean statement instead quantifies universally,
  `∀ pz ∈ k '' Ioo σ σ', dist e pz = dist e z → midset pz z = {e, x}`. This is at least as
  strong as the paper's claim about the unique `p_z`, and it is not vacuous: the proof builds
  `p_z` with `intermediate_value_Ioo` at line 649. But the existence of `p_z` is not part of the
  exported statement. It follows in a few lines from (a) and the IVT, so this is cosmetic.
  Consider adding `∃ pz ∈ k '' Ioo σ σ', dist e pz = dist e z` (uniqueness follows from (a)).
- **m2 (Centers.lean:546-554).** The set `Z` is written out four times in the statement of
  `lemma_7_3`. A local `def`/`abbrev` (for example `matchSet k σ σ'`) would make the statement
  easier to read and to check against the paper.
- **m3 (Centers.lean:880 and 883).** `ownedge_case2` calls `lemma_7_3` twice with the same
  arguments: once to destructure (b)/(c) and once to get openness. One `obtain` would do.
- **m4 (Centers.lean:398, 600).** `pos_of_mul_pos_left this hfq.le |>.trans_le' le_rfl`: the
  `.trans_le' le_rfl` does nothing.
- **m5.** There are 3 unused-section-variable warnings (`IsArcParam.seg_image` at EdgeTools:71,
  `IsTip.mem_oddVertices` at Centers:521, `IsEdgeParam.symm` at Centers:806). `omit ... in` or
  narrower instance arguments would remove them. The many deprecation warnings (`push_neg`, and
  so on) are harmless with the pinned Mathlib.
- **m6 (naming, EdgeTools.lean:194).** `exists_Icc_of_subset_edge` works for any `IsArcParam γ`,
  not only for edge parametrizations, so the name is slightly misleading. Its docstring is
  accurate.
- **m7 (Lemma 7.2 statement).** The paper's remark "its ends may be vertices" and the fact
  `x ∉ K` appear only in the proof. Both are informational and not needed downstream, so nothing
  is lost.

## Per-statement faithfulness

| Paper | Lean (file:line) | Hypotheses | Conclusion | Assessment |
|---|---|---|---|---|
| Lemma 7.1 (tips are not centers) | `lemma_7_1`, Centers.lean:248 | `TreeHyp T`, `HasDMP T`, `IsTip x`; `I`, `r` arbitrary | `¬ IsSphericalArc I x r` (an arc homeomorphic to [0,1], `r > 0`, `I ⊆ S(x,r)`) | Faithful. "Branched" is not assumed, which matches the paper's remark that 7.1 also holds for the arc. |
| Lemma 7.2 (the center is a crossing) | `lemma_7_2`, Centers.lean:37 | `x ∉ vertices T` (edge point), `0 < r`, `K = connectedComponentIn (sphere x r) z` with `z ∈ sphere x r`, `K.Nontrivial` | `IsArc K`; `∃ ℓ, IsEdge ℓ ∧ K ⊆ ℓ`; for all distinct `p, q ∈ K`: `IsStrictPair p q`, `Even (oddCount p q)`, `∃ y, midset p q = {x, y}`, `y` in every arc between `p` and `q` with `y ≠ p, q`, and `x` and `y` both crossings of `sgnf p q` | Faithful. Writing "`y ∈ (p,q)`" as "in every arc between p and q, distinct from both ends" is correct: arcs are unique in the dendrite, and an arc between `p` and `q` exists (`seg`), so the condition is not vacuous. Since `x ∉ K` and `y ∈ seg p q ⊆ K`, `x ≠ y`, so `{x, y}` really has two points. |
| Lemma 7.3 (matching beyond the center) | `lemma_7_3`, Centers.lean:541 | `IsEdge ℓ`; `k` continuous, `InjOn k [0,1]`, `k '' [0,1] = ℓ`; `IsTip (k 1)`; `0 < σ < σ' < ξ < 1`; `0 < r`; `k '' [σ,σ'] ⊆ S(k ξ, r)` | (a) `StrictMonoOn (dist (k 1) ∘ k) [σ,σ']`; (b) `Z` open, and for all `a ∈ k''(σ,σ')` there is `b ∈ Z` with `h_e b = h_e a`; (c) `Z ⊆ S(x,r) ∩ k''(ξ,1)`, and for all `z ∈ Z` and all `pz ∈ k''(σ,σ')` with `h_e pz = h_e z`, `M(pz,z) = {e,x}` | Faithful, with m1. Using an explicit parametrization is harmless: by `exists_param_of_isEdge` (reversed with `IsEdgeParam.symm` if needed) every configuration in the paper has such a `k` with `e = k 1`, and `isEdgeParam_of_isEdge` shows that `k 0`, `k 1` are the ends and `k(0,1)` is the open edge. So `σ > 0` and `ξ < 1` say exactly that `s, s', x` are edge points of `ℓ`, and increasing parameter is the order "towards `e`". `Z` is the paper's `{z ∈ (s',e) : h_e(s) < h_e(z) < h_e(s')}` with `(s',e) = k''(σ',1)`, and `(x,e) = k''(ξ,1)`. "`Z ≠ ∅`" follows from (b). |
| Lemma 7.4 (no center in the arc's own edge) | `lemma_7_4`, Centers.lean:900 | `HasDMP T`, `∃ v, IsBranchPoint v`, `IsSphericalArc I x r`, `IsOpenEdge W`, `I ⊆ W` | `x ∉ W` | Faithful (`W` = `ℓ°`). |
| Case 1 of 7.4 | `ownedge_case1`, Centers.lean:811 | edge parametrization `γ`, `γ 0` a branch point, `0 < ξ < α < β < 1`, `γ[α,β] ⊆ S(γ ξ, r)` | `False` | Matches the paper's Case 1 (`x` between `w` and `I`). It uses Lemma 4.3 (`lemma_4_3`) for `h_w(p) ≤ h_w(q)`. |
| Case 2 of 7.4 | `ownedge_case2`, Centers.lean:872 | as above, with `0 < α < β < ξ < 1` | `False` | Matches the paper. If `γ 1` is a branch point, it reverses the edge and applies Case 1. Otherwise `γ 1` is a tip (`end1` resolved), and it applies Lemma 7.3 and then Case 1 to a parameter interval `[t₀-η', t₀+η'] ⊆ γ⁻¹(Z) ∩ (ξ,1)`. This is the paper's `I₂`. |

## Soundness of the proof deviations

### Lemma 7.1: modified function instead of cutting the tree

The paper cuts off `(x',x]` to get a tree `T'` and applies the parity lemma there. The Lean proof
(Centers.lean:400-473) stays on `T` and uses `g = max(f_{p,q}, δ − d(x,·))`, where:
- `δ ≤ δ₁/2`, and `tip_nhds` gives `ball x δ₁ ⊆ k '' [0,τ)` (the part of `[x, s]` from `x` to just
  before `q`) and `δ₁ ≤ d(x,u)` for every vertex `u ≠ x`;
- `δ ≤ r/2`, so `g(p) = max(f(p), δ − r) < 0`.

I checked the following:
1. **Zeros (`hgzero`).** `g(z) = 0 ⟺ z = y`. On the closed ball `d(x,z) ≤ δ`, `g(x) ≥ δ > 0`, and
   for `z ≠ x`, `f(z) > 0` (`hnear`, from `hpos`: `f > 0` on `k''(0,τ]`). Off the ball,
   `δ − d < 0`, so `g = 0` forces `f = 0`, which forces `z ∈ {x, y}`, so `z = y`. Also
   `d(x,y) > δ`, so `g(y) = f(y) = 0`.
2. **Crossing (`hcross`).** `y` is the only zero of `g` on `[p,q]`, `g(p) < 0 < g(q)`, and `y` is
   not a vertex (by the choice of `p`). `isCrossing_of_arc` then gives `IsCrossing g y`. So the
   set of crossings of `g` is exactly `{y}`. This matches the paper's "single zero, which is a
   crossing" on `T'`.
3. **Vertex signs (`hS`).** `g(x) > 0`. For a vertex `u ≠ x`, `d(x,u) ≥ δ₁ > δ`, so
   `g(u) < 0 ⟺ f(u) < 0`. Hence `{u ∈ Odd : g u < 0} = {u ∈ Odd : u ≠ x ∧ f u < 0}`.
4. `lemma_5_4` on `T` then gives `1 ≡ |{u ∈ Odd \ {x} : f_{p,q}(u) < 0}| (mod 2)`. This is
   exactly the parity statement the paper derives on `T'`. The new tip `x'` of `T'` has
   `f(x') > 0` and so does not contribute there either.

The rest follows the paper. `b = k tb`, with `tb < τ` close to `τ`, lies on `(q, x]` near `q`, so
`h_x(b) < r` (`hbelow`). Sign persistence at the vertices `≠ x`, together with
`f_{p,b}(x) = r − h_x(b) > 0`, gives a strict pair `(p,b)` with `N` odd. This contradicts
`lemma_6_3` at the interior point `p` of `I₀`. The arc `I` is shrunk to the middle third `I₀` so
that it lies in the open edge (the paper's "shrink `I`"). `s` is obtained with `exists_exit`, and
`q` as the infimum of the parameters on the sphere along `k` from `x`. Both match the paper. The
deviation is sound and arguably simpler, since it avoids building `T'` and its vertex and odd
sets.

### Lemma 7.2

The proof follows the paper: the exit end `q₀` via `exists_exit`, off-sphere points accumulating
at `q₀` (`hacc`), and `N(p,q₀)` even via `strict_nhds` and `lemma_6_3`. It then transfers to
every pair using strict monotonicity of `h_u` on all of `K`. Lean proves this directly on `Icc α β`
with `strictMonoOn_of_injOn_Icc'`, treating separately a vertex `u` that is an end of `K`. This
is the paper's "detour through the interior". It uses `even_oddCount_swap` for reversed order and
`cor_5_5` for the crossings. Sound.

### Lemma 7.3

(a) uses the sign table of the paper: zeros of `f_{p,q}` only at `y ∈ (t₁,t₂)` and at `ξ`, with
`f > 0` on `(ρ, ξ)`, a crossing at `ξ`, and so `f < 0` on `(ξ,1]`, hence `f(e) < 0`. (b) uses the
IVT on `[σ', 1]`. (c) argues by contradiction with `h_x(z) ≠ r`. `M(p_z,z) = {e, y'}` with `y'` in
the open edge, so all other vertex signs are nonzero. `sign_persist` gives two sites `tp ± η'`
whose counts differ by exactly the tip `e` (`he.mem_oddVertices`). Both are even by `lemma_6_3`,
a contradiction. Then `M = {e,x}`, and the zero of `f` on `[p_z, z]` must be `x`, so `tz > ξ`.
This matches the paper.

### EdgeTools

All the tools are generic and correctly stated. `isEdgeParam_of_isEdge` is used to turn the
arbitrary parametrization `k` of Lemma 7.3 into an edge parametrization: any arc
parametrization of an edge has the two vertices at its ends and none inside. `tip_nhds` gives
small balls around a tip inside any arc from it (proved via the order-1 / triod argument), and
`exists_exit` shows that the first entry into a subarc of an edge is at one of its ends. I found
no problems.

## Vacuity

The hypotheses of each lemma are consistent with the paper's setting and are not artificially
strengthened. Like the paper's lemmas, they become vacuous once the main theorem shows that no
finite tree has the DMP. That is inherent to the proof by contradiction, not a defect of the
formalization. Inside the proofs the existential witnesses are built explicitly (an arc between
`p` and `q`, the point `p_z`, the site `b`).
