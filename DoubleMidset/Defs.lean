module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Data.Set.Card

/-!
# Definitions

The definitions used in the statements of the paper "The Double Midset Conjecture for Metric
Continua" (Lucas Alves de Almeida, 22 November 2026). `Challenge.lean` copies this
file verbatim.

Conventions.

* A *continuum* is a nondegenerate compact connected metric space. For a type with a
  `MetricSpace` instance "compatible metric" is automatic: the topology is the one of the metric.
* The *midset* of `a` and `b` is `{x | d(x, a) = d(x, b)}`; cardinalities are `Set.encard`
  (with value `⊤` for infinite sets), so `encard = 2` means "exactly two points".
* Arcs, simple closed curves and simple triods are subsets homeomorphic to `[0,1]`, to the circle
  `Circle ⊆ ℂ`, and to the union of three arcs meeting only in a common end.
* The *order* of a point `p` is the number of components of `X \ {p}`, a value in `ℕ∞`
  (`⊤` stands for any infinite number).
* Vertices, open edges and edges of a finite tree are defined intrinsically: vertices are the tips
  and the branch points, open edges are the components of the complement of the set of vertices,
  and edges are the closures of open edges. Lemma 2.7 (`lemma_2_7`) shows that these edges have
  the properties the paper lists.
-/

@[expose] public section

open Set Topology Metric

namespace DoubleMidset

universe u

section Metric

variable {X : Type u} [MetricSpace X]

/-- The *midset* (equidistant set, bisector) of the sites `a` and `b`:
`M(a, b) = {x ∈ X : d(x, a) = d(x, b)}`. -/
def midset (a b : X) : Set X := {x | dist x a = dist x b}

/-- The *double midset property*: `|M(a, b)| = 2` for all distinct `a, b`. -/
def HasDMP (X : Type u) [MetricSpace X] : Prop :=
  ∀ a b : X, a ≠ b → (midset a b).encard = 2

/-- The upper bound `|M(a, b)| ≤ 2` for all distinct `a, b`. -/
def MidsetsAtMostTwo (X : Type u) [MetricSpace X] : Prop :=
  ∀ a b : X, a ≠ b → (midset a b).encard ≤ 2

/-- The sign function `f_{a,b}(y) = d(y, a) - d(y, b)` (Definition 2.1). -/
def sgnf (a b : X) (y : X) : ℝ := dist y a - dist y b

end Metric

section Topology

variable {X : Type u} [TopologicalSpace X]

/-- `A ⊆ X` is an *arc*: homeomorphic to `[0,1]`. -/
def IsArc (A : Set X) : Prop := Nonempty (A ≃ₜ unitInterval)

/-- `A` is an arc with ends `p` and `q`: the image of an embedding `f` of `[0,1]` with
`f 0 = p` and `f 1 = q`. -/
def IsArcBetween (A : Set X) (p q : X) : Prop :=
  ∃ f : unitInterval → X, IsEmbedding f ∧ range f = A ∧ f 0 = p ∧ f 1 = q

/-- `C ⊆ X` is a *simple closed curve*: homeomorphic to the circle. -/
def IsSimpleClosedCurve (C : Set X) : Prop := Nonempty (C ≃ₜ Circle)

/-- `Y ⊆ X` is a *simple triod*: the union of three arcs that pairwise meet only in a common
end `v`. -/
def IsSimpleTriod (Y : Set X) : Prop :=
  ∃ (v p₁ p₂ p₃ : X) (A₁ A₂ A₃ : Set X), IsArcBetween A₁ v p₁ ∧ IsArcBetween A₂ v p₂ ∧
    IsArcBetween A₃ v p₃ ∧ A₁ ∩ A₂ = {v} ∧ A₁ ∩ A₃ = {v} ∧ A₂ ∩ A₃ = {v} ∧ Y = A₁ ∪ A₂ ∪ A₃

/-- The *order* of a point `p`: the number of components of `X \ {p}`. -/
noncomputable def order (p : X) : ℕ∞ :=
  {C : Set X | ∃ x, x ≠ p ∧ C = connectedComponentIn {p}ᶜ x}.encard

/-- A *tip* (end): a point of order one. -/
def IsTip (p : X) : Prop := order p = 1

/-- A *branch point*: a point of order at least three. -/
def IsBranchPoint (p : X) : Prop := 3 ≤ order p

/-- A *continuum*: a nondegenerate compact connected metrizable space. -/
def IsContinuum (X : Type u) [TopologicalSpace X] : Prop :=
  CompactSpace X ∧ ConnectedSpace X ∧ Nontrivial X ∧ TopologicalSpace.MetrizableSpace X

/-- A *dendrite*: a locally connected continuum that contains no simple closed curve. -/
def IsDendrite (X : Type u) [TopologicalSpace X] : Prop :=
  IsContinuum X ∧ LocallyConnectedSpace X ∧ ∀ C : Set X, ¬ IsSimpleClosedCurve C

/-- A *finite tree* (Definition 2.6): a dendrite with finitely many branch points, each of finite
order. -/
def IsFiniteTree (X : Type u) [TopologicalSpace X] : Prop :=
  IsDendrite X ∧ {p : X | IsBranchPoint p}.Finite ∧ ∀ p : X, IsBranchPoint p → order p ≠ ⊤

/-- The *vertices*: the tips and the branch points. -/
def vertices (X : Type u) [TopologicalSpace X] : Set X := {p | IsTip p ∨ IsBranchPoint p}

/-- The vertices of odd degree (order). -/
def oddVertices (X : Type u) [TopologicalSpace X] : Set X :=
  {p | p ∈ vertices X ∧ ∃ n : ℕ, order p = n ∧ Odd n}

/-- An *open edge*: a component of the complement of the set of vertices. -/
def IsOpenEdge (W : Set X) : Prop :=
  ∃ x, x ∉ vertices X ∧ W = connectedComponentIn (vertices X)ᶜ x

/-- An *edge*: the closure of an open edge. -/
def IsEdge (ℓ : Set X) : Prop := ∃ W, IsOpenEdge W ∧ ℓ = closure W

/-- An *open arc*: an open subset homeomorphic to an open interval. -/
def IsOpenArc (U : Set X) : Prop := IsOpen U ∧ Nonempty (U ≃ₜ Ioo (0 : ℝ) 1)

/-- A zero `y` of `g` that is an edge point is a *crossing* (Definition 5.3): for a small open
arc `J ∋ y` in its open edge with `J ∩ g⁻¹(0) = {y}`, `g` has opposite signs on the two sides of
`y` (the two components of `J \ {y}`). -/
def IsCrossing (g : X → ℝ) (y : X) : Prop :=
  y ∉ vertices X ∧ g y = 0 ∧ ∃ J : Set X, IsOpenArc J ∧ y ∈ J ∧ (∃ W, IsOpenEdge W ∧ J ⊆ W) ∧
    J ∩ g ⁻¹' {0} = {y} ∧
    ∀ z₁ ∈ J \ {y}, ∀ z₂ ∈ J \ {y},
      connectedComponentIn (J \ {y}) z₁ ≠ connectedComponentIn (J \ {y}) z₂ → g z₁ * g z₂ < 0

/-- A zero `y` of `g` that is an edge point is a *touch* (Definition 5.3): for a small open arc
`J ∋ y` in its open edge with `J ∩ g⁻¹(0) = {y}`, `g` has the same sign on the two sides of
`y`. -/
def IsTouch (g : X → ℝ) (y : X) : Prop :=
  y ∉ vertices X ∧ g y = 0 ∧ ∃ J : Set X, IsOpenArc J ∧ y ∈ J ∧ (∃ W, IsOpenEdge W ∧ J ⊆ W) ∧
    J ∩ g ⁻¹' {0} = {y} ∧
    ∀ z₁ ∈ J \ {y}, ∀ z₂ ∈ J \ {y},
      connectedComponentIn (J \ {y}) z₁ ≠ connectedComponentIn (J \ {y}) z₂ → 0 < g z₁ * g z₂

end Topology

section TreeMetric

variable {X : Type u} [MetricSpace X]

/-- A *strict pair* (Definition 5.2): distinct sites such that no vertex is equidistant from
them. -/
def IsStrictPair (a b : X) : Prop := a ≠ b ∧ ∀ u ∈ vertices X, sgnf a b u ≠ 0

/-- `N(a, b)`: the number of odd-degree vertices closer to `a` than to `b` (Definition 5.2). -/
noncomputable def oddCount (a b : X) : ℕ := {u | u ∈ oddVertices X ∧ sgnf a b u < 0}.ncard

/-- A *spherical arc* with center `x` and radius `r` (Definition 6.1): a (nondegenerate) arc
contained in the metric sphere `S(x, r)` with `r > 0`. -/
def IsSphericalArc (I : Set X) (x : X) (r : ℝ) : Prop :=
  IsArc I ∧ 0 < r ∧ I ⊆ sphere x r

/-- A *box* (Definition 6.4): two disjoint open arcs `U` and `V`, each contained in an open
edge. -/
def IsBox (U V : Set X) : Prop :=
  IsOpenArc U ∧ IsOpenArc V ∧ Disjoint U V ∧ (∃ W, IsOpenEdge W ∧ U ⊆ W) ∧
    ∃ W, IsOpenEdge W ∧ V ⊆ W

/-- An *odd box*: a box all of whose pairs are strict with `N` odd. -/
def IsOddBox (U V : Set X) : Prop :=
  IsBox U V ∧ ∀ a ∈ U, ∀ b ∈ V, IsStrictPair a b ∧ Odd (oddCount a b)

/-- A tip `e` *uses* the pair `{ℓ, ℓ'}` of edges at a branch point `v` (Definition 9.1): the
function `h_e = d(e, ·)` has the same direction on `ℓ` and on `ℓ'` in the direction away from
`v`. (By Proposition 8.2 (a), `h_e` is strictly monotone on each edge, so its direction on an edge
at `v` is decided by comparing `h_e(a)` with `h_e(v)` for any point `a ≠ v` of the edge.) -/
def UsesPair (e v : X) (ℓ ℓ' : Set X) : Prop :=
  ∀ a ∈ ℓ, ∀ a' ∈ ℓ', a ≠ v → a' ≠ v → (dist e v < dist e a ↔ dist e v < dist e a')

end TreeMetric

end DoubleMidset
