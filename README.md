# The Double Midset Conjecture for Metric Continua — Lean 4 formalization

Lean 4 / Mathlib formalization of the paper *The Double Midset Conjecture for Metric Continua*
(Lucas Alves de Almeida, 22 November 2026). The paper proves the Loveland–Wayment conjecture
(1974).

* **Theorem A** (`theorem_A`): a nondegenerate compact connected metric space in which every two
  distinct points have exactly two equidistant points (the *double midset property*, DMP) is
  homeomorphic to the circle. Its converse, that the Euclidean circle has the DMP, is
  `circle_hasDMP`. The resulting characterization (`theorem_A_iff`) says that a metrizable
  continuum admits a compatible DMP metric if and only if it is a simple closed curve.
* **Theorem B** (`theorem_B`): no finite tree admits a compatible metric with the DMP. In
  particular neither an arc nor a simple triod does.
* **Theorem C** (`theorem_C`): under the upper bound `|M(a, b)| ≤ 2`, a dendrite has order at
  most 4 everywhere, satisfies `(m - 2)(|B| - 1) ≤ m`, has at most four branch points, and is a
  finite tree.

Every definition, lemma, fact (in the form used), proposition, corollary and theorem of
Sections 2–12 is formalized: 47 compared statements in `Challenge.lean`. Examples, figures,
remarks and the questions of Section 13 are out of scope. R. L. Moore's general theorem
(Fact 2.5) is formalized only in the consequence form the paper uses: a dendrite without branch
points is an arc.

## Layout

| Path | Contents |
|---|---|
| `Challenge.lean` | Statement surface: the definitions, copied verbatim from `DoubleMidset/Defs.lean`, and the 47 statements, each closed by `sorry` (imports Mathlib only) |
| `Solution.lean` | The same 47 statements, proved from the library |
| `DoubleMidset/` | The library (about 11,000 lines, no `sorry`) |
| `DoubleMidset/Classical/` | Classical facts not in Mathlib: arcs in Peano continua, uniform local connectedness, boundary bumping |
| `comparator.json` | Comparator configuration: the 47 theorem names, permitted axioms, nanoda enabled |
| `formalization.yaml` | Metadata, scope, fidelity notes and the statement-by-statement alignment |
| `scripts/` | `verify_all.sh` (all checks), `check_sources.py`, `axioms.lean`, `check_axioms.py` |
| `reports/` | Verification report, the per-file reviews and the final comparison with the paper |

### Library modules, in paper order

| Paper | Modules |
|---|---|
| §2 Preliminaries | `Defs`, `Arc`, `Circle`, `Dendrite` (Fact 2.3), `Order` (Lemma 2.4), `NoBranch` (Fact 2.5, consequence form), `TreeStructure` and `Edges` (Lemma 2.7 and the paragraph after it), `Extrema` (Lemmas 2.2, 2.8, 2.9) |
| §3 Reduction to dendrites | `Reduction` (Props 3.1, 3.2, Cor 3.4) |
| §4 Branch points | `Branch` (Lemmas 4.2–4.4, Theorem 4.5, Cor 4.6, Theorem C) |
| §5 Signs on a finite tree | `ParamParity`, `Crossing`, `Parity` (Lemma 5.4), `Types` (Cor 5.5, Lemma 5.6) |
| §6 Spherical arcs, odd boxes | `Spherical` (Lemmas 6.2, 6.3), `OddBox` (Lemma 6.6, Prop 6.5, Cor 6.7) |
| §7 Centers | `EdgeTools`, `Centers` (Lemmas 7.1–7.4) |
| §8 Distances to tips | `Tips` (Lemma 8.1, Prop 8.2) |
| §9 Counting tips | `Count` (Def 9.1 in `Defs`, Lemma 9.2, Prop 9.3) |
| §10, §11 | `Triod` (Theorem 10.1 in tree form), `ArcCase` (Theorem 11.1 in tree form) |
| §12 Main theorems | `Main` (Theorems A, B; converse; characterization), `Special` (arcs and simple triods are finite trees; Theorems 10.1, 11.1) |

## Conventions and fidelity

* Metric spaces are Mathlib `MetricSpace`s, so "compatible metric" is automatic.
  `theorem_A_iff` quantifies over metrics whose topology equals the given one.
* `HasDMP X` means `(midset a b).encard = 2` for all `a ≠ b`. The weaker `MidsetsAtMostTwo`
  (`≤ 2`) is used where the paper only needs the upper bound (Section 4, Lemma 6.2).
* The standing conventions are explicit hypotheses: `IsDendrite X` with `MidsetsAtMostTwo X` in
  Section 4, and `IsFiniteTree T` with `HasDMP T` in Sections 5–11.
* The vertices of a finite tree are its tips and branch points. Its open edges are the
  components of the complement of the vertices, and its edges are their closures.
  `lemma_2_7` proves these have the paper's properties.
* Orders take values in `ℕ∞`. Crossings and touches are defined through an open arc around the
  zero inside an open edge.
* "Strictly monotone along an arc" is stated as injectivity on the arc. For continuous
  functions on arcs the two are equivalent.

`formalization.yaml` (field `fidelity`) lists every divergence, and the reports in `reports/`
discuss the proof techniques that differ from the paper's.

## Building and checking

Requirements: the toolchain in `lean-toolchain` (Lean v4.35.0-rc2) and Mathlib at the pinned
revision.

```sh
lake build                      # library, Challenge, Solution
lake env lean scripts/axioms.lean | python3 scripts/check_axioms.py
lake comparator --config comparator.json
bash scripts/verify_all.sh      # every check, with logs in logs/verify-*/
```

`verify_all.sh` runs the following steps:

* the static source checks;
* a clean build;
* the axiom audit;
* Comparator with the Lean kernel and nanoda;
* `lake check` and `lake check --paranoid`;
* Comparator `--paranoid`;
* a Palomar-style configuration with the external kernels nanoda and con-ron;
* two negative controls, a `sorry` in `Solution.lean` and an altered definition in
  `Challenge.lean`, which must both be rejected.

Without `bwrap` the sandboxed steps are recorded as not run. With `ALLOW_NO_SANDBOX=1` they are
also run unsandboxed and labelled `-NOSANDBOX`. The results of the run used for this snapshot
are in `reports/verification_report.md`.

## Provenance

Claude Opus 5.5 wrote all the Lean code in agent sessions. After each batch of files, a fresh
agent with no memory of the work reviewed it line by line, and a final fresh agent compared every
statement with the paper; their reports are in `reports/`. No human has reviewed the Lean
statements.

## Licence

Apache-2.0 (see `LICENSE`).
