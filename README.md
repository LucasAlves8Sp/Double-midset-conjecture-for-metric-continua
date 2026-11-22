# The Double Midset Conjecture for Metric Continua

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24447757.svg)](https://doi.org/10.5281/zenodo.24447757)
[![Hexagon](https://img.shields.io/badge/hexagon-2611.00899_(in_moderation)-9ca3af.svg)](https://hexagonmath.org/)
[![Lean 4](https://img.shields.io/badge/Lean_4-all_results_of_Sections_2--12_formalized-2f6f4f.svg)](lean/)

**Lucas Alves de Almeida** (independent researcher)

**Main result.** Let $(X,d)$ be a nondegenerate compact connected metric space in which every two distinct points have exactly two equidistant points (the *double midset property*, DMP). Then **$X$ is homeomorphic to a circle**. This settles the double midset conjecture of Loveland and Wayment (1974) with no assumption on the metric beyond compatibility with the topology. Consequently, a metrizable continuum admits a compatible metric with the DMP if and only if it is a simple closed curve. **Every result of Sections 2–12 of the paper is formalized in Lean 4 with Mathlib**; the examples, figures, remarks and the questions of Section 13 are not.

| | |
| --- | --- |
| Paper (PDF) | [`paper/double-midset-conjecture.pdf`](paper/double-midset-conjecture.pdf) |
| Zenodo | [doi:10.5281/zenodo.24447758](https://doi.org/10.5281/zenodo.24447758) (all versions: [10.5281/zenodo.24447757](https://doi.org/10.5281/zenodo.24447757)), published 22 November 2026 |
| Hexagon preprint | hexagon:2611.00899v1 [math.GN], submitted 22 November 2026, awaiting moderation |
| Lean formalization | [`lean/`](lean/); 47 statements compared by Comparator, main theorem `DoubleMidset.Paper.theorem_A` |
| Palomar | submission of commit [`aa5681a`](https://github.com/LucasAlves8Sp/Double-midset-conjecture-for-metric-continua/tree/aa5681a7c48f59e8eb59b492989781ddd79ea98b) (branch [`palomar`](https://github.com/LucasAlves8Sp/Double-midset-conjecture-for-metric-continua/tree/palomar)), 22 November 2026; Palomar's sandboxed mechanical verification [completed successfully](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45061350900); automated review pending; not yet registered |
| Review and verification | [`REVIEW_AND_VERIFICATION.md`](REVIEW_AND_VERIFICATION.md) |
| AI disclosure | [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md) |

## Abstract

Let $(X,d)$ be a nondegenerate compact connected metric space such that, for any two distinct points $a,b\in X$, exactly two points of $X$ are equidistant from $a$ and $b$. We prove that $X$ is homeomorphic to a circle. This settles the double midset conjecture of Loveland and Wayment from 1974. It was previously known for plane continua with the Euclidean metric and under additional convexity or continuity hypotheses. No assumption on the metric is made beyond compatibility with the topology. We first show that a counterexample would be a finite tree. On a finite tree, a parity count of the sign changes of $d(\cdot,a)-d(\cdot,b)$, combined with a Baire category argument, forces whole intervals onto metric spheres. This rigidity is incompatible with a branch point and with an arc. The results of the paper are formalized in Lean 4.

**Main theorems.**

- **Theorem A.** A nondegenerate compact connected metric space with the DMP is homeomorphic to $S^1$. A nondegenerate metrizable continuum admits a compatible metric with the DMP if and only if it is a simple closed curve.
- **Theorem B.** No finite tree admits a compatible metric with the DMP. In particular, neither an arc nor a simple triod does.
- **Theorem C.** If a dendrite has a compatible metric with $|M(a,b)|\le 2$ for all distinct $a,b$, then every point has order at most four, the set $B$ of branch points satisfies $(m-2)(|B|-1)\le m$ when there is a branch point of order $m$, so $|B|\le 4$, and the dendrite is a finite tree.

Section 13 records which strengths of the hypothesis are used where, asks whether continua with $|M(a,b)|=n$ for all distinct $a,b$ must have $n\le 2$, and states the higher-dimensional **$(n-1)$-sphere midset conjecture** (a continuum all of whose midsets are $(n-1)$-spheres is an $n$-sphere), with questions on the case $n=2$.

## Contents

| Path | Description |
| --- | --- |
| [`paper/double-midset-conjecture.pdf`](paper/double-midset-conjecture.pdf) | The paper (PDF, 26 pages, 22 November 2026) |
| [`paper/double-midset-conjecture.tex`](paper/double-midset-conjecture.tex) | LaTeX source (`amsart`, figures in TikZ, bibliography inline) |
| [`lean/`](lean/) | Lean 4 / Mathlib formalization; see [`lean/README.md`](lean/README.md) |
| [`lean/reports/`](lean/reports/) | Verification report and the reviews by fresh AI agents |
| [`lean/logs/`](lean/logs/) | Logs of the last full verification run |
| [`REVIEW_AND_VERIFICATION.md`](REVIEW_AND_VERIFICATION.md) | Coverage of the paper by the Lean code, divergences, and the checks performed |
| [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md) | The AI disclosure and the formalization statement, as they appear in the paper |
| [`LICENSE.md`](LICENSE.md) | CC BY 4.0 for the paper and texts; Apache-2.0 for the Lean code |

## The Lean formalization

The folder [`lean/`](lean/) contains a Lean 4 / Mathlib development that proves **every definition, lemma, proposition, corollary and theorem of Sections 2–12 of the paper**, and the facts of Section 2 in the form in which they are used: 47 statements, collected in `lean/Challenge.lean` and proved under the same names in `lean/Solution.lean`. It uses Lean `v4.35.0-rc2` and Mathlib at the tag of the same name, has about 11,000 lines in 31 library files, and uses the Lean module system throughout. There is no `sorry` outside `Challenge.lean` and no added axiom: all 47 compared results depend only on `propext`, `Classical.choice` and `Quot.sound`.

The main theorem and the characterization are

```lean
theorem DoubleMidset.Paper.theorem_A {X : Type u} [MetricSpace X]
    [CompactSpace X] [ConnectedSpace X] [Nontrivial X] (h : HasDMP X) :
    Nonempty (X ≃ₜ Circle)

theorem DoubleMidset.Paper.theorem_A_iff {Y : Type u} [t : TopologicalSpace Y]
    (hY : IsContinuum Y) :
    (∃ m : MetricSpace Y, m.toUniformSpace.toTopologicalSpace = t ∧ @HasDMP Y m) ↔
      Nonempty (Y ≃ₜ Circle)
```

where `HasDMP X` means `(midset a b).encard = 2` for all `a ≠ b`, `midset a b = {x | dist x a = dist x b}`, and `IsContinuum Y` says that `Y` is a nondegenerate compact connected metrizable space (see `lean/Challenge.lean`).

**Not formalized:** the examples, the figures, the remarks and the questions of Section 13. R. L. Moore's theorem (Fact 2.5) is formalized only in the consequence the paper uses (a dendrite without branch points is an arc), and equation (5) only as the parity statement. `lean/formalization.yaml` lists every divergence between the formal and the written statements.

**Checks** (details in [`lean/reports/verification_report.md`](lean/reports/verification_report.md)):

| Check | Result |
| --- | --- |
| clean `lake build` against the pinned Mathlib | no errors; the only `sorry`s are the deliberate ones in `Challenge.lean` |
| axiom audit (all 47 compared results) | only `propext`, `Classical.choice`, `Quot.sound` |
| `lake comparator`, `Solution` against `Challenge` | accepted by the Lean kernel and nanoda (unsandboxed run) |
| `lake comparator --paranoid` | accepted by the Lean paranoid kernel, lean4lean, nanoda, con-leche, con-ron and the Lean kernel (unsandboxed) |
| Palomar-style run with nanoda and con-ron as external kernels | accepted (unsandboxed) |
| `lake check --paranoid` on the whole project export | five checkers accept; nanoda ran out of memory in the 8 GB workspace (exit 137), so this step is recorded as failed |
| negative controls (a `sorry` in `Solution.lean`; an altered definition in `Challenge.lean`) | both rejected, as they should be |
| Palomar's mechanical verification (sandboxed, Lean kernel and nanoda) | [passed](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45061350900) on 22 November 2026 |

The local runs were unsandboxed, because bubblewrap was not available where the code was written. Palomar's verification above is the sandboxed Comparator run. The [CI workflow](.github/workflows/ci.yml) runs the whole suite sandboxed on GitHub Actions; its first complete attempt (22 November 2026) built the project and passed the static checks and the axiom audit, but the runner was shut down during `lake check --paranoid` on the whole export, so that run gives no result for the later steps.

## Building

**Paper.** In `paper/`, run `latexmk -pdf double-midset-conjecture.tex`.

**Lean.** In `lean/`, with Lean `v4.35.0-rc2` (installed by `elan` from `lean-toolchain`):

```
lake exe cache get
lake build                           # library and Solution
lake build Challenge                 # the statement file
lake env lean scripts/axioms.lean | python3 scripts/check_axioms.py
lake comparator --config comparator.json   # needs bubblewrap
bash scripts/verify_all.sh           # every check, logs in logs/verify-*/
```

## How to cite

Lucas Alves de Almeida, *The Double Midset Conjecture for Metric Continua*, preprint, Zenodo, 2026. [doi:10.5281/zenodo.24447757](https://doi.org/10.5281/zenodo.24447757). Also submitted to Hexagon as hexagon:2611.00899v1 (in moderation).

The concept DOI above always resolves to the latest version.

| Version | Content | DOI |
| --- | --- | --- |
| v1 | paper (PDF), 22 November 2026 | [10.5281/zenodo.24447758](https://doi.org/10.5281/zenodo.24447758) |

```bibtex
@misc{AlvesdeAlmeida2026doublemidset,
  author    = {Alves de Almeida, Lucas},
  title     = {The Double Midset Conjecture for Metric Continua},
  year      = {2026},
  publisher = {Zenodo},
  note      = {Preprint},
  doi       = {10.5281/zenodo.24447757},
  url       = {https://doi.org/10.5281/zenodo.24447757}
}
```

## Status

No independent expert has yet verified the proofs, and no human has yet compared the Lean statements with the paper; that comparison has been made only by AI agents (see `lean/reports/reviews/`). The work was done with extensive AI assistance; see [`AI_DISCLOSURE.md`](AI_DISCLOSURE.md).
