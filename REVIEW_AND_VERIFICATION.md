# Review and verification

This file records the coverage of the paper by the Lean formalization, how the formal statements differ from the written ones, the reviews, and the checks run. The paper is the version of 22 November 2026 in `paper/`. The Lean development is in `lean/`; the verification report is [`lean/reports/verification_report.md`](lean/reports/verification_report.md) and its logs are in [`lean/logs/`](lean/logs/).

## 1. Outcome

**Every definition, lemma, proposition, corollary and theorem of Sections 2–12 of the paper is proved in Lean 4**, together with the facts of Section 2 in the form in which they are used: 47 statements compared by Comparator. There is no `sorry` outside `Challenge.lean`, and the only axioms are Lean's standard three, `propext`, `Classical.choice` and `Quot.sound` (`lean/scripts/axioms.lean`).

* **Size.** About 11,000 lines in 31 library files (`lean/DoubleMidset/`), plus `Challenge.lean` (574 lines) and `Solution.lean`.
* **Not formalized.** The examples, the figures, the remarks and the questions of Section 13 (including the $(n-1)$-sphere midset conjecture). R. L. Moore's theorem behind Fact 2.5 is formalized only in the consequence the paper uses: a dendrite without branch points is an arc.
* **Classical facts proved along the way** (not in Mathlib): arcs in Peano continua, uniform local connectedness, boundary bumping (`lean/DoubleMidset/Classical/`).
* **The formalization found no mathematical gap** in the paper.
* **Palomar.** Registered as [PALOMAR-2026-11-22-000025 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-22-000025&version=1) on 22 November 2026, from commit `aa5681a` (branch `palomar`).
* **Not yet done.** No human has refereed the paper, and no human has compared the Lean statements with the paper. That comparison needs only `lean/Challenge.lean` and the paper.

**What one must trust:** the Lean kernel; Mathlib's definitions of the objects in the statements (metric spaces, `CompactSpace`, `ConnectedSpace`, `Set.encard`, `Homeomorph`, `Circle`); and the definitions at the top of `lean/Challenge.lean` (`midset`, `HasDMP`, `MidsetsAtMostTwo`, arcs, dendrites, finite trees and their edges, crossings and touches, and the other notions of Sections 2–9). Theorem A itself depends only on `midset` and `HasDMP`, which are one-line definitions.

## 2. Coverage: paper → Lean

All names are in the namespace `DoubleMidset.Paper`. Statements are in `lean/Challenge.lean`; the same names are proved in `lean/Solution.lean`; the proofs are in `lean/DoubleMidset/`. The verdicts are those of the final comparison by a fresh AI agent ([`review-11`](lean/reports/reviews/review-11-final-paper-comparison.md)): *faithful*, *stronger* (a hypothesis the proof does not need is dropped, or a conclusion is strengthened), *weaker*.

| Paper result | Lean declaration (`DoubleMidset.Paper.`) | Verdict of the final comparison |
| --- | --- | --- |
| Lemma 2.2(a) | `lemma_2_2_a` | stronger |
| Lemma 2.2(b) | `lemma_2_2_b` | faithful |
| Fact 2.3 (D1) | `fact_2_3_D1` | faithful |
| (D2) | `fact_2_3_D2` | faithful |
| (D3) | `fact_2_3_D3` | faithful |
| (D4) | `fact_2_3_D4` | faithful |
| Lemma 2.4 | `lemma_2_4` | faithful |
| Fact 2.5 | `fact_2_5` | faithful (consequence form) |
| Lemma 2.7 | `lemma_2_7` | faithful |
| Paragraph after Lemma 2.7 and eq. (3) | `tree_facts` | faithful (partial coverage) |
| Lemma 2.8(i) | `lemma_2_8_i` | stronger |
| Lemma 2.8(ii) | `lemma_2_8_ii` | faithful |
| Lemma 2.8(iii) | `lemma_2_8_iii` | faithful |
| Lemma 2.9 | `lemma_2_9` | faithful |
| Prop 3.1 | `prop_3_1` | faithful |
| Prop 3.2 | `prop_3_2` | stronger |
| Cor 3.4 | `cor_3_4` | faithful |
| Lemma 4.2 | `lemma_4_2` | stronger |
| Lemma 4.3 | `lemma_4_3` | faithful |
| Lemma 4.4 | `lemma_4_4` | faithful |
| Thm 4.5 | `theorem_4_5` | faithful |
| Cor 4.6 | `cor_4_6` | faithful |
| eq. (5) | `eq_5_2` | weaker (parity only) |
| Lemma 5.4 | `lemma_5_4` | faithful |
| Cor 5.5 | `cor_5_5` | faithful |
| Lemma 5.6 | `lemma_5_6` | faithful |
| Lemma 6.2 | `lemma_6_2` | stronger |
| Lemma 6.3 | `lemma_6_3` | faithful |
| Prop 6.5 | `prop_6_5` | faithful |
| Lemma 6.6 | `lemma_6_6` | faithful |
| Cor 6.7 | `cor_6_7` | stronger |
| Lemma 7.1 | `lemma_7_1` | faithful |
| Lemma 7.2 | `lemma_7_2` | faithful |
| Lemma 7.3 | `lemma_7_3` | faithful / slightly stronger |
| Lemma 7.4 | `lemma_7_4` | faithful |
| Lemma 8.1 | `lemma_8_1` | faithful |
| Prop 8.2(a) | `prop_8_2_a` | faithful |
| Prop 8.2(b) | `prop_8_2_b` | faithful |
| Lemma 9.2 | `lemma_9_2` | faithful |
| Prop 9.3 | `prop_9_3` | faithful |
| Thm 10.1 | `theorem_10_1` | faithful |
| Thm 11.1 | `theorem_11_1` | faithful |
| Thm A, first sentence; Conjecture 1.1 | `theorem_A` | faithful |
| Converse in the proof of Thm A | `circle_hasDMP` | faithful |
| Thm A, second sentence | `theorem_A_iff` | faithful |
| Thm B | `theorem_B` | faithful |
| Thm C | `theorem_C` | faithful |

No statement differs in meaning from the paper. The one weaker statement is equation (5): only the parity statement $N(a,b)\equiv N(b,a) \pmod 2$ is formalized, not the identity $N(b,a)=|O|-N(a,b)$; only the parity is used later.

## 3. Divergences between the formal and the written statements

These are listed in `lean/formalization.yaml` (field `fidelity`). In short:

1. Vertices, open edges and edges of a finite tree are defined intrinsically (tips and branch points; components of the complement of the vertices; their closures). `lemma_2_7` proves that they have the paper's properties.
2. Orders take values in `ℕ∞`, and midset sizes use `Set.encard`.
3. Crossings and touches (Definition 5.3) are defined through an open arc around the zero inside an open edge.
4. "Strictly monotone along an arc" is stated as injectivity on the arc; for continuous functions on arcs the two are equivalent.
5. Lemma 7.3 is stated with an explicit parametrization of the edge, and Definition 9.1 (used pairs) intrinsically.
6. Theorems 10.1 and 11.1 are derived from Theorem B and the facts that arcs and simple triods are finite trees; inside the library the arguments of Sections 10 and 11 are carried out for branched and unbranched finite trees.
7. Some proofs differ in technique: Lemma 7.1 uses $\max(f,\delta-d(x,\cdot))$ instead of cutting the tree, and Proposition 6.5 replaces Hausdorff continuity by a continuity lemma for unique zeros.

## 4. Reviews

All reviews were made by fresh AI agents (Claude Opus 5.5) with no memory of the work; they are in [`lean/reports/reviews/`](lean/reports/reviews/).

* **Line-by-line reviews** (`review-01` to `review-10`), one after each batch of files: every verdict was *accept* or *accept with minor changes*, and the minor changes were made.
* **Final comparison with the paper** (`review-11`): every statement of `Challenge.lean` against the paper. No critical, major or moderate issue. Its minor and cosmetic points about docstrings (two misnumbered equations, the wording of one clause in `tree_facts`) were fixed afterwards. Its line references are to the version of the paper it read, whose Sections 2–12 are identical to the present ones.

## 5. Checks

From the last full run of `lean/scripts/verify_all.sh` (logs in `lean/logs/verify-20261122T174514Z/`), with comment-only changes afterwards that were rechecked by build and Comparator:

| Check | Result |
| --- | --- |
| static source checks | passed (35 Lean files, `module` headers, no forbidden tokens, `Challenge.lean` imports only Mathlib) |
| clean build | passed |
| axiom audit (47 results) | only `propext`, `Classical.choice`, `Quot.sound` |
| Comparator (Lean kernel and nanoda) | passed, **unsandboxed** |
| `lake check` | passed, unsandboxed |
| Comparator `--paranoid` (25,834 declarations) | accepted by the Lean paranoid kernel, lean4lean, nanoda, con-leche, con-ron and the Lean kernel, unsandboxed |
| Palomar-style run, external kernels nanoda and con-ron | passed, unsandboxed |
| `lake check --paranoid` (312,655 declarations) | **failed**: five checkers accept, nanoda was killed for lack of memory (exit 137) |
| negative controls | both rejected as expected |

Bubblewrap was not available where the code was written, so no sandboxed run was made there.

**Sandboxed runs elsewhere (22 November 2026).**

* **Palomar.** Commit `aa5681a` of the branch `palomar` (the same Lean files as `lean/`) was submitted to Palomar. Palomar's sandboxed verification, which runs `lake comparator` with Lean's kernel and the nanoda replay, [completed successfully](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45061350900). Palomar's automated review (an AI review by `codex:gpt-6-sol`, not human) identified no problems, and the result was **registered on 22 November 2026 as [PALOMAR-2026-11-22-000025 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-22-000025&version=1)**.
* **GitHub Actions.** The [CI workflow](.github/workflows/ci.yml) built the project and passed the static checks and the axiom audit. In the sandboxed verification job the runner was shut down during `lake check --paranoid` on the whole export (312,655 declarations), the step where nanoda also ran out of memory locally, and no logs were uploaded. So that job gave no result for its steps. Since then CI skips that one step (`SKIP_FULL_EXPORT_PARANOID=1`, recorded as not-run) and runs all the others. After a fix to the workflow (the toolchain's `bin/` was not on PATH, so Comparator could not find `nanoda_bin`), the [run of 23 November 2026](https://github.com/LucasAlves8Sp/Double-midset-conjecture-for-metric-continua/actions/runs/45127914972) passed every step sandboxed: static checks, clean build, axiom audit, `lake comparator`, `lake check`, `lake comparator --paranoid`, the Palomar-style run with nanoda and con-ron, and both negative controls (rejected with the expected messages).
