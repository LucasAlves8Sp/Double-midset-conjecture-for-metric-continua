# AI disclosure

*This is the AI disclosure of the paper and its section on the Lean formalization, reproduced as they appear there (paper of 22 November 2026). Theorem numbers refer to the paper.*

## Disclosure of the use of artificial intelligence

Artificial intelligence was used extensively in this work: to obtain the results, to proofread and write the paper, and to test the results adversarially. The models used were Claude Opus 5.5 (Anthropic), ChatGPT Astra 6.2 and ChatGPT Sol 6.1 (OpenAI). Claude Opus 5.5 was the main model for the proof of the first part of the argument, and ChatGPT Astra 6.2 for the triod and dendrite cases.

The author guided the work throughout. He proposed the subgoals and directed the proofs. Many rounds of review were carried out, in which proof attempts, reports and candidate results were produced and checked. The Lean code of the formalization described in the next section, both statements and proofs, was written by Claude Opus 5.5 at the author's request.

The author takes full responsibility for the content of this paper.

## Formalization in Lean 4

The results of this paper have been formalized in Lean 4 with the library Mathlib. The development is in [`lean/`](lean/). It was compiled with Lean `v4.35.0-rc2` and the Mathlib release of the same tag.

*What is formalized.* Every definition, lemma, proposition, corollary and theorem of Sections 2–12, and the facts of Section 2 in the form in which they are used: 47 statements in all, collected in the file `Challenge.lean`. They include Theorems A, B and C, the converse that the Euclidean circle has the DMP, and the resulting characterization: a metrizable continuum admits a compatible metric with the DMP if and only if it is a simple closed curve. The classical facts that are not in Mathlib, such as the existence of arcs in Peano continua and boundary bumping, are proved in the development. Every formal proof is complete, uses no axiom beyond the three standard ones of Lean with classical logic (`propext`, `Classical.choice`, `Quot.sound`), and was accepted by the Lean kernel and by the independent proof checkers run through the tool Comparator. The repository records exactly which checks were run and under which conditions.

*What is not formalized.* The examples, the figures, the remarks and the questions of Section 13. R. L. Moore's theorem (Fact 2.5) is formalized only in the consequence used here, that a dendrite without branch points is an arc, and equation (5) only as the parity statement $N(a,b)\equiv N(b,a) \pmod 2$. Several formal statements are slightly more general than the written ones; the file `formalization.yaml` lists every divergence. The correspondence between the formal statements and the statements of the paper has so far been checked only by AI systems.
