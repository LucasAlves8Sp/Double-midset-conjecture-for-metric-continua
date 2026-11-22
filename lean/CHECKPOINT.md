# CHECKPOINT: Lean formalization of "The Double Midset Conjecture for Metric Continua"

State on 2026-11-22: **formalization complete, verified locally (unsandboxed), not submitted.**

## Done

- Library `DoubleMidset/` (Sections 2–12 of the paper and the classical facts in `Classical/`):
  compiles, no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`.
- `Challenge.lean` (575 lines, about 27 KiB): the definitions copied verbatim from
  `DoubleMidset/Defs.lean` and the 47 statements with `sorry`. It imports Mathlib only.
- `Solution.lean`: the same 47 statements, each proved by a library theorem (or a short unpacking
  of `IsFiniteTree` / `IsDendrite`).
- `comparator.json`, `formalization.yaml` (47 alignment entries), `LICENSE`, `README.md`,
  `.github/workflows/ci.yml`, `scripts/`.
- Reviews: `reports/reviews/review-01` … `review-10` (fresh agents, one per batch of files, all
  ACCEPT or ACCEPT WITH MINOR) and `review-11-final-paper-comparison.md` (fresh agent, every
  statement against the paper: no critical, major or moderate issue). Its minor points (equation
  numbers in two docstrings, the wording of the `tree_facts` edge clause) were fixed.
- Verification: `reports/verification_report.md` and `logs/verify-*/`.

## Not done (cannot be done in this workspace)

- Sandboxed runs: `bwrap` is not installed and there is no network.
- NanoDa on the whole `lake check --paranoid` export: killed for lack of memory (exit 137).
  NanoDa accepts the Comparator closure of the Solution.
- Push, CI run, Palomar submission: not done; nothing has been submitted.

## Build notes

`lakefile.toml` has `defaultTargets = ["DoubleMidset", "Solution"]`. `Challenge` is a separate
library target (`lake build Challenge`): `Challenge` and the library declare the same names, so
they must not be in one environment, and `lake check` fails if both are default targets.
