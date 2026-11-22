# Verification report — 2026-11-22

The evidence is in `logs/verify-20261122T174514Z/`: `provenance.txt`, `steps.tsv` and one log per
step. It was produced by `ALLOW_NO_SANDBOX=1 bash scripts/verify_all.sh` on the delivered sources
(Lean sources and configuration hash `1ea7f120…be1bc8c`, in `provenance.txt`), after the last
change to any Lean file.

## The five statuses

| Status | Result |
|---|---|
| **Lean build passed** | **yes**: clean rebuild of the library, `Solution` and `Challenge`; no `sorry` outside `Challenge.lean` |
| **Comparator passed** | **yes, unsandboxed only**, all 47 statements. bubblewrap is not installed in the workspace, so every Comparator run used `--inadvisably-no-sandbox`. No sandboxed run has happened. |
| **Independent kernel checks passed** | **not fully**: see the table below |
| **Locally prepared for submission** | **no**: there is no commit and no remote, and no sandboxed run has been made on the commit to be submitted |
| **Registered by Palomar** | **no**: nothing has been pushed or submitted |

Results of the independent kernel checks:

| Check | Declarations | Result |
|---|---|---|
| Comparator `--paranoid` on the Solution closure | 25,834 | accepted by the Lean paranoid checker, lean4lean, NanoDa, con-leche, con-ron and the Lean default kernel (unsandboxed) |
| `lake check --paranoid` on the whole project export | 312,655 | accepted by the Lean paranoid checker, lean4lean, con-leche, con-ron and the Lean default kernel; **NanoDa was killed with exit 137** (out of memory: about 8 GB RAM, no swap), so this step is recorded as **failed** |

The NanoDa failure was reproduced in two separate runs (before and after the last docstring edits).
The log line "nanoda kernel rejected the solution" is followed by "error: nanoda exited with 137":
the process was killed, it did not report a type error.

## The checks

| # | Check | Step(s) | Exit | Result |
|---|---|---|---|---|
| 0 | Static source checks | `00-sources` | 0 | passed: 35 Lean files, every file has a `module` header, no forbidden token, Challenge imports only Mathlib. One warning: `Challenge.lean` has 575 lines / 27,877 bytes, above the 300-line review preference (hard limits 1,000 lines / 100 KiB) |
| 1 | Clean build | `01-clean`, `01-build`, `01-build-challenge` | 0 | passed: `.lake/build` deleted and every project module rebuilt; Mathlib's build products reused |
| 2 | Axiom audit | `02-axioms-print`, `02-axioms-check` | 0 | passed: the 47 compared theorems depend only on `propext`, `Quot.sound`, `Classical.choice` |
| 3 | Comparator | `03-comparator` | not-run | sandboxed form not run: bwrap absent |
| | | `03-comparator-NOSANDBOX` | 0 | passed **unsandboxed**: NanoDa and the Lean kernel accept all 47 theorems |
| 4 | Kernel replay (`lake check`) | `04-check` | not-run | sandboxed form not run |
| | | `04-check-NOSANDBOX` | 0 | passed **unsandboxed** |
| 5 | Paranoid mode incl. NanoDa | `05-check-paranoid` | not-run | sandboxed form not run |
| | | `05-check-paranoid-NOSANDBOX` | **1** | **failed**: NanoDa ran out of memory (exit 137); the other five checkers accepted |
| | | `06-comparator-paranoid` | not-run | sandboxed form not run |
| | | `06-comparator-paranoid-NOSANDBOX` | 0 | passed **unsandboxed**: all six checkers accepted the Solution closure, NanoDa included |
| 6 | con-ron | in 5, 6 and 7 | — | the bundled con-ron accepted. **Palomar's pinned con-ron build was not available offline and was not run.** |
| 7 | Local equivalent of Palomar's pipeline | `07-palomar-local` | not-run | sandboxed form not run |
| | | `07-palomar-local-NOSANDBOX` | 0 | passed **unsandboxed**: protected config with `nanoda_bin` and `con-ron` as `external_kernels` |
| neg | Negative controls | `08-negative-sorry-NOSANDBOX` | 1 (expected) | rejected as expected: `Illegal axiom detected: 'sorryAx'` |
| | | `09-negative-definition-NOSANDBOX` | 1 (expected) | rejected as expected: `Const does not match between challenge and target 'DoubleMidset.HasDMP'` (`encard = 2` changed to `≤ 2` in `Challenge.lean`) |

The script exited with status 1 because of step 5. That is the correct outcome: step 5 did not
pass.

## What would close the gaps

- **Sandbox.** The workspace has no network, so bubblewrap cannot be installed. The CI workflow
  (`.github/workflows/ci.yml`) installs it and runs `scripts/verify_all.sh` sandboxed on a GitHub
  runner. It has never run, because no remote exists.
- **NanoDa on the whole export.** This needs more memory than the workspace has. A GitHub runner
  (16 GB) or Palomar's own pipeline would settle it.

## Human review

None. The Lean statements were reviewed only by fresh AI agents (`reports/reviews/`). Before
submission a human should read `Challenge.lean` against the paper, at least for Theorems A, B and
C and the definitions in the first half of the file.

## Toolchain and tools

- Lean 4.35.0-rc2 (commit `11acb17e…`), Lake 5.0.0-src+11acb17.
- Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- The SHA-256 of every bundled checker executable is in `provenance.txt`.

## Addendum — comment-only changes after the run above (2026-11-22)

After the run above, the paper was retitled *The Double Midset Conjecture for Metric Continua*
and redated 22 November 2026 (Sections 2–12 and their numbering are unchanged). The title and date
were updated in comments only: the module docstrings of `Challenge.lean`, `Solution.lean` and
`DoubleMidset/Defs.lean` (outside the copied definitions), plus `README.md` and
`formalization.yaml`. No declaration changed. The source hash is now `95316d7c…17342ed`.
After the change: `lake build` and `lake build Challenge` passed, the static source checks
passed, and Comparator (unsandboxed, NanoDa and the Lean kernel) accepted all 47 theorems. The
full `verify_all.sh` run was not repeated on this hash.
