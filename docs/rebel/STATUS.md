# ReBeL status — public-posterior proof validated; M06 incomplete

## Current checkpoint

Work branch: `rebel/m06-conditioned-query-20260925`.
Resume source: `6bc06761937a81eb4468fb3f7f5ec89e019b8ca6`.
Validated Lean source: `5df5e6a049c9550bcc944c3ca8599a3b215605e7`
(committed 2026-09-26T19:01:39Z).
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; M05 is accepted.
M06 and paper Theorem 3 are NOT complete. M07 is not started.

The pending public-posterior compiler failure is repaired without changing its
statement or support premise. Dependent simplification transports the projected
law's conditioning witness; Set.preimage_ofPred_eq also normalizes the public
event's preimage. The first simplification-only checkpoint a76f1f3 failed and
is preserved as failed evidence. Read M06-public-posterior-validation.md for
the exact diagnostics, source identity, actual artifacts and their hashes.
M06-public-posterior-repair.md retains the earlier failed repair history.

The existing three-module slice now has a compiled positive-support
projection/conditioning theorem, actual public-event mass and possibility
identities, full joint public-history posterior identification, and the native
finite-T bound divided by the actual public-observation probability. Its genuine
two-iterate solver consumer, noninjective public-output control, hidden-selection
negative control and impossible-observation control are compiled and audited.
The fix changes only one proof body and its comments. No statements, gates,
expected counts, imports, target lists, dependency pins or original ledger
statuses were changed.

## Validation of that exact source

- M06 targeted run 36264603809 / job 108466761911: SUCCESS; target compilation,
  normal/slow lint for all 107 configured modules, and transitive axiom audit
  of all 1,684 declarations. All 58 declarations in the three affected modules
  are included; every one of the candidate manifest's 14 names was found.
- Full CI run 36264603829 / job 108466874178: SUCCESS; full build, full public
  lint, reuse inventory, Phase 1/2/3 architecture and reachability audits, and
  tracked-file cleanliness.
- ReBeL checks run 36264603792 / job 108467000492: SUCCESS; compilation and
  normal/slow lint for all 251 modules, transitive axiom checks for all 4,861
  declarations, ledger/adversarial fixtures, actual Lean rational-runtime
  cross-check, architecture and tracked-file cleanliness.
- Source inventory run 36264603756: SUCCESS.

The exact source snapshot was obtained through the GitHub plugin. Offline
coverage and inventory checks preserve all 3,054 items and their statuses;
all 97 Python tests passed with warnings treated as errors. No local Lean or
PowerShell execution is claimed. All GitHub access and both source commits
used the plugin, not local Git or direct local GitHub HTTP.

The source SHA above owns the validation evidence. A later documentation-only
checkpoint does not change those Lean source bytes or turn an in-progress new
workflow into a success claim. The machine-readable record is
M06-public-posterior-coverage.json; its project candidate and original source
obligations remain pending rather than being promoted by compiler success.
Earlier conditioned-query evidence is retained in M06-conditioned-query-repair.md
and is not substituted for validation of this public-posterior slice.

## Remaining M06 boundary

The posterior identity is for the resulting PUBLIC trace under fixed legal
execution opponents. It is not a public update for arbitrary hidden seed/type
selections and does not assert independent posterior tags. The native gap STILL
uses the SAME computed average comparison opponent at the ORIGINAL compatible
full joint TYPE kernels, not new posterior kernels.

In resolvedNextState the stored model posterior is updated using chosen,
whereas carriedResolvedStep executes Profile.update unknown who (chosen who).
The repaired theorem does not silently identify these different opponent
models or discharge their support/event and value differences.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Independently re-solved public-carried-PBS identification, quantitative
support/first-exit/event rates, independently changing-opponent/PBS native and
late rates, recursive re-solving safety and CarriedResolveStepBounds remain.
Do not assume an event-mass floor, expose private seeds, discard finite-T
residuals or replace test-time safety with learner convergence.

## User decision for M07 onward

Keep one fixed integration branch for each milestone. Continue ordinary
sequential implementation on that branch; a new chat alone does not justify
a new branch. Use temporary branches for substantial experiments or parallel
work and integrate accepted changes back into the milestone branch. Record
validated checkpoints by exact commit SHA or an intentionally created tag.
This decision does not authorize beginning M07 before its prerequisites or
deleting existing M06 branches with unaccounted-for changes.
