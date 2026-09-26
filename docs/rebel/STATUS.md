# ReBeL status — validated opponent transport; M06 integration in progress

## Current checkpoint

Continue `rebel/m06-conditioned-query-20260925`.
Validated implementation: `334f259f450e6ce1818cb1037214bd849ffc98ed`.
Main remains accepted M05 at `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.
M06 and paper Theorem 3 are NOT complete. M07 is not started.

Repository-wide latest push workflows and a fresh branch-ref read identify
334f259 as the newest implementation, despite the branch's older date suffix.
The separate public-event-rates branch at
`1d3011f3e1541268411c403f99fa2e86ce5e33f4` is older and diverged: its merge
base with 334f259 is `a76f1f32403f3cc1834d8f39d11b9802626ee592`.
Do not replace the latest source with that older branch.

## Inspected validation

The previously pending opponent/model transport slice is now validated at
334f259. Its actual source, target and all-ReBeL artifacts were obtained using
the GitHub plugin, their archive hashes checked, and their logs inspected.
Target 36271821127 / job 108487104213 passed compilation, normal/slow lint of
110 modules and 1,733 transitive declaration checks. All-ReBeL
36271821152 / job 108487174934 passed 253 modules and 4,904 declaration checks.
All inspected axiom sets are subsets of propext, Classical.choice, Quot.sound;
all 22 declarations listed in the slice coverage occur in those audits.
Full CI 36271821124 / job 108487337344 passed build, public lint, compiler reuse
signatures, Phase 1/2/3 architecture gates and tracked-file cleanliness.
Inventory 36271821169 succeeded. See M06-opponent-model-transport-validation.md
and the updated M06-opponent-model-transport-coverage.json for exact artifacts,
source blobs, assumptions and semantic limitations.

No local Lean or PowerShell execution is claimed. GitHub file writes are not
compiler evidence; old successful runs will not validate the next source edit.

## Next dependency-closed task

Integrate the unmerged actual conditioned/public native-tail estimates and
positive/negative controls from 1d3011f onto the validated latest branch.
Preserve the latest public-posterior dependent proof repair, all three opponent
transport modules, original tests, workflows, audit consumers and dependency
pins. Inspect the older branch's target results before acceptance; run exact-SHA
validation on the combined source. Do not mark integration verified just because
either parent compiles. Keep the original public-event branch and its history.

## Remaining M06 boundary

The executed source charge is a derived bound, NOT a proof that independently
changing opponents make it small. It retains incoming actual/PBS law mismatch,
including point-mass actual histories and zero continuation fuel. Public
posterior identification concerns fixed execution profiles. Native value gaps
still use the original compatible type kernels and the same computed average
comparison opponent; conditional event rates must retain actual event mass.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Independently re-solved carried-PBS identification, quantitative small support/
first-exit rates, changing-opponent/PBS native and late rates, recursive safety
and CarriedResolveStepBounds remain. No event-mass floor, private-seed disclosure,
discarded finite-T residual or learner-convergence premise is authorized.

## Branch policy

From M07 onward keep one integration branch per milestone, as already decided
by the user. Temporary branches need substantial experiments or parallel work,
not merely a new chat. This does not authorize starting M07 now or deleting
unaccounted-for M06 branches. This continuation stays on the latest M06 branch.
