# ReBeL status — support-rate candidate; M06 incomplete

## Current source and branch

Continue `rebel/m06-support-rates-20260927`, based on the latest combined
integration `7326f1e40011b1d4329f09e743491cc7bc7e5746` from
`rebel/m06-conditioned-query-20260925`. The first continuation checkpoint is
`3de54cc88fe0ccb87e2aa603c4d833ac5a3d1662`. A separate branch avoids cancelling
the still-running integration-wide audit through branch-local concurrency.
Both original integration parents and all earlier implementations are retained.
Main remains accepted M05 at `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.
M06 and paper Theorem 3 are NOT complete. M07 is not started.

## Current dependency-closed change

The new support-only charge derives carried posterior support-failure rates
from incoming unsupported mass plus actual-visit one-step support leakage.
Unlike the previous full source-atom variation charge, differing positive
weights inside the same model support do not cost anything. The candidate
proves finite-horizon propagation, comparison with the old charge, and zero
charge under explicit primitive support inclusions. It includes the actual
budget-1/8 information-set CFR child consumer and hostile finite-law examples.
No law equality, changed-opponent convergence, support floor, or child Nash
certificate is used to remove genuine support failures.

Read M06-support-rates.md, M06-support-rates-coverage.json and
M06-support-rates-validation.md. All previous statements and tests remain.
The existing 110 target modules and 253 globally discovered modules, imports,
auditors, workflows, dependency pins and 3,054 source items are unchanged.
Prepared-source Python discovery passed 112 tests, including five additional
support controls and 16,384 new exhaustive exact-rational cases. This is not
Lean proof evidence. No local Lean or PowerShell execution is claimed.

## Validation and next action

NEW-SOURCE compiler, normal/slow lint, transitive axioms, all-ReBeL, full CI and
inventory are PENDING the source push. Inspect its exact-SHA workflows and
actual diagnostics next. Repair any failed proof without weakening statements
or suppressing warnings. Do not substitute source-parent passes for this build.

The combined parent 7326f1e4 has an inspected target artifact: run 36275563682,
job 108497496370, artifact 10916654865, 110 lint passes, 1,739 allowlisted axiom
records, and EXACT_LEAF_VALIDATION_PASS. Its full CI 36275563654 / 108497657992
reports success but detailed logs have not yet been inspected in this slice.
Its global ReBeL run 36275563642 / 108497538005 was still running at the first
checkpoint. Inspect that final artifact and the source inventory as well.
Hashes and exact parent-source evidence are in M06-support-rates-validation.md.

## Remaining semantic boundary

This is a fixed-profile finite continuation support bound, not a completed
first-exit theorem for independently re-solved carried schedules. Support-only
zero charge requires actual one-step support dominance; it is not automatic
for arbitrary unknown opponents. Establishing small accumulated leakage for
the full algorithm remains open. Being inside a PBS support is not equality
between the stored model PBS and the actual conditional distribution.

The preserved native gaps use original compatible joint type kernels and the
SAME computed average comparison opponent. Public conditional rates retain the
actual event-mass denominator. Changed-PBS native/late rates, full recursive
re-solving safety and CarriedResolveStepBounds remain unproved.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No learner convergence or dropped finite-T residual is used to bypass safety.

## Branch policy

M07 onward retains the user's one-integration-branch-per-milestone policy.
This task does not start M07, delete older M06 branches, force-push, or update main.
