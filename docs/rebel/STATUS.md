# ReBeL status — conditioned-query compiler repair; M06 incomplete

## Current work

Work branch: `rebel/m06-conditioned-query-20260925`.
Repair source: `6d111a4aa3060be10fa7e655d0dbfde13660cc7c`.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; M05 is accepted.
M06 and Theorem 3 are NOT complete.

The history-marginal proof now explicitly normalizes identity history maps
using the existing FinDist.map_id theorem. Its source compiled at
`03f5beebc6d75109bf9b0166c083b0c9ed071f84`; that run then reached previously
uncompiled example proofs. The follow-up repairs their tagged atom masses,
event expectation and finite product sums without changing any statement,
assumption, example, dependency pin or validation gate.

## Validation

All four workflows for the exact repair source succeeded:
- [M06 target 36210326495](https://github.com/marshmallowday/leanrebel/actions/runs/36210326495):
  compilation, normal/slow lint for 107 modules and 1,669 declaration axiom checks.
- [ReBeL checks 36210326388](https://github.com/marshmallowday/leanrebel/actions/runs/36210326388):
  251 modules, 4,848 declaration axiom checks, 92 Python tests and rational
  runtime validation, with architecture and source-cleanliness gates.
- [Full CI 36210326436](https://github.com/marshmallowday/leanrebel/actions/runs/36210326436):
  full build, public-library lint, reuse checks and all Phase 1/2/3 audits.
- [Source inventory 36210326380](https://github.com/marshmallowday/leanrebel/actions/runs/36210326380).

Actual target, ReBeL and full-CI job logs were read through the GitHub plugin.
The history theorem uses exactly [propext, Classical.choice, Quot.sound].
See M06-conditioned-query-repair.md and M06-conditioned-query-coverage.json.
The subsequent documentation checkpoint changes no Lean source or validation
configuration; the successful compiler evidence belongs to the source SHA above.

## Remaining M06 boundary

Read M06-conditioned-query.md for the semantic scope. The query conditions
actual retained-seed/type/history execution on a positive-mass event. Its
native error is measured against the SAME computed average opponent at the
ORIGINAL compatible full joint-history kernels, retaining finite-T error.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Public-carried-PBS identification, quantitative support/first-exit/event rates,
independently changing-opponent/PBS native and late rates, recursive re-solving
safety and CarriedResolveStepBounds remain. Do not assume an event-mass floor,
expose private seeds, discard finite-T residuals or replace test-time safety
with learner convergence.

## User decision for M07 onward

Keep one fixed integration branch for each milestone. Continue ordinary
sequential implementation on that branch; a new chat alone does not justify
a new branch. Use temporary branches for substantial experiments or parallel
work and integrate accepted changes back into the milestone branch. Record
validated checkpoints by exact commit SHA or an intentionally created tag.
This decision does not authorize beginning M07 before its prerequisites or
deleting existing M06 branches with unaccounted-for changes.
