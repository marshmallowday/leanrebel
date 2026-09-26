# ReBeL status — public-posterior repair candidate; M06 incomplete

## Current work

Work branch: `rebel/m06-conditioned-query-20260925`.
Starting checkpoint: `543849ea0fc3df25c95629d957561936ee16527a`.
Public-posterior planning checkpoint: `af2b4da1776e97ee70c437c886fc80f8a633fae8`.
First public-posterior source: `3affbb7a48646ebaf9427463568e9aadbe51c7e6`.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; M05 is accepted.
M06 and Theorem 3 are NOT complete.

The first public-posterior source failed targeted compilation in three new
FinDistSelection equality-transport terms and failed the unchanged Phase 2
source-transport gate. Actual target artifact and all-ReBeL job logs were read.
The repair replaces those proof terms with explicit membership rewriting,
repairs the same pattern in the negative example and normalizes the output-map
proof. Statements, controls, bounds and all validation gates remain unchanged.
Read M06-public-posterior-repair.md for exact failed run/job IDs and log hashes.
The repair's Lean compilation, normal/slow lint, transitive axioms and all CI
are PENDING the new source push. All 97 Python tests passed again locally;
new-source static transport counts are restored to Math=1 and Analysis=0.
No local Lean or PowerShell execution is claimed.

The slice extends the existing three conditioned-query modules with a
positive-support projection/conditioning theorem, actual public-event mass and
possible-observation identities, canonical joint public-posterior identification,
and the native finite-T bound with its actual public mass. It adds a genuine
solver consumer and positive, hidden-selection and impossible-observation
controls. Read M06-public-posterior.md and its pending candidate coverage.
No validation configuration, dependency pin or original source status changes.

## Previous validated source (not new-source evidence)

Conditioned-query repair source: `6d111a4aa3060be10fa7e655d0dbfde13660cc7c`.
The history-marginal proof explicitly normalizes identity history maps using
FinDist.map_id. Its source compiled at
`03f5beebc6d75109bf9b0166c083b0c9ed071f84`; the follow-up repaired the original
example proofs without changing their statements or gates.

All four workflows for that exact repair source succeeded:
- M06 target 36210326495: compilation, normal/slow lint for 107 modules and
  1,669 declaration axiom checks.
- ReBeL checks 36210326388: 251 modules, 4,848 declaration axiom checks,
  92 Python tests, rational runtime, architecture and source-cleanliness gates.
- Full CI 36210326436: full build, public lint, reuse and Phase 1/2/3 audits.
- Source inventory 36210326380.

Actual job logs were read through the GitHub plugin in the prior checkpoint.
The history theorem uses exactly [propext, Classical.choice, Quot.sound].
See M06-conditioned-query-repair.md and M06-conditioned-query-coverage.json.
The preceding documentation-only head also has successful repository workflows;
none of those results validates the new public-posterior proof additions.

## Remaining M06 boundary

The new posterior claim is only for events observable from the resulting
PUBLIC trace under fixed legal execution opponents. It is not a public update
for arbitrary private seed/type selections. The native gap STILL uses the SAME
computed average comparison opponent at the ORIGINAL compatible full joint
TYPE kernels. Projected posterior equality does not transfer its value gap to
changed kernels/opponents or prove independent posterior tags.

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
