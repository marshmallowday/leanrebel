# ReBeL status — actual public-event native tails; M06 incomplete

## Current work and resume point

Work branch: `rebel/m06-public-event-rates-20260927`.
Base source: `a76f1f32403f3cc1834d8f39d11b9802626ee592`.
Planning checkpoint: `65a1612311836767d6a27c1ce47de82e1611cd46`.
The original `rebel/m06-conditioned-query-20260925` branch advanced concurrently
from `6bc06761937a81eb4468fb3f7f5ec89e019b8ca6` while work was being prepared.
A fresh ref read caught this before any branch update. Its newer proof and
comments are retained; this isolated branch avoids overwriting parallel work.
No force update, merge to main, or local Git operation is used.

M06 and Theorem 3 are NOT complete. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.
Read M06-public-event-rates.md for the scope and concurrency record, and
M06-public-event-rates-validation.md for exact diagnostics and validation.

## Current source slice

The existing conditioned-query module now derives positive-threshold tail
bounds for the actual event-conditioned native query. Its denominator retains
the actual event mass. A second theorem directly bounds the unconditional
joint event-and-bad-native-gap probability without constructing a posterior;
a public-observation specialization therefore covers impossible observations.
All bounds retain the native finite-T residual and the SAME computed average
comparison opponent at the ORIGINAL compatible full joint type kernels.

The existing example module adds a real full-AOH budget-1/8 solver consumer:
any public observation AND a native error at least 1/4 has unconditional
probability at most 1/2. A sharp finite-law control has conditional tail one
but event-weighted tail one half, and rejects omitting the event denominator.
All earlier solver, hidden-selection, correlation and impossible-output controls
remain. No new module, target list, audit, gate, expected count or pin is added.

The inherited public-posterior proof still failed on base a76f1f3: actual target
run 36264124596 / job 108465401160 was read through the plugin. Dependent
simplification repaired the history-law motive but left the event preimage
unnormalized at line 273. The current source normalizes that preimage too;
the theorem statement and supported-observation witness are unchanged.

Current source blobs:
- PBSConditionedNativeGap: fc18d3354976dce4c1d70bcff285689419de2c9d.
- Examples.PBSConditionedNativeGap: 5d3d3572bc110241c7dfc1513e5fbbb85d99c663.
Compilation, normal/slow lint, transitive axioms, all-ReBeL and full CI are
PENDING this source push. Do not promote either candidate based on a source
inventory badge. Inspect exact-SHA jobs and actual logs first; repair any
remaining compiler diagnostic without weakening a statement or gate.

## Previous validation is historical, not new-source evidence

Conditioned-query source `6d111a4aa3060be10fa7e655d0dbfde13660cc7c`
has previously inspected successful workflows:
- Target 36210326495: 107 configured modules, 1,669 declaration axiom checks.
- ReBeL 36210326388: 251 modules, 4,848 declaration axiom checks, 92 Python
  tests, rational runtime, source-cleanliness and architecture checks.
- Full CI 36210326436 and source inventory 36210326380.

See M06-conditioned-query-repair.md. The later public-posterior checkpoint's
97 Python tests are also historical; no new local Lean, PowerShell or Python
execution is claimed here. Failed public-posterior repairs remain documented
in M06-public-posterior-repair.md. The new tail candidate has its own pending
M06-public-event-rates-coverage.json, not a promoted paper obligation.

## Remaining semantic boundary

Execution opponents are arbitrary fixed legal policies, not functions of the
private seed. Public history-posterior identification does not imply that the
posterior tags are independent, nor transport a native gap to changed kernels
or changing comparison opponents. The unconditional JOINT public-and-bad-gap
rate must not be read as a conditional rate after a rare public observation.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Independently re-solved public-carried-PBS identification, quantitative
support/first-exit rates, changing-opponent/PBS native and late rates, recursive
re-solving safety and CarriedResolveStepBounds remain. No event-mass floor,
disclosed seed, discarded finite-T residual or learner-convergence premise
is introduced. M07 is not started.

## User decision for M07 onward

Use one fixed integration branch per milestone; an ordinary new chat does not
justify another branch. Temporary branches are for substantial experiments or
parallel work; integrate accepted changes and preserve exact-SHA checkpoints.
Do not delete existing M06 branches with unaccounted-for changes.
