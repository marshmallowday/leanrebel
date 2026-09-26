# ReBeL status — opponent/model transport candidate; M06 incomplete

## Current work

Work branch: `rebel/m06-conditioned-query-20260925`.
Starting checkpoint: `b8be33668cce9b9238692bc86da545a89d2bad5d`.
Planning checkpoint: `4364543b02494a94e038a40ae8de9c86e51e5a32`.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; M05 is accepted.
M06 and paper Theorem 3 are NOT complete. M07 is not started.

The new dependency-closed slice computes the discrepancy between actual
continuation under `Profile.update unknown who (chosen who)` and stored-model
continuation under `chosen`. It derives finite-kernel contraction/perturbation,
accumulates one-step source variation along ACTUAL prefix laws, and preserves
initial actual/PBS mismatch even at zero fuel. It bounds failure of the actual
carriedBeliefUpdate to contain the resulting history, including both impossible
public observations and hidden support loss, and bounds mean public conditional
transport under the actual public law. No model/actual posterior equality is
assumed. The live consumer uses a computed budget-1/8 CFR child and a point-mass
actual history; finite-law controls expose lost support and wrong-prefix charges.

Read M06-opponent-model-transport.md and M06-opponent-model-transport-coverage.json.
The three new modules extend the existing umbrella, target list and additional
axiom/lint module list; no old module is removed and no validation algorithm,
workflow, architecture expectation or dependency pin changes. The additional
module list now has 110 entries. Global discovery must also include all three.

New-source Lean compilation, normal/slow lint, transitive axioms, all-ReBeL and
full CI are PENDING the source push. Local exact-rational and wiring tests all
passed: 103 Python tests, including 16,384 kernel/horizon comparisons, with
warnings treated as errors. Coverage/inventory checks preserve 3,054 items and
all original statuses. No local Lean or PowerShell execution is claimed.
Next action: inspect the target-SHA compiler and full validation logs; repair
proofs without weakening statements, examples or gates, then record exact
source, run IDs and inspected axiom evidence.

## Previous validated source (not new-source evidence)

Public-posterior proof source: `5df5e6a049c9550bcc944c3ca8599a3b215605e7`.
Its dependent conditioning proof and all positive/negative controls are already
validated. M06 target 36264603809 / 108466761911 passed compilation, normal/slow
lint of 107 modules and 1,684 transitive declaration checks. Full CI
36264603829 / 108466874178 passed full build, public lint, reuse and Phase 1/2/3
audits. ReBeL checks 36264603792 / 108467000492 passed all 251 modules and
4,861 declaration axiom checks, fixtures, rational runtime and cleanliness.
Source inventory 36264603756 succeeded. Actual artifacts and hashes are in
M06-public-posterior-validation.md and M06-public-posterior-coverage.json.

The documentation-only starting checkpoint b8be336 also has successful CI,
ReBeL and inventory workflows. These results do not validate the new modules.
The prior conditioned-query evidence and failed repair history remain in
M06-conditioned-query-repair.md and M06-public-posterior-repair.md.

## Remaining M06 boundary

The executed source charge is a derived bound, NOT a proof that independently
changing opponents make it small. It retains any incoming law mismatch; a
point-mass actual history must not be silently replaced by the model PBS.
The public posterior equality still concerns fixed execution profiles. Native
value gaps still use the original compatible type kernels and the same
computed average comparison opponent. No changed-PBS gap bound follows just
from the new source-law estimate or the scalar child Nash property.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Independently re-solved public-carried-PBS identification, quantitative small
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
