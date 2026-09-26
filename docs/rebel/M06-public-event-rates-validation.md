# M06 event-tail source validation

## Actual inherited compiler diagnostics

The work branch is `rebel/m06-public-event-rates-20260927`, descended from
`a76f1f32403f3cc1834d8f39d11b9802626ee592` through planning commit
`65a1612311836767d6a27c1ce47de82e1611cd46`. See the scope document for the
concurrent ref advance and the deliberately unused stale repair commit.

Base target run 36264124596 / job 108465401160 completed with FAILURE.
The actual decoded job log was read through the GitHub plugin. It records
exact source a76f1f3, Lean 4.33.1 and pinned mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
FinDistSelection and the prerequisites compile. The only target source error
is PBSConditionedNativeGap.lean:273: dependent simplification leaves the
preimage of a set-builder on one side and the explicit event set-builder on
the other. The projected conditional support proof and history-law transport
are retained. The downstream example and target lint/axiom step were not reached.
Artifact ID 10913219197; reported ZIP SHA256
f98ab92e6cd69156521b08c9072ff9ce17acf9f83103c0c221f70784183672b0.
This artifact digest is from the actual job log, not a local artifact download.

The current proof-only repair adds Set.preimage and Set.mem_setOf_eq to the
restricted dependent simplification. It does not change the public event,
theorem statement, positive-support witness or canonical joint history law.
The base's explanatory proof comments are preserved.

## New tail statements and controls

The conditioned-tail theorem composes the existing finite-T mean theorem with
FinDist.markov_inequality, keeping B_T / (actual event mass * threshold).
The unconditional event-tail theorem applies probOf_le_expect_div directly to
the actual tagged execution. Its observable is the original native gap at the
retained tag; the tag marginal theorem reduces its mean to the established
native CFR mean bound. Restricting to an event only restricts the bad set; no
possible-event certificate is required. The public theorem is this statement
at the canonical public-trace event, not a new posterior-kernel value estimate.

A live full-AOH budget-1/8 solver has public-and-error-at-least-1/4 probability
at most 1/2. The diagonal finite-law diagnostic has conditional threshold-one
tail one, weighted tail one half, and contradicts a conditional coefficient
with the actual event mass omitted. The diagnostic is not a claimed CFR gap
table. All earlier controls remain unchanged.

Source blobs prepared through the plugin:
- Main: fc18d3354976dce4c1d70bcff285689419de2c9d.
- Examples: 5d3d3572bc110241c7dfc1513e5fbbb85d99c663.

## Validation at source push

All new-source compiler, normal/slow lint, transitive-axiom, all-ReBeL and full
CI outcomes are PENDING. Existing auditors, 107 configured target modules,
251 globally discovered modules, source ledger, inventory, workflows and pins
are unchanged. The added Bounds import uses the existing public finite-law API.
No local Lean, PowerShell or new Python execution is claimed at this point.

Resume by reading exact-SHA workflow jobs and their actual logs. Record all
failures and repairs without removing statements or controls. The pending
candidate coverage is not source-paper acceptance. M06, Theorem 3 and the
four original parent obligations remain incomplete.
