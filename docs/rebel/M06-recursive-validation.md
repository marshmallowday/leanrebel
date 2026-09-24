# M06 recursive solver — exact-source validation log

Proof source: a42467929bbedb0f26bd100e5915d5743ec9025d on
`rebel/m06-recursive-solver-20260924`.
Documentation/restart branch: `rebel/m06-recursive-reviewed-20260924`.
This recording checkpoint changes only documentation, not the validated Lean,
registration files, workflows, scripts, pins or coverage statuses. The proof
branch is preserved so its independent ReBeL run is not cancelled by these notes.
All repository reads and writes use the GitHub plugin. Main is not a write target.

## Accepted a4246792 target and whole-library CI

M06 target run35954274909/job107489146383: SUCCESS, completed
2026-09-24T04:19:51Z. All declared targets, including PBSComposedDepth,
PBSRecursiveDepth and Examples.PBSRecursiveDepth, compiled. The full completed
job log was inspected, not only the green build step. It records:

    EXACT_LEAF_AXIOM_AUDIT_PASS declarations=961
    EXACT_LEAF_VALIDATION_PASS modules=92

The supplemental auditor checked every registered module's public, private and
generated declarations transitively. Only propext, Classical.choice and Quot.sound
were allowed. Every module passed the normal Batteries linters and the separate
slow defLemma linter. In particular all three new modules have both normal/slow
success and their EXACT_LEAF_LINT_PASS markers. No skipped audit is counted.

Full run35954275026/job107489156548: SUCCESS, completed
2026-09-24T04:19:42Z. The job confirms the complete public-library build, exact
source/toolchain identification, inventory and compiler-resolved reuse signatures,
architecture Phases1/2/3 and reachability probes, public-library lint, and tracked
file cleanliness. The Windows-only toolchain exposure step was correctly skipped
on the Ubuntu runner; the actual build and architecture/lint gates all succeeded.
Inventory35954274949/job107489146497 and source snapshot35954274920/
job107489146729 also succeeded at this same SHA.

Independent ReBeL run35954274920/job107489146886: IN PROGRESS at recording.
Its line-width, static-architecture, ledger/inventory/adversarial-fixture and
rational-runtime/independent-pure-response steps had all succeeded. Its whole
ReBeL compile/lint/transitive-axiom step and final cleanliness still need the run's
final result. Keep this pending result distinct from the completed target and
full-CI validations. Inspect the preserved run before new implementation work.

## Preserved accepted predecessors

Finite-budget704e96ff6ed5b73b279191ea2d01629cc331e8d8 also passed independent
ReBeL35946360239/job107465227645. Nestedf9d4def18411b43fc14c508b079fadb0378bd178
also passed independent ReBeL35947018175/job107467137458. Both include all-module
compilation, lint/transitive axiom auditing, rational runtime/independent pure
responses, architecture/inventory and cleanliness. Earlier pending entries were
stale, not failed checks; do not repeat completed work.

Repair751ad17af36d6ff4f3deea2c1ee513f10dc754d9 passed target35951624022/
job107481206024, with all named targets and complete supplemental normal/slow
lint and public/private axiom audit: modules=89. Full35951624454/job107481206699
and inventory35951624043/job107481205391 succeeded. Independent ReBeL35951624061/
job107481299594 is now also confirmed SUCCESS, completed2026-09-24T03:54:04Z,
including all-module lint/axioms, rational runtime/independent responses and
tracked-file cleanliness. This completes its formerly pending evidence.

## Compiler loop retained for recovery

Parenta01832184554acc81da55d991f118654ef5c5442: target35952219144/
job107483131698 compiled all named targets. Its supplemental audit was not yet
complete before the next push; no whole validation is claimed for that source.

Initial recursionf375294fa122dcca803319d3466d0a96925e6ce5:
target35952776340/job107484869406 failed when the equation elaborator introduced
the family's implicit protocol before the branch tactic. Explicit protocol
arguments in both computational families repair the shifted introductions.
The proof-local instance style rule was obeyed, not disabled.

Sampler97fcab0bf7740de4a6ca72013d34ab266d2511d3:
target35953636852/job107487235722 compiled PBSComposedDepth, including the exact
private-round history law, and all of PBSRecursiveDepth, including structural
induction, positive noise, sampling/value laws and the canonical carried resolver.
All older targets compiled. Only Examples.PBSRecursiveDepth failed: it needed
its own finite-menu instance, and simplifier transparency obstructed the concrete
Nash conclusions. Its supplemental audit was SKIPPED and is not accepted evidence.

Independent ReBeL35953636757/job107487342381 stopped before compilation at the
static line-width gate: eight lines were101--107 UTF-16 code units. The a4246792
successor wraps all eight without changing the100-column gate. It installs the
canonical finite-menu instance and applies the derived Nash theorem directly at
[1,1,1], [0,1,1,1] and [1]. All theorem conclusions and boundary controls remain.
The exact-source successes above validate this final repaired implementation.

## Proof scope and acceptance boundary

No source placeholder, custom axiom, heartbeat increase, dropped boundary case,
weakened warning/lint gate or toolchain/dependency change was used. All previous
module registrations are retained; three were added to the analytic root,
M06 targets and supplemental audit. The final documentation commit's own CI is
not silently equated to this inspected source: its Lean and CI inputs are the
same, while its metadata changes are explicitly recorded separately.

The derived finite recursive local solver and complete private-sampling history
law are accepted by the completed checks. They do not establish source-level
fresh conditional-value drift, useful support/first-exit error rates or
CarriedResolveStepBounds for arbitrary repeated independent fresh solves.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
Retain the distinction between model PBS and actual opponent-conditioned law,
and between the printed and corrected source Theorem3 statements.
