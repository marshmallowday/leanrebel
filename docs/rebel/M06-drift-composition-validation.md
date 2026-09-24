# M06 fresh-value drift — compiler and resume log

Work branch: `rebel/m06-fresh-drift-20260924`, based on
`a5e0700f18ddd19e768c0967d29f1802276ecb55`. Main is not a write target.
All remote reads, branch creation and commits use the GitHub plugin.
The accepted recursive source and its review branch are preserved.

## Accepted predecessor — do not repeat completed work

Proof source `a42467929bbedb0f26bd100e5915d5743ec9025d` has now completed
independent ReBeL run 35954274920 / job 107489146886 successfully at
2026-09-24T04:46:13Z. The job's all-module compile/lint/transitive-axiom gate,
rational solver and independent pure-response gate, architecture/inventory and
tracked-file cleanliness all passed. The downloaded validation log was also
inspected and ends with `REBEL_VALIDATION_PASS modules=231`.
This is a different consumer from the completed supplemental 92-module audit;
neither count replaces the other. Failure-only diagnostic publication was
correctly skipped because the actual gate succeeded.

The previously accepted target run 35954274909 / job 107489146383 and full CI
35954275026 / job 107489156548 remain evidence for that same proof source.
The review commit changes only three documentation files. Old pending entries
in predecessor documents describe the earlier inspection, not the current result.

## Current proof slice

The previous unattached draft contained three same-reference-law composition
lemmas for CFRDFreshValueChange, CFRDFreshValueDrift and CFRDFreshUniformDrift.
That draft has not yet been accepted as Lean-validated evidence. Apply it to the
unchanged proof source, inspect exact-source target CI, and add hostile controls.
Do not infer a small conditional drift from scalar Nash accuracy or identify a
model posterior with the actual unknown-opponent posterior.

Next: derive and test the law-sensitive composition boundary and connect useful
bounds to constructed fresh continuation families without assuming the desired
safety conclusion. Each new source SHA requires its own compile, normal/slow lint
and public/private transitive axiom audit. No gate, target, pin, warning policy,
heartbeat limit, axiom whitelist or existing control may be weakened.

## Original acceptance boundary

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
A same-reference algebraic composition theorem alone does not derive fresh-solve
rates, useful first-exit/support-defect rates, or CarriedResolveStepBounds for
arbitrary repeated independent solves. Preserve all accepted M05 evidence and
the distinction between printed and corrected Theorem 3.
