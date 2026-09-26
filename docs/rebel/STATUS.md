# ReBeL status — randomized resolver support candidate; M06 incomplete

## Resume branch

Continue `rebel/m06-resolver-support-20260927`, created from the latest observed
checkpoint `3d272004909c9e70226aeb430813d3d53f038fdd` on
`rebel/m06-support-rates-checkpoint-20260927`. Its parent implementation is
`b833d49b430ac44c433658f3cc72fd130ff0a87f`; the combined integration
`7326f1e40011b1d4329f09e743491cc7bc7e5746` and both prior integration parents
are retained. Main stays at accepted M05
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. No force-push or branch deletion.

The new candidate extends PBSOpponentModelTransport with a support bound for
the actual randomized public resolver and its retained-memory transition,
then averages over arbitrary actual full-state laws. It does not replace the
random draw with a pooled model posterior. Stopped and missing-belief cases
are explicit. Read M06-resolver-support.md and its subordinate coverage JSON
for exact declarations, premises, validation state and unclosed obligations.

## Validation boundary

The new declarations are NOT yet compiler-accepted. Check the exact new HEAD's
M06 targeted proof feedback, ReBeL checks, full CI and inventory. Existing
normal/slow lint and axiom consumers already cover both edited proof/example
modules; no gate, dependency pin, original theorem or test is weakened.

Baseline b833 evidence remains in M06-support-rates-b833-validation.md,
M06-support-rates-coverage.json and M06-support-rates-axioms.log. Its earlier
failed f14 compiler attempt remains recorded, not reclassified as success.
The inspected prior target had 110 module lint passes and 1,774 complete
allowlisted axiom records; new declarations must have their own actual output.
Prior full CI and 112 Python tests do not validate this new implementation.

At this session's first check, b833 global run 36277876590 / diagnostics job
108504099546 was still in its compiler/lint/axiom step; source snapshot job
108504099412 had succeeded. The separate new branch preserves this run. Fetch
its final jobs/artifacts and inspect actual output before claiming global
success. The old documentation checkpoint also has distinct workflow identities.

## Next steps and remaining M06

Compile and repair the candidate against pinned Lean 4.33.1, add and inspect
randomized-pairing and stopped/missing controls, then record exact source SHA,
run/job IDs, actual lint and axiom evidence. GitHub edits alone are not Lean
validation. Pending work must be resumed from those checkpoints, not repeated
from an earlier branch or inferred from old target passes.

Full native schedule first-exit composition, small accumulated support rates,
changed-PBS native/late value gaps and source-specific CarriedResolveStepBounds
remain open. A supported stored PBS is not the actual conditional law and is
not itself a security value bound. Preserve joint-type compatibility, the
same comparison opponent, actual event denominators and finite-T residuals.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
M06 and original paper Theorem 3 are incomplete. No learner convergence premise
is used to bypass test-time safety. M07 onward retains the one-integration-
branch-per-milestone policy.
