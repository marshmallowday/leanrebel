# ReBeL status — M06 in progress; M05 accepted

## Current continuation

Resume from `rebel/m06-fiber-lint-repair-20260925` and read
`M06-fiber-lint-repair.md`. This repair descends from documentation checkpoint
e27fee69332f1b55a08f99e68defdd7b5823074e and exact source
4b4395714c62ac8fca0974f1254b7f86c832cd38. The preceding STATUS is preserved
byte-for-byte in `STATUS-before-fiber-lint-repair.md`.

The previous target run36084113146/job107912150501 has now FINISHED with
FAILURE. Compilation of all131 declared M06 targets succeeded, but supplemental
lint rejected an unused `[NeZero t]` argument of
`freshChainControl_parent_fiber_zero` in
GameTheory/Analysis/ReBeL/Examples/CFRDSourceRates.lean:275.
The later transitive-axiom step was not reached; do not count this as an audit pass.

The only Lean change removes that unnecessary hypothesis. Its proof body and
all consumers are unchanged. Source blob is
b452aa3707f7ed9b85a5b18b7319473c06e55663. No module, test, lint, audit, dependency
pin or exception allowance is removed or weakened. New exact-SHA CI must be
inspected before accepting the repair.

## Next proof obligation

Continue from the established actual-law bound
childLoss + B * outcomeRate + 4 * B * referenceRate.
The existing actual two-solve consumer derives referenceRate=0 at the SAME cut.
A small continuation outcomeRate is still an input, not a consequence of Nash.
Investigate a proved one-sided continuation-value guarantee rather than
assuming convergence of whole outcome laws. Preserve the unknown opponent's
actual seed/history law and supported/off-path cases.

Independent re-solving at later carried PBSs, native first-exit rates and
CarriedResolveStepBounds remain open. SEARCH-FRONTIER, SEARCH-CFRD,
SEARCH-ERROR and SAFE-THEOREM3 coverage statuses stay pending. M06 is not
accepted and main is unchanged. The printed/corrected Theorem3 distinction
and real-proof/executable-numerical boundary remain in force.

## Preserved evidence

See `M06-fiber-rates-validation.md` and `STATUS-before-fiber-lint-repair.md`
for predecessor commits, exact workflow IDs, accepted slices and remaining
source obligations. Do not reapply old snapshots or redo accepted slices.
All repository reads, writes and commits use the GitHub plugin; downloaded
artifacts may be inspected and compiled offline without local Git operations.
