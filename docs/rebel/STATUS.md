# ReBeL status — M06 in progress; M05 accepted

## Current continuation

Resume from `rebel/m06-calibration-controls-20260925` and read
`M06-value-calibration.md`. This extends source checkpoint
59a90791825122208247ea912a9c94833cad05b6 and lint repair
c984277c2238e4dd1249ff3ace6fc5444175858a. The earlier STATUS is preserved in
`STATUS-before-fiber-lint-repair.md`; do not reapply its old source snapshots.

The lint repair passed its declared-target build and supplemental validation
(run36093962253/job107942125914), full build/lint/architecture checks
(run36093962268/job107942126260), inventory and source snapshot. Its independent
ReBeL job107942125979 was still running at the last check. The calibration-core
commit's CI is separately tracked under run36095287300/job107946171666.
No result for one SHA is evidence that a later source SHA passed.

## Added proof slice

The existing CFRDSourceRates module now derives the ACTUAL private seed/history
weighted loss bound childLoss + oldError + newError from a shared information-local
value target, equal unilateral reference laws and supported-live calibration.
It does not require closeness of whole continuation outcome laws.
The extended example derives reference equality from the actual two fresh
same-cut solves and consumes this bound in the biased finite-parent security
claim. A nonconstant-payoff tie control has L1 distance two and zero value error.
A separate coarse calibration baseline is proved with errors two and two from
the actual payoff bound; it is NOT a vanishing native solver rate.

## Corrected predecessor audit evidence

The 4b439571 target run36084113146/job107912150501 failed on the unused
`[NeZero t]` argument in freshChainControl_parent_fiber_zero AFTER successful
compilation AND transitive axiom audit. Its log explicitly records
`EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1491`. The audit script runs axioms
before supplemental lint. The earlier repair note's claim that the axiom step
was not reached was incorrect and is corrected here and in that note.
The exact failure is retained; no lint allowance was added.

## Remaining M06 obligations

Derive sharp common-target calibration from the intended native oracle/solver,
not from scalar Nash quality alone. Independent later carried-PBS re-solving,
native first-exit rates and CarriedResolveStepBounds remain open.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
M06 is not accepted and main is unchanged. The printed/corrected Theorem3
distinction and real-proof/executable-numerical boundary remain in force.

New declarations extend existing umbrella imports, M06 targets and supplemental
audit modules; no prior module or gate is removed or weakened. Inspect the
latest commit's exact CI, fix any diagnostics, then record its completed checks
before accepting this proof slice. GitHub access and commits use the plugin.
