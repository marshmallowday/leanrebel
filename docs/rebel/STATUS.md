# ReBeL status — support rates compiler-validated; M06 incomplete

## Resume branch and exact implementation

Continue `rebel/m06-support-rates-checkpoint-20260927`. This evidence-only
checkpoint descends from `b833d49b430ac44c433658f3cc72fd130ff0a87f` on
`rebel/m06-support-rates-20260927`; the three Lean source files, Python tests,
imports, validation scripts, workflows and dependency pins are unchanged.
The separate checkpoint branch preserves the still-running b833 global ReBeL
audit from same-branch concurrency cancellation. It is not a new algorithm
variant or the start of M07. Check the exact implementation's pending global
run below before changing its source branch.

The implementation descends from combined integration
`7326f1e40011b1d4329f09e743491cc7bc7e5746`, retaining both integration parents.
Feature checkpoint `f14ec3bddd5e61ba3e4eb505cd2c73a37f7f3068` failed its first
compiler attempt; b833 repaired only proof normalization, not statements or
hypotheses. That failure remains recorded. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. M06 and paper Theorem 3 are NOT
complete. Main is not updated and no branch is force-pushed or deleted.

## Completed dependency slice

The support-specific rate bounds genuine carried posterior containment
failure by incoming unsupported mass plus one-step kernel support leakage
averaged along ACTUAL execution. Unlike full source-atom variation, unequal
positive weights inside model support incur no incoming support cost.
Finite-horizon propagation, comparison with the old variation charge and zero
charge under explicit support inclusions are now compiler-validated. The
consumer uses the actual budget-1/8 information-set CFR child, a supported
actual history and an arbitrary fixed legal unknown opponent. Canonical
finite-law controls expose differing positive weights and wrong-prefix
undercharging. Original source statements and tests are preserved.

## Exact b833 evidence actually inspected

Read M06-support-rates-b833-validation.md for current evidence and hashes;
M06-support-rates-validation.md is the earlier checkpoint/failure history.
M06-support-rates-coverage.json gives exact declarations and source blobs.
M06-support-rates-axioms.log preserves the 16 new declarations' actual records.

Target run 36277876540 / job 108503997685 / artifact 10917649066 succeeded:
Lean 4.33.1, two successful builds, 110 normal/slow lint passes, all 1,774
complete transitive-axiom records allowlisted, and final validation pass.
All 16 new public declarations occur in the actual output. No Lean compiler
or lint error/warning diagnostic was found. This is b833 evidence, not a
reused pass from either integration parent.

Full CI 36277876544 / 108504133348 / artifact 10918131435 succeeded. The
actual job and artifact logs were inspected: full build, compiler-backed
inventory, phase 1/2/3 architecture, full lint and tracked-file cleanliness.
Source inventory 36277876557 / 108503997761 also succeeded; its actual log
includes all 112 Python tests. Local exact-source Python checks also pass.
Python arithmetic and inventory structure are not semantic Lean proofs.

## Pending global audit and next step

For implementation b833, global ReBeL run 36277876590 / diagnostics job
108504099546 is still running its compiler/lint/axiom stage at this checkpoint.
Its exact-source snapshot job 108504099412 succeeded, but the final global
diagnostics artifact has not yet been inspected. First fetch this run's jobs
and artifacts through the GitHub plugin, inspect the actual complete output,
and retain any failure. Do not label it passed based on target/full-CI success.
The documentation-only checkpoint HEAD has its own workflow identity; those
new runs are not represented here as already successful.

The original 110 target modules, 253 globally discovered modules and 3,054
ledger/inventory items remain unchanged. No local Lean or PowerShell execution,
warning suppression, audit-count adjustment or skipped CI is claimed.

## Remaining semantic boundary

The proved bound is for a fixed-profile finite continuation, not the complete
independently re-solved carried schedule. Support dominance is an explicit
sufficient premise, not a property established for every unknown opponent.
Small accumulated leakage, changed-PBS native/late rates and
CarriedResolveStepBounds remain separate obligations. Being in a stored PBS
support does not identify the actual conditional law with that stored PBS.
Original compatible joint type kernels, the same computed comparison opponent,
actual public event-mass denominators and finite-T residuals remain visible.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No learner convergence or dropped residual term bypasses test-time safety.
M07 onward retains the user's one-integration-branch-per-milestone policy.
