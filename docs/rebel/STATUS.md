# ReBeL status — joint-query compiler repair; M06 incomplete

## Resume exactly here

Work branch: `rebel/m06-joint-query-repair-20260925`; read its latest head.
Parent: `8179309e5adb72d9fd848b7712d8aac870f73646`.
Initial source `ada439cebe48ad3c522afd95c61c2efe32412bde` is retained on
`rebel/m06-joint-query-20260925`. Read M06-joint-query-compiler-repair.md,
then M06-joint-query-repair.md and M06-joint-query.md. Preserve all checkpoints.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; M05 is accepted.
M06 and Theorem 3 are NOT complete.

## Completed diagnosis, current source awaiting validation

Initial target `36148111692` / `108114248701` compiled PBSJointNativeGap and
its three new main theorems. The controls failed at an incorrect map_map API
name and a product-expectation simplification order. Actual log/artifact hashes
are retained. The current source repairs those two control proofs using the
canonical map_comp/map_id and an explicit expect_product rewrite, without
changing statements or weakening any control. Initial lint/axiom collection
was skipped: do not infer any new-module axiom result from the main compilation.

The separate local-hypothesis rename to jointDensity was already confirmed by
parent 8179309 ReBeL `36148730537` / `108116314777` passing static architecture
and line widths. Its exact source passed all 87 Python tests, ledger/inventory
structure and all 580 public-file width checks. Parent targeted `36148749730`
/ `108116381897` and full CI `36148730659` / `108116316098` are not current-
source evidence and may be superseded by this push.

Inspect the CURRENT head's M06 targeted, all-ReBeL and full-CI runs next.
New-source compile, individual normal/slow lint and complete transitive axiom
sets remain PENDING. No local Lean run is claimed. Preserve the independent
accepted native predecessor e65152038f6a9068be68aff28ad6845f74097e94 and its
247-module/4799-declaration global audit in M06-native-gap-global-validation.md;
do not redo it or misattribute it to the new joint modules.

## Mathematical scope and remaining M06

The fixed-slice, fixed-average-opponent native gap has a bounded JOINT seed/type
density interface, a tagged seed-dependent kernel bridge and computed positive-
budget bound. The actual query need not be independent. The exact joint cap
remains explicit; equal marginals alone are insufficient, as the preserved
factor-two diagonal control demonstrates. Off-support actual mass is excluded
by a separate boundary. Finite-law diagnostics are not CFR-generated gap tables.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
Construct the actual carried seed/history/query law and its density, support
and first-exit rates; independently changing opponents/PBS native and late
rates, recursive re-solving safety and CarriedResolveStepBounds remain.
Keep private retained seeds, compatible off-path kernels and finite-T residuals.
Learner convergence must not replace independent test-time safety.
