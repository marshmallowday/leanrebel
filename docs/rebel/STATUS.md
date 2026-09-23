# ReBeL status — M06 in progress; M05 accepted

## Active integration checkpoint

Resume from actual remote HEAD of `rebel/m06-carried-integration-20260923`.
It descends from `e83ad7db3ab6cfb9374a2d3faad8c53d6213ee7b`, preserved on
`rebel/m06-carried-resolve-20260923`. Main remains accepted M05 at
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`. No main merge or history rewrite.

## Exact-source validation and integration repair

The M06 target-build step for `e83ad7db3ab6cfb9374a2d3faad8c53d6213ee7b`
succeeded in run `35823903393`, job `107061395827`. This includes all four
new modules and their controls. Its supplemental lint/transitive-axiom step
was still running when this integration checkpoint was prepared.

That source's full ReBeL run `35823903390`, job `107061395668`, passed widths,
static architecture and the frozen ledger/inventory checks. The existing
`test_m04_proof_surface` correctly rejected missing DIRECT imports for the
four new modules in `GameTheory/Analysis/ReBeL.lean`, although Search already
included their transitive build closure. This checkpoint adds all four direct
imports; the test, proof bodies, audit allowlist and dependency pins are unchanged.
Its own exact-SHA validation remains to be inspected.

The previous sampled-value checkpoint `e630e689df13eddedafbe3c88c2bf12561b8d1a6`
has now passed full ReBeL run `35820699300`, job `107051833911`, including
compiler, lint, transitive axiom audit, rational runtime and tracked cleanliness.
That success is not attributed to the new source SHA or to unrestricted M06.

## New carried-solver slice

The resolver runs actual information-set CFR on the STORED joint PBS and
samples a fresh private child iteration with its posterior-dependent count.
It is connected to the actual noisy sampled-value parent and finite canonical
carried execution. Missing model beliefs retain the newest private policy,
not the original parent. The whole missing-PBS recursive law is unchanged,
so its additional replacement loss is zero. Expected remaining loss is
localized to available-PBS states under the actual carried-state law.

Controls preserve positive child tolerance, arbitrary fixed opponents,
nonempty private memory and a two-point payoff difference from resetting the
policy. A fixed unknown opponent actually reaches a live public observation
with no incumbent model posterior; this is proved, not assumed as a support
certificate. Read `M06-carried-resolve-review.md` for exact assumptions,
source interfaces, controls and the supported-branch proof obligation.

## Earlier diagnostics retained

`eb59ccf754862f1e584deeee4eb3a44df39cce60`: run `35822279205`, job
`107056486306`, stopped-run import and none-match proof repair.
`2b1d8c7d2daac51a36f46eb079c017e514d8766e`: run `35823272134`, job
`107059492921`, recursive case indentation and additive allowance repair.
The theorem statements, losses and adversarial controls were not weakened.

## Original M06 obligation still open

Fresh solving on available carried PBSs needs its derived counterfactual
opponent-value envelope, including actual histories outside model support.
The generic `CarriedResolveStepBounds` premise is not that derivation.
Zero extra missing-PBS loss is not individual-iterate safety or full recursive
safety. Keep prediction error, finite outer T, positive child loss, and the
printed/corrected Theorem 3 distinction.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending.
No complete-M06, original-algorithm refinement or numerical-execution claim.
