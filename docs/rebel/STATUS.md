# ReBeL status — M06 in progress; M05 accepted

## Active carried-solver checkpoint

Resume from actual remote HEAD of `rebel/m06-carried-resolve-20260923`.
Main remains accepted M05 `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.
No main merge, force update, source-ledger completion or dependency change.

## Exact compiler feedback preserved

`eb59ccf754862f1e584deeee4eb3a44df39cce60` failed in targeted run
`35822279205`, job `107056486306`: missing stopped-run import and unreduced
resolver match. Both were repaired at `2b1d8c7d2daac51a36f46eb079c017e514d8766e`.

That successor's targeted run `35823272134`, job `107059492921`, compiled
`CFRDInformationResolve` and elaborated the whole-schedule missing-PBS
induction without an error there. It failed later on a case-branch indentation
and the order of the additive Nash allowance in `CFRDInformationResolveRecursion`.
This newest source repairs those scripts, retaining all statements and losses.
Its own exact-SHA build, lint and transitive axiom results are still required.

## Construction and controls now present

The resolver runs the actual information-set CFR backend on the STORED joint
PBS, samples a fresh child iteration with a posterior-dependent budget, and
propagates the canonical carried state. A missing PBS retains the newest
private policy, not the initial parent. The entire missing-PBS recursive law
and its zero additional replacement loss are proved by schedule induction.
Remaining expected replacement loss is isolated to available-PBS states.
The actual noisy sampled-value parent is connected by `cfrDInformationRecursivePlay`.

`Examples/CFRDInformationResolve` retains the positive tolerance `1/4`, live
children, arbitrary fixed opponents, nonempty private memory and a two-point
payoff difference from wrongly resetting the policy. The new
`Examples/CFRDInformationMissingModel` constructs a fixed uniform legal
opponent for whom a genuinely model-impossible LIVE public observation is
actually reached. Its carried state has `none`, and its later recursive law
uses the proved incumbent preservation. No support hypothesis is supplied.
All four new modules are in the Search/Analysis build closure and explicit
supplemental lint/axiom consumers.

## Preserved earlier checkpoint and remaining original obligation

The sampled-value parent source `b3d63c722d94a5aaee60403025a5a71d4b650a4b`
passed M06 run `35820010308`, job `107049652032`; its finite outer-T,
prediction error and positive child loss remain unchanged. See the existing
`M06-sampled-values.md` and `M06-sampled-values-validation.md`.

Fresh solving on available carried PBSs still needs a derived counterfactual
opponent-value envelope, including actual histories outside the model support.
The generic `CarriedResolveStepBounds` is not such a derivation. Zero EXTRA
loss at a missing PBS is not individual-iterate safety or supported-branch
recursive safety. Preserve printed/corrected Theorem 3 distinctions.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending.
`M06-carried-resolve.md` records the supplemental scope and semantic boundaries.
