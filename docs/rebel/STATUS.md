# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-carried-checkpoint-20260923`.
This documentation-only checkpoint descends from integration commit
`e7360412dacd76216823b1fa28702b84c1b4ae4c`, whose branch
`rebel/m06-carried-integration-20260923` is preserved for its CI run.
The tested theorem source `e83ad7db3ab6cfb9374a2d3faad8c53d6213ee7b` remains
on `rebel/m06-carried-resolve-20260923`. Main is unchanged at accepted M05
`6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

## Confirmed compiler, lint and axiom evidence

For e83ad7db, M06 targeted run `35823903393`, job `107061395827`: SUCCESS.
The declared targets, all four new modules, their adversarial controls, and
supplemental normal/slow lint passed. The inspected transitive audit reported
`EXACT_LEAF_AXIOM_AUDIT_PASS declarations=2335` and
`EXACT_LEAF_VALIDATION_PASS modules=62`, with only propext, Classical.choice
and Quot.sound allowed. This is scoped exact-source evidence, not full M06.

The integration commit e7360412 adds the four missing direct analytic-root
imports, plus documents only. The theorem bodies, tests, audit script and
dependency pins are unchanged from the successful e83ad7db target.

For e7360412, source inventory run `35824538883` succeeded. ReBeL run
`35824538878`, job `107063312144`, passed widths, static architecture,
ledger/inventory/adversarial fixtures and rational runtime; its full compiler/
lint/axiom step was still running at last inspection. Full CI run
`35824538900` was also still running. Check those exact runs before claiming
full integration acceptance. This documentation push does not invent a pass
for its own SHA or replace a source run's evidence.

`M06-carried-resolve-validation.md` preserves exact commits, commands, run/job
IDs, audit counts and failed checkpoints. `M06-carried-resolve-review.md`
records declaration-level assumptions and the original remaining obligation.

## Completed scoped construction

`CFRDInformationResolve` runs actual information-set CFR at the STORED joint
PBS and draws a fresh private child iteration with a posterior-dependent
conditional budget. The new finite schedule is connected to the actual noisy
sampled-value parent in `cfrDInformationRecursivePlay`. Existing canonical
carried execution retains each selected model profile and propagates its PBS.

If the stored PBS is absent, the newest private incumbent is retained rather
than resetting to the initial parent. `cfrDInformationResolveStages_run_none`
proves that the entire finite remaining schedule has exactly that incumbent's
canonical continuation law against any fixed unknown opponent. Its additional
replacement loss is zero; the remaining expected loss is localized to states
with an available PBS, under the actual carried-state law.

The controls include a live positive-tolerance child solve, nonempty private
memory, zero and positive execution intervals, and an explicit payoff 2 versus
0 when incorrectly resetting the incumbent. A separate fixed uniform legal
opponent actually reaches a live observation with no incumbent model posterior:
reachability, missing belief and liveness are separately proved, not supplied
as support assumptions. The resulting missing-PBS recursive law is checked.

## What must not be redone or overclaimed

The sampled-value parent remains validated; its prior checkpoint e630e689
passed full ReBeL run `35820699300`, job `107051833911`. The new source target
also passed after the recorded import/match/indentation/allowance repairs.
The analytic-root registration failure was corrected by adding imports, not
by weakening its test. No source obligation was removed or relabeled verified.

## Remaining original M06 work

First finish the exact-source integration review using the runs above. Then
derive the counterfactual OPPONENT-value upper envelope for fresh solves at
available carried PBSs, including actual histories outside a present model
law's support, and propagate it through the actual recursive execution.
The generic `CarriedResolveStepBounds` premise is not that derivation.

Zero additional missing-PBS loss is not individual-iterate optimality or full
recursive safety. The model-root sampled-child bound alone does not transfer
to arbitrary actual roots. Keep numerical error, finite outer T, positive child
loss and the printed/corrected Theorem 3 distinction. The explicit none fallback
is a completion policy, not a proved refinement of every source implementation.
`SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, `SAFE-THEOREM3` remain pending.
No complete-M06, single-draw accuracy or numerical-execution claim.
