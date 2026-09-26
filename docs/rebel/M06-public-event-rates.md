# M06 actual public-event native-tail slice

## Starting checkpoint and concurrency

Work branch: `rebel/m06-public-event-rates-20260927`.
Base: `a76f1f32403f3cc1834d8f39d11b9802626ee592`, tree
`6f81e399ffc5f489dbaba2857cadc00fb7d0c89e`.

Initial branch enumeration and latest repository push workflows identified
`rebel/m06-conditioned-query-20260925` at `6bc06761937a81eb4468fb3f7f5ec89e019b8ca6`.
A fresh ref read before writing detected the concurrent advance to `a76f1f3`.
Its full commit diff was inspected: it contains the dependent simplification
repair of the public-posterior proof. That change and its comments are preserved.
The isolated branch avoids overwriting concurrent work or cancelling its CI.
An independently prepared unreferenced repair commit `7f9d8e7a9e9e5a2c362f559921322583f8cd9323`
was NOT used to update the advancing branch. No history is rewritten.

The actual failed target log for starting source `6bc0676` was read through
the GitHub plugin: run 36262881059, job 108461920726. Its dependent `rw` motive
failed at PBSConditionedNativeGap.lean:270; FinDistSelection compiled, but the
downstream example and audits were not reached. The new base's target run
36264124596 / job 108465401160 was still compiling when inspected. Its full CI
run is 36264124553. Those pending jobs are not acceptance evidence.

## Dependency-closed implementation scope

Extend the already-imported and audited conditioned-query module and its
existing example module. Reuse the public `FinDist` Markov inequality; do not
add a probability representation or modify an auditor, gate, target or pin.

Prove a positive-threshold tail estimate for the ACTUAL event-conditioned
retained seed/type query, with the actual event mass in the denominator.
Also prove the unconditional joint event-and-bad-native-gap rate directly from
the actual tagged execution. The latter requires no possible-event witness and
therefore includes impossible public observations without inventing a posterior.
Retain finite-T residuals and specialize to publicly observable events.

Provide a genuine full-AOH finite-budget solver consumer and a sharp finite-law
selection control showing why the conditional tail cannot use an unconditional
coefficient. These law-level controls are not claimed to be CFR-generated gap
tables. Preserve all existing positive, hidden-selection and impossible-output
controls.

## Semantic boundary

Both estimates still use the ORIGINAL compatible joint type kernels and the
SAME computed average comparison opponent in the native gap. Execution opponents
remain arbitrary fixed legal policies. An event may correlate the initially
independent private seed/type tags. No hidden seed is supplied to any policy,
no event mass floor is assumed, and no learner-convergence premise is added.

This is not a gap at changed posterior kernels, a changing-opponent estimate,
a fresh independently re-solved carried PBS, or recursive re-solving safety.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
Quantitative first-exit/support rates, changing-opponent/PBS native and late
rates, and CarriedResolveStepBounds remain open. M06 is incomplete; M07 is not
started. Main remains the accepted M05 checkpoint.

## Validation

This is the planning checkpoint, not compiled source. New declarations and
controls must pass exact-SHA target compilation, normal/slow lint and transitive
axiom audit, followed by the unchanged repository workflows. Record source SHA,
run/job IDs and actual log outcomes before claiming acceptance. No local Lean,
PowerShell or new Python test result is claimed at this checkpoint.

All GitHub reads, writes and commits use the GitHub plugin. No local Git
operations or direct GitHub HTTP are used.
