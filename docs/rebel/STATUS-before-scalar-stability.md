# ReBeL status — M06 in progress; M05 accepted

## Resume from the value-coupling checkpoint

Documentation/checkpoint branch: `rebel/m06-value-checkpoint-20260925`.
Validated source: `4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5` on
`rebel/m06-value-stability-20260925`. The checkpoint adds documentation only;
the source branch remains fixed to avoid canceling its wider CI runs.
The predecessor is `c984277c2238e4dd1249ff3ace6fc5444175858a`.
Main and predecessor branches are unchanged. The previous STATUS is preserved
in `STATUS-before-value-coupling.md`.

Read `M06-value-coupling-validation.md`, `M06-value-coupling-review.md`,
`M06-value-coupling-coverage.json` and `M06-value-coupling-axioms.json`.
The initial resumption record remains `M06-value-stability-progress.md`.

## Newly validated conditional source slice

The three new modules are FinDistValueCoupling, CFRDValueCoupling and its
example. An explicit coupling preserves both actual continuation marginals
and charges only a positive opponent-payoff change. It yields the actual-law
weighted fresh-resolving charge bound

    childLoss + valueRate + 4*B*referenceRate.

A nonconstant two-type payoff control has outcome L1 variation 2 and directed
cost 0. Direction and incorrect-marginal negative controls also compile.
The finite noisy-parent/two-fresh-solve security consumer discharges the
reference fiber rate internally by same-cut preservation. It retains positive
parent bias, finite T and distinct child losses. Its small directed cost is
an explicit source premise, not a consequence of scalar Nash accuracy.

Target run `36103763186`, job `107971683742`, completed SUCCESS at the source
SHA above. The downloaded log was inspected: 134 declared targets compiled;
`EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1527` and
`EXACT_LEAF_VALIDATION_PASS modules=96`. Every parsed transitive axiom belongs
to {propext, Classical.choice, Quot.sound}. New-module counts are 6/3/27,
including generated/private declarations, with individual lint/axiom passes.
All old targets and audit consumers are retained. Inventory CI36103763176
also succeeded; offline ledger/inventory checks and all 76 Python tests passed.
The evidence documents retain both failed source attempts and their repairs.

## Full CI passed; independent ReBeL census still running

Full CI `36103763182`, job `107971742837`, also completed SUCCESS. Its downloaded
audit artifact10851056189 identifies the same source SHA; Phase1/2/3 logs each
end in VERIFIED=1 and GameTheory.LintAll passed. The job also passed the full
build, inventory/compiler-signature checks and tracked-file cleanliness gate.

At checkpoint assembly, independent ReBeL run `36103763078`, diagnostics job
`107971751432`, was still in progress in its all-ReBeL compile/lint/axiom step.
Read that exact-SHA result before further implementation or integration. Its
partial successes are separate from final success; no background follow-up
is implied.

## Remaining M06 obligations

Construct small one-sided value bounds for native/late-training solver queries.
A small directed coupling cost is sufficient but not necessary: equal expected
payoffs alone do not supply it. Do not substitute this conditional bridge for
a native rate proof. Later independent carried-PBS re-solving, native first-
exit rates and CarriedResolveStepBounds are still required. Preserve the actual
private seed/history law, off-path support, model-versus-actual belief boundary,
and the distinction between native iteration and final-average sampling.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending in
the canonical ledger. The scoped companion records this conditional result
without promoting the parents. M06 is NOT complete. Keep finite-T error at
zero oracle error and preserve printed/corrected Theorem3 distinctions.
