# M06 sampled values: parent-recurrence connection

## Scope and status

Project slice of `docs/rebel/ROADMAP.md` M06, continuing the completed factual
and zero-factual-reach query sampling construction. The implementation branch
is `rebel/m06-sampled-values-20260923`. This record is a supplemental coverage
and semantic-review note, not a replacement for `coverage.json` or its hashed
source ledgers. No original source obligation is reclassified as verified.

Initial implementation: `ce8c0f044f315f04fa6d9da83279f11df65b7785`.
Its targeted run `35819139077`, job `107047034616`, reached the new driver and
reported two unused section-variable lint errors; the successor moves the
unneeded decidable-equality instance below the pure oracle identities.
The safety result and two additional controls are part of that successor and
require fresh target-SHA validation. Pending results must not be cited as passes.

## Exact declarations

All declarations below are under `GameTheory.ReBeL` in
`GameTheory/Analysis/ReBeL/CFRDInformationSampledDriver.lean`.

| Declaration | What is connected | Premises or scope |
| --- | --- | --- |
| `cfrDDepthProfile_live_value` | Restoring the pre-cut trunk preserves the conditional continuation value. | Supported private/live reference fiber, canonical observation clock and finite local menus. |
| `cfrDInformationQuerySample_prediction` | The completed child sampling expectation plus this round's perturbation equals the original parent's prediction. | Supported reference query; no positivity of the child tolerance needed for this identity. |
| `cfrDConstructedSampledInformationOracle` | A total parent response that actually evaluates the sampling law on supported queries. | Unsupported vector entries retain the existing reference convention. |
| `cfrDConstructedSampledInformationOracle_prediction` | Reference-supported queries select that sampling branch, including zero factual mass. | No factual-support restriction is added. |
| `cfrDConstructedSampledInformationOracle_eq` | Equality as oracle functions for every round and trunk, before the coupled recurrence is formed. | Same perturbation function, not an independently supplied strategy sequence. |
| `cfrDConstructedSampledInformationOracle_state_eq` | Equality of the actual recursively computed cumulative regret states at every finite round. | Same canonical initial state and update operator. |
| `cfrDConstructedSampledInformationOracle_carried_security` | Corrected finite-time one-sided security for the sampled-value parent's retained continuation. | Finite legal histories/actions, full AOH, bounded two-player zero-sum utility, positive child tolerance, bounded prediction noise, positive outer T and a reference equilibrium naming game value. |

The carried bound is exactly the existing sum of the two prediction-error
constants times error, plus the two finite-iteration constants divided by
sqrt(T), plus twice the child tolerance. No constant is dropped or absorbed
into a claim of exact optimality. The arbitrary unknown opponent is selected
outside the private parent seed binder. Reference equilibrium is an anchor
for game value, not a child-policy certificate supplied to the solver.

## Positive and boundary controls

`GameTheory/Analysis/ReBeL/Examples/CFRDInformationSampledDriver.lean` uses the
canonical hidden-type game and keeps child loss `1/4` and prediction bias `1/8`.
Its `sampledParentControl_*` declarations cover:

- `off_path_prediction`: an inhabited reference query whose factual mass is
  zero selects the completed sampled-value branch, rather than being discarded.
- `biased_state`: equality of the actual coupled state at every round, not only
  agreement of two externally chosen policies.
- `zero_remaining`: no live fiber exists at zero continuation fuel; the total
  reference convention is preserved and no posterior is fabricated.
- `biased_accuracy` and `biased_isNash`: a nonzero numerical allowance and positive
  child tolerance transfer to the actual output and all behavioral deviations.

The previously proved controls for unknown/randomized opponents, independent
private indices versus a diagonal draw, supported-root reweighting, and
zero-fuel continuation remain imported and unchanged.

## Coverage accounting

| Original obligation | This slice contributes | Still open |
| --- | --- | --- |
| `SEARCH-FRONTIER` | Supported live-query semantics preserve the trunk and early-terminal distinction. | Full original frontier/recursive-algorithm acceptance. |
| `SEARCH-CFRD` | Actual sampled-value response and equality of the coupled parent recurrence. | Fresh independently solved carried-PBS recursion and complete source-algorithm correspondence. |
| `SEARCH-ERROR` | Same numerical perturbation, positive child tolerance and explicit finite-T term. | Error propagation for fresh recursive solves and numeric implementation refinement. |
| `SAFE-THEOREM3` | Corrected retained-continuation bound, not a value-only identity. | The recursive deployed-policy guarantee, preserving original versus corrected statements. |

All four original rows remain pending in the source ledger. This table does
not discharge or silently narrow any of their original obligations.

## Semantic review and next proof boundary

The parent prediction is an **expectation of actual retained child iterates**.
It is not a theorem that one sampled estimate has deterministically small
error, nor that each child iterate is optimal. Positive child tolerance is
used in the quality bound, while sampling law equalities themselves do not
assert optimality.

The supported private/live query conditional is a proof/value-consumer object,
not a policy observation and not a private posterior substituted for a PBS.
It retains the complete correlated history law. Completed zero-factual-mass
queries select the existing computed off-path response; unsupported reference
fibers never acquire a sampling interpretation through the total vector fallback.

`privateCarriedContinue` retains the selected parent continuation. It does not
invoke a fresh child solver at every subsequent PBS. The existing coherent
multi-stage re-draw result preserves a fixed parent family and is likewise not
fresh independent re-solving. Connecting independently solved child recurrences
requires a proof that also handles actual histories outside the model support
under an unknown opponent; it must not introduce a caller-supplied final-safety,
posterior-equality or support-domination certificate.

## Validation consumers

Both new modules are in the opt-in Analysis umbrella, `m06-targets.txt`, and
`audit_exact_leaf.py`. The supplemental audit also now explicitly includes the
pre-existing `CFRDInformationQuerySampling` module. Its collection of every
transitive axiom retains only `propext`, `Classical.choice`, and `Quot.sound`;
normal/slow Batteries lint remains enabled. No architecture budget, warning
option, test statement, dependency pin or hashed source row is weakened.

Exact run/job outcomes and the current resume branch are recorded in `STATUS.md`.
