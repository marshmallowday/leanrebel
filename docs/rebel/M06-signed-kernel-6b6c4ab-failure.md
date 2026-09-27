# Signed-kernel batch: 6b6c4ab exact-SHA feedback

Candidate: 6b6c4ab3ce5dd934806a3a9f4f3a35010549f387.
Branch: rebel/m06-kernel-value-repair-20260927.
Main was re-read as 6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098.
The connected account is marshmallowday with current admin/push access.
Continue this existing candidate branch because it contains the pending M06
signed-kernel batch and its supported-fibre repair.

## Actual Actions evidence

All runs below report exactly the candidate head SHA. Complete decoded job
logs and artifact metadata were read through the GitHub plugin.

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36322384444](https://github.com/marshmallowday/leanrebel/actions/runs/36322384444) | 108628587135 | failure |
| ReBeL checks | [36322384401](https://github.com/marshmallowday/leanrebel/actions/runs/36322384401) | 108628586922 | failure |
| M06 targeted | [36322384519](https://github.com/marshmallowday/leanrebel/actions/runs/36322384519) | 108628587396 | failure |
| Source inventory | [36322384377](https://github.com/marshmallowday/leanrebel/actions/runs/36322384377) | 108628586869 | success |

All three Lean jobs report the same unused-section-instance errors:
- PBSKernelValueTransport.lean:52, conditionalPayoff_ofJointBelief.
- PBSKernelValueTransport.lean:73, conditionalPayoff_ofJointBelief_mean.
- PBSCarriedValue.lean:317, carriedReplacementSignedLoss_le_valueCoupling.
- PBSCarriedValue.lean:372, executeCarriedResolves_loss_eq_signed.

The unused instance is [Fintype E.History]. TypeBeliefSlice now compiles,
so the preceding supported-fibre proof repair has passed this build stage.
This does not constitute complete new-source acceptance.

Checks passed LIBRARY_LINES_OVER_100=0 and TRANSPORT_ANALYSIS_SOURCE=0,
164 Python tests (11.722 seconds), and the rational solver/runtime gate.
Inventory independently passed 164 tests (7.643 seconds).
Complete build, normal/slow lint, and transitive axiom acceptance were blocked.
No local Lean, lint, axiom audit, or Python execution is claimed.

Artifacts:
- Target 10932753111, digest
  sha256:6afb62a41a1f9c188a034a4571220292cdf1c44b103d5ebc9cac420c5a6976ed.
- Global diagnostics 10933211130, digest
  sha256:73061d8a99a286445f099c2a75cc4a7047a7ce052b7ab94cd91e2c8438ded420.
- Source snapshot 10932049124, digest
  sha256:4e900ee1e9625dca8107c6bdf6014f9c6f4b513c062954b0bd662b1ed72a95f4.
Binary archives were not downloaded; diagnosis uses complete decoded job logs.

## Consolidated repair

Use Lean's explicit omit [Fintype E.History] in on the four reported theorems.
Also remove this unnecessary section instance from their three downstream
consumers carriedSignedSequenceLoss_const,
carriedResolveStepBounds_of_valueCoupling, and
privateRecursiveResolve_inherits_signedLoss. Their earlier proof dependencies
retained the instance solely through the affected theorem signatures.
Execution-charge and initial CFR theorems retain their necessary finiteness.

The seven theorem proof bodies, payoff expressions, hypotheses other than the
irrelevant instance, and conclusions are unchanged. Removing an unused premise
generalizes these statements; it does not weaken the conclusions or disable
the linter. The complete chain will be checked together by Actions.

Workflow, target lists, audit code, tests, and mathematical specification are
unchanged. Preserve 156 targets, 118 targeted/261 global modules and 164 tests.
Current CI push, ReBeL rebel/** push, and targeted rebel/m06* plus Analysis
path conditions cover this repair. No manual dispatch is assumed.

The frozen historical coverage blob remains
2fc8cc9ad6607d61bfe397707fb96ac322fbb800; the previous owner ledger is archived
verbatim at M06-kernel-value-transport-coverage-at-6b6c4ab.json.
Original acceptance rows remain pending. The signed-kernel batch is not
accepted until its repaired SHA passes all gates. M06 remains incomplete;
d771e88 validation is historical evidence only.
