# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual HEAD of `rebel/m06-first-exit-review-20260924` for the latest
checkpoint record. Its Lean source and validation configuration are identical
to `487aaedd795d5d3a8b41a608c6a4e13d1967cb1c` on the preserved source branch
`rebel/m06-first-exit-20260924`. The review checkpoint changes documentation only.
Keeping the source branch unchanged avoids cancelling its running CI checks.
Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`; do not write main.

First inspect the exact-source runs below. Do not repeat the completed support
repair or reimplement the validated first-exit theory and controls. Never infer
that a pending check passed, and never use the base's passing results for the
new proof source. The independent repository-wide checks remain required.

## Completed recovery checkpoint

Source `01245b31164eabcb7012e98b36d57b470496dd8e` on
`rebel/m06-first-hit-recovery-20260924` has all four inspected workflows passing:
M06 target35939097445/job107442786882; ReBeL35939097447/job107442786889;
full repository CI35939097488; inventory35939097484.
The ReBeL job completed its compiler/lint/transitive-axiom audit and tracked-file
cleanliness check successfully. This supersedes earlier pending snapshots.
The repair removed the concrete support proof's transport elaboration without
raising heartbeats, weakening architecture budgets, or changing its statement.

## New first-exit source: target compiler and supplemental audits passed

Exact source: `487aaedd795d5d3a8b41a608c6a4e13d1967cb1c`.

| Check | Inspected result |
| --- | --- |
| M06 target35941683756/job107450728931 | SUCCESS: declared-target compilation and supplemental lint/transitive-axiom validation. |
| ReBeL35941683758/job107450798403 | In progress: width, static architecture, ledger/inventory/adversarial fixtures and rational solver checks passed; complete proof audit still running. |
| Full CI35941683736/job107450816152 | In progress: inventory and Phase1 architecture passed; Phase2 architecture/reachability running. |
| Inventory35941683774/job107450728949 | Success. |
| Source snapshot35941683758/job107450798669 | Success. |

The target's complete, untruncated log identifies this exact SHA, reports the
three extended modules built successfully, and ends with
EXACT_LEAF_AXIOM_AUDIT_PASS and EXACT_LEAF_VALIDATION_PASS. The lint report
contains no errors. This supersedes the earlier pending supplemental-audit
snapshot and the failed9165ff11 candidate. It does not establish a final result
for the independent ReBeL/full-CI runs, nor completion of M06.
See M06-first-exit-validation.md for the source-specific evidence boundary.

## Preserved work and current mathematical result

The source sequence is support repair01245b31, first-exit theory6be7364c,
concrete controls9165ff11, Option.isSome repair9537c4f3 and trigger fix487aaedd.
The last repair adds probability-only changes to the M06 targeted workflow;
every prior trigger, target and validation command remains unchanged.

FinDistFirstHit constructs the first exceptional state paired with its unexecuted
suffix, including the exceptional stage. Its Boolean image is the existing hit
law. Complete signed payoff discrepancy equals expected signed suffix discrepancy
at native first-exit witnesses. Expected absolute suffix discrepancy refines the
old 2*observableBound*hitProbability bound.

PBSCarriedDepthFirstHit instantiates the result for the actual noisy solver,
preserving all private profile/model-PBS/history correlation. The existing real
two-stage executeCarriedResolves runner is connected. Controls include late,
absent and repeated events, retained suffixes, kernel invariance, signed -2,
a harmless future with hit probability1, and fractional probability1/4/charge1/2.
Positive prediction bias1/8, child tolerance1/4 and iteration counts2/3 remain.
See M06-first-exit.md and M06-first-exit-controls.md.

## Remaining original obligations

The real-valued suffix charge depends on the actual unknown-opponent kernels
and future observable. It is not an executable learned estimate, a convergence
rate, or a uniform unknown-opponent security budget. Derive useful source-level
suffix/support-defect bounds and model-value drift. Connect arbitrary-depth child
solving; deepest children still use full-root CFR. Discharge
CarriedResolveStepBounds rather than supplying it as an assumption.
Retain finite outer T, positive numerical/child errors, zero-reach completion,
and the printed/corrected Theorem3 distinction.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
No unrestricted M06 completion or executable numeric-refinement claim. Earlier
source qualifications, source ledgers, and M05 acceptance are unchanged.
