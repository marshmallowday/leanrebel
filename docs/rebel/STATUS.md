# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-nested-depth-review-20260924` for the
latest review checkpoint. Its Lean source and validation configuration are
identical to f9d4def18411b43fc14c508b079fadb0378bd178 on the preserved source
branch `rebel/m06-nested-depth-20260924`. This review changes documentation only,
so recording completed work does not cancel the source branch's running checks.
The separate budget-integration branch remains at704e96ff. Main remains
6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098 and is not a write target.
Inspect exact-SHA runs before resuming; never promote a pending result to success.

## Completed predecessor validation

First-exit source487aaedd passed M06 target35941683756/job107450728931,
ReBeL35941683758/job107450798403, full CI35941683736/job107450816152 and
inventory35941683774. The earlier support recovery01245b31 is separately accepted.
Do not redo their support repairs, first-exit construction or probability controls.

Finite-budget source704e96ff6ed5b73b279191ea2d01629cc331e8d8 now has completed
M06 target35946360278/job107465069923 successfully, INCLUDING its supplemental
lint/transitive-axiom step. Full CI35946360214/job107465224924 also succeeded,
including all architecture phases, full-library lint and tracked-file cleanliness.
Inventory35946360322/job107465069843 succeeded. The independent ReBeL
35946360239/job107465227645 was still in its complete proof audit at inspection.
This supersedes older snapshots that marked the budget supplemental audit pending.
The fixed budget source is preserved on rebel/m06-depth-budget-integration-20260924.

## New nested source: declared-target compilation passed

Exact proof source: f9d4def18411b43fc14c508b079fadb0378bd178.
M06 run35947018152/job107467137173 has completed declared-target compilation
successfully, including CFRDDepthChild, CFRDNestedDepthDriver and their controls.
Its supplemental lint/transitive-axiom validation was still in progress at the
latest inspection. Compilation success alone is not final audit acceptance.

ReBeL35947018175/job107467137458 passed width, static architecture, ledger/
inventory/adversarial fixtures and executed rational solver checks; its complete
compiler/lint/transitive-axiom step remained in progress. Source snapshot
job107467137602 and inventory35947018259/job107467137512 succeeded.
Full CI35947018228/job107467419037 was still in progress. Inspect final outcomes
for these exact runs, not the failing22b15778 or passing704e96ff predecessor.
See M06-nested-depth-validation.md for the diagnostics and acceptance boundary.

## Implemented mathematical slice

The existing previously unwired finite-budget modules were recovered from
2c9bfd52, integrated at e9d651b2 and repaired at704e96ff without altering their
accuracy contract. They compute a positive finite count AFTER subtracting fixed
numerical and child error; the positive joint-law mass floor supplies conditional
accuracy. Fixed nonzero prediction error cannot be eliminated by raising T.

CFRDDepthChild now installs this actual depth solver at every current factual
joint PBS, preserves complete baseline and unilateral laws under public splicing,
and derives the all-query child contract through zero-own-reach completion.
CFRDNestedDepthDriver puts this child in each actual noisy parent update and
derives finite-T full-game Nash and private carried security. Outer and inner
prediction errors remain distinct. A bounded strictly positive child predictor
is constructed; no child equilibrium or local-optimality certificate is input.

Controls retain outer bias1/8, positive requested child loss1/4, randomized
replacement, impossible/zero-fuel fallbacks and nonzero finite parent T. The
2+1+0 split contains real parent and child decisions; the1+1+1 split has a chance
parent cut followed by real child and suffix decisions. Neither invents a third
decision in this protocol. All new modules and every old entry remain in the
analytic root, M06 target list and supplemental lint/transitive-axiom audit.

## Remaining original obligations

This constructs one additional nesting step, not arbitrary-depth structural
recursion. The deepest backend still uses full-root CFR. Derive source-level
model-value drift and useful first-exit/support-defect estimates and discharge
CarriedResolveStepBounds. A private carried continuation is not independent
repeated re-solving. No model/actual posterior identity, learned-network accuracy
or executable numeric-refinement theorem is claimed. Retain finite T, positive
errors, zero-reach completion and the printed/corrected Theorem3 distinction.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending;
source qualifications, ledgers and M05 acceptance are unchanged.
