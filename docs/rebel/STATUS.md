# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-recursive-envelope-20260923`.
This branch follows the fully checked predecessor
`e630e689df13eddedafbe3c88c2bf12561b8d1a6` on the preserved sampled-values branch.
No accepted predecessor proof needs to be redone. Main remains unchanged.

## Current implementation

CFRDFreshValueDrift computes the positive maximum of new-minus-old conditional
MODEL values on live opponent-reference queries. CFRDFreshResolve constructs
new finite information-set children with a separate positive tolerance,
including counterfactual completion. Its fresh finite-plan draw realizes the
NEW averaged policy at every legal history, without model-support assumptions.

cfrDFreshInformationResolver_envelope discharges reference-prefix preservation
and child optimality internally. cfrDFreshInformation_security connects this
constructed envelope to the actual noisy sampled-value parent. The allowance
retains prediction error, finite outer T, old and new child loss, and computed
drift. No caller supplies final safety, root regret, an envelope or child Nash.

Eight theorem-level controls include a live none-posterior interface record,
a factually absent reference query, constructed envelope, equal-policy and
zero-fuel drift, no-query stopping, distinct positive old/new losses with
nonzero prediction bias, and a finite-law mean-versus-uniform negative guard.

## Verification at checkpoint creation

All three new modules compiled with the pinned Lean 4.33.1 direct compiler,
using only previously plugin-downloaded offline artifacts. Changed project
dependencies were rebuilt from e630 source; dependency manifest matches the
workbench. A direct transitive axiom audit passed for 43 declarations, with
only propext, Classical.choice and Quot.sound. This offline feedback does NOT
replace the exact-commit Actions gates. Inspect this HEAD's own targeted,
ReBeL, inventory and full-CI runs before integration acceptance.

Initial checkpoint b037b0c700b4eb549c4f8a7e78281a82fc1f238f failed targeted run
35826357295/job 107068841120 at a Finset maximum type-inference expression.
It also failed static architecture in ReBeL 35826357312/job 107069006262
because the new proof used one forbidden change tactic. Both proof expressions
are repaired; no lint rule, architecture expectation or trust gate was weakened.

The predecessor e630 has successful full CI 35820699262/job 107051920490,
ReBeL 35820699300/job 107051833911 and inventory 35820699260/job 107051708579.
Earlier sampled-parent validation remains in M06-sampled-values-validation.md.

## Remaining source obligations

The new theorem is ONE fresh public-cut solve with computed value drift, not
the paper's unrestricted recursive algorithm. Fresh plan draws of an average
are not actual CFR-iterate draws. The resolver reconstructs all child entries
from the retained parent model; it does not independently use a later carried
posterior as the next root game. Prove the appropriate source-dependent drift
bound and connect later genuine carried-PBS solves without assuming the desired
CarriedResolveStepBounds or posterior equality. Preserve finite-T and nonzero
errors. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
See M06-fresh-envelope.md for declarations, coverage mapping and semantic review.
