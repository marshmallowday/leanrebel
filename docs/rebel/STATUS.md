# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-recursive-envelope-20260923`.
This documentation-only checkpoint directly follows the tested source commit
`dd66907138cf052a52435d8c31dcb3ecaea5703e`. Lean modules, target lists, audit
scripts, dependency pins and original source-coverage rows are unchanged.
Inspect the current HEAD's CI before integration; do not redo the passed
fresh-child slice. Main remains `6a6cbdaa8b4fb43b35a9d3e555a7c1a614130098`.

## Confirmed source validation

For dd66907138cf052a52435d8c31dcb3ecaea5703e:

- M06 targeted run 35828662651, job 107075968088: SUCCESS. Declared target
  build: 3425 jobs. Supplemental build: 3417 jobs. All 61 named modules
  passed normal/slow lint; 731 declaration-level transitive axiom sets were
  checked against propext, Classical.choice and Quot.sound. The three new
  modules account for 43 declarations (14 + 9 + 20).
- The plugin-downloaded artifact 10735963541 was inspected, including every
  logged axiom set and each new module's lint pass. Exact hashes and extracted
  summary are in M06-fresh-envelope-validation.md and M06-fresh-envelope-compiler.txt.
- Source inventory 35828662685, job 107075968266: SUCCESS.
- ReBeL 35828662704, job 107075968786: widths, static architecture,
  ledger/inventory, adversarial controls and rational runtime passed; its
  repository-wide compiler/lint/axiom step was still running at last check.
- Full CI 35828662759, job 107075968744: still running at last check.
  A documentation push may supersede these two in-progress runs. Do not count
  a cancelled or unfinished run as success; inspect this HEAD's own runs.

## Completed fresh-child slice

CFRDFreshValueDrift computes the positive maximum of new-minus-old conditional
MODEL values on live opponent-reference queries. CFRDFreshResolve constructs
new finite information-set children with a separate positive tolerance,
including counterfactual completion. Its fresh finite-plan draw realizes the
NEW averaged policy at every legal history, without model-support assumptions.

cfrDFreshInformationResolver_envelope discharges reference-prefix preservation
and child optimality internally. cfrDFreshInformation_security connects this
constructed envelope to the actual noisy sampled-value parent. Its allowance
retains prediction error, finite outer T, old and new child loss, and computed
drift. No caller supplies final safety, root regret, an envelope or child Nash.
The eight compiled controls and the exact semantic boundary are recorded in
M06-fresh-envelope.md. The original milestone rows remain pending.

## Earlier checkpoints — do not repeat completed repairs

b037b0c700b4eb549c4f8a7e78281a82fc1f238f failed targeted run 35826357295/job
107068841120 at one finite-maximum type-inference expression. ReBeL run
35826357312/job 107069006262 also rejected one authored change tactic.
Both were repaired in dd669071 without weakening any audit or hiding a module.

The fully checked predecessor e630e689df13eddedafbe3c88c2bf12561b8d1a6 remains
on rebel/m06-sampled-values-20260923. Its successful runs are full CI
35820699262/job 107051920490, ReBeL 35820699300/job 107051833911, and inventory
35820699260/job 107051708579. Its earlier evidence is preserved separately.

## Remaining source obligations

The new theorem is ONE fresh public-cut solve with computed value drift, not
the paper's unrestricted recursive algorithm. Fresh plan draws of an average
are not actual CFR-iterate draws. The resolver reconstructs all child entries
from the retained parent model; it does not independently use a later carried
posterior as the next root game. Prove the appropriate source-dependent drift
bound and connect later genuine carried-PBS solves without assuming the desired
CarriedResolveStepBounds or posterior equality. Preserve finite-T and nonzero
errors. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
No complete-M06, unrestricted Theorem 3, or executable numeric-refinement claim.
