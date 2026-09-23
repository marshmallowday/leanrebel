# ReBeL status — M06 in progress; M05 accepted

## Resume point

Use the actual remote HEAD of `rebel/m06-recursive-envelope-20260923`.
This branch starts from `e630e689df13eddedafbe3c88c2bf12561b8d1a6` on the preserved
`rebel/m06-sampled-values-20260923` branch. Do not redo its sampled-parent proofs.
All GitHub reads and writes use the GitHub connector; no local Git is needed.

## Confirmed predecessor validation

The exact predecessor `e630e689df13eddedafbe3c88c2bf12561b8d1a6` now has:

- Full CI `35820699262`, job `107051920490`: SUCCESS, including full build,
  library lint, Phase 1/2/3 architecture/reachability and tracked cleanliness.
- ReBeL checks `35820699300`, job `107051833911`: SUCCESS, including the complete
  ReBeL compiler/lint/transitive-axiom step, runtime controls and cleanliness.
- Source inventory `35820699260`, job `107051708579`: SUCCESS.

Its Lean source is identical to `b3d63c722d94a5aaee60403025a5a71d4b650a4b`, whose
M06 targeted run `35820010308`, job `107049652032`, also succeeded. Earlier
validation and immutable diagnostics remain in M06-sampled-values-validation.md.

## Current slice — compiler acceptance pending

`CFRDFreshValueDrift` defines a finite positive maximum of the new-minus-old
conditional MODEL values over live counterfactual reference queries. It proves
same-continuation and zero-remaining controls, then derives the opponent envelope
from a new family's local optimality and preserved reference prefix. The drift
is computed from the two actual families, not supplied as a safety certificate.

The next step is to instantiate both strategic premises with independently
recomputed finite information-set children and connect the existing global
security bound. Inspect this HEAD's M06 targeted workflow before extending it.
The new module is included in the public analytic root, declared target list,
and supplemental lint/transitive-axiom auditor. No new module is hidden from CI.

## Coverage and semantic boundaries

See M06-fresh-envelope.md for the supplemental declaration/coverage map.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
A computed value-drift term is not automatically bounded by the paper's numerical
oracle error or child regret. Independent Nash does not prove fixed-opponent
no-loss. The old negative controls and printed/corrected Theorem 3 distinction
remain unchanged. No complete-M06 or executable numeric-refinement claim.

Main remains the accepted M05 baseline; this work is not merged into main.
