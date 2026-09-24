# M06 reference reweighting: recovery checkpoint

Base: 66a8b9ecd01a5dbbf120ce1b56479ccec6c1dad7.
Work branch: rebel/m06-reference-reweight-20260924.
All remote access and commits use the GitHub plugin; main is not a write target.

## Accepted predecessor

On 2026-09-24, the GitHub plugin returned SUCCESS for independent ReBeL
run 35964794487, compiler/lint/axiom job 107520978527, source
46126f37dbaa83a2f064f511e9617843d0ce308a. This includes all-ReBeL compile/lint,
transitive axiom checks, rational runtime and independent pure-response checks,
and final tracked-file cleanliness. The old pending note is superseded.
The targeted and full-CI evidence remains in M06-fresh-chain-validation.md.

## Next dependency-closed slice

Recover the previously unapplied CFRDReferenceReweight candidate and its
unequal-law, support-direction, hidden-conditional and actual-chain controls.
Validate with the pinned compiler and existing target/lint/axiom consumers.
Information-local OLD-from-NEW density is an explicit structural premise,
not a consequence of arbitrary fresh solves or scalar Nash accuracy.
Inspect nonzero transport/support defects after validating this special case.

No new Lean candidate is accepted by this recording commit. Keep every M05
result, existing control, dependency pin, warning gate and allowed axiom intact.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
