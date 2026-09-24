# M06 reference transport: exact-source compiler loop

All remote source and CI access uses the GitHub plugin. Main is not modified.
Recovery parent8783159, reweight implementation44a98bb4, transport750d738d.

## Accepted exact reweight slice

44a98bb4395db046e1ed602d8dc8fcb8f80df00d is retained on
rebel/m06-reference-reweight-20260924. M06 run35970620266/job107539230730
SUCCEEDED, including all126 target builds and the supplemental lint/axiom gate.
Plugin-downloaded artifact10795259873 (8170-line log) has SHA256
71a557cc774d1f259e5b3c4c85d818a5008088a807ff5f820a5a859778fd563d,
matching the API. Log identifies source44a98bb4 and pinned Lean4.33.1.
It records all88 lint-pass/module-axiom-pass markers and:

    EXACT_LEAF_MODULE_AXIOM_PASS ...CFRDReferenceReweight: declarations=4
    EXACT_LEAF_MODULE_AXIOM_PASS ...Examples.CFRDReferenceReweight: declarations=32
    EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1327
    EXACT_LEAF_VALIDATION_PASS modules=88

No source error or warning appears. Full CI and independent ReBeL results
must be recorded separately; targeted success does not imply their completion.

## First transport compile and repair

750d738d10395ecfd0dcdb0c104aa9a7b51a25d0 FAILED target35971823287/
job107543069745. The plugin-downloaded diagnostic artifact10796393611
identifies one error: unused simp argument `if_pos rfl` in the hidden-flip
negative control at Examples/CFRDReferenceReweight.lean:133. Both new core
modules compiled. The repair removes exactly that redundant simp argument;
no statement, control, warning policy, heartbeat or axiom whitelist changes.
The skipped supplemental step at750 is not accepted validation evidence.
The repair commit must receive its own complete target/lint/axiom result.

## Independent arithmetic checks

Python Fraction checks enumerated35 four-point laws of denominator4,
1225 OLD/NEW law pairs and both public tags. All170100 supported value tests
passed for {-1,0,1} observables. There were1800 jointly supported query cases,
300 disappearing queries and350 OLD-absent queries. Costs lie in[0,2].
These checks are independent sanity checks, not Lean or CI acceptance.

The original four M06 parent obligations remain pending. See
M06-reference-transport.md for the generic envelope and its actual-chain
consumer, the distinction between transport and value drift, and remaining
useful rates and CarriedResolveStepBounds. Preserve all accepted M05 evidence.
