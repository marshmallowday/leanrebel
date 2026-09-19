# M06 live continuation and conditional Nash checkpoint

Parent: dc3d4a2cdac5dbb6969de8db932fcddfdb16c065, on rebel/m06-recovery.
Its target run 35467132599 and inventory run 35467132606 passed. Its full
repository run 35467132586 exposed an auto-generated local-instance name
collision between CFRDExecution and an existing LocalRegret example. All new
example instances now have distinct explicit names. No theorem or test is
removed. The complete analytic ReBeL umbrella compiles after this repair.

## Actual live cut, not a full-search substitute

Examples/CFRDLiveControl searches the first simultaneous strategic round of
the established HiddenTypes game, then stops with the second round still
live (cut=2, remaining=1). It constructs independent fair continuation laws
and computes exact information-state oracle values. Canonical one-step
execution proves that EVERY legal future unilateral deviation has zero gain
at EVERY live hidden history, even off path. This derives the conditional
leaf-optimality contract rather than assuming it. The genuine coupled solver
therefore satisfies its full-game finite-time Nash bound at every positive T.
The proof does not replace hidden histories by actions in the policy interface.

## Canonical PBS Nash to local continuation optimality

PBSLeafOptimality proves that a Nash equilibrium of a canonical TypeBeliefSlice
attains the best-response infostate value at every supported own type. The
proof uses M05's one legal remembered-type splice and equality of expectations
under pointwise bounds. It derives the local inequality for every complete
behavioral deviation. Zero-mass types remain explicitly excluded: on-path
Nash alone does not certify counterfactual completions. This theorem is an
adapter, not an assertion that the entire recursive oracle is constructed.

## Validation and next boundary

Both new modules and all sixteen targeted roots compile under the restored
pinned Lean 4.33.1 with warnings as errors. The complete analytic umbrella
also compiles; inventory structure passes. Exact-commit full/slow lint and
transitive axiom gates remain mandatory. No acceptance is inferred from
individual target compilation alone.

Continue with general recursive continuation replacement for actual test-time
re-solving, its explicit accumulated bound, and its source mapping. Current
carried-state safety preserves one selected complete continuation; it does
not justify arbitrary replacements. M06 is still in progress and main is
unchanged. All repository mutations use the GitHub connector without force.
