# M06 fiber-rate lint repair — 2026-09-25

## Source and preserved failure

Parent documentation checkpoint: e27fee69332f1b55a08f99e68defdd7b5823074e.
Original Lean source: 4b4395714c62ac8fca0974f1254b7f86c832cd38.
Repair commit: c984277c2238e4dd1249ff3ace6fc5444175858a.
Work branch: rebel/m06-fiber-lint-repair-20260925.

The previous targeted run36084113146/job107912150501 failed AFTER all131 M06
targets compiled. The supplemental unusedArguments linter found one unused
argument, `[NeZero t]`, in
GameTheory.ReBeL.Examples.HiddenTypes.freshChainControl_parent_fiber_zero.

Correction after reading the full log and exact audit script: the transitive
axiom audit DID run before lint and passed1491 declarations. The original
version of this note incorrectly said it had not been reached. The exact log
marker is `EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1491`. The later lint failure
remains a failure of that source checkpoint, not a pass of the complete gate.

The diagnostic artifact10842823775 was downloaded through the GitHub plugin.
Its recorded ZIP SHA256 is
86ed32cf8447708ad5f0e27655b1a4872710c3f4f87e8f95c47a9bf70a139c16.
The source snapshot artifact10843311802 was downloaded through the same plugin;
its ZIP SHA256 was independently verified as
ed8f79bbc8919bce563eff9e3786fc1616d125573eea311fe2cbcbb3dda15e93.
It identifies the exact4b439571 source. Artifact inspection is not compilation.

## Focused repair

Remove only `[NeZero t]` from freshChainControl_parent_fiber_zero.
The finite index n:Fin t already supplies the indexing needed by this theorem;
the proof body does not require an additional typeclass hypothesis.
The new blob is b452aa3707f7ed9b85a5b18b7319473c06e55663. All theorem bodies,
other signatures and consumers were unchanged in the repair. No nolint
attribute, custom axiom, placeholder or weakened workflow was introduced.

## Validation and coverage

Repair c984277 passed M06 run36093962253/job107942125914 including declared-target
compilation and the constructed exact-child validation step. Full CI
run36093962268/job107942126260 also passed. Inventory job107942125975 and source
snapshot job107942125862 passed. Independent ReBeL job107942125979 was still
running at the last check; inspect it rather than inferring its result.

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending;
the lint repair itself changes no mathematical coverage. The preceding STATUS
is retained in STATUS-before-fiber-lint-repair.md. The next supported-value
calibration slice is described in M06-value-calibration.md; it must be validated
at its own exact source SHA and must not be mistaken for completed native rates.
