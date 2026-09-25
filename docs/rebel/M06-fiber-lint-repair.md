# M06 fiber-rate lint repair — 2026-09-25

## Source and preserved failure

Parent documentation checkpoint: e27fee69332f1b55a08f99e68defdd7b5823074e.
Original Lean source: 4b4395714c62ac8fca0974f1254b7f86c832cd38.
Work branch: rebel/m06-fiber-lint-repair-20260925.

The previous targeted run36084113146/job107912150501 failed AFTER all131 M06
targets compiled. The supplemental unusedArguments linter found one unused
argument, `[NeZero t]`, in
GameTheory.ReBeL.Examples.HiddenTypes.freshChainControl_parent_fiber_zero.
The transitive axiom audit was not reached. This is a lint failure, not a
remaining Lean proof goal. Preserve the original failure and do not suppress it.

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
The new blob is b452aa3707f7ed9b85a5b18b7319473c06e55663, checked against the
one-line edit of the downloaded exact source. All theorem bodies, tests,
other signatures and consumer statements are unchanged. No nolint attribute,
custom axiom, placeholder or weakened workflow is introduced.

## Validation and coverage

The repair is a source checkpoint, not an acceptance claim. Inspect its own
M06 targeted, full CI, independent ReBeL and inventory/snapshot runs. Record
the exact source SHA and actual lint/transitive-axiom output before acceptance.
The existing target list and supplemental audit list are unchanged.

Owning coverage rows SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 remain pending; this repair changes no mathematical coverage.
The preceding STATUS is retained in STATUS-before-fiber-lint-repair.md.
Continue the source-level rate and later carried-PBS obligations described in
M06-fiber-rates-validation.md; do not promote a conditional rate to a theorem
about the native solver or conflate model beliefs with actual posteriors.
