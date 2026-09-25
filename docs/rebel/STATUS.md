# ReBeL status — M06 in progress; M05 accepted

## Current scalar-stability continuation

Work branch: `rebel/m06-scalar-stability-20260925`.
Starting checkpoint: `2e1de273b9164743decdd8a283b3249f34bf5600`.
Read `M06-scalar-stability-resume.md`, `M06-scalar-stability-validation.md`
and `M06-scalar-stability-coverage.json`. The preceding STATUS is preserved
byte-for-byte in `STATUS-before-scalar-stability.md`.

The previous uncommitted candidate is now being tested as a source checkpoint.
PBSValueStability and its example compare two approximate Nash values on the
SAME joint PBS and instantiate the premises with actual information-set CFR,
positive-budget child solves, and allocated noisy depth-limited solves.
The negative control has equal scalar values at exact Nash but every valid
outcome coupling costs one half. Do not infer conditional vector stability
or a native iteration rate from scalar value stability.

The implementation awaits its own exact-SHA Lean compiler, lint and axiom
results. Local structural checks and all 82 Python tests passed. Two new
imports/targets/audit modules were added; all old targets and checks remain.
No theorem, workflow, dependency pin, test or axiom allowance was weakened.
Main and predecessor refs are unchanged.

## Predecessor independent gate resolved

Source `4f73dcefb0d9f0e0b24b5a390a754e6debbdd0e5` now has a SUCCESS result for
independent ReBeL run36103763078/job107971751432, completed
2026-09-25T07:18:47Z. This result was re-read via the GitHub plugin. The old
value-coupling target/full-CI evidence remains in its validation documents.
Do not reuse predecessor success as compilation evidence for the new source.

## Remaining obligations

SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 stay pending.
M06 is NOT complete. Native/late-training conditional value rates, first-exit
rates, later independent carried-PBS re-solving and CarriedResolveStepBounds
remain. Preserve the actual private seed/history law, off-path support,
model-versus-actual beliefs, finite-T error at zero oracle error, and the
printed/corrected Theorem3 distinction. The scoped companion records a project
lemma without promoting its canonical parents.
