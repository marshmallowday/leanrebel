# M06 weighted transport — exact-source validation checkpoint

## Immutable proof source and resume branch

Proof source: fd3770c4c4123cefec9cc5456f99b18f5b52c697, preserved on
rebel/m06-weighted-transport-20260924. Documentation and restart branch:
rebel/m06-weighted-transport-reviewed-20260924. The recording commit changes
three documentation files only. The proof ref is not advanced by these notes,
so its full CI and independent ReBeL run are not cancelled by record updates.

## Observed target-SHA result at this checkpoint

Target run35984130871/job107582693551 compiled ALL 128 declared M06 targets
successfully at 2026-09-24T10:00:40Z, including the new weighted comparison,
constructed noisy-parent/fresh-child root consumer and canonical hostile tests.
Its supplemental lint and public/private/generated transitive axiom audit was
still IN PROGRESS at recording. Do not treat compilation alone as completed
supplemental acceptance. Full CI35984130854/job107582847450 and independent
ReBeL35984130849/job107582791762 were also IN PROGRESS.
Inventory35984130885/job107582693947 and exact source snapshot
35984130849/job107582792124 succeeded. Recheck the exact source runs before
starting further implementation. No remaining workflow is claimed successful.

## Compiler loop and source preservation

Recovery checkpoint: 1dd9bcf8a334081eb4fa8dd4d51d7e23cd070d75.
Initial weighted source: 72faa00ec9c41c4f69d153a7c3d016b9fc4c19fe (FAILED target).
Repair and constructed consumer: fd3770c4c4123cefec9cc5456f99b18f5b52c697.
M06-weighted-transport-compiler-loop.md records the three concrete compiler
errors and repairs. No heartbeat, warning, source statement or axiom gate was
weakened. The failed source and its artifact remain identified in the history.

The plugin compare from d7ab37e1 to fd3770c4 reports exactly three commits,
no divergence, two new Lean modules (485 and 159 lines), the three append-only
registration edits, and documentation. The old proof bodies, workflows and
pins are untouched. Local source comparison confirms preservation of every
126-to-128 target and 88-to-90 audit entry and unchanged auditor implementation.
Local inventory/ledger checks and exact Fraction experiments are supplementary,
not Lean compiler or transitive axiom evidence.

## Recovered predecessor: do not redo it

Previous conversational restart 66a8b9ec was stale. Remote inspection found
44a98bb4395db046e1ed602d8dc8fcb8f80df00d and the already committed bounded
reference-transport successor d7ab37e1e36b0c89dde76dd03bce5505e99163b0.
The old unapplied reference-reweight ZIP must not be reapplied.

For d7ab37e1, preserved on rebel/m06-reference-transport-20260924, ALL were
completed SUCCESS: M06target35972597733/job107545544376 at 08:12:32Z,
fullCI35972597726/job107545723011 at 08:15:34Z, independentReBeL35972597771/
job107545726694 at 08:38:46Z, inventory35972597738/job107545544094 and exact
source snapshot35972597771/job107545726266 (all 2026-09-24).
The plugin-downloaded source artifact10796652341 identifies d7ab37e1 and has
verified SHA256 afccf13adc5008ba48944c6ff7b82e4ccd168cf8dfd88c0a263de0b5ba999a8b.

Fresh-chain source46126f37 also has independentReBeL35964794487/
job107520978527 SUCCESS, including final tracked-file cleanliness. Its prior
pending note is superseded. Preserve all earlier recursion/composition/budget
records and all M05 acceptance. All remote access and checkpoints use the
GitHub plugin; no local Git operation is used and main is not a write target.

## Acceptance boundary

See M06-weighted-transport.md for the exact statement and explicit assumptions.
The weighting improvement is a fixed-cut security theorem, not a proof of
independent later carried-PBS re-solving or a useful vanishing error rate.
All four M06 parent rows remain pending. Keep finite T, positive prediction
error, model/actual posterior distinctions and the printed/corrected source
formula separate.
