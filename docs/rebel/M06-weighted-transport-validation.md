# M06 weighted transport — accepted exact-source slice and restart

## Immutable proof source and documentation-only resume branch

Proof source: fd3770c4c4123cefec9cc5456f99b18f5b52c697, preserved on
rebel/m06-weighted-transport-20260924. Documentation/restart branch:
rebel/m06-weighted-transport-reviewed-20260924. Relative to the proof source,
the final recording tree changes FIVE DOCUMENTATION FILES ONLY, including the
reproducible supplementary finite-law check. No Lean source, target list,
audit script, workflow or dependency pin is changed by these recording commits.
The code ref remains untouched so its independent ReBeL run is not cancelled.

## Target-SHA compilation, lint and transitive axiom acceptance

M06 run35984130871/job107582693551: SUCCESS, completed
2026-09-24T10:07:53Z. All128 declared targets compiled at10:00:40Z;
the supplemental proof-slice lint and transitive axiom gate completed at10:07:48Z.
No skipped supplemental gate is counted. The GitHub-plugin-downloaded artifact
10802160810 is m06-targeted-fd3770c4c4123cefec9cc5456f99b18f5b52c697, with
verified archive SHA256:

    1abd8b736f2e9398bb521550dd0a98832f9572c817e277ebcaa993dfa7321496

The complete8447-line m06-targeted.log identifies the exact proof SHA and
Lean4.33.1, compiler commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Its actual acceptance markers are:

    EXACT_LEAF_MODULE_AXIOM_PASS ...CFRDWeightedTransport: declarations=16
    EXACT_LEAF_MODULE_AXIOM_PASS ...Examples.CFRDWeightedTransport: declarations=27
    EXACT_LEAF_AXIOM_AUDIT_PASS declarations=1396
    EXACT_LEAF_VALIDATION_PASS modules=90

Every one of the90 registered modules has BOTH a lint-pass and module-axiom-pass
marker. The root constructed-security theorem, uniform comparison, positive-bias
canonical control and negative independent-seed/query control have explicit
successful audit entries. The auditor includes public, private and generated
declarations and their transitive dependencies. Only propext, Classical.choice
and Quot.sound are allowed. No source error or warning appears in this log.
The pinned Batteries lint configuration and auditor implementation are unchanged;
no separately executed defLemma command or independent kernel checker is claimed.

## Whole-library CI and independent ReBeL status

Full CI35984130854/job107582847450: SUCCESS, completed
2026-09-24T10:12:20Z. The complete library build, exact source/toolchain report,
inventory and compiler-resolved reuse signatures, architecture Phases1/2/3
and reachability probes, whole-library lint and tracked-file cleanliness passed.
Only Windows-specific toolchain exposure was skipped on the Ubuntu runner.
Inventory35984130885/job107582693947 and exact source snapshot
35984130849/job107582792124 also succeeded at this same proof source.

Independent ReBeL35984130849/job107582791762 was IN PROGRESS at recording.
Its line-width, static architecture, ledger/inventory/adversarial fixtures and
rational Lean solver with independently checked pure responses had succeeded.
The all-ReBeL compile/lint/transitive-axiom step and final tracked-file cleanliness
still need the final result. This is distinct from the completed supplemental
audit and full CI above. Recheck this preserved exact-source run first on resume.
Do not infer its success from other workflows or cancel it with record updates.

## Compiler loop and source preservation

Recovery checkpoint:1dd9bcf8a334081eb4fa8dd4d51d7e23cd070d75.
Initial weighted source:72faa00ec9c41c4f69d153a7c3d016b9fc4c19fe, FAILED target.
Repair and constructed consumer:fd3770c4c4123cefec9cc5456f99b18f5b52c697.
Interim compile-only documentation checkpoint:466f82c59e6565d50ab7d89115d72158c377a85e.
M06-weighted-transport-compiler-loop.md records the concrete errors and repair.
No statement, heartbeat, warning policy, positive/negative control or axiom gate
was weakened. The failed source and verified failure artifact remain identified.

The plugin comparison d7ab37e1..fd3770c4 reports three commits, no divergence,
two new Lean modules (485/159 lines), three append-only registrations, and docs.
All126 old M06 targets and88 old supplemental modules are retained, with two
appended to each. Existing proof bodies, workflows and pins are untouched.
Local inventory/ledger checks are supplementary, not Lean acceptance.
The exact-Fraction experiment and portable reproduction are preserved separately
in M06-weighted-transport-finite-check.md, with their non-Lean scope explicit.

## Recovered predecessor: do not redo it

The previous conversational restart66a8b9ec was stale. Remote inspection found
44a98bb4395db046e1ed602d8dc8fcb8f80df00d and already committed bounded
reference-transport successor d7ab37e1e36b0c89dde76dd03bce5505e99163b0.
Do not reapply the old unapplied reference-reweight ZIP.

For d7ab37e1, preserved on rebel/m06-reference-transport-20260924, ALL were
completed SUCCESS: M06target35972597733/job107545544376 at08:12:32Z,
fullCI35972597726/job107545723011 at08:15:34Z, independentReBeL35972597771/
job107545726694 at08:38:46Z, inventory35972597738/job107545544094 and source
snapshot35972597771/job107545726266 (all2026-09-24).
Source artifact10796652341 identifies d7ab37e1 and its locally verified SHA256 is
 afccf13adc5008ba48944c6ff7b82e4ccd168cf8dfd88c0a263de0b5ba999a8b.
Fresh-chain source46126f37 also has independentReBeL35964794487/
job107520978527 SUCCESS, including final tracked-file cleanliness.

All remote access and checkpoints use the GitHub plugin. No local Git operation
is used; main is not a write target. Preserve all prior accepted M05 evidence.

## Original acceptance boundary

The weighted theorem and uniform comparison form a dependency-closed fixed-cut
slice. Later carried-PBS independent re-solving, useful fresh drift/transport
and first-exit rates, and CarriedResolveStepBounds remain original obligations.
A weighted expectation alone is not a vanishing error rate. All four M06 parent
rows remain pending. Preserve finite T, positive numerical error, the model/actual
posterior distinction and the printed/corrected Theorem3 distinction.
