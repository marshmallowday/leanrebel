# First-hit depth-sampling validation record

## Initial integrated candidate b180c2ba

Source: b180c2bacf91d32c95ab5b8eaf767c4f768c303d.
M06 run35937714298/job107438753355 failed at the last monotonicity step of
sequenceFirstHitProbability_le_eventMass. The unqualified add_le_add_left
resolved to a different argument orientation. All earlier declarations in the
same file, including the first-hit kernel-discrepancy induction, emitted no
diagnostics, but the module was not accepted because its build failed.
The source-side first-hit consumer and examples were consequently unvalidated.

Full ReBeL run35937714282/job107438411510 separately found two lines of width101.
Inventory run35937714244/job107438410873 found that the umbrella edit had
mistakenly changed the accepted Examples.ValueKink import to ValueKink.
The tests correctly rejected the loss of the explicit existing test surface.

Repair160569f68d1c9d206a5f7002e2082a0679e5a152 wraps both long lines, restores
exactly the Examples.ValueKink import, and proves the monotonicity step by
linear arithmetic from the same induction hypothesis. No statement, semantic
premise, validation condition, or original test coverage was weakened.

Failed target artifact10783658213 has GitHub-reported SHA256:
347d19bfb95242a93d400d948dbbaddd0ca066db516459cc2fd15bbabc7161b2.

## Repaired core160569f6

M06 run35938303113/job107440275573 compiled both FinDistFirstHit and
PBSCarriedDepthFirstHit successfully. The full source candidate still FAILED:
Examples/PBSCarriedDepthSampling.lean line29 exceeded200000 heartbeats during
its initial change tactic. Supplemental lint and axiom acceptance did not run.
No whole-slice acceptance is inferred from the two compiled modules.

Inventory35938302894/job107440274766 passed. Full ReBeL35938303006/
job107440275185 passed line-width checking, then rejected the same authored
change tactic under the frozen TRANSPORT_ANALYSIS_SOURCE=0 condition.

The following repair explicitly unfolds only depthControlState and
 depthControlBelief with dsimp before applying the existing support-map API.
No heartbeat limit or audit condition is relaxed. Two further controls construct
an actual unsupported hidden-type root with the same public trace and check
that its first-hit probability is one. Existing controls are retained.

Failed target artifact10784440888 has GitHub-reported SHA256:
6146f57b2c794d90fe5ef89caa6754d1aa8355f33f4bf962c46be44f652a62a9.
Failed structural artifact10783746670 has GitHub-reported SHA256:
13ac985223f285e6efe2900514bdbe27d314e9ae900d641d4be3d41192ec1df7.

All artifacts above record intermediate failures, not acceptance evidence.
The next exact-SHA build, normal/slow lint and transitive axiom audit must pass.
