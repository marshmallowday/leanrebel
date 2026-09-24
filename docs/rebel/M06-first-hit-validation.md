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

The repair wraps both long lines, restores exactly the Examples.ValueKink import,
and proves the monotonicity step by linear arithmetic from the same induction
hypothesis. No theorem statement or semantic premise changes. No tests or
validation gates are removed, suppressed, or relaxed. The correction must pass
its own exact-source compiler, normal/slow lint, and transitive axiom checks.

The failed target artifact10783658213 has GitHub-reported SHA256:
347d19bfb95242a93d400d948dbbaddd0ca066db516459cc2fd15bbabc7161b2.
This artifact records a failure and is not acceptance evidence.
