# M06 scalar-tail architecture repair — 2026-09-25

## Preserve the rejected source

Parent source: 0382af933e2520c3eb152fe98ae9b45f73c4601d.
The target run36112787339/job107999829165 completed its compilation step
successfully; supplemental lint and axiom validation were still running when
this checkpoint was prepared. This is compilation evidence, not a full pass.

The independent ReBeL run36112787359/job107999916653 failed before Lean setup.
Its actual job log was read through the GitHub plugin. The unchanged Phase2
architecture gate reported TRANSPORT_ANALYSIS_SOURCE: expected0, got2.
The source-level policy counts the two `change` tactics introduced by the
previous example repair. The earlier claim that gates were not weakened is
still true, but the repair did NOT yet satisfy those unchanged gates.

Its failure artifact10853932057 has reported SHA256
08bcaaae277d2988510a5f8e3d315ecf18458b8f6a367a2b91627b55b79e7cbe.
The exact source artifact10853991273 was downloaded via the GitHub plugin;
ZIP SHA25629fd4af429b57573a058d8d65e7ac5dafcbf9bf6767f4d813cfde2d0094e2543
and embedded TAR SHA256c2094432234b2a378c7d3d4f36911c1309c2493f1553b5d67b0585d771980082
were independently checked against the artifact and embedded metadata. All
seven source/integration/test files matched the prepared bytes exactly.

## Minimal repair

Delete only the two `change` tactics and their displayed target lines in
profile_isNash and the local approximate-Nash proof in value_comparison.
The subsequent explicit proof terms already have the required types by
canonical definitional reduction. No theorem statement, semantic definition,
build target, linter, architecture expectation, workflow, dependency pin or
axiom allowance is changed. The repaired example blob is
637566705f6e6a31369aba9539721c11c40b441c.

A new branch rebel/m06-scalar-tail-repair-20260925 preserves both predecessor
refs and their unfinished targeted audit runs. This repair is not accepted
until its own exact-SHA compiler, supplemental lint/axioms, architecture and
full-CI results are inspected. The canonical M06 parents remain pending.

The local source-token check now finds zero new transport tokens in both new
Lean modules and no line over100 UTF16 code units. The83 Python tests still
pass. These are static/numerical checks, not substitutes for Lean validation.

## Continuation

Read this repair branch's exact-SHA checks. Record the main7 theorem audit,
all example/private/generated declaration audits, and wider CI outcomes in
M06-scalar-tail-validation.md or a linked final review. Keep M06 incomplete:
common-PBS scalar output tails do not establish native-iterate conditional
rates, changed-belief transport or CarriedResolveStepBounds.
