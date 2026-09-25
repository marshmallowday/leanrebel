# M06 native-gap compiler-loop repair

Work branch: `rebel/m06-native-gap-repair-20260925`.
Initial source: `0bfa5ce2d1b67f5d14790e82e75e3db986b21fbd`, preserved on
`rebel/m06-native-conditional-gap-20260925`. The repair changes proof bodies
only; all theorem statements and positive/adversarial controls remain intact.

## Observed exact-source failures

Target run `36128708985`, job `108050731655`, failed. Its compiler log shows
`GameTheory.Analysis.ReBeL.PBSNativeConditionalGap` compiled successfully.
The example module has two unsolved scalar goals at lines 82 and 84:
`(FinDist.pure (1 == 0)).prob true` was not simplified. The repair adds the
existing `FinDist.prob_pure_eq_ite` lemma to the two normalization calls;
it does not weaken the exact-Nash or mean-absolute-drift conclusions.

Independent ReBeL run `36128708957`, job `108050823347`, failed its static
Phase 2 architecture check before Lean ran. The observed failure was
`TRANSPORT_ANALYSIS_SOURCE: expected 0, got 1`. One new `change` tactic
accounted for it. The support proof now unfolds `TypeBeliefSlice.mixture`
by a named rewrite and uses the identical existing support-bind theorem.
The transport budget, audit script, and all expected counts stay unchanged.

The initial targeted artifact `10861530263` was downloaded through the GitHub
plugin and checked against ZIP SHA-256
`bb5393f6da44a7e822a32f829c0059cc59c95aff6555d980a36cd525a3e3a0a8`.
The static-failure artifact `10860254510` ZIP SHA-256 is
`5b4b47fb79ab7946985d985f029194c49fd405784dc740e2d29d4dda5d46ea44`.
The latter contains measurements; the failure reason above comes from the
actual job log, not an invented interpretation of its artifact.

Initial source artifact `10860039736` from the same ReBeL run's snapshot job
`108050823538` has ZIP SHA-256
`9ac3ef802a056064ced57593f474f4c1a83fcd4c95eddc24f7442b983e30c4c8` and
embedded tar SHA-256
`3f5e0b32d66518b84f07f7048bc364f51cac35dea5057b34fc7358943f48c631`.
The embedded commit matches 0bfa5ce2. All 83 Python tests and ledger/inventory
structure checks passed on this exact exported snapshot. Those checks are
not Lean compilation, lint, or an axiom audit of the repaired source.

## Parent gate resolved

Parent proof `5cf1369cf1e886650a90a4e027347dacf589d50b` full CI
`36125907627`, job `108041951383`, now reports completed SUCCESS for build,
reuse signatures, Phase 1/2/3 architecture, full-library lint and cleanliness.
Parent independent ReBeL `36125907531` / job `108041928085` was still running
at the latest inspection. Parent results never substitute for this repair's
own exact-SHA validation. Preserve the predecessor query-gap evidence files.

## Acceptance still pending

Read this branch's current head and exact-SHA Actions. Both new modules are
still imported by the umbrella and named in M06 targets. The unchanged global
ReBeL audit is their transitive-axiom and configured-lint consumer. The unchanged
100-module exact-leaf audit does not include these two new modules.
No full acceptance, successful new-module axiom audit or M06 completion is
claimed here. Remaining semantic work is listed in M06-native-conditional-gap.md.
