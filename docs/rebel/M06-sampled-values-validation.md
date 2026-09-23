# Sampled-parent checkpoint: exact-source validation

## Source under test

Repository: `marshmallowday/leanrebel`.
Branch: `rebel/m06-sampled-values-20260923`.
Tested commit: `b3d63c722d94a5aaee60403025a5a71d4b650a4b`.
Tested tree: `64d2c0b5e414ef2313ac5ac3422d78298ef17469`.
Parent: `ce8c0f044f315f04fa6d9da83279f11df65b7785`.

This follow-up checkpoint changes documentation only. It does not alter the
compiled proof sources, the target/audit module lists or their checks. It is
not labelled as having its own CI pass merely because its source parent passed.

## Confirmed M06 proof and audit result

Workflow: **M06 targeted proof feedback**.
Run: `35820010308`, attempt 1.
Job: `107049652032` (`compile`).
Reported head SHA: `b3d63c722d94a5aaee60403025a5a71d4b650a4b`.
Conclusion: **success**, completed `2026-09-23T04:57:59Z`.

The read-only job result was inspected through the GitHub plugin. It reports:

| Gate | Result | Completion, UTC |
| --- | --- | --- |
| Compile the declared M06 targets | success | 04:54:47 |
| Validate the constructed exact child proof slice | success | 04:57:55 |
| Expose compiler diagnostics for read-only review | success | 04:57:55 |
| Upload diagnostic artifact | success | 04:57:56 |

The first gate runs `lake build` over `scripts/rebel/m06-targets.txt`.
The second runs `scripts/rebel/audit_exact_leaf.py`, compiling its registered
modules, collecting all declarations' transitive axioms and invoking the
configured Batteries linter. The allowed axiom list remains exactly
`propext`, `Classical.choice`, and `Quot.sound`. Both new modules and the
previously omitted supplemental `CFRDInformationQuerySampling` entry are in
that audit. No audit has been skipped or relaxed to obtain this result.

Diagnostic artifact: `10733760063`.
Name: `m06-targeted-b3d63c722d94a5aaee60403025a5a71d4b650a4b`.
Server-reported archive size: `22149` bytes.
Server-reported SHA256:
`8a36cc1dc17d480d0f0eb94f2c08108dfb041df91bb84760c800d4ecb5d0d848`.
The artifact metadata states expiration `2026-09-30T04:57:55Z`.
The digest above is GitHub's artifact metadata, not a claimed local rehash.

## Other gates: keep completed and pending evidence separate

`ReBeL source inventory` run `35820010299` on the same SHA completed successfully.

`ReBeL checks` run `35820010297`, job `107049908587`, had succeeded through
library line widths, static architecture, ledger/inventory/adversarial fixtures,
and the rational-runtime differential check. Its full compiler/lint/transitive-
axiom step remained in progress at the last inspection. Source-snapshot job
`107049908568` succeeded. These observations are not an overall ReBeL-run pass.

Full `CI` run `35820010272`, job `107049651853`, also remained in progress.
Check the current branch HEAD after this documentation commit. A subsequent
push can supersede in-progress runs; never reuse the older target SHA's green
status as a claim that a new commit's complete workflow has finished.

## Repair provenance

`013382138804d944ecd19c1b911d09bd5f02dfc9` repairs the original off-path live
control without the forbidden Analysis transport tactic. Its targeted run
`35817553525` succeeded. Its predecessor failed the static gate, rather than
having a proven compiler error on the repaired direct proof.

`ce8c0f044f315f04fa6d9da83279f11df65b7785` introduced the sampled-parent source.
Run `35819139077`, job `107047034616`, failed on two unused `DecidableEq`
section variables in the pure oracle identity theorems. Diagnostic artifact:
`10733130401`. The tested successor places the instance only over the actual
state and security statements. No lint option is disabled.

## Semantic acceptance boundary and next task

The implemented, target-validated declarations and five concrete controls are
mapped in `M06-sampled-values.md`. This is a sampled-expectation-to-parent-state
connection with a retained-continuation security bound. The positive prediction
allowance, positive child tolerance and finite-T term remain explicit.

Fresh independently solved recursive carried-PBS execution is still open in
this project. Its local replacement-quality conditions must be proved from the
actual constructed solver; the existing generic telescoping theorem does not
provide them. Actual unknown-opponent histories outside model support cannot
be discharged by assuming model/actual posterior equality or support domination.

Original source obligations and their hashed inventory rows remain unchanged
and pending. Full integration is not accepted here, and main is untouched.
