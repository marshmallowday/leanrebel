# 3dfa native randomized resolver support — compiler checkpoint

Implementation source: `3dfa8c78375218bae5a323803f889b06342aecc2` on
`rebel/m06-resolver-support-20260927`. The new review checkpoint is on
`rebel/m06-resolver-support-checkpoint-20260927`, based directly on that source.
This checkpoint changes documentation only and leaves its source branch's
in-progress target/global validation uninterrupted. Its own workflows are
separate and are not represented as completed evidence.

## Actual observed compiler progress

Target run 36281726973 / job 108514712577 identifies exactly 3dfa. Its
`Compile the declared M06 targets` step completed successfully at
2026-09-27T00:15:36Z. The next `Validate the constructed exact child proof slice`
step was still in progress at this checkpoint. Consequently the compiler-step
success is recorded, but complete normal/slow lint, transitive axiom output and
final target success are NOT yet claimed. Fetch the completed target artifact
and inspect all complete axiom records before accepting the slice.

Core proof blob: `76df5514e9e878fde6e8ff4691c2ec341d88bf35`.
Example blob: `f440ce96ada7fb34f13caa0929a7d6d6cf06d309`.
The core's separately proved stopped indicator has no authored transport step.
The two example repairs keep all original and added statements intact.
Earlier failures are preserved in M06-resolver-support-63aa-failure.md and
M06-resolver-support-461-failure.md, not reclassified as successes.

Global run 36281726986 / job 108514756082 passed static architecture, line width,
ledger/inventory/fixtures, and rational Lean runtime steps. It was in its
full compiler/lint/axiom step when inspected. Snapshot job 108514756302 succeeded.
Inventory run 36281726972 / job 108514712773 succeeded. Full CI has its own run
and must be checked separately; no earlier full-CI result validates 3dfa.

## Scope and completed inherited work

This is a project dependency for M06, not a paper Theorem 3 proof. The seven
new support definitions/theorems and four controls are catalogued in the
semantic review and coverage JSON. They retain the actual resolver's private
profile/model/history pairing and arbitrary correlated incoming state laws.
Missing beliefs and stopped stages are explicit. Small primitive leakage,
finite-schedule first-exit composition and signed value/security bounds remain
unproved; a supported model PBS is not an actual-posterior identification.

The inherited b833 global audit has been completed and actually inspected:
4,939 complete allowlisted axiom records, 253 module lint passes, global and
architecture success. Its owning M06-support-rates-coverage.json is now updated
with the exact source/artifact/log identity and its earlier pending observation
retained as history. This evidence applies only to b833, not to the new code.
M06 remains incomplete and all four original pending source obligations stay open.
