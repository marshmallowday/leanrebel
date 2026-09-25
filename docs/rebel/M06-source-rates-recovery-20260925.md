# M06 source-rate recovery — 2026-09-25

## Restart checkpoint

Working branch: `rebel/m06-source-rates-repair-20260925`.
Starting commit: `bd5cdaa304cb0791379c94fd0454ed28eabb683d` on
`rebel/m06-transport-rates-20260924`, re-read through the GitHub plugin.
The original branch, main, accepted predecessor refs, dependency pins,
coverage statuses, and all validation gates are unchanged.

The GitHub plugin successfully created this work branch from the exact source
commit. This document is a restart checkpoint, not proof acceptance.
No local Git operation is used for remote access or commits.

## Immediate work

1. Recheck the source-rate example failures against the exact source and CI.
2. Repair the example proofs without changing their statements or assumptions.
3. Compile the declared M06 targets, inspect lint and transitive axiom output,
   and inspect full CI and independent ReBeL checks at the resulting source SHA.
4. Record observed run/job IDs, successful evidence and any remaining failures.
5. Continue source-law transport / drift consumers only from validated code.

The earlier chat's proposed proof edits have not been applied at this checkpoint
and are not treated as compiler evidence. Source presence and successful Python
checks alone do not establish Lean proof acceptance.

## Scope retained

M06 remains in progress. SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and
SAFE-THEOREM3 are not promoted. Native first-exit rates, independent re-solving
at later carried PBSs, and CarriedResolveStepBounds remain explicit obligations.
The printed/corrected Theorem 3 distinction and the proof/numerical boundary
must remain visible. Resume by inspecting this branch's current HEAD and CI,
not by reapplying an old archive or trusting a prior chat summary.
