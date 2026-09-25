# M06 one-sided continuation value stability — 2026-09-25

## Resume and preserved source

Work branch: `rebel/m06-value-stability-20260925`.
Base: `c984277c2238e4dd1249ff3ace6fc5444175858a` on
`rebel/m06-fiber-lint-repair-20260925`; this includes the repair after
`e27fee69332f1b55a08f99e68defdd7b5823074e`. Do not reapply the removed
`[NeZero t]` argument or rewrite earlier branches. Main is unchanged.

## Evidence actually inspected in this continuation

The GitHub plugin reports full CI run `36093962268`, independent ReBeL run
`36093962238`, and inventory run `36093962214` successful at the base SHA.
The independent ReBeL source artifact `10846741980` was downloaded through
that plugin. ZIP SHA-256 is
`d9b2d996fabfd2dd2a644aef1e55313f45c6ad569697c51c299b38157b733894`;
`source-commit.txt` identifies exactly the base SHA.
Validation artifact `10847312931` was also downloaded and inspected offline.
Its log contains `REBEL_VALIDATION_PASS modules=239` and explicit lint passes
for both the source-rate module and its example. No local git operation or
local GitHub request was used. Source/validation artifacts are inspection
inputs, not evidence that new code has compiled.

## Next dependency-closed slice

Investigate one-sided continuation value comparison rather than assume
convergence of entire continuation outcome laws. Connect it to the established
actual-law child-loss/weighted-drift transport machinery. Preserve the actual
unknown-opponent seed/history law, supported and off-path cases, finite T,
and the distinction between model PBS and actual posterior.

Implementation and target-SHA compilation are not yet performed at this
checkpoint. Existing M06 coverage statuses remain pending. This checkpoint
is not M06 acceptance or a claim that native solver stability is proved.

Next checkpoint must include the exact Lean statements, positive and negative
controls, lint/axiom consumers, the corresponding ledger/STATUS update, and
actual CI outcomes. Keep previous failures and accepted evidence intact.
