# M04 recovery — 2026-09-18

## Recovered remote state

Read through the GitHub plugin, not inferred from a previous chat:
- `main`: `cf733bd1ffa977681d1197bf80b1dfd7be82ff6e` (accepted M03).
- `rebel/m04`: `7bcb033348cdc55d3b23db011a524ad14891ae77`.
- The work is remotely committed; no local Git state or unpushed changes are assumed.
- ReBeL run `35292212066`, job `105437351313`: failed.
- Full CI run `35292212076`, job `105437346012`: failed.
- Inventory run `35292212157`: succeeded.
- Compiler export run `35292212065`: succeeded.

The exact-source artifact `10526307096` reports the recovered commit above.
The validation artifact `10526912348` was downloaded through the plugin.
Its log shows all 1773 build jobs passed, including FiniteSites and its genuine
two-stage example. Transitive axiom output includes the new best-response
attainment theorem with only propext, Classical.choice, Quot.sound. Normal lint
then stopped on the undocumented local history Fintype instance in
`GameTheory/ReBeL/Examples/FiniteSites.lean`. This recovery commit supplies that
missing documentation. It does not disable docBlame or alter an audit baseline.
All checks must be rerun on the repaired SHA; the failed run is not acceptance.

## Work to resume

Preserve the finite-plan implementation and the five remaining slices in
`M04-checkpoint.md`: actual chronological decomposition, coupled CFR trace,
own-reach averaging and Nash bridge, rational solver/refinement, target-SHA
acceptance and ledger update. Do not count the existence theorem or a supplied
decomposition as a completed full-game CFR solver. M04 remains in progress.

All GitHub reads and writes use the plugin. Offline inspection of plugin-
obtained source is not a Git connection. No force push, reset, worktree, pin
upgrade, or unvalidated main integration is used. Subsequent checkpoints must
record actual compiled declarations and remaining obligations, not chat claims.
