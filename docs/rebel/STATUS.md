# ReBeL status — changed-kernel control and architecture repair; M06 incomplete

Continue rebel/m06-kernel-value-repair-20260927. The third focused repair is a
child of 628b6212a9c64189c99355a6aea46fcc0487b9d7; the starting latest checkpoint
was dac8bd902ba368357d4a53f0d0b6b90a6d3dddeb, not main. Earlier commits and
source-specific failure/acceptance evidence remain preserved.

## Latest inspected feedback and repair

628b6212 TARGET 36292939236 / job 108546359029 compiled both the generic kernel
value transport and its actual noisy depth-parent integration. The example
module then FAILED: a Bool projection split did not reduce the conditional,
and eager slice unfolding prevented the intended explicit payoff rewrite.
Both control proofs are repaired without changing or deleting any statement.

628b6212 GLOBAL 36292939304 / job 108546413147 FAILED the static architecture
gate: analysis transport expected 0, got 2. Replace the two unnecessary change
steps in the attained-maxima proof with ordinary beta reduction by dsimp only.
No gate, expected count, dependency pin, import or theorem premise is changed.
See M06-kernel-value-repair-628b6212-validation.md for complete artifact hashes,
exact diagnostics and independently checked source/Python evidence.

The owner ledger M06-kernel-value-transport-coverage.json is current, with its
full predecessor archived at M06-kernel-value-transport-coverage-at-628b6212.json.
All 149 Python tests and coverage/inventory structure checks passed on exact
628b6212 source; INVENTORY 36292939239 succeeded. These are not new-source Lean
acceptance. That failed source's lint/axiom validation never ran.

## Immediate continuation

Inspect the new exact-SHA target and global runs. Require all declared controls,
116 targeted / 259 global module audits, complete allowed-axiom records and
normal/slow lint. Keep the 154-entry build manifest and all public imports.
FULL CI is separate; prior run 36292939302 / job 108546412609 had no inspected
final result and may be superseded by the new push. No completed changed-kernel
slice is claimed until its exact source is validated.

## Preserved scope and remaining mathematics

The same comparison opponent, horizon, actual correlated event-selected query,
finite-T error and event denominator remain explicit. New complete compatible
kernels can depend on the seed and queried types can be retagged. This does not
identify them with actual recursively re-solved posteriors or make their L1
variation small. Changed opponents, small primitive kernel/leakage rates,
late-value transport and constructed signed CarriedResolveStepBounds remain open.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
The accepted 51d5 target/global/full-CI evidence is separate in the depth-native
gap acceptance reviews. M06 is incomplete; learner convergence is not test-time safety.
