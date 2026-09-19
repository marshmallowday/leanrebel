# M06 terminal-exact backup checkpoint

Resume branch: `rebel/m06-recovery`. Do not rewind to the older `rebel/m06`.
The preserved base `7eec0533a97f8a4ae5b2872b9d4b4dc0b385d6d3` passed all five
checks: targeted M06 run 35457629151, ReBeL compiler/lint/axioms and source
snapshot run 35457629127, full build/lint/architecture run 35457629192, and
inventory run 35457629177. No main integration is made by this checkpoint.

The new generic terminal-exact information-value backup is committed at
`719270f018f3fa454af4638d63ec3d932334b135`. Its targeted M06 compilation passed
in run 35462531449 (job 105948835771). Full validation is separately tracked;
a targeted build is not a completed milestone gate.

## Semantic change

`conditionalOracle_live_value` conditions on both information state and the
live-leaf flag. `terminalExact_reweight_error` proves the delta error bound
with accuracy assumed only for supported LIVE fibers; exact terminal rewards
are added without querying the vector. `terminalExact_no_live` proves the
no-oracle boundary for arbitrary predictions. No hidden-history pointwise
accuracy or terminal-status observability is required of a player's policy.

`CFRDCutBackup.lean` connects that finite-law theorem to the canonical runner,
positive uniform own-reach probes and the actual full continuation. Its
numerical score executes only the prefix. It establishes score accuracy,
score magnitude and canonical action-regret transfer. The comparison score
has an action-independent offset: it is NOT identified with counterfactual
action utility. The offset cancels under the current local action law.
The zero-remaining-fuel boundary ignores every prediction, but does not claim
that a finite number of regret-matching iterations produces an exact Nash
profile. The new module is included in the umbrella and targeted checks.

## Validation and remaining work

At creation of this checkpoint the new game-level module awaits its own
exact-SHA compiler/lint/axiom results. No coverage row is promoted to verified.
The generic information-value lemmas above already passed the stated target
run. Continue by constructing the coupled value-response adapter, transferring
its actual numerical regrets to the trunk/root bound, and proving the
continuation replacement and private random-iteration safety statements.
Keep `A_d * delta + B_d / sqrt(T)` distinct from the printed Theorem 3 formula.

The earlier complete 68-file review and source-manifest hash are preserved in
M06-oracle-reweighting.md; the three later recovery documents have also been
read. The current session rechecked the root and ReBeL AGENTS, README, STATUS,
ROADMAP's M06 acceptance conditions and the relevant coverage obligations.
