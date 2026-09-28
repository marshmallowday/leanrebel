# Recomputed-value cbda1b3 failure and conditional-instance repair

Exact failed source: cbda1b336c5a8705813376340597cfba51851021.
This repair is pending new-SHA Actions. M06 remains incomplete.

## Complete Actions evidence

| Gate | Run / job | Result |
| --- | --- | --- |
| CI | [36410876412](https://github.com/marshmallowday/leanrebel/actions/runs/36410876412) / 108890489866 | failure |
| ReBeL checks | [36410876476](https://github.com/marshmallowday/leanrebel/actions/runs/36410876476) / 108890490469 | failure |
| Targeted proof feedback | [36410876360](https://github.com/marshmallowday/leanrebel/actions/runs/36410876360) / 108890489545 | failure |
| Source inventory | [36410876580](https://github.com/marshmallowday/leanrebel/actions/runs/36410876580) / 108890490470 | success |

All four run/job head SHAs match. Full decoded logs were obtained and inspected:
82367 / 175936 / 55611 / 53949 characters after timestamp/ANSI removal.
The three compiler jobs report the same two source diagnostics, at
PBSRecursiveRecomputedValue.lean:79:8 and :95:8. No other source diagnostic
was found. PBSRecursivePosteriorValue compiled in 4.6s / 3.3s / 2.6s respectively.

Checks reports LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS, and 210 Python tests in 9.409s. Inventory independently
passes 210 tests in 10.131s. These do not replace Lean compilation, umbrella
integration, full normal/slow lint or transitive axiom review. The new example
module and complete lint/axiom gates were not accepted.

Artifact metadata reviewed: targeted 10963484998, global 10964339928,
source snapshot 10963649039; no CI or inventory artifacts.
ZIP payloads were not read. Complete decoded job logs are the diagnostic evidence.

## One cause, two branches

The proof applied carriedMemoryStep_selected_late_expect and then used
dsimp only to reduce the configuration/stage aliases before rewriting the
resulting if. The visible condition was reduced to config.fuel, while the
implicit Decidable argument still referred to the unreduced stage.fuel.

Both diagnostics explicitly say the goal is not type-correct under the
rewrite tactic's implicit transparency level. The reported mismatch is:

- supplied Decidable (cfrDCutLive
  (pbsRecursiveConfigStage M fallback payoff bound initial config).fuel
  state.history = true);
- expected Decidable (cfrDCutLive config.fuel state.history = true).

The two fuel expressions are definitionally equal at normal elaboration
transparency. The failure is caused by partial unfolding before rewriting;
it is not evidence of different mathematical fuel or a missing liveness premise.
The previous static review missed this implicit-instance/transparency interaction.

## Repair and precommit consumer review

Only the proof of pbsRecursiveRecomputedOutcome_value changes.

- At a live state with a saved PBS, derive support from the existing explicit
  non-exception premise and apply the already accepted
  pbsRecursiveDepthStage_selected_late_value directly. Its exact signature was
  re-read: same full model, initial memory, unknown opponent, focal player,
  configuration noise/cuts/tolerance, stage fuel and late fuel, state, indexed
  belief, stored equation, liveness, support, and payoff.
- At a missing-belief state, name liveness at the unreduced stage.fuel and
  consume the generic if before unfolding stage aliases. The resolver's pure
  retained profile and the old total-fuel tail then agree.
- In the stopped branch, likewise name the negated condition at the unreduced
  stage.fuel, remove that if first, and only unfold the comparison law's own
  condition. No partial dsimp of a condition while its Decidable witness remains
  folded is left.

The remainder of the module and all three concrete consumers were re-read.
The policy-change identity and expected-loss inequality use complete simp
rewrites, not the failing partial dsimp/if sequence. The schedule induction
unfolds list/scalar accounting without exposing an if on a rewritten stage
condition. The concrete zero-fuel test uses its literal config.fuel; the chain
states totalFuel=3 under its exact stage alias. The parent residual retains
typed PBSChildSolve/trunk aliases, explicit full-model S, and the same
dependent possible proof. No downstream signature was changed.

The reviewed dependencies are byte-identical to the previously inspected
sources: PBSRecursiveCarriedReplay ddae2a04aa37892550c4c8e49980c58d62f44984,
PBSCarriedValue fcbd341c45a4b40f88e9321fb77c5ffa425b55d3,
PBSRecursiveDepth 3460c686ccb617486fc9475cf901c4a4937c5af2.
New public declarations and all mathematical statements, definitions and
premises remain unchanged. No workflow, test, audit criterion, heartbeat limit
or accepted-source pin is modified. No suppression or new instance is added.

This is a static review, not a successful compiler run. The full 178-target,
140 targeted/281 global module and 210-test surface must pass on the new SHA.
The accepted ce81eae checkpoint is documented separately and is not reused
as validation for the new source. The exact cbda1b3 owner ledger is preserved
as M06-kernel-value-transport-coverage-at-cbda1b3.json.

## Meaning boundary

The computed budget still needs a useful solver-specific bound; it is not
automatically a small convergence rate. Rooted/original solver correspondence,
native support estimates and SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 remain open.
See M06-recomputed-value-batch.md for the unchanged scope and controls.
