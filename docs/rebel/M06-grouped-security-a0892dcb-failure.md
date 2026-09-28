# Canonical grouped security: a0892dcb failed verification

Source: `a0892dcb783e05041bb7d222287daa1361b1cd4e`, branch `rebel/m06-kernel-value-repair-20260927`.
This is failed-candidate evidence, not source-obligation acceptance.

## Exact-SHA runs and complete logs

| Workflow | Run | Job | Result |
| --- | --- | --- | --- |
| CI | [36474810425](https://github.com/marshmallowday/leanrebel/actions/runs/36474810425) | 109105717843 | failure |
| ReBeL checks | [36474810236](https://github.com/marshmallowday/leanrebel/actions/runs/36474810236) | 109105716931 | failure |
| Targeted | [36474810276](https://github.com/marshmallowday/leanrebel/actions/runs/36474810276) | 109105716988 | failure |
| Source inventory | [36474810191](https://github.com/marshmallowday/leanrebel/actions/runs/36474810191) | 109105716304 | success |

All four runs completed on the source SHA above. Source snapshot job109105716577
also succeeded. Complete decoded logs were read: CI110720 characters,
checks240413, target74899, inventory73884, source14434.
The three compiler diagnostics below agree after timestamp removal.
All three compiler logs contain zero transitive axiom records.

Checks passed LIBRARY_LINES_OVER_100=0, TRANSPORT_ANALYSIS_SOURCE=0,
RATIONAL_RUNTIME_PASS and225 Python tests in9.396s. Inventory passed225
tests in9.026s. These successes do not validate downstream Lean compilation,
all-module lint, or axioms; none is accepted for this source.

## Diagnostics

```text
error: GameTheory/Analysis/ReBeL/PBSRecursiveGroupedValue.lean:92:9: unsolved goals
case none
E : ExecutionProtocol (Fin 2)
M : InformationModel E
inst✝¹ : Fintype E.History
inst✝ : (who : Fin 2) → Fintype (E.Action who)
K : Type v
fallback : Profile M.strategicSignature
payoff : Fin 2 → E.History → ℝ
bound : ℝ
initial : K → Profile (fullInformation M).behavioralSignature
unknown : Profile (fullInformation M).behavioralSignature
who : Fin 2
config : PBSRecursiveResolveConfig
remaining : ℕ
query : PBSRecursiveGroupQuery M
states : FinDist (PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K))
agrees : ∀ state ∈ states.support, PBSRecursiveGroupAgrees M fallback payoff bound initial config query state
state : PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K)
supported : state ∈ states.support
live : cfrDCutLive config.fuel state.history = true
old : carriedMemoryProfile (fullInformation M) initial state.iteration = query.old
stored : state.belief = none
computed :
  none = some (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief config.tolerance)
⊢ pbsRecursiveRecomputedLoss M fallback payoff bound initial unknown who config remaining state (payoff who) =
    ((fullInformation M).runBehavioralFrom (unknown.update who (query.old who)) (config.fuel + remaining)
            state.history).expect
        (payoff who) -
      ((fullInformation M).runBehavioralFrom
            (unknown.update who
              (pbsRecursiveDepth config.noise config.cuts E M fallback payoff bound query.belief config.tolerance who))
            (config.fuel + remaining) state.history).expect
        (payoff who)
error: GameTheory/Analysis/ReBeL/PBSRecursiveGroupedValue.lean:267:11: unsolved goals
case pos.none
E : ExecutionProtocol (Fin 2)
M : InformationModel E
inst✝¹ : Fintype E.History
inst✝ : (who : Fin 2) → Fintype (E.Action who)
K : Type v
fallback : Profile M.strategicSignature
payoff : Fin 2 → E.History → ℝ
bound : ℝ
initial : K → Profile (fullInformation M).behavioralSignature
config : PBSRecursiveResolveConfig
states : FinDist (PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K))
label : Option (PBSRecursiveGroupQuery M)
present : label ∈ (FinDist.map (pbsRecursiveNativeGroupKey M initial config) states).support
query : PBSRecursiveGroupQuery M
chosen : id label = some query
state : PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K)
reached : state ∈ (states.condOnFibre (pbsRecursiveNativeGroupKey M initial config) label).support
labelEq : label = some query
live : cfrDCutLive config.fuel state.history = true
stored : state.belief = none
tagged : none = some query
⊢ PBSRecursiveGroupAgrees M fallback payoff bound initial config query state
error: GameTheory/Analysis/ReBeL/PBSRecursiveGroupedValue.lean:274:2: unsolved goals
case neg
E : ExecutionProtocol (Fin 2)
M : InformationModel E
inst✝¹ : Fintype E.History
inst✝ : (who : Fin 2) → Fintype (E.Action who)
K : Type v
fallback : Profile M.strategicSignature
payoff : Fin 2 → E.History → ℝ
bound : ℝ
initial : K → Profile (fullInformation M).behavioralSignature
config : PBSRecursiveResolveConfig
states : FinDist (PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K))
label : Option (PBSRecursiveGroupQuery M)
present : label ∈ (FinDist.map (pbsRecursiveNativeGroupKey M initial config) states).support
query : PBSRecursiveGroupQuery M
chosen : id label = some query
state : PrivateIterationState (fullInformation M) (CarriedResolveMemory (fullInformation M) K)
reached : state ∈ (states.condOnFibre (pbsRecursiveNativeGroupKey M initial config) label).support
labelEq : label = some query
live : ¬cfrDCutLive config.fuel state.history = true
tagged : none = some query
⊢ PBSRecursiveGroupAgrees M fallback payoff bound initial config query state

```

## Repair and precommit type review

Restricted simp reduced each hypothesis to an impossible equality but did
not eliminate it. The repair adds `cases computed` or `cases tagged` after
the existing simplification in all three branches: missing belief in
pbsRecursiveGroup_loss_eq, missing belief in canonical compatibility, and
the stopped branch of canonical compatibility. It uses constructor
disjointness of Option.none/Option.some and supplies no new premise.

The previous static review incorrectly assumed simp only would close these
contradictory branches. It did not. This is a proof-completion failure, not
evidence that the mathematical statements or type signatures should change.

Re-read PBSRecursiveGroupQuery/GroupAgrees and the exact compiler contexts:
the first Option carries a nondependent full behavioral Profile after
mapping the history-indexed belief; the other two carry the same
PBSRecursiveGroupQuery M. Constructor contradiction needs no cross-model
cast, extra equality premise, DecidableEq, or new universe inference.
Generic fullInformation retains all six explicit universes; state.history,
publicTrace signal carrier, saved PBS index and independent memory/label
universes remain unchanged.

Re-read all consumers in PBSRecursiveGroupedValue, PBSRecursiveGroupedSecurity
and its examples, plus actual dependency signatures for recomputedLoss
equality, carriedResolveFuel_config_eq and finite-parent recursive security.
The live/some path, signed direction, supported conditional fibers, native
next-state law, tail alignment, Fin t seed, old/fresh argument order and
both total-horizon3 examples remain unchanged. The full public declarations,
definitions, assumptions, instances and theorem signatures are identical;
only three proof branches change. All other cases were checked for the same
unfinished impossible-Option pattern. No additional occurrence was found.

Static checks preserve 100-column core lines, zero existing transport-regex
matches after comments are removed, all186 targets and148/289 audit modules.
Workflow triggers were reread; no workflow, linter, heartbeat bound, test or
solver setting is changed. This review is not Lean compilation or a local
audit/test run. The next exact SHA must pass Actions.

## Artifacts

Metadata was read; binary ZIP contents were not read. Complete decoded logs
are the compiler evidence.

| Artifact | Bytes | SHA256 |
| --- | ---: | --- |
| 10992953139 | 5353 | sha256:1dabde286b1d337072beee70bb460713eb467216336010daa47dcfae7c44295f |
| 10994153618 | 21704 | sha256:5059e2399c8c4999559bb07ae210e9a5e9131cd9a37887850ea39eeebdfd74ef |
| 10993011419 | 2875391 | sha256:103a1f81b5eb19a89782cfe8f5deea86d83e4bf71a30a42efbf7dab6eaa26350 |

CI and inventory produced no artifacts. Latest accepted dependency remains
5a4710d; its successful results are not transferred to this candidate.
The owner ledger at this failed SHA is preserved without rewriting its blob
621eb5a91e2a10c57c00280adf21258614ea3c50 in
M06-kernel-value-transport-coverage-at-a0892dcb.json.
Frozen coverage.json and all source acceptance pins are unchanged.
SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3 and full M06 remain pending.
