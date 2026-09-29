# Cross-query recursive scalar values and stored public/live inputs

Parent and accepted dependency:
`ffab72bcee96bd262a0a1c5f3966a5e96b41aed7`.
New source is pending exact-SHA Actions. M06 remains incomplete.

## Mathematical scope and reuse

PBSValueStability already compares two finite solves on one PBS, and
PBSConditionalValueStability retains opponent conditions for conditional
information-state values. This batch concerns TWO possibly different PBSs
and the actual recursive solver. It neither duplicates the same-PBS CFR
theorems nor removes necessary conditional-value assumptions.

For two zero-sum approximate Nash profiles, take the first profile's
opposing-player deviation (accepted behavioralNash_model_security) and
the second profile's own deviation. The shared cross profile has expected
payoff difference at most rootError between the two root laws. Thus:

```
abs(first_model_selfplay - second_model_selfplay)
    <= first_tolerance + second_tolerance + rootError.
```

The generic helper requires a uniform bound for COMMON fixed profiles.
The concrete root-law consumer supplies it by Markov contraction and
bounded payoff:
rootError = bound * atomVariation(firstBelief.law, secondBelief.law).
This is not an assumption of already-computed value stability. Nash at the
second root is independently established; moving the first profile to that
root is not assumed to preserve its Nash property.

Both actual pbsRecursiveDepth invocations discharge their Nash premises,
with independently selected noise families/contracts, cut partitions,
fallbacks, positive tolerances and observation-indexed PBS inputs.
The original protocol, payoff and total horizon must agree. Cuts.sum
equality does not equate two algorithms or their policy distributions.

The second actual finite private draw secures the first computed model
value within firstTolerance + 2*secondTolerance + rootError against an
arbitrary opponent chosen outside the draw. The second tolerance appears
once in scalar comparison and once in its own one-sided guarantee.
This is on the second MODEL root law, not an unproved calibration assertion
for a native conditional state distribution.

## Actual saved public posterior versus live child

CFRDStoredSolveValue instantiates the uniform fixed-profile comparison with
the accepted cfrDFactualChild_public_continuation_error. Crucially, both
policies are then RECOMPUTED by real recursive solves on the two inputs:

```
abs(public_recursive_selfplay - live_recursive_selfplay)
  <= firstTolerance + secondTolerance
     + 2*bound*stoppedPublicMass/publicReach.
```

The earlier fixed-kernel result alone did not justify comparing recomputed
policies. The two Nash arguments now justify this scalar result. A positive
live query supplies public positivity; zero public reach is not divided by.
Public-only storage is unchanged and not silently replaced by live filtering.
The stopped-mass ratio need not be small.

The hidden-type noisy parent example retains the actual saved-state equality
from hiddenStoredPublic, full joint PBS, bias1/8, recursive child[1], selected
round, state.history-dependent observation and existing prior. Two later
searches use tolerances1/8 and1/4. This game's proved publicly observable
termination makes the stopped mass zero, so only their tolerances remain.
This does not identify the internal chance-rooted child with an original
fresh computation, and never identifies MODEL with an unknown factual law.

Further concrete consumers compare actual [1,1,1] and [3] searches at the
initial PBS and transport the old computed value to the new private draw
against arbitrary unknown opponents. Their horizon is3, their budgets
differ, and no profile equality is claimed.

## Five independent Fraction controls

The controls are finite rational games, not CFR or Lean executions:

1. 729 changed-root/profile combinations and both players, each with its
   OWN root's independently computed deviation error.
2. Public/live re-solving with rare public reach, plus constant-action
   exact equilibria attaining2*bound*stoppedMass/publicReach. Removing the
   denominator fails.
3. Equal scalar exact-Nash values with different policies and a typewise
   gap2; moving a root can destroy an old profile's equilibrium.
4. Private pure-policy mixture security with both solve tolerances and
   one root term. Omitting the new solver's error can fail.
5. Different horizon/late rewards, private draw resampling, and loss of
   key/history correlation. Equal aggregate roots do not prove equal
   conditional roots.

## Precommit type and semantic review

Read accepted PBSValueStability/PBSConditionalValueStability,
PBSRecursivePotential, actual recursive Nash/draw definitions,
CFRDStoredChildDefect, FinDistConditioningError and real noisy-parent
consumer signatures. Used canonical preferences, utilities and cross
profiles. No parallel equilibrium, game or solver definition is introduced.

The generic cross-root helpers have NO unnecessary Fintype section variables.
The scalar root helper adds only finite History; action finiteness starts
with actual recursive instantiation. Both old/new observation indices stay
attached to their own PublicBelief. All generic fullInformation applications
carry six explicit universes; @ recursive Nash/root helper calls specify
protocol, model, instances and observations in the actual signature order.

Checked both inequality directions and both players. Second Nash is rewritten
to the first total fuel ONLY via the explicit sum equality. The private
consumer uses the accepted actual-draw theorem on the SECOND belief and
secondCuts.sum, keeping its second error separate. No private seed appears
in the unknown opponent binder.

For stored/live comparison, condition's S and every publicTrace use the full
model; possible, condition and child share the same obs. firstCuts.sum and
secondCuts.sum each equal remaining, while cut remains the parent's prefix.
The fixed-profile bound is used before comparing different computed outputs.
The concrete parent solve and trunk aliases retain explicit PBSChildSolve
and full behavioral Profile types. Original/full models, state.history
indices, Choice/InfoState instances, selected round, fallback and horizons
were followed through all consumers. Static review caught the draft binder
name public as a keyword risk and renamed it posterior before commit.

All10 public names were checked against the complete accepted axiom records
without collision. All new public declarations/local instances have docstrings,
all new Lean lines are at most100 UTF-16 code units, and the existing
comment-stripped transport regex has0 matches. No casts, change tactic,
axioms, placeholders, linter suppression or heartbeat increases were added.
These static checks are NOT a compiler/lint/axiom/test run.

## Integrated validation and remaining groups

Adds2 core modules,1 example and5 tests in one batch. Registration adds only:
193->196 build targets;155->158 targeted/295->298 global audit modules;
235->240 Python tests. Workflows and audit criteria are unchanged.
M06-security-potential-ffab72b-accepted.md separately records exact-parent
evidence, which is not validation of the new source.

Dependency-ordered remaining work:

1. Validate this entire new SHA and repair all observed causes together.
2. Apply scalar potential stability to actual successive native queries
   while proving needed conditional-root/support bounds. History-clock and
   changing-horizon relationships cannot be replaced by this same-horizon
   theorem. Incumbent payoff surplus still need not be small.
3. Relate internal chance-rooted child and fresh original-game computations,
   preserving posterior, protocol-dependent noise, fallback, budget, clock
   and root encoding. Value closeness here is not computation identity.
4. Integrate general recursive small-rate safety and complete source review
   for SEARCH-CFRD/SEARCH-ERROR/SAFE-THEOREM3.

The boundary at2/3 is mathematical: scalar same-horizon comparison is now
supplied, but native-query calibration/support and representation/clock
relationships remain. This batch includes the dependent primitives, actual
solvers, stored-state consumer, examples and tests instead of splitting them
into separate short-lemma workflow waits.

No conditional infostate-vector equality, old/new policy closeness, last
iterate convergence, learned-network accuracy or Theorem3 completion is
asserted. Prediction error, finite T and child loss remain independent.
The original/formalized Theorem3 distinction remains in its dedicated record.
Frozen coverage.json and all source acceptance pins are unchanged. The
previous owner ledger is saved with exact blob
14c8922307cd48a3af1b099ba22c8ab9433301c7 at
M06-kernel-value-transport-coverage-at-ffab72b.json.
