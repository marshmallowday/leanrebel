# M06: joint completion consumed by the actual leaf contract

Starting source: `943964003e6ae661af85fd3a1a03b5e9493b1527` on
`rebel/m06-joint-completion-20260920`. This follows the preserved merged
`b5978ef6` work, query support, and the canonical-oracle identifier repair.

## New proof boundary

Source: `GameTheory/Analysis/ReBeL/CFRDCompletedContract.lean`.

- `cfrDCompleteZeroReach_referenceLaw` preserves the complete unilateral
  reference law, using the canonical uniform-legal focal policy.
- `cfrDCompleteZeroReach_currentPBS` preserves the complete factual and
  counterfactual query packet, not just its marginal observations.
- `cfrDCompleteZeroReach_referenceDeviationValue` preserves every complete
  focal deviation's conditional value on a sampled reference query. This does
  not assert that the played continuation itself is unchanged at zero own reach.
- `TypeBeliefSlice.conditionalPayoff_eq_of_reachable_agreement` permits actual
  public-state splicing: only decisions on a conditional kernel's legal future
  must agree. No global policy equality at unrelated public states is required.
- `TypeBeliefSlice.completed_value_eq_of_local_response` derives supported-type
  optimality from canonical Nash and zero-own-reach optimality from the locally
  implemented finite conditional best-response plan.
- `cfrDCompleteZeroReach_leafOptimal_of_queryGames` derives the existing
  all-behavioral-deviation `CFRDLeafOptimal` at zero loss. It uses the completed
  profile's reference law, proves opponents' reach conditions from actual
  reference support, and distinguishes supported and unsupported factual types.

## Explicit remaining construction

The final theorem requires each sampled live reference query to come with a
compatible typed canonical PBS game, an actual Nash equilibrium of that game,
its kernel and factual-support identities, and local implementation of the
computed response by one legal completion. These are structural/equilibrium
obligations, not supplied continuation inequalities. They must still be
constructed for the recursive child solver. No arbitrary-query, unrestricted
recursive, finite-T-child, or complete Theorem 3 acceptance is claimed.

The original main/supplement statements remain separately recorded in the
existing source inventory and roadmap R5 audit. This intermediate bridge does
not change the printed finite-T coefficient, numerical-error contract, or any
source status. The original M06 parent rows stay pending until acceptance.

## Validation

Registered in the analytic umbrella and declared M06 target list, and therefore
in the existing compiler/lint/transitive-axiom consumers. Exact new-source CI
must be read; earlier green jobs do not verify this addition. Positive and
zero-reach boundary controls and final validation evidence are the next step.
