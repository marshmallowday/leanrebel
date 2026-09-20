# M06: joint completion consumed by the actual leaf contract

Implementation source: `482ebe19486c92035f395fee92acf2bd49ab183c`.
Resume from `rebel/m06-contract-checkpoint-20260920`, containing the same Lean
source plus validation records. The previous joint-completion source branch is
retained so its exact-source full checks can finish without cancellation.

## New proof boundary

Source: `GameTheory/Analysis/ReBeL/CFRDCompletedContract.lean`.

- `cfrDCompleteZeroReach_referenceLaw` preserves the complete unilateral
  reference law, using the canonical uniform-legal focal policy.
- `cfrDCompleteZeroReach_currentPBS` preserves the complete factual and
  counterfactual query packet, not just its marginal observations.
- `cfrDCompleteZeroReach_referenceDeviationValue` preserves every complete
  focal deviation's conditional value on a sampled reference query. This does
  not assert that played continuation is unchanged at zero own reach.
- `TypeBeliefSlice.conditionalPayoff_eq_of_reachable_agreement` permits
  public-state splicing: only decisions on a conditional kernel's legal future
  must agree. It does not construct the cross-public-state splice itself.
- `TypeBeliefSlice.completed_value_eq_of_local_response` derives supported-type
  optimality from canonical Nash and zero-own-reach optimality from the locally
  implemented finite conditional best-response plan.
- `cfrDCompleteZeroReach_leafOptimal_of_queryGames` derives the existing
  all-behavioral-deviation `CFRDLeafOptimal` at zero loss. It uses the completed
  profile's reference law, derives opponents' reach from actual reference
  support, and distinguishes supported and unsupported factual types.

## Assumptions and explicit remaining construction

The reference-law results use finite players, perfect recall, and finite legal
menus for the uniform reference policy. The finite best-response results also
use finite legal histories/actions and the existing remembered-type slice.
The reachable-agreement lemma does not need a redundant finite-menu premise;
its section scope was corrected rather than silencing the unused-variable lint.
These are generic-player results; the downstream security theorem separately
requires its two-player zero-sum and bounded-payoff hypotheses.

The final theorem requires each sampled live reference query to have a
compatible typed canonical PBS game, a Nash equilibrium of that game, its
kernel and factual-support identities, and local implementation of the computed
response by one legal completion. These structural/equilibrium obligations
remain to be constructed for the recursive child solver. No arbitrary-query,
unrestricted recursive, finite-T-child, or complete Theorem 3 acceptance is claimed.

The original source statements remain separately recorded in the inventory and
roadmap R5 audit. This bridge does not change the printed finite-T coefficient,
numerical-error contract, or any original coverage status. The M06 parent rows
stay pending until their actual construction and acceptance obligations close.

## Validation and controls

The exact-source target run `35482474735`, retry job `106002870720`, passed all
35 declared targets (3,278 Lake jobs), including this module and five new
HiddenTypes controls in `Examples/CFRDZeroReachControl.lean`. The module remains
in the analytic umbrella and the recursive compiler/lint/axiom consumers.

The controls test the reference-law and supported-query boundary, not an
instantiation of the final theorem's entire `queries` premise. Their numerical
sanity check explicitly separates a changed individual-history payoff from an
unchanged private-information-conditioned mean.

See [M06-query-contract-validation.md](M06-query-contract-validation.md) for
source hashes, compiler repairs, workflow IDs, preserved failures, and the
remaining full validation gates. Read the live job results before acceptance.
