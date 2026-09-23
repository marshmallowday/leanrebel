# M06 native iteration draws at carried public beliefs

## Source and scope

This slice addresses the random-iteration and carried-model execution steps in
main Theorem 3 / supplement G, printed pages 21-22. It does not claim the full
recursive error rate or the printed formula. The preserved predecessor is
b17501a84ec76c6cd996864144f4a616ac251a00. Its full CI 35829793150/job107079581547
and ReBeL 35829793185/job107079633154 succeeded. Prior fresh-child evidence is
in M06-fresh-envelope-validation.md. All original M06 source rows remain pending.

## Implemented semantic changes

PBSCarriedSampling.pbsCarriedCFRResolver takes the incoming optional joint
PublicBelief as a new root game. With an existing belief it calls the actual
pbsInformationCFRIterate recurrence, drawing a uniform private index in Fin t.
No old averaged finite-plan draw is substituted for this native iteration.
Neither the actual hidden history nor the unknown opposing policy is a solver
argument. The retained old family is used only for the no-model-belief case.

pbsCarriedCFRResolver_step_some expands the complete canonical next-state law:
each selected native iterate is paired with the posterior propagated through
that very iterate. It uses carriedResolvedStep/resolvedNextState unchanged.
This statement applies even to actual histories outside the stored support.
pbsCarriedCFRStage installs this solver into the existing finite list runner
executeCarriedResolves; later stages receive the posterior actually stored by
the preceding stage, never a reset run from the original game root. At missing
beliefs the existing selected policy is retained. Real terminals and zero-fuel
stages retain the canonical no-query rule.

The child learner here solves its prescribed finite root game by full-root CFR.
This is not yet a recursively depth-limited child oracle or a claim of source
algorithm identity. Training horizon, stage execution fuel and t remain distinct.

## Exact single-step sampling comparison

pbsCarriedCFRAverageResolver solves the same incoming belief using the same t,
and chooses its own-reach average. The existing supported-root law theorem
proves equality of the resulting complete history laws outside the event

    E = {state | live(state) and stored belief exists
                 and actual history is outside that belief's support}.

Missing beliefs and stopped states are NOT exceptional: the two executions
use the same fallback/no-query rule there. For every actual finite incoming
state law rho, every fixed unknown behavioral opponent and |V| <= B,
pbsCarriedCFRResolver_actual_error proves

    |E[rho bind sampledTail] V - E[rho bind averageTail] V|
        <= 2 * B * rho(E).

There is no caller-supplied support domination, posterior equality, individual
iterate optimality, root-regret bound, envelope or final safety premise. The
exceptional mass is measured under the actual incoming law, not the model law.
It is retained explicitly; no theorem says it is zero or tends to zero.

The independent probability module FinDistEventError proves the one-sided,
absolute and finite-kernel versions of this event estimate from the public
FinDist expectation algebra. It does not introduce another probability model
or any game-specific import in GameTheory.Math.

## Main declaration map

- FinDist.expect_sub_le_of_eq_off_event
- FinDist.abs_expect_sub_le_of_eq_off_event
- FinDist.abs_expect_bind_sub_le_of_eq_off_event
- pbsCarriedCFRResolver_none / pbsCarriedCFRResolver_some
- pbsCarriedCFRResolver_model_law / pbsCarriedCFRResolver_step_some
- pbsCarriedCFRResolver_tail_eq_average / pbsCarriedCFRResolver_actual_error
- pbsCarriedCFRStage / pbsCarriedCFRStage_zero_history

The ReBeL declarations are in GameTheory.ReBeL; the finite-law declarations
are in GameTheory.Math.Probability.FinDist. Finiteness is required only on
original legal histories and original actions for the native rooted solver.
Full AOH provides its existing perfect-recall interpretation. The event lemma
itself requires no finite carrier, only finite-support laws.

## Controls

Examples.PBSCarriedSampling constructs a genuine factual live hidden-type state
and derives its support, rather than assuming it. The controls cover live
execution against arbitrary unknown opponents, independence from the old family
when the stored PBS is present, the full iterate/posterior pairing, absent
belief fallback, zero fuel, the explicit 4 * rho(E) error for payoff bound 2,
and a two-stage schedule with different finite iteration counts. The schedule
fuel equality is not a computed multi-stage equilibrium claim.

Two separate finite-law controls show that the event bound can be sharp and
that equal history marginals do not justify substituting full private-state
laws in a later transition. These are guards against invalid proof steps,
not counterexamples to the game-level source theorem.

## Verification checkpoints

Initial source 64bc087f4b559ba25979ea43e394d47dc58d3074, target run35831741238 /
job107085699414 compiled FinDistEventError and all inherited targets. It failed
on precisely two unused simp arguments in PBSCarriedSampling (lines138/145).
The repair removes only those redundant stored-equality arguments, keeps the
required support proof, and does not weaken any lint or axiom gate. This
checkpoint adds the examples to the root, target list and supplemental auditor.
Check its exact-source CI before treating the added slice as accepted.

## Supplemental coverage, not source-row promotion

| Original row | Added evidence | Remaining |
| --- | --- | --- |
| SEARCH-FRONTIER | Existing stopped rules exercised by native carried stages | Source acceptance review |
| SEARCH-CFRD | Incoming-PBS native iteration solver in the existing finite runner | Recursive depth-limited child/oracle connection |
| SEARCH-ERROR | Derived sampling defect on arbitrary actual incoming state laws | Source-dependent exceptional-mass and model-drift rate |
| SAFE-THEOREM3 | Genuine iteration and posterior pairing, not an averaged reset | Full recursive corrected source guarantee |

A later proof must preserve the complete selected-profile/posterior state law.
History marginal equality alone cannot establish the induction. No invocation
of CarriedResolveStepBounds, unproved support inclusion or equality with an
unknown opponent's posterior may replace that missing argument. Preserve finite
outer T, nonzero prediction and child errors, and the corrected/printed Theorem3
separation. This slice makes no executable numeric-refinement claim.
