# M06 native iteration draws at carried public beliefs

## Source and scope

This slice addresses the random-iteration and carried-model execution steps in
main Theorem 3 / supplement G, printed pages 21-22. It does not claim the full
recursive error rate or the printed formula. The preserved predecessor is
b17501a84ec76c6cd996864144f4a616ac251a00. Its full CI 35829793150/job107079581547
and ReBeL 35829793185/job107079633154 succeeded. Prior fresh-child evidence is
in M06-fresh-envelope-validation.md. All original M06 source rows remain pending.

## Implemented semantic changes

pbsCarriedCFRResolver takes the incoming optional joint PublicBelief as a NEW
root game. With an existing belief it calls the actual pbsInformationCFRIterate
recurrence, drawing a uniform private index in Fin t. No old averaged finite-plan
draw is substituted for this native iteration. Neither the actual hidden history
nor the unknown opposing policy is a solver argument. The retained old family
is used only for the no-model-belief case.

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

## Full-state history-first disintegration

The new pbsCarriedCFRHistoryFirstStep is an ANALYSIS-ONLY comparison kernel,
not another legal public resolver. Write N_s for the native full next-state
law and A_s for the same child's average HISTORY law. It is defined as

    H_s = A_s.bind (N_s.condOnFibre (fun next => next.history)).

Outside E, pbsCarriedCFRResolver_step_eq_historyFirst proves N_s = H_s using
the public FinDist disintegration theorem and the supported-root marginal
identity. The history-first expression retains the conditional joint law of
the native selected profile AND the model posterior propagated through it.
It does not reset either component to the averaged policy or its posterior.

Consequently pbsCarriedCFRHistoryFirstStep_future_error proves, for ANY finite
future kernel F from the complete retained state and any |V| <= B,

    |E[(rho bind N) bind F] V - E[(rho bind H) bind F] V|
        <= 2 * B * rho(E).

F may inspect the retained private profile, the model belief and the history;
it need not factor through the history marginal. In particular, the existing
remaining recursive runner may be composed with the unchanged memory storage
map to supply such an F. The theorem compares the SAME future kernel on both
sides, not two independently solved future sequences.

H_s can depend on the actual incoming hidden history and the unknown opponent
through N_s. It is not an executable public-only strategy, and its actual joint
conditional law is not identified with the stored MODEL belief. No probability-
zero conditional convention is used without an allowance: possible defects
remain inside the explicit event charge. This construction repairs the invalid
history-marginal substitution step but does not establish recursive security.

## Main declaration map

- FinDist.expect_sub_le_of_eq_off_event
- FinDist.abs_expect_sub_le_of_eq_off_event
- FinDist.abs_expect_bind_sub_le_of_eq_off_event
- pbsCarriedCFRResolver_none / pbsCarriedCFRResolver_some
- pbsCarriedCFRResolver_model_law / pbsCarriedCFRResolver_step_some
- pbsCarriedCFRResolver_tail_eq_average / pbsCarriedCFRResolver_actual_error
- pbsCarriedCFRHistoryFirstStep / pbsCarriedCFRResolver_step_eq_historyFirst
- pbsCarriedCFRHistoryFirstStep_future_error
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

Two further native-solver controls check the full-state disintegration at the
supported root and the 4 * rho(E) estimate after an arbitrary state-reading
future kernel. Two separate finite-law controls show that the event bound can
be sharp and that equal history marginals do not justify substituting full
private-state laws. They are guards against invalid proof steps, not source
Theorem 3 counterexamples. There are fourteen named theorem controls in total.

## Verification checkpoints

Initial source 64bc087f4b559ba25979ea43e394d47dc58d3074, target run35831741238 /
job107085699414 compiled FinDistEventError and inherited targets. It failed on
two unused simp arguments in PBSCarriedSampling (lines138/145), repaired in
71dc6950ee683eea4361189cccbba30367436d52. That source compiled both core modules,
but two example proof elaborations required a local classical instance and
unfolding the named state-history field. No audit or theorem statement changed.

Source 1a6bab28e1c04fa11ea692321ce32f3e312f576e passed M06 target run35833737612 /
job107092156662, including the complete 64-module supplemental lint/axiom step.
GitHub reported artifact10739080371, digest
8f07521eef5cb49549b972eb1fd83a08ae4ac6b1d6501cbd271852b903879b19.
This is the confirmed pre-disintegration checkpoint; its success does not
validate the subsequently added full-state declarations or two new controls.
The current source must pass its own compiler, lint and axiom checks.

## Supplemental coverage, not source-row promotion

| Original row | Added evidence | Remaining |
| --- | --- | --- |
| SEARCH-FRONTIER | Existing stopped rules exercised by native carried stages | Source acceptance review |
| SEARCH-CFRD | Incoming-PBS native iteration solver in the existing finite runner | Recursive depth-limited child/oracle connection |
| SEARCH-ERROR | Sampling defect for actual laws, preserved through arbitrary future kernels | Source-dependent exceptional-mass and model-drift rate |
| SAFE-THEOREM3 | Native iteration/PBS pairing and correct full-state disintegration | Full recursive corrected source guarantee |

The native conditional coupling is now explicit, but the parent oracle and
the recursively solved future games still need their joint security argument.
No use of CarriedResolveStepBounds, unproved support inclusion or equality with
an unknown opponent's posterior may replace it. Preserve finite outer T,
nonzero prediction and child errors, and the printed/corrected Theorem 3
separation. This slice makes no executable numeric-refinement claim.
