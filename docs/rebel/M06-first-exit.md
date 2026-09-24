# M06 first-exit witness and continuation-error decomposition

## Source and acceptance boundary

Read STATUS.md on `rebel/m06-first-exit-review-20260924` for the latest checkpoint.
The fixed validation source is487aaedd795d5d3a8b41a608c6a4e13d1967cb1c on the
preserved source branch `rebel/m06-first-exit-20260924`. The review checkpoint
changes documentation only, leaving that source's running checks undisturbed.
Main is not a write target. M06-first-exit-validation.md distinguishes the passed
targeted compiler/supplemental audit from the pending repository-wide checks.

This slice contributes to SEARCH-ERROR and the sampling component needed by
SAFE-THEOREM3 (main section6 and supplementG/I). It does not independently
verify either complete original obligation. The printed/corrected Theorem3
boundary from the source ledger is unchanged.

## Exact mathematical statement

Let K and L be finite kernels indexed by a finite schedule S, and let E mark
exceptional states at each stage. Require K(i,x)=L(i,x) whenever x is outside
E(i). This is equality on the COMPLETE state, not merely its public history.
Let mu be any finite-support initial law, F any future kernel, and g any real
observable. No relation between mu and an auxiliary model posterior is assumed.

The native stopping law eta returns either none, or the first exceptional state
x paired with its unexecuted suffix R. R INCLUDES the exceptional stage, but
excludes the already executed safe prefix. This analysis law stops; neither the
native nor comparison execution is changed.

Define D(none)=0 and

    D(some(R,x)) = E[g after K(R) then F, starting at x]
                - E[g after L(R) then F, starting at x].

Then the constructed identity is

    E_mu[g after K(S) then F] - E_mu[g after L(S) then F] = E_eta[D].

Thus C=E_eta[abs(D)] bounds the absolute complete discrepancy. If abs(g)<=B
on every outcome, then C<=2*B*P_eta(some). This refines the old first-hit
allowance using actual suffix values. No safety bound on D is supplied as input.
The proof inducts on the schedule: the first hit supplies its own suffix;
otherwise the shared next-state kernel transports the induction hypothesis.

## Declaration and premise review

All probability declarations below are in GameTheory.Math.Probability.FinDist:

| Declaration | Premises and result |
| --- | --- |
| sequenceFirstExit | Canonical FinDist bind constructs the native witness law. |
| sequenceFirstExit_hit | Its Option.isSome image equals sequenceFirstHit. |
| sequenceFirstExit_hitProbability | Equality persists for an arbitrary root law. |
| sequenceFirstExit_eq_of_eq_off_event | Complete off-event equality gives equal witness laws. |
| sequenceFirstExitValue | Computes D from complete remaining executions. |
| expect_bindSequence_sub_eq_firstExit | Derives the signed identity using off-event equality. |
| abs_expect_bindSequence_sub_le_firstExit | Bounds absolute discrepancy by E_eta[abs(D)]. |
| firstExitValue_expect_abs_le_firstHit | An observable bound implies C<=2*B*hitProbability. |

The final coarsening does not require off-event equality; it bounds the computed
suffix charge even when no global comparison identity is available. The signed
identity and refined global bound DO require off-event equality. All expectations
have finite support; no unproved limiting or measurable-selection theorem is used.

## Constructed noisy solver connection

GameTheory.ReBeL.PBSCarriedDepthExit retains the actual history, entire private
iteration/profile memory, carried model PBS, and remaining depth-parameter list.
GameTheory.ReBeL.pbsCarriedDepthFirstExit uses the existing configured native
carriedMemoryStep. Its comparator is the existing history-first step, retaining
the native conditional private profile paired with that profile's model PBS.

The existing pbsCarriedDepthConfiguredStep_eq_historyFirst proves the needed
equality outside pbsCarriedCFRException. That event means a live history outside
an existing model belief's support. Missing beliefs and zero-fuel/stopped stages
use the existing completion behavior; they are not counted as new solve events.
No average-PBS reset, independent profile/PBS draw, actual/model posterior equality,
or opponent knowledge of the private sampled iteration is introduced.

The new GameTheory.ReBeL declarations pbsCarriedDepthFirstExit_future_identity,
pbsCarriedDepthFirstExit_future_error and pbsCarriedDepthFirstExitCharge_le_firstHit
instantiate the signed identity, refined bound and coarsening respectively.
pbsCarriedDepthFirstExit_hitProbability preserves the prior Boolean probability.

The real existing runner is connected by
GameTheory.ReBeL.Examples.HiddenTypes.depthSampling_existing_runner_first_exit.
It rewrites executeCarriedResolves to the native state sequence with its unchanged
carriedSelectedTail, then applies the refined theorem. It is not an alternative
runner or a marginal-only comparison.

## Controls and preserved parameters

Examples/PBSCarriedDepthSampling preserves the positive prediction bias1/8,
child tolerance1/4 and distinct finite iteration counts2 and3. Existing supported,
reweighted, full-state, missing/stopped and two-stage first-hit controls remain.

New tests distinguish a late hit, repeated event labels, no hit, signed difference
-2, and invariance of the full witness law despite differing complete executions.
A future erasing the difference gives C=0 although hit probability is1. A genuine
1/4-3/4 mixture gives hit probability1/4 and C=1/2, including its no-hit branch.
These are probability-accounting controls, not a proof or refutation of the
paper's game-theoretic safety result. See M06-first-exit-controls.md.

The two extended proof modules and their example module already belong to the
analytic import closure, M06 targets, supplemental lint and transitive axiom
audit. The targeted workflow now also triggers for probability-only edits.
No gate, target, audit command, dependency pin, heartbeat or old test was weakened.

## Unresolved original obligations

C is a real-valued analysis quantity depending on the actual unknown-opponent
kernels and future observable. It is not an executable learned estimate, a
uniform opponent-independent error budget, or an O(delta+1/sqrt(T)) rate.

To establish the original recursive-security result, derive useful source-level
bounds on these continuation discrepancies and model-value drift, connect the
arbitrary-depth child solver (deepest children still use full-root CFR), and
discharge CarriedResolveStepBounds rather than supplying it as a premise.
Preserve finite outer T, positive numerical/child errors and zero-reach completion.
SEARCH-FRONTIER, SEARCH-CFRD, SEARCH-ERROR and SAFE-THEOREM3 remain pending.
