# Semantic review: fresh carried-PBS information-set solves

This is supplemental project coverage for ROADMAP M06, not acceptance of the
paper's unrestricted recursive safety claim. Compiler and axiom evidence for
the final source SHA is recorded separately in `M06-carried-resolve-validation.md`.
All declarations below have namespace `GameTheory.ReBeL`, except controls in
`GameTheory.ReBeL.Examples.HiddenTypes`.

## Data and execution actually used

The new resolver consumes the existing `CarriedPublicResolver` inputs:
retained private memory, a public observation trace, and the optional STORED
joint `PublicBelief`. It does not receive the actual hidden history or the
unknown opposing strategy. `cfrDInformationResolveDraw` uses
`pbsInformationCFRIterate`, not a separately supplied equilibrium or a draw of
the old incumbent family. Its positive iteration count is
`pbsInformationConditionalRounds`, computed from that same model law and
its `positiveMassFloor * loss` budget.

A fresh draw means a new finite-distribution bind at the current query,
conditionally on the stored model and memory. It does not assert independence
of the resulting actions from public observations, earlier private memory,
or the selected policies. Only the deploying player's coordinate is used
against the fixed unknown opponent. The complete selected model profile is
retained by the existing referee for subsequent model-belief propagation.
This is not a shared seed made available to the actual opponent.

`cfrDInformationResolveStages` trains for the entire remaining horizon at
each stage and executes that stage's own interval. The sum of the intervals
plus the final retained tail is exactly the canonical execution fuel.
Terminal and zero-fuel stages use the existing no-query rule. No alternative
history runner, probability law, policy observation, or equilibrium predicate
has been introduced.

## Theorems and their exact scope

| Declaration | What is established | Assumptions not discharged by it |
| --- | --- | --- |
| `cfrDInformationResolveDraw_law` | The expected law of a fresh retained child draw is the computed conditional child average against any fixed opponent, starting under the supplied model PBS. | This model root law is not an arbitrary actual root distribution. |
| `cfrDInformationResolver_some` | A present stored PBS invokes the fresh information-set solver. | It says nothing about safety of the resulting recursion. |
| `cfrDInformationResolver_none` | A missing PBS chooses the newest incumbent as a point mass. | This is an explicit completion policy, not a refinement of every source implementation. |
| `cfrDInformationResolveStage_none` | The whole next carried-state law is the incumbent's canonical transition law with unchanged missing-model status and retained memory. | It assumes the current model belief is `none`, not merely that one actual history is absent from a present model law. |
| `cfrDInformationResolveStages_run_none` | Every finite later schedule has exactly the incumbent continuation law. | It does not claim the incumbent is individually optimal or safe. |
| `cfrDInformationResolveLoss_none` | The additional full-schedule replacement loss is exactly zero for every history payoff. | Zero additional loss is not zero exploitability. |
| `cfrDInformationResolveLoss_supported_part` | Under any supplied actual state law, the remaining expected replacement loss is exactly its contribution from states with a present stored PBS. | The remaining contribution has not been bounded by this identity. No equality of actual and model state laws is used. |
| `cfrDInformationResolveDraw_gain_le` | The sampled child has the derived model-root averaged deviation allowance `positiveMassFloor * loss`. | Zero-sum bounded payoff and positive child tolerance are required; no individual-iterate or changed-root guarantee follows. |
| `cfrDInformationRecursivePlay_nil` | With no subsequent re-solving, the actual noisy sampled-value parent is recovered exactly. | Nonempty schedules remain a distinct safety obligation. |

Structural assumptions are finite legal original histories and action
carriers, the canonical full-AOH model, and a complete legal fallback. The
parent wrapper additionally uses the existing finite local menus and
information-equality instances required by its abstract real-valued learner.
Neither custom axioms, supplied root-regret certificates, posterior identities,
caller-provided support domination, nor a desired safety conclusion is a
premise of the missing-PBS induction.

## Adversarial controls

`Examples/CFRDInformationResolve` uses the canonical live hidden-type PBS,
child tolerance `1/4`, and arbitrary fixed opponents. A memory state with a
newest `true` policy and an original `false` policy exercises `[0, 1, 0]`:
a positive execution interval is surrounded by two no-query intervals.
The actual payoff is 2; resetting to the original policy would give 0.
This arbitrary legal memory test checks retention, not reachability of that
particular memory under the new solver.

Reachability is separately tested in `Examples/CFRDInformationMissingModel`.
The deploying player is player one, retaining the incumbent `false` policy.
A fixed player-zero opponent uses the canonical uniform legal policy. The
actual prefix law is the existing positive unilateral reference law, so
`zeroControlHistory` is genuinely reached. Its public observation has zero
probability under the incumbent model, hence `missingModelState` has no
model posterior. The history is live with positive remaining fuel.
`missingModel_state_reached`, `missingModel_state_none`, and
`missingModel_state_live` are separate checked statements, followed by the
whole-schedule law `missingModel_recursive_law`. Thus the missing-model
boundary is not justified by assuming support for an invented state law.

## Remaining supported-branch obligation

A present stored PBS need not support every actual history under an unknown
opponent. The fresh draw's model-root realization identity alone cannot be
applied to such actual histories. Moreover, a selected CFR iterate need not
be individually optimal. Proving that an arbitrary fresh Nash policy retains
its predecessor's exploitation against one weak opponent is the wrong target;
the preserved `CFRDEquilibriumReplacement` controls rule out that shortcut.

The next mathematical target is a derived counterfactual OPPONENT-value
upper envelope for the newly solved continuation on the same reference
information fibers used by the parent, propagated through changed carried
states and subsequent fresh draws. `CFRDResolverEnvelope` and
`cfrDResolverEnvelope_of_prediction` expose the comparison needed by the
parent trunk-regret proof. Supplying those local inequalities as new fields,
or merely invoking `CarriedResolveStepBounds`, would leave the main obligation
unchanged. The actual solver must discharge them, including present-PBS
states with actual histories outside model support.

The original pending rows `SEARCH-FRONTIER`, `SEARCH-CFRD`, `SEARCH-ERROR`, and
`SAFE-THEOREM3` are retained. The finite outer iteration term, numerical error,
positive child loss, and printed-versus-corrected Theorem 3 distinction are
not dropped. No executable numerical refinement or complete-M06 claim is
made by this slice.
