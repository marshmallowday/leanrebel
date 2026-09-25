/-
# Native conditional-gap controls

A live hidden-type information-set CFR solve consumes its own private uniform
iteration sampler. A canonical exact-Nash counterexample separately forbids
moving absolute value across an expectation when the OPPONENT changes.
The negative family uses the same uniform index law, not claimed CFR iterates.
-/

import GameTheory.Analysis.ReBeL.PBSNativeConditionalGap
import GameTheory.Analysis.ReBeL.Examples.PBSConditionalValueStability

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Use every legal history, rather than a current-support-only carrier. -/
local instance nativeConditionalHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Two genuine native iterates preserve a supported type's conditional
payoff against arbitrary fixed opponents; they are not coordinate-averaged. -/
theorem pbsNativeConditionalGap_live_type
    (opponents : Profile (model fullPrior).behavioralSignature)
    (type : PublicRootType (reducedModel fullPrior)
      (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace) 0)
    (supported : type ∈
      (fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0).support) :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0
    (cfrIterationLaw 2).expect (fun n => slice.conditionalPayoff opponents 1 (cfrPayoff 0)
        (pbsInformationCFRIterate (reducedModel fullPrior) (slice.mixture own)
          pbsRootControlFallback cfrPayoff 1 n.val 0) type) =
      slice.conditionalPayoff opponents 1 (cfrPayoff 0)
        (pbsInformationCFR (reducedModel fullPrior) (slice.mixture own)
          pbsRootControlFallback cfrPayoff 1 2 0) type :=
  pbsInformationCFR_conditional_sampling_value (reducedModel fullPrior)
    (fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0)
    (fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0)
    pbsRootControlFallback cfrPayoff 1 2 opponents 1 (cfrPayoff 0) type supported

/-- A real budget-1/8 solve bounds the EXPECTATION OF ABSOLUTE native gaps,
not only the absolute mean. The bound requires no minimum own-type mass and
retains the actual budget-computed positive iteration count. -/
theorem pbsNativeConditionalGap_live_budget :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0
    let t := pbsInformationBudgetRounds (reducedModel fullPrior)
      (slice.mixture own).law (fun _ => 2) 1 (1 / 8)
    own.expect (fun type => (cfrIterationLaw t).expect (fun n =>
      |pbsInformationCFRConditionalDrawGap (reducedModel fullPrior) slice own
        pbsRootControlFallback cfrPayoff 1 t type n|)) ≤ 1 / 8 :=
  pbsInformationBudget_native_mean_abs_le (reducedModel fullPrior)
    (fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0)
    (fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0)
    pbsRootControlFallback 1 (fun h player => cfrPayoff player h)
    (cumulative_zeroSum fullPrior) 2 (by norm_num)
    (fun h player => cfrPayoff_abs_le_two player h) (1 / 8) (by norm_num)

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.ConditionalValueStability

open GameTheory.Math.Probability GameTheory.MatrixGame

/-- Every sampled opponent is an exact root equilibrium, yet its centered
conditional value has mean zero and mean absolute value one half. Thus exact
root Nash and signed cancellation cannot replace the fixed-opponent condition.
These are a necessary-hypothesis control, not asserted solver-generated iterates. -/
theorem nativeConditionalGap_changed_opponent_control :
    (∀ n : Fin 2,
      IsNash (form (Fin 2 → Unit) Bool).mixed (euPreference (utility driftMatrix))
        (mixedProfile (FinDist.pure (fun _ => ())) (FinDist.pure (n.val == 0)))) ∧
    |(cfrIterationLaw 2).expect (fun n =>
      TypeGame.infoValue driftPayoff (FinDist.pure (n.val == 0)) 0 - 1 / 2)| = 0 ∧
    (cfrIterationLaw 2).expect (fun n =>
      |TypeGame.infoValue driftPayoff (FinDist.pure (n.val == 0)) 0 - 1 / 2|) = 1 / 2 := by
  refine ⟨fun _ => drift_isNash _ _, ?_, ?_⟩
  · norm_num [FinDist.expect_eq_sum, Fin.sum_univ_two, cfrIterationLaw,
      FinDist.prob_ofWeights, TypeGame.infoValue, driftPayoff, FinDist.expect_pure]
  · norm_num [FinDist.expect_eq_sum, Fin.sum_univ_two, cfrIterationLaw,
      FinDist.prob_ofWeights, TypeGame.infoValue, driftPayoff, FinDist.expect_pure]

end GameTheory.ReBeL.Examples.ConditionalValueStability
