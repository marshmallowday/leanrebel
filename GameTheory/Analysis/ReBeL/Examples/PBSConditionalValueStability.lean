/-
# Conditional stability: a live solve and necessary-hypothesis controls

A genuine HiddenTypes information-set solve exercises current-opponent Eq. (1)
accuracy. A canonical finite type-plan zero-sum game shows why two different
opponents cannot be compared conditionally just from exact root Nash. The
inherited rare/absent-type controls retain the other necessary hypothesis.
-/

import GameTheory.Analysis.ReBeL.PBSConditionalValueStability
import GameTheory.Analysis.ReBeL.Examples.PBSRootDecode
import GameTheory.Analysis.ReBeL.Examples.CFRDApproximateLeaf

noncomputable section

namespace GameTheory.ReBeL.Examples.ConditionalValueStability

open GameTheory.Math.Probability GameTheory.MatrixGame

/-- The opponent can transfer one unit between two equally likely own types.
The row has no choice, so no illegal dependence on hidden opponent data occurs. -/
def driftPayoff (type : Fin 2) (_action : Unit) (opponent : Bool) : ℝ :=
  if opponent then if type = 0 then 1 else -1 else 0

/-- Compile complete type-local plans into the existing canonical game. -/
def driftMatrix : (Fin 2 → Unit) → Bool → ℝ :=
  TypeGame.matrix driftPayoff (fun _ => 1 / 2)

/-- Every root payoff is zero although the two conditional values can differ. -/
theorem driftMatrix_zero (plan : Fin 2 → Unit) (opponent : Bool) :
    driftMatrix plan opponent = 0 := by
  cases opponent <;> norm_num [driftMatrix, TypeGame.matrix, Fin.sum_univ_two, driftPayoff]

/-- The root equality covers arbitrary independent mixed deviations. -/
theorem drift_expected_zero (row : FinDist (Fin 2 → Unit)) (column : FinDist Bool) :
    expectedPayoff driftMatrix row column = 0 := by
  have zero : driftMatrix = fun _ _ => (0 : ℝ) := by
    funext plan opponent
    exact driftMatrix_zero plan opponent
  rw [expectedPayoff_eq_expect_rows, zero]
  simp only [expectedPayoff_pure_row, FinDist.expect_const]

/-- Every mixed profile is genuinely exact Nash in the canonical zero-sum game. -/
theorem drift_isNash (row : FinDist (Fin 2 → Unit)) (column : FinDist Bool) :
    IsNash (form (Fin 2 → Unit) Bool).mixed (euPreference (utility driftMatrix))
      (mixedProfile row column) := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  rcases (by decide : ∀ player : Fin 2, player = 0 ∨ player = 1) who with rfl | rfl
  · rw [mixedProfile_update_zero, expectedUtility_zero_mixedProfile,
      expectedUtility_zero_mixedProfile, drift_expected_zero, drift_expected_zero]
  · rw [mixedProfile_update_one, expectedUtility_one_mixedProfile,
      expectedUtility_one_mixedProfile, drift_expected_zero, drift_expected_zero]

/-- Positive mass and even exact Nash do not eliminate conditional vector drift
when opponents change. Both witnesses use the same own-type prior and payoff. -/
theorem different_opponents_conditional_counterexample :
    IsNash (form (Fin 2 → Unit) Bool).mixed (euPreference (utility driftMatrix))
      (mixedProfile (FinDist.pure (fun _ => ())) (FinDist.pure true)) ∧
    IsNash (form (Fin 2 → Unit) Bool).mixed (euPreference (utility driftMatrix))
      (mixedProfile (FinDist.pure (fun _ => ())) (FinDist.pure false)) ∧
    (0 : ℝ) < 1 / 2 ∧
    TypeGame.infoValue driftPayoff (FinDist.pure true) 0 -
      TypeGame.infoValue driftPayoff (FinDist.pure false) 0 = 1 := by
  refine ⟨drift_isNash _ _, drift_isNash _ _, by norm_num, ?_⟩
  norm_num [TypeGame.infoValue, driftPayoff, FinDist.expect_pure]

/-- The inverse-mass factor cannot be replaced by the root error: at p=1/4
there is a full canonical approximate equilibrium but a conditional gain of one. -/
theorem rare_type_quarter_control :
    IsNash (form (Fin 2 → Bool) Unit).mixed
      (euPreferenceWithin (1 / 4) (utility (ApproximateLeaf.rareMatrix (1 / 4))))
      (mixedProfile (FinDist.pure (fun _ => false)) (FinDist.pure ())) ∧
    (1 / 4 : ℝ) < ApproximateLeaf.rarePayoff 0 true () -
      ApproximateLeaf.rarePayoff 0 false () := by
  exact ⟨ApproximateLeaf.rare_approxNash (1 / 4) (by norm_num), by
    norm_num [ApproximateLeaf.rarePayoff]⟩

end GameTheory.ReBeL.Examples.ConditionalValueStability

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Preserve all physically legal histories, not only current posterior support. -/
local instance conditionalStabilityHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A live child is actually solved by information-set CFR with a positive
one-eighth root budget. Every supported full-AOH type receives the corresponding
inverse-mass conditional Eq. (1) guarantee against that solve's own opponents. -/
theorem pbsConditionalValueStability_live_budget
    (type : PublicRootType (reducedModel fullPrior)
      (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace) 0)
    (supported : type ∈
      (fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0).support) :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0
    let output := pbsInformationBudgetProfile (reducedModel fullPrior) (slice.mixture own)
      pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 (1 / 8)
    |slice.infoValue
        (fun who => liftPolicy (reducedModel fullPrior) who (pbsRootControlFallback who)) 1
        (cfrPayoff 0) output type -
      slice.conditionalPayoff output 1 (cfrPayoff 0) (output 0) type| ≤
      (1 / 8) / own.prob type :=
  pbsInformationBudgetProfile_infoGap_abs_le (reducedModel fullPrior)
    (fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0)
    (fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0)
    pbsRootControlFallback 1 (fun h who => cfrPayoff who h) (cumulative_zeroSum fullPrior)
    2 (by norm_num) (fun h who => cfrPayoff_abs_le_two who h) (1 / 8) (by norm_num)
    type supported

end GameTheory.ReBeL.Examples.HiddenTypes
