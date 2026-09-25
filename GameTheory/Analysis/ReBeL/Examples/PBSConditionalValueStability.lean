/-
# Conditional stability: a live solve and necessary-hypothesis controls

A genuine HiddenTypes information-set solve exercises current-opponent Eq. (1)
accuracy. A canonical finite type-plan zero-sum game shows why two different
opponents cannot be compared conditionally just from exact root Nash. The
inherited rare/absent-type controls retain the other necessary hypothesis.
Query-law controls distinguish mean error from uniform oracle accuracy.
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

/-- The rare-type control as an actual finite probability law, including its
normalization proof. It reuses the canonical quarter-error game above. -/
def rareQueryPrior : FinDist (Fin 2) :=
  FinDist.ofWeights (ApproximateLeaf.rareWeight (1 / 4))
    (ApproximateLeaf.rareWeight_simplex (1 / 4) (by norm_num) (by norm_num)).1
    (ApproximateLeaf.rareWeight_simplex (1 / 4) (by norm_num) (by norm_num)).2

/-- In this control the always-true plan attains each conditional optimum. -/
theorem rareQuery_infoValue (type : Fin 2) :
    TypeGame.infoValue ApproximateLeaf.rarePayoff (FinDist.pure ()) type =
      ApproximateLeaf.rarePayoff type true () := by
  apply le_antisymm
  · rw [TypeGame.infoValue, FinDist.expect_pure]
    by_cases zero : type = 0
    · simp only [ApproximateLeaf.rarePayoff, if_pos zero, if_true]
      cases TypeGame.typeResponse ApproximateLeaf.rarePayoff (FinDist.pure ()) type <;> norm_num
    · simp [ApproximateLeaf.rarePayoff, zero]
  · simpa only [FinDist.expect_pure] using
      TypeGame.le_infoValue ApproximateLeaf.rarePayoff (FinDist.pure ()) type true

/-- Concentrating queries on the rare type multiplies its mass by four. -/
theorem rareQuery_density (type : Fin 2) :
    (FinDist.pure (0 : Fin 2)).prob type =
      rareQueryPrior.prob type * (if type = 0 then 4 else 0) := by
  fin_cases type <;>
    norm_num [rareQueryPrior, FinDist.prob_pure_eq_ite, FinDist.prob_ofWeights,
      ApproximateLeaf.rareWeight]

/-- The factor four is necessary for MEAN error: actual root approximate Nash
has mean conditional error 1/4, but the dominated query law sees error one.
This is not a counterexample to preservation of a UNIFORM oracle error. -/
theorem rareQuery_amplification :
    IsNash (form (Fin 2 → Bool) Unit).mixed
      (euPreferenceWithin (1 / 4) (utility (ApproximateLeaf.rareMatrix (1 / 4))))
      (mixedProfile (FinDist.pure (fun _ => false)) (FinDist.pure ())) ∧
    rareQueryPrior.expect (fun type =>
      |TypeGame.infoValue ApproximateLeaf.rarePayoff (FinDist.pure ()) type -
        ApproximateLeaf.rarePayoff type false ()|) = 1 / 4 ∧
    (FinDist.pure (0 : Fin 2)).expect (fun type =>
      |TypeGame.infoValue ApproximateLeaf.rarePayoff (FinDist.pure ()) type -
        ApproximateLeaf.rarePayoff type false ()|) = 4 * (1 / 4) ∧
    ¬ (FinDist.pure (0 : Fin 2)).expect (fun type =>
      |TypeGame.infoValue ApproximateLeaf.rarePayoff (FinDist.pure ()) type -
        ApproximateLeaf.rarePayoff type false ()|) ≤ 1 / 4 := by
  refine ⟨ApproximateLeaf.rare_approxNash (1 / 4) (by norm_num), ?_, ?_, ?_⟩
  · norm_num [FinDist.expect_eq_sum, Fin.sum_univ_two, rareQueryPrior,
      FinDist.prob_ofWeights, rareQuery_infoValue, ApproximateLeaf.rareWeight,
      ApproximateLeaf.rarePayoff]
  · norm_num [FinDist.expect_pure, rareQuery_infoValue, ApproximateLeaf.rarePayoff]
  · norm_num [FinDist.expect_pure, rareQuery_infoValue, ApproximateLeaf.rarePayoff]

/-- A newly queried absent type has no finite density against the old law.
The query theorem cannot silently certify an off-path conditional value. -/
theorem absent_query_not_dominated :
    ¬ ∃ ratio : Fin 2 → ℝ, ∀ type,
      (FinDist.pure (0 : Fin 2)).prob type =
        (FinDist.pure (1 : Fin 2)).prob type * ratio type := by
  rintro ⟨ratio, density⟩
  have impossible := density 0
  norm_num [FinDist.prob_pure_eq_ite] at impossible

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

/-- The live information-set solve controls its mean conditional absolute gap
under its actual own-type law, with density one. No inverse mass floor or
supported-type premise is needed for this expectation statement. -/
theorem pbsConditionalValueStability_live_mean_budget :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0
    let output := pbsInformationBudgetProfile (reducedModel fullPrior) (slice.mixture own)
      pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 (1 / 8)
    own.expect (fun type =>
      |slice.infoValue
          (fun who => liftPolicy (reducedModel fullPrior) who (pbsRootControlFallback who)) 1
          (cfrPayoff 0) output type -
        slice.conditionalPayoff output 1 (cfrPayoff 0) (output 0) type|) ≤ 1 / 8 := by
  simpa only [one_mul] using
    pbsInformationBudgetProfile_reweighted_infoGap_abs_le (reducedModel fullPrior)
      (fullAOHBeliefSlice (reducedModel fullPrior) finiteBudgetControlBelief 0)
      (fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0)
      pbsRootControlFallback 1 (fun h who => cfrPayoff who h) (cumulative_zeroSum fullPrior)
      2 (by norm_num) (fun h who => cfrPayoff_abs_le_two who h) (1 / 8) (by norm_num)
      (fullAOHOwnLaw (reducedModel fullPrior) finiteBudgetControlBelief 0)
      (fun _ => 1) 1 (by norm_num) (fun _ => (mul_one _).symm) (fun _ _ => le_rfl)

end GameTheory.ReBeL.Examples.HiddenTypes
