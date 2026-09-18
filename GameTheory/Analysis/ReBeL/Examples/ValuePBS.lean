/-
# Theorem 1 on the genuine two-stage hidden-type game

This example instantiates the full canonical PBS-to-value-to-geometry path.
The complete joint prior can be correlated, anticorrelated, or concentrated
on one hidden type. All legal behavioral deviations remain in the Nash domain.
The scalar geometry tests in ValueRadial and ValueKink are separate controls.
-/

import GameTheory.Analysis.ReBeL.PBSTheorem1
import GameTheory.ReBeL.Examples.PublicBelief
import GameTheory.ReBeL.Examples.Schedule

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol InformationModel GameTheory.Math.Probability

local instance valueHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- A legal total policy, supplied by the already validated original game. -/
def valueFallback (who : Player) : (model fullPrior).Policy who :=
  fullPlanPolicy fullPrior who (baselinePlans who)

/-- The theorem constructs an equilibrium and its concave extension for the
actual two remaining stages, not for a separately supplied payoff matrix. -/
theorem twoStage_joint_theorem1 (law : FinDist Types) :
    let slice := fullAOHBeliefSlice (reducedModel fullPrior) (drawBelief law) 0
    let own := fullAOHOwnLaw (reducedModel fullPrior) (drawBelief law) 0
    ∃ (profile : Profile (model fullPrior).behavioralSignature)
      (extension : (PublicRootType (reducedModel fullPrior)
        [Phase.first, Phase.initial] 0 → ℝ) → ℝ),
      IsNash (behavioralBeliefForm (model fullPrior) (drawBelief law) 2)
        (euPreference (cumulativeUtility (reward fullPrior))) profile ∧
      Set.EqOn extension
        (slice.value valueFallback 2 (fun history => cumulativeUtility (reward fullPrior) history 0))
        (stdSimplex ℝ (PublicRootType (reducedModel fullPrior)
          [Phase.first, Phase.initial] 0)) ∧
      ConcaveOn ℝ Set.univ extension ∧
      (∀ point, extension point ≤ extension own.prob +
        ∑ type, slice.centeredVector valueFallback 2
          (fun history => cumulativeUtility (reward fullPrior) history 0)
          own.prob profile type * (point type - own.prob type)) ∧
      (∀ type, slice.infoValue valueFallback 2
          (fun history => cumulativeUtility (reward fullPrior) history 0) profile type =
        expectedUtility (cumulativeUtility (reward fullPrior)) 0
          ((behavioralBeliefForm (model fullPrior) (drawBelief law) 2).play profile) +
        slice.centeredVector valueFallback 2
          (fun history => cumulativeUtility (reward fullPrior) history 0)
          own.prob profile type) :=
  theorem1_fullAOH (reducedModel fullPrior) (drawBelief law) valueFallback 2
    (cumulativeUtility (reward fullPrior)) (cumulative_zeroSum fullPrior)

/-- The factory reconstructs each correlated joint law, including a point
mass. Current support is not used to truncate the finite infostate domain. -/
theorem valueSlice_preserves_joint (law : FinDist Types) :
    (fullAOHBeliefSlice (reducedModel fullPrior) (drawBelief law) 0).mixture
      (fullAOHOwnLaw (reducedModel fullPrior) (drawBelief law) 0) = drawBelief law :=
  fullAOHBeliefSlice_eq (reducedModel fullPrior) (drawBelief law) 0

/-- Retaining just marginals would give a wrong downstream payoff. The two
factory outputs preserve the actual separation on the same game and public cut. -/
theorem valueSlice_correlation_control :
    (∀ who, (drawBelief correlated).marginal who =
      (drawBelief anticorrelated).marginal who) ∧
    (PublicBelief.continuationLaw (model fullPrior) pbsProfile 2
      ((fullAOHBeliefSlice (reducedModel fullPrior) (drawBelief correlated) 0).mixture
        (fullAOHOwnLaw (reducedModel fullPrior) (drawBelief correlated) 0))).expect
          (fun history => cumulativeUtility (reward fullPrior) history 0) = 2 ∧
    (PublicBelief.continuationLaw (model fullPrior) pbsProfile 2
      ((fullAOHBeliefSlice (reducedModel fullPrior) (drawBelief anticorrelated) 0).mixture
        (fullAOHOwnLaw (reducedModel fullPrior) (drawBelief anticorrelated) 0))).expect
          (fun history => cumulativeUtility (reward fullPrior) history 0) = 0 := by
  rw [valueSlice_preserves_joint, valueSlice_preserves_joint]
  exact ⟨drawBelief_same_marginals, drawBelief_payoff_separation⟩

end GameTheory.ReBeL.Examples.HiddenTypes
