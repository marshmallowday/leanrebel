/-
# Constructive finite depth-budget controls

The canonical hidden-type game is solved at a real four-point joint PBS.
A genuinely nonzero predictor fits the allocated allowance, and the child loss
is positive. No equilibrium certificate or caller-selected iteration count
is supplied. Fixed 1/8 predictor bias and 1/4 child loss are tested separately.
-/

import GameTheory.Analysis.ReBeL.PBSInformationDepthBudget
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Reuse the existing exhaustive finite history model. -/
local instance allocatedDepthHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The actual game's error coefficient, not a freely chosen constant. -/
def allocatedDepthErrorFactor : ℝ :=
  pbsRootDepthErrorFactor (reducedModel fullPrior) depthControlBelief.law
    pbsRootControlFallback 1 1

/-- Half the positive numerical allowance is an actual nonzero prediction bias. -/
def allocatedDepthNoise (tolerance : ℝ) :
    PBSRootDepthNoise (reducedModel fullPrior) depthControlBelief.law :=
  fun _ _ _ _ => pbsDepthAllocationError allocatedDepthErrorFactor tolerance / 2

/-- The supplied predictor satisfies the derived allowance at every rooted query. -/
theorem allocatedDepthNoise_bounded (tolerance : ℝ) (positive : 0 < tolerance) :
    ∀ n trunk who info, |allocatedDepthNoise tolerance n trunk who info| ≤
      pbsDepthAllocationError allocatedDepthErrorFactor tolerance := by
  intro n trunk who info
  have allowance := pbsDepthAllocationError_pos allocatedDepthErrorFactor tolerance positive
  dsimp only [allocatedDepthNoise]
  rw [abs_of_pos (by positivity)]
  linarith

/-- Numerical perturbations are strictly positive, rather than an exact-oracle special case. -/
theorem allocatedDepthNoise_positive (tolerance : ℝ) (positive : 0 < tolerance) :
    ∀ n trunk who info, 0 < allocatedDepthNoise tolerance n trunk who info := by
  intro n trunk who info
  have allowance := pbsDepthAllocationError_pos allocatedDepthErrorFactor tolerance positive
  dsimp only [allocatedDepthNoise]
  positivity

/-- Computed rounds are nonempty even for an infeasible request; accuracy then
requires the separate feasibility condition rather than being silently asserted. -/
theorem allocatedDepth_rounds_nonempty (error loss tolerance : ℝ) :
    0 < pbsRootDepthBudgetRounds (reducedModel fullPrior) depthControlBelief.law
      pbsRootControlFallback 1 1 2 error loss tolerance :=
  Nat.zero_lt_succ _

/-- Positive target accuracy preserves positive numerical and child tolerances. -/
theorem allocatedDepth_positive_errors (tolerance : ℝ) (positive : 0 < tolerance) :
    0 < pbsDepthAllocationError allocatedDepthErrorFactor tolerance ∧
      0 < tolerance / 8 :=
  ⟨pbsDepthAllocationError_pos allocatedDepthErrorFactor tolerance positive, by positivity⟩

/-- All unilateral deviations satisfy the requested target with the computed
finite iteration count and the actual nonzero allocated predictor. -/
theorem allocatedDepth_nash (tolerance : ℝ) (positive : 0 < tolerance) :
    IsNash (behavioralBeliefForm (model fullPrior) depthControlBelief 2)
      (euPreferenceWithin tolerance (fun history who => cfrPayoff who history))
      (pbsInformationAllocatedDepthProfile (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 tolerance (allocatedDepthNoise tolerance)) := by
  apply pbsInformationAllocatedDepthProfile_isNash (reducedModel fullPrior) depthControlBelief
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 2 tolerance
    (by norm_num) positive cfrPayoff_abs_le_two
  exact allocatedDepthNoise_bounded tolerance positive

/-- An explicit quarter-accuracy instance still searches one round and solves
one child round; neither the game nor its predictor is replaced by an exact solution. -/
theorem allocatedDepth_quarter_nash :
    IsNash (behavioralBeliefForm (model fullPrior) depthControlBelief 2)
      (euPreferenceWithin (1 / 4) (fun history who => cfrPayoff who history))
      (pbsInformationAllocatedDepthProfile (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4) (allocatedDepthNoise (1 / 4))) :=
  allocatedDepth_nash (1 / 4) (by norm_num)

/-- Conditional child use scales accuracy by the actual joint law's mass floor.
The floor and every iteration count are constructed from the game, not assumed. -/
theorem allocatedDepth_conditional_nash :
    IsNash (behavioralBeliefForm (model fullPrior) depthControlBelief 2)
      (euPreferenceWithin (depthControlBelief.law.positiveMassFloor * (1 / 4))
        (fun history who => cfrPayoff who history))
      (pbsInformationConditionalDepthProfile (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (allocatedDepthNoise (depthControlBelief.law.positiveMassFloor * (1 / 4)))) := by
  apply pbsInformationConditionalDepthProfile_isNash (reducedModel fullPrior) depthControlBelief
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 2 (1 / 4)
    (by norm_num) (by norm_num) cfrPayoff_abs_le_two
  exact allocatedDepthNoise_bounded _
    (mul_pos (FinDist.positiveMassFloor_pos depthControlBelief.law) (by norm_num))

/-- Leave one unit of finite-iteration allowance after the original fixed errors. -/
def fixedDepthTarget : ℝ := allocatedDepthErrorFactor * (1 / 8) + 2 * (1 / 4) + 1

/-- The original 1/8 perturbation and 1/4 child loss survive the computed-round guarantee. -/
theorem allocatedDepth_fixed_noise_nash :
    IsNash (behavioralBeliefForm (model fullPrior) depthControlBelief 2)
      (euPreferenceWithin fixedDepthTarget (fun history who => cfrPayoff who history))
      (pbsInformationDepthBudgetProfile (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 8) (1 / 4) fixedDepthTarget
        (depthControlNoise depthControlBelief.law)) := by
  apply pbsInformationDepthBudgetProfile_isNash (reducedModel fullPrior) depthControlBelief
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 1 1 2 (1 / 8) (1 / 4)
    fixedDepthTarget (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
  · dsimp only [fixedDepthTarget, allocatedDepthErrorFactor]
    linarith
  · intro n trunk who info
    norm_num [depthControlNoise]

/-- A child tolerance above the target fails the allocation guard even when the
numerical coefficient is zero; extra iterations cannot remove this budget term. -/
theorem allocatedDepth_infeasible_guard :
    ¬ ((0 : ℝ) * (1 / 8) + 2 * (1 / 4) < 1 / 4) := by
  norm_num

end GameTheory.ReBeL.Examples.HiddenTypes
