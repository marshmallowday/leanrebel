/-
# Fixed-trace average limits in the canonical hidden-type game

The ideal live-child oracle has vanishing Nash error. The actual finite
recursive parent keeps its positive child tolerance and prediction allowance.
Neither statement asserts convergence of the final selected policy.
-/

import GameTheory.Analysis.ReBeL.PBSAverageLimit
import GameTheory.Analysis.ReBeL.Examples.CFRDExactDriver
import GameTheory.Analysis.ReBeL.Examples.PBSRecursiveDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate every legal original history for the all-deviation bound. -/
local instance limitHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Information equality remains local and does not reveal the hidden world. -/
local instance limitInfo (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Active and inactive legal action menus are both finite. -/
local instance limitChoice (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- A real live child remains outside the searched two-step trunk. The same
constructed exact oracle generates every average in this epsilon-N statement. -/
theorem exactDriverAverage_converges :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ threshold : Nat, 0 < threshold ∧
      ∀ t : Nat, threshold ≤ t →
        IsNash ((model fullPrior).toBehavioralGameForm 3)
          (euPreferenceWithin epsilon (fun h who => cfrPayoff who h))
          (cfrDDepthAveragedProfile (model fullPrior)
            (fullObservationClock (reducedModel fullPrior))
            cfrFallback cfrPayoff 2 1 exactDriverControlOracle (t + 1)) :=
  cfrDConstructedExactAverage_converges (reducedModel fullPrior) cfrFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 (by norm_num) cfrPayoff_abs_le_two

/-- The generalized outer-count family includes the original three-level
computed solver exactly at its allocated finite count. -/
theorem recursiveAverage_allocated (tolerance : ℝ) :
    pbsRecursiveParentAverage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
        recursiveInitialBelief pbsRecursiveAllocatedNoise 1 [1, 1] tolerance
        (pbsRootDepthBudgetRounds (reducedModel fullPrior) recursiveInitialBelief.law
          pbsRootControlFallback 1 2 2
          (pbsDepthAllocationError
            (pbsRootDepthErrorFactor (reducedModel fullPrior) recursiveInitialBelief.law
              pbsRootControlFallback 1 2) tolerance)
          (tolerance / 8) tolerance) =
      recursiveInitialProfile tolerance :=
  pbsRecursiveParentAverage_allocated (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 recursiveInitialBelief pbsRecursiveAllocatedNoise 1 [1, 1] tolerance

/-- Arbitrarily late averages of the actual recursive parent retain its
nonzero noise and child tolerance. Only the finite outer term shrinks. -/
theorem recursiveAverage_after (tolerance epsilon : ℝ)
    (htol : 0 < tolerance) (positive : 0 < epsilon) (t : Nat) [NeZero t]
    (large : cfrDAverageThreshold
      (pbsRootDepthFiniteFactor (reducedModel fullPrior) recursiveInitialBelief.law
        pbsRootControlFallback 1 2 2) epsilon ≤ t) :
    IsNash (behavioralBeliefForm (model fullPrior) recursiveInitialBelief 3)
      (euPreferenceWithin
        (pbsRootDepthErrorFactor (reducedModel fullPrior) recursiveInitialBelief.law
            pbsRootControlFallback 1 2 *
          pbsDepthAllocationError
            (pbsRootDepthErrorFactor (reducedModel fullPrior) recursiveInitialBelief.law
              pbsRootControlFallback 1 2) tolerance +
          2 * (tolerance / 8) + epsilon) (fun h who => cfrPayoff who h))
      (pbsRecursiveParentAverage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
        recursiveInitialBelief pbsRecursiveAllocatedNoise 1 [1, 1] tolerance t) :=
  pbsRecursiveParentAverage_after (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    recursiveInitialBelief pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    1 [1, 1] (cumulative_zeroSum fullPrior) (by norm_num) cfrPayoff_abs_le_two
    tolerance epsilon htol positive t large

/-- Zero finite coefficient needs a nonempty mean, but no division by zero. -/
theorem averageThreshold_zero (epsilon : ℝ) :
    cfrDAverageThreshold 0 epsilon = 1 := by
  norm_num [cfrDAverageThreshold]

end GameTheory.ReBeL.Examples.HiddenTypes
