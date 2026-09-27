/-
# Recursive search returns a policy and a root information-value vector

These controls instantiate the actual three-level hidden-type solver, its
nonzero allocated noise and a zero-width cut. No supplied child solver or
per-round Nash certificate is used.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveValueTarget
import GameTheory.Analysis.ReBeL.Examples.PBSRecursiveDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Retain the canonical finite legal-history enumeration. -/
local instance recursiveTargetHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The policy component is exactly the existing three-level solver. -/
theorem recursiveTraining_policy (tolerance : ℝ) :
    (pbsRecursiveTrainingOutput (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      recursiveInitialBelief pbsRecursiveAllocatedNoise [1, 1, 1] tolerance).1 =
      recursiveInitialProfile tolerance := rfl

/-- The same output has an all-deviation policy guarantee and a conditional
value-vector error guarantee at each root information state. -/
theorem recursiveTraining_correct (tolerance : ℝ) (positive : 0 < tolerance) :
    IsNash (behavioralBeliefForm (model fullPrior) recursiveInitialBelief 3)
        (euPreferenceWithin tolerance (fun h who => cfrPayoff who h))
        (pbsRecursiveTrainingOutput (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          recursiveInitialBelief pbsRecursiveAllocatedNoise [1, 1, 1] tolerance).1 ∧
      ∀ who type,
        |(pbsRecursiveTrainingOutput (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
            recursiveInitialBelief pbsRecursiveAllocatedNoise [1, 1, 1] tolerance).2 who type -
          cfrDValueTargetMean (fun n =>
            pbsRecursiveOriginalRound (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
              recursiveInitialBelief pbsRecursiveAllocatedNoise [1, 1, 1] tolerance n who)
            (pbsRecursiveTargetRounds (reducedModel fullPrior) pbsRootControlFallback 2
              recursiveInitialBelief [1, 1, 1] tolerance) type| ≤
          pbsRecursiveTargetError (reducedModel fullPrior) pbsRootControlFallback
            recursiveInitialBelief [1, 1, 1] tolerance :=
  pbsRecursiveTrainingOutput_correct (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    recursiveInitialBelief pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    [1, 1, 1] (cumulative_zeroSum fullPrior) (by norm_num) cfrPayoff_abs_le_two
    tolerance positive

/-- A zero-width first cut still returns a vector from the same recursively
computed continuation, with all three original transitions in the comparator. -/
theorem recursiveTraining_zero_cut_error (tolerance : ℝ) (positive : 0 < tolerance)
    (who : Player) (type : (model fullPrior).InfoState who) :
    |pbsRecursiveValueTarget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
        recursiveInitialBelief pbsRecursiveAllocatedNoise [0, 1, 1, 1] tolerance who type -
      cfrDValueTargetMean (fun n =>
        pbsRecursiveOriginalRound (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          recursiveInitialBelief pbsRecursiveAllocatedNoise [0, 1, 1, 1] tolerance n who)
        (pbsRecursiveTargetRounds (reducedModel fullPrior) pbsRootControlFallback 2
          recursiveInitialBelief [0, 1, 1, 1] tolerance) type| ≤
      pbsRecursiveTargetError (reducedModel fullPrior) pbsRootControlFallback
        recursiveInitialBelief [0, 1, 1, 1] tolerance :=
  pbsRecursiveValueTarget_error (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    recursiveInitialBelief pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    [0, 1, 1, 1] tolerance positive who type

/-- The empty schedule computes the current conditional payoff without noise
or a child query, even for a total off-support coordinate. -/
theorem recursiveTraining_empty (tolerance : ℝ) (who : Player)
    (type : (model fullPrior).InfoState who) :
    pbsRecursiveValueTarget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
        recursiveInitialBelief pbsRecursiveAllocatedNoise [] tolerance who type =
      conditionalOracleValue recursiveInitialBelief.law
        (fun h => (model fullPrior).infoOf who h.trace) (cfrPayoff who) type :=
  pbsRecursiveValueTarget_nil (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    recursiveInitialBelief pbsRecursiveAllocatedNoise tolerance who type

end GameTheory.ReBeL.Examples.HiddenTypes
