/-
# Root target vector, actual noisy parent, and averaging controls

The hidden-type example uses the same finite-child parent as its execution
controls. A second two-coordinate trace distinguishes vector averaging from
last-iterate output without making a convergence assertion.
-/

import GameTheory.Analysis.ReBeL.CFRDValueTarget
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Exhaustive canonical history enumeration, including off-model histories. -/
local instance targetHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Nonzero prediction bias is propagated through the current learner's
backed-up, per-information-state vector and every finite uniform average. -/
theorem valueTarget_noisy_mean (t : Nat) [NeZero t]
    (type : (model fullPrior).InfoState 0) :
    let M := reducedModel fullPrior
    let roots := depthControlBelief.law
    |pbsRootDepthValueTargetMean M roots pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise roots) t 0 type -
      cfrDValueTargetMean (fun n tag =>
        cfrDDepthExactTarget (pbsRootFullInformation M roots)
          (fullObservationClock (pbsRootInformation (fullInformation M) roots))
          (pbsRootFallback M roots pbsRootControlFallback) (pbsRootPayoff roots cfrPayoff) 2 1
          (pbsRootDepthOracle M roots pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
            (depthControlNoise roots)) n 0 (pbsRootValueReadout M roots 0) (some tag)) t type| ≤
        1 / 8 := by
  intro M roots
  apply pbsRootDepthValueTargetMean_error M roots pbsRootControlFallback cfrPayoff
    1 1 2 (1 / 4) (depthControlNoise roots) (1 / 8) (by norm_num)
  intro n trunk who info
  norm_num [depthControlNoise]

/-- Different hidden worlds with the same own root AOH receive the same
target coordinate, even while the stored vector keeps distinct own types. -/
theorem valueTarget_no_hidden_leak (round : Nat) :
    pbsRootDepthValueTarget (reducedModel fullPrior) depthControlBelief.law
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise depthControlBelief.law) round 0
        ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) =
      pbsRootDepthValueTarget (reducedModel fullPrior) depthControlBelief.law
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise depthControlBelief.law) round 0
        ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) := rfl

/-- An explicit two-coordinate trace for target accumulation only. It is not
claimed to be a CFR trajectory or an equilibrium convergence example. -/
def targetVectorControl (round : Nat) (type : Bool) : ℝ :=
  if type then 4 * round + 2 else 2 * round - 1

/-- Uniform accumulation retains both coordinates and differs from the last
vector. Replacing a vector by a scalar or by the final round fails this control. -/
theorem valueTarget_vector_control :
    cfrDValueTargetMean targetVectorControl 2 false = 0 ∧
      cfrDValueTargetMean targetVectorControl 2 true = 4 ∧
      targetVectorControl 1 false = 1 ∧ targetVectorControl 1 true = 6 := by
  norm_num [cfrDValueTargetMean_eq_sum, targetVectorControl, Finset.sum_range_succ]

end GameTheory.ReBeL.Examples.HiddenTypes
