/-
# Recursive PBS solver controls in the canonical hidden-type game

Three scheduled transitions retain the original chance draw and both real
player-decision stages. The constructed noise is positive at every positive
allocated query. Empty schedules, zero-width cuts, all behavioral deviations,
hidden-information locality and zero-own-reach completion remain explicit.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveDepth
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationChild

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Use every legal history, not just histories reached by the candidate policy. -/
local instance recursiveHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The joint initial PBS precedes chance and the two real decision stages. -/
def recursiveInitialBelief : PublicBelief (model fullPrior).toInfoSignals
    (publicTrace (model fullPrior).toInfoSignals (protocol fullPrior).initHistory.trace) where
  law := FinDist.pure (protocol fullPrior).initHistory
  supported h hs := by
    rw [FinDist.mem_support_pure.mp hs]

/-- Three actual recursive levels; no full-root child backend is supplied. -/
def recursiveInitialProfile (tolerance : ℝ) : Profile (model fullPrior).behavioralSignature :=
  pbsRecursiveDepth pbsRecursiveAllocatedNoise [1, 1, 1] (protocol fullPrior)
    (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief tolerance

/-- Accuracy is derived for every positive request, including arbitrary
randomized behavioral replacements, with no child-optimality input. -/
theorem recursiveInitial_isNash (tolerance : ℝ) (positive : 0 < tolerance) :
    IsNash (behavioralBeliefForm (model fullPrior) recursiveInitialBelief 3)
      (euPreferenceWithin tolerance (fun h who => cfrPayoff who h))
      (recursiveInitialProfile tolerance) := by
  simpa only [List.sum_cons, List.sum_nil, recursiveInitialProfile] using
    pbsRecursiveDepth_isNash pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
      [1, 1, 1] (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      (cumulative_zeroSum fullPrior) 2 (by norm_num) cfrPayoff_abs_le_two
      recursiveInitialBelief tolerance positive

/-- A fresh randomized deviation is covered in the original history game. -/
theorem recursiveInitial_randomized_gain (tolerance : ℝ) (positive : 0 < tolerance) :
    (PublicBelief.continuationLaw (model fullPrior)
      (Profile.update (recursiveInitialProfile tolerance) 0 freshBitPolicy) 3
      recursiveInitialBelief).expect (cfrPayoff 0) ≤
    (PublicBelief.continuationLaw (model fullPrior) (recursiveInitialProfile tolerance) 3
      recursiveInitialBelief).expect (cfrPayoff 0) + tolerance := by
  have equilibrium := recursiveInitial_isNash tolerance positive
  rw [isNash_iff] at equilibrium
  exact equilibrium 0 freshBitPolicy

/-- The produced policy cannot read the other player's hidden bit. -/
theorem recursiveInitial_no_hidden_leak (tolerance : ℝ) :
    recursiveInitialProfile tolerance 0
      ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) =
    recursiveInitialProfile tolerance 0
      ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) := rfl

/-- An empty cut schedule does not call any full-game solver. -/
theorem recursiveInitial_empty (tolerance : ℝ) :
    pbsRecursiveDepth pbsRecursiveAllocatedNoise [] (protocol fullPrior) (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief tolerance =
        (fun who => (informationControlFullFallback who).toBehavioral) := rfl

/-- A zero-width cut still terminates by structural list recursion and retains
all three original transitions; it is not counted as a player decision. -/
theorem recursiveInitial_zero_cut (tolerance : ℝ) (positive : 0 < tolerance) :
    IsNash (behavioralBeliefForm (model fullPrior) recursiveInitialBelief 3)
      (euPreferenceWithin tolerance (fun h who => cfrPayoff who h))
      (pbsRecursiveDepth pbsRecursiveAllocatedNoise [0, 1, 1, 1] (protocol fullPrior)
        (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief tolerance) := by
  simpa only [List.sum_cons, List.sum_nil] using
    pbsRecursiveDepth_isNash pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
      [0, 1, 1, 1] (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      (cumulative_zeroSum fullPrior) 2 (by norm_num) cfrPayoff_abs_le_two
      recursiveInitialBelief tolerance positive

/-- The concrete parent's perturbation really uses a positive allowance. -/
theorem recursiveInitial_noise_positive (tolerance : ℝ) (positive : 0 < tolerance)
    (n : Nat) (trunk) (who : Fin 2) (info) :
    0 < pbsRecursiveAllocatedNoise (protocol fullPrior) (reducedModel fullPrior)
      recursiveInitialBelief.law (pbsDepthAllocationError
        (pbsRootDepthErrorFactor (reducedModel fullPrior) recursiveInitialBelief.law
          pbsRootControlFallback 1 2) tolerance) n trunk who info :=
  pbsDepthAllocationError_pos _ tolerance positive

/-- The factual-child adapter can consume the proved recursive solver and
complete zero-own-reach queries without accepting any child Nash certificate. -/
theorem recursiveChild_leafOptimal (loss : ℝ) (positive : 0 < loss) (who : Player) :
    CFRDLeafOptimal (model fullPrior)
      (cfrDComposedChildContinuation (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2)
        (fun h player => cfrPayoff player h))
      informationControlFullFallback who (cfrPayoff who) 2 1 loss := by
  apply cfrDComposedChildContinuation_leafOptimal (reducedModel fullPrior)
    (carriedBitProfile false) pbsRootControlFallback 2 1 loss positive
  intro obs belief tolerance targetPositive
  simpa only [List.sum_cons, List.sum_nil] using
    pbsRecursiveDepth_isNash pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
      [1] (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      (cumulative_zeroSum fullPrior) 2 (by norm_num) cfrPayoff_abs_le_two
      belief tolerance targetPositive

/-- A sampled actual parent with recursive children realizes the full original
history law against any fixed unknown opponent, not just a payoff scalar. -/
theorem recursiveInitial_sample_law (tolerance : ℝ)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (steps : Nat) :
    (pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [1, 1, 1] (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief tolerance).bind
        (fun chosen => recursiveInitialBelief.law.bind ((model fullPrior).runBehavioralFrom
          (Profile.update unknown who (chosen who)) steps)) =
      recursiveInitialBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (recursiveInitialProfile tolerance who)) steps) :=
  pbsRecursiveDepthDraw_law pbsRecursiveAllocatedNoise [1, 1, 1] (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief tolerance unknown who steps

/-- An absent posterior retains the incumbent, even for an impossible observation. -/
theorem recursiveInitial_missing_belief (tolerance : ℝ)
    (observations : List (model fullPrior).PublicSignal) :
    pbsRecursiveDepthResolver pbsRecursiveAllocatedNoise [1, 1, 1] (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2 tolerance (fun _ : Unit => carriedBitProfile false)
      () observations none = FinDist.pure (carriedBitProfile false) := rfl

/-- Zero execution fuel preserves every actual history and bypasses the solver. -/
theorem recursiveInitial_zero_execution (tolerance : ℝ)
    (initial : Unit → Profile (model fullPrior).behavioralSignature)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (state : PrivateIterationState (model fullPrior) (CarriedResolveMemory (model fullPrior) Unit)) :
    (carriedMemoryStep (model fullPrior) initial unknown who
      (pbsRecursiveDepthStage pbsRecursiveAllocatedNoise [1, 1, 1] (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 2 tolerance 0 initial) state).map
          (fun next => next.history) = FinDist.pure state.history :=
  pbsRecursiveDepthStage_zero_history pbsRecursiveAllocatedNoise [1, 1, 1] (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 2 tolerance initial unknown who state

end GameTheory.ReBeL.Examples.HiddenTypes
