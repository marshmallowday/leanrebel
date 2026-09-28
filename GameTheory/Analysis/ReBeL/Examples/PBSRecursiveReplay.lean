/-
# Recursive replay in the actual hidden-type game

These consumers keep allocated nonzero noise, factual joint roots, all late
fuel and the native private-profile/posterior pairing.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveCarriedReplay
import GameTheory.Analysis.ReBeL.Examples.PBSRecursiveDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Include every legal history of the canonical hidden-type protocol. -/
local instance replayHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Menus are the same finite classical subtypes used by the actual child. -/
local instance replayChoice (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Three-level private replay agrees from the concrete initial history. -/
theorem recursiveReplay_initial (tolerance : ℝ)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (fuel : Nat) :
    (pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [1, 1, 1] (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief tolerance).bind
        (fun chosen => (model fullPrior).runBehavioralFrom
          (Profile.update unknown who (chosen who)) fuel (protocol fullPrior).initHistory) =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (recursiveInitialProfile tolerance who))
        fuel (protocol fullPrior).initHistory := by
  apply pbsRecursiveDepthDraw_from_support (reducedModel fullPrior)
    pbsRecursiveAllocatedNoise [1, 1, 1] pbsRootControlFallback cfrPayoff 2
    recursiveInitialBelief tolerance unknown who fuel
  exact FinDist.mem_support_pure.mpr rfl

/-- The real composed child, with its exact mass-scaled target, can be replayed.
Support is exposed rather than replacing the actual root by the model mixture. -/
theorem recursiveReplay_factual_child (loss : ℝ) (obs : List (model fullPrior).PublicSignal)
    (possible : CFRDFactualChildPossible (reducedModel fullPrior) (carriedBitProfile false)
      2 1 obs)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (history : (protocol fullPrior).History)
    (supported : history ∈ (cfrDFactualChildBelief (reducedModel fullPrior)
      (carriedBitProfile false) 2 1 obs possible).law.support) (fuel : Nat) :
    (pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [1] (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2
      (cfrDFactualChildBelief (reducedModel fullPrior) (carriedBitProfile false) 2 1 obs possible)
      ((cfrDFactualChildBelief (reducedModel fullPrior) (carriedBitProfile false)
        2 1 obs possible).law.positiveMassFloor * loss)).bind
          (fun chosen => (model fullPrior).runBehavioralFrom
            (Profile.update unknown who (chosen who)) fuel history) =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (cfrDComposedChildProfile (reducedModel fullPrior)
          (carriedBitProfile false) pbsRootControlFallback 2 1 loss
          (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
            (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) who)) fuel history :=
  pbsRecursiveDepthDraw_composed_child (reducedModel fullPrior) pbsRecursiveAllocatedNoise
    [1] pbsRootControlFallback cfrPayoff 2 (carriedBitProfile false) 2 1 loss possible
    unknown who history supported fuel

/-- Completion changes only irrelevant own-zero-reach choices, even when the
opponent differs from the one used in the child's factual model. -/
theorem recursiveReplay_completion (loss : ℝ)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (fuel : Nat) :
    (model fullPrior).runBehavioral (Profile.update unknown who
      (cfrDComposedChildContinuation (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2)
        (fun h player => cfrPayoff player h) who)) fuel =
    (model fullPrior).runBehavioral (Profile.update unknown who
      (cfrDComposedChildProfile (reducedModel fullPrior) (carriedBitProfile false)
        pbsRootControlFallback 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) who)) fuel :=
  cfrDComposedChildContinuation_unilateral_run (reducedModel fullPrior)
    pbsRootControlFallback (carriedBitProfile false) 2 1 loss _ _ unknown who fuel

/-- Later solvers may read the private draw and stored posterior together. -/
theorem recursiveReplay_native_state (tolerance : ℝ)
    (plays : Unit → Profile (model fullPrior).behavioralSignature)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (fuel : Nat)
    (state : PrivateIterationState (model fullPrior) Unit)
    (outside : ¬ pbsCarriedCFRException (reducedModel fullPrior) fuel state) :
    carriedResolvedStep (model fullPrior) plays
      (pbsRecursiveDepthResolver pbsRecursiveAllocatedNoise [1, 1, 1]
        (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 tolerance plays)
      unknown who fuel state =
    pbsRecursiveHistoryFirstStep (reducedModel fullPrior) pbsRecursiveAllocatedNoise
      [1, 1, 1] pbsRootControlFallback cfrPayoff 2 tolerance plays unknown who fuel state :=
  pbsRecursiveDepthResolver_step_eq_historyFirst (reducedModel fullPrior)
    pbsRecursiveAllocatedNoise [1, 1, 1] pbsRootControlFallback cfrPayoff 2 tolerance
    plays unknown who fuel state outside

end GameTheory.ReBeL.Examples.HiddenTypes
