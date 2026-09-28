/-
# Noisy sampled parent followed by a fresh native solve

The initial parent trains for finite T. Its private iteration is carried into
a fresh two-level solver and a positive late tail. No initial-security
certificate or child Nash certificate is supplied by these consumers.
-/

import GameTheory.Analysis.ReBeL.CFRDRecursiveSecurity
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationSampledDriver
import GameTheory.Analysis.ReBeL.Examples.PBSRecursiveDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- All legal hidden-type histories, including off-path ones. -/
local instance recursiveSecurityHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Full AOH action menus for the actual noisy parent. -/
local instance recursiveSecurityChoice (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Noncomputable equality does not reveal the private iteration to the opponent. -/
local instance recursiveSecurityInfo (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- One fresh two-level solve covers one stage and one retained-draw late step. -/
def recursiveSecurityConfigs : List PBSRecursiveResolveConfig.{0} :=
  [⟨pbsRecursiveAllocatedNoise, [1, 1], 1 / 8, 1⟩]

/-- Positive tolerance, actual numerical contract and the full two-step horizon. -/
theorem recursiveSecurityConfigs_aligned :
    PBSRecursiveNashAligned 1 recursiveSecurityConfigs :=
  ⟨pbsRecursiveAllocatedNoise_bounded, by norm_num, rfl, True.intro⟩

/-- A sampled finite parent with bias 1/8 and child loss 1/4 supplies its own
initial security. The reference only anchors the three-step game value.
The arbitrary unknown opponent's transport and support penalties remain. -/
theorem recursiveSecurity_noisy_parent
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h player => cfrPayoff player h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    let plays := fun n : Fin t => cfrDDepthPlay (model fullPrior)
      (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback cfrPayoff 1 2
      (cfrDConstructedSampledInformationOracle (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 1 2 2 (1 / 4) (fun _ _ _ _ => 1 / 8)) n.val
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff who) -
      (cfrDDepthAverageErrorFloor (model fullPrior)
          (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback
          1 2 (1 / 8) (1 / 4) +
        cfrDDepthAverageFiniteFactor (model fullPrior)
          (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback
          1 2 2 / Real.sqrt t +
        pbsRecursiveNashBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          plays unknown who 1 recursiveSecurityConfigs
          ((privateCarriedPrefix (model fullPrior) (cfrIterationLaw t) plays unknown who 1).map
            (enterCarriedMemory (model fullPrior)))) ≤
      (privateRecursiveResolve (model fullPrior) (cfrIterationLaw t) plays unknown who 1 1
        (recursiveSecurityConfigs.map
          (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
            plays))).expect (cfrPayoff who) := by
  exact cfrDRecursiveNash_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 1 1 recursiveSecurityConfigs 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    (fun _ _ _ _ => 1 / 8) (by intros; norm_num) reference equilibrium unknown who t
    recursiveSecurityConfigs_aligned

/-- A parent with an actual player decision in its trunk, followed by the
last decision's fresh solve; there is no extra late step after termination. -/
def recursiveSecurityLastConfigs : List PBSRecursiveResolveConfig.{0} :=
  [⟨pbsRecursiveAllocatedNoise, [1], 1 / 8, 1⟩]

/-- The last fresh solve covers precisely the remaining single decision. -/
theorem recursiveSecurityLastConfigs_aligned :
    PBSRecursiveNashAligned 0 recursiveSecurityLastConfigs :=
  ⟨pbsRecursiveAllocatedNoise_bounded, by norm_num, rfl, True.intro⟩

/-- This consumer includes a trained player decision before the fresh query.
It complements the previous consumer's positive retained-draw late tail. -/
theorem recursiveSecurity_last_decision
    (reference : Profile (model fullPrior).behavioralSignature)
    (equilibrium : IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreference (fun h player => cfrPayoff player h)) reference)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (t : Nat) [NeZero t] :
    let plays := fun n : Fin t => cfrDDepthPlay (model fullPrior)
      (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback cfrPayoff 2 1
      (cfrDConstructedSampledInformationOracle (reducedModel fullPrior) pbsRootControlFallback
        cfrPayoff 2 1 2 (1 / 4) (fun _ _ _ _ => 1 / 8)) n.val
    ((model fullPrior).runBehavioral reference 3).expect (cfrPayoff who) -
      (cfrDDepthAverageErrorFloor (model fullPrior)
          (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback
          2 1 (1 / 8) (1 / 4) +
        cfrDDepthAverageFiniteFactor (model fullPrior)
          (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback
          2 1 2 / Real.sqrt t +
        pbsRecursiveNashBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          plays unknown who 0 recursiveSecurityLastConfigs
          ((privateCarriedPrefix (model fullPrior) (cfrIterationLaw t) plays unknown who 2).map
            (enterCarriedMemory (model fullPrior)))) ≤
      (privateRecursiveResolve (model fullPrior) (cfrIterationLaw t) plays unknown who 2 0
        (recursiveSecurityLastConfigs.map
          (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
            plays))).expect (cfrPayoff who) := by
  exact cfrDRecursiveNash_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 0 recursiveSecurityLastConfigs 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    (fun _ _ _ _ => 1 / 8) (by intros; norm_num) reference equilibrium unknown who t
    recursiveSecurityLastConfigs_aligned

/-- At exact numerical predictions the finite parent term and twice the
positive child loss remain. This is not an attained-error lower bound. -/
theorem recursiveSecurity_exact_prediction (t : Nat) :
    cfrDDepthAverageErrorFloor (model fullPrior)
        (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback
        2 1 0 (1 / 4) +
      cfrDDepthAverageFiniteFactor (model fullPrior)
        (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback
        2 1 2 / Real.sqrt t =
    cfrDDepthAverageFiniteFactor (model fullPrior)
        (fullObservationClock (reducedModel fullPrior)) informationControlFullFallback
        2 1 2 / Real.sqrt t + 2 * (1 / 4 : ℝ) :=
  cfrDRecursive_zero_prediction_allowance (reducedModel fullPrior)
    pbsRootControlFallback 2 1 2 (1 / 4) t

/-- With no fresh stages the new charge is zero even with a positive late tail.
This identity does not remove the parent's finite regret or child loss. -/
theorem recursiveSecurity_empty_budget
    (plays : Unit → Profile (model fullPrior).behavioralSignature)
    (unknown : Profile (model fullPrior).behavioralSignature)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    pbsRecursiveRecomputedBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      plays unknown 0 2 (cfrPayoff 0) 2 [] states = 0 ∧
    pbsRecursiveNashBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      plays unknown 0 2 [] states = 0 :=
  ⟨rfl, rfl⟩

end GameTheory.ReBeL.Examples.HiddenTypes
