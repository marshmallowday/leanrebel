/-
# Canonical grouping in the hidden-type native chain

The actual finite sampled parent and native fresh queries are unchanged.
Grouping is analysis-only and retains private incumbent/PBS correlation.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveGroupedSecurity
import GameTheory.Analysis.ReBeL.Examples.CFRDRecursiveSecurity

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- All legal hidden-type histories, including off-path ones. -/
local instance groupedSecurityHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Full AOH action menus for the actual noisy parent. -/
local instance groupedSecurityChoice (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Noncomputable equality does not reveal the private iteration to the opponent. -/
local instance groupedSecurityInfo (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- A sampled finite parent with bias 1/8 and child loss 1/4 supplies its own
initial security. The reference only anchors the three-step game value.
The arbitrary unknown opponent's transport and support penalties remain. -/
theorem groupedSecurity_noisy_parent
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
        pbsRecursiveGroupedBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          plays unknown who 1 recursiveSecurityConfigs
          ((privateCarriedPrefix (model fullPrior) (cfrIterationLaw t) plays unknown who 1).map
            (enterCarriedMemory (model fullPrior)))) ≤
      (privateRecursiveResolve (model fullPrior) (cfrIterationLaw t) plays unknown who 1 1
        (recursiveSecurityConfigs.map
          (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
            plays))).expect (cfrPayoff who) := by
  exact cfrDRecursiveGrouped_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 1 1 recursiveSecurityConfigs 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    (fun _ _ _ _ => 1 / 8) (by intros; norm_num) reference equilibrium unknown who t
    recursiveSecurityConfigs_aligned

/-- This consumer includes a trained player decision before the fresh query.
It complements the previous consumer's positive retained-draw late tail. -/
theorem groupedSecurity_last_decision
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
        pbsRecursiveGroupedBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          plays unknown who 0 recursiveSecurityLastConfigs
          ((privateCarriedPrefix (model fullPrior) (cfrIterationLaw t) plays unknown who 2).map
            (enterCarriedMemory (model fullPrior)))) ≤
      (privateRecursiveResolve (model fullPrior) (cfrIterationLaw t) plays unknown who 2 0
        (recursiveSecurityLastConfigs.map
          (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
            plays))).expect (cfrPayoff who) := by
  exact cfrDRecursiveGrouped_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 0 recursiveSecurityLastConfigs 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    (fun _ _ _ _ => 1 / 8) (by intros; norm_num) reference equilibrium unknown who t
    recursiveSecurityLastConfigs_aligned


/-- The live-cell computational identities follow from the canonical key for
any actual hidden-type memory law, not from a supplied solver equality. -/
theorem groupedSecurity_key_compatible
    (plays : Unit → Profile (model fullPrior).behavioralSignature)
    (config : PBSRecursiveResolveConfig.{0})
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    PBSRecursiveGroupingCompatible (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      plays config states (pbsRecursiveNativeGroupKey (reducedModel fullPrior) plays config) id :=
  pbsRecursiveNativeGroupKey_compatible (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 plays config states

/-- An uncertified cell retains its exact signed value, even if it contains
stopped states or a missing PBS. It is not a free replacement. -/
theorem groupedSecurity_uncertified
    (plays : Unit → Profile (model fullPrior).behavioralSignature)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (config : PBSRecursiveResolveConfig.{0}) (remaining : Nat)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    pbsRecursiveGroupedCharge (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      plays unknown who config remaining states (fun _ => ()) (fun _ => none) =
    states.expect (fun state => pbsRecursiveRecomputedLoss (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2 plays unknown who config remaining state
        (cfrPayoff who)) :=
  pbsRecursiveGroupedCharge_none (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    plays unknown who config remaining states (fun _ => ())

/-- No fresh stages means no grouped charge, including a positive late tail. -/
theorem groupedSecurity_empty
    (plays : Unit → Profile (model fullPrior).behavioralSignature)
    (unknown : Profile (model fullPrior).behavioralSignature)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    pbsRecursiveGroupedBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      plays unknown 0 2 [] states = 0 := rfl

end GameTheory.ReBeL.Examples.HiddenTypes
