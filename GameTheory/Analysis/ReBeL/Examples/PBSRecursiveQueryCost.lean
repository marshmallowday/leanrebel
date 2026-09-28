/-
# Actual query costs in the hidden-type native chain

The actual finite sampled parent and native fresh queries are unchanged.
Grouping is analysis-only and retains private incumbent/PBS correlation.
-/

import GameTheory.Analysis.ReBeL.CFRDRecursiveQuerySecurity
import GameTheory.Analysis.ReBeL.Examples.CFRDRecursiveSecurity

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- All legal hidden-type histories, including off-path ones. -/
local instance queryCostHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Full AOH action menus for the actual noisy parent. -/
local instance queryCostChoice (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Noncomputable equality does not reveal the private iteration to the opponent. -/
local instance queryCostInfo (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- A sampled finite parent with bias 1/8 and child loss 1/4 supplies its own
initial security. The reference only anchors the three-step game value.
The arbitrary unknown opponent's transport and support penalties remain. -/
theorem queryCost_noisy_parent
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
        min (pbsRecursiveGroupedBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
          plays unknown who 1 recursiveSecurityConfigs
          ((privateCarriedPrefix (model fullPrior) (cfrIterationLaw t) plays unknown who 1).map
            (enterCarriedMemory (model fullPrior))))
          ((2 - (-2 : ℝ)) * pbsRecursiveQueryVisits (reducedModel fullPrior)
            pbsRootControlFallback cfrPayoff 2 plays unknown who recursiveSecurityConfigs
            ((privateCarriedPrefix (model fullPrior) (cfrIterationLaw t) plays unknown who 1).map
              (enterCarriedMemory (model fullPrior))))) ≤
      (privateRecursiveResolve (model fullPrior) (cfrIterationLaw t) plays unknown who 1 1
        (recursiveSecurityConfigs.map
          (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
            plays))).expect (cfrPayoff who) := by
  exact cfrDRecursiveQuery_capped_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 1 1 recursiveSecurityConfigs 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    (fun _ _ _ _ => 1 / 8) (by intros; norm_num) reference equilibrium unknown who t
    recursiveSecurityConfigs_aligned (-2) 2
    (fun h => (abs_le.mp (cfrPayoff_abs_le_two who h)).1)
    (fun h => (abs_le.mp (cfrPayoff_abs_le_two who h)).2)

/-- This consumer includes a trained player decision before the fresh query.
It complements the previous consumer's positive retained-draw late tail. -/
theorem queryCost_last_decision
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
        (2 - (-2 : ℝ)) * pbsRecursiveQueryVisits (reducedModel fullPrior)
          pbsRootControlFallback cfrPayoff 2 plays unknown who recursiveSecurityLastConfigs
          ((privateCarriedPrefix (model fullPrior) (cfrIterationLaw t) plays unknown who 2).map
            (enterCarriedMemory (model fullPrior)))) ≤
      (privateRecursiveResolve (model fullPrior) (cfrIterationLaw t) plays unknown who 2 0
        (recursiveSecurityLastConfigs.map
          (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
            plays))).expect (cfrPayoff who) := by
  exact cfrDRecursiveQuery_security (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 0 recursiveSecurityLastConfigs 2 (1 / 8) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) cfrPayoff_abs_le_two
    (fun _ _ _ _ => 1 / 8) (by intros; norm_num) reference equilibrium unknown who t
    (-2) 2 (fun h => (abs_le.mp (cfrPayoff_abs_le_two who h)).1)
    (fun h => (abs_le.mp (cfrPayoff_abs_le_two who h)).2)


/-- Zero stage fuel makes the exact native signed loss zero even when a
positive late tail remains, without restricting the stored PBS or history. -/
theorem queryCost_zero_fuel
    (plays : Unit → Profile (model fullPrior).behavioralSignature)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (config : PBSRecursiveResolveConfig.{0})
    (state : PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit)) :
    carriedReplacementSignedLoss (model fullPrior) plays unknown who
      (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
        plays { config with fuel := 0 }) 2 state (cfrPayoff who) = 0 := by
  exact pbsRecursiveReplacement_inactive (reducedModel fullPrior) pbsRootControlFallback
    cfrPayoff 2 plays unknown who { config with fuel := 0 } 2 state
    (by simp [pbsRecursiveQueryEvent, cfrDCutLive_zero]) (cfrPayoff who)

/-- An empty native schedule makes no fresh queries. It does not remove
the finite parent error or the positive retained-draw late payoff. -/
theorem queryCost_empty
    (plays : Unit → Profile (model fullPrior).behavioralSignature)
    (unknown : Profile (model fullPrior).behavioralSignature)
    (states : FinDist (PrivateIterationState (model fullPrior)
      (CarriedResolveMemory (model fullPrior) Unit))) :
    pbsRecursiveQueryVisits (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      plays unknown 0 [] states = 0 := rfl

end GameTheory.ReBeL.Examples.HiddenTypes
