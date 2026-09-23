/-
# Controls for fresh carried-PBS solves and missing-model execution

A live hidden-type posterior uses a positive child tolerance. A genuinely
unvisited public observation produces no model posterior. Nonempty retained
memory must use its newest policy, not reset to the initial parent. That
reset changes the actual payoff by two in the explicit live continuation.
-/

import GameTheory.Analysis.ReBeL.CFRDInformationResolveRecursion
import GameTheory.Analysis.ReBeL.Examples.CFRDInformationChild
import GameTheory.Analysis.ReBeL.Examples.CFRDResolveNegative

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate all legal histories, including those outside the incumbent support. -/
local instance carriedResolveHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Available stored beliefs really produce fresh actual CFR iteration draws. -/
theorem carriedResolveControl_some :
    cfrDInformationResolver (reducedModel fullPrior) (fun _ : Unit => carriedBitProfile false)
      pbsRootControlFallback cfrPayoff 1 2 (1 / 4) () _ (some finiteBudgetControlBelief) =
      cfrDInformationResolveDraw (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback cfrPayoff 1 2 (1 / 4) := rfl

/-- The same fresh draw realizes the computed child law against an arbitrary
fixed opponent, with a positive child tolerance and a genuinely live PBS. -/
theorem carriedResolveControl_child_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    (cfrDInformationResolveDraw (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback cfrPayoff 1 2 (1 / 4)).bind
        (fun chosen => finiteBudgetControlBelief.law.bind
          ((model fullPrior).runBehavioralFrom (Profile.update unknown who (chosen who)) 1)) =
      finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who
          (pbsInformationConditionalProfile (reducedModel fullPrior) finiteBudgetControlBelief
            pbsRootControlFallback 1 (fun h player => cfrPayoff player h) 2 (1 / 4) who)) 1) :=
  cfrDInformationResolveDraw_law (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff 1 2 (1 / 4) unknown who 1

/-- This missing posterior is computed from a genuinely unvisited public
observation of the incumbent model, not assigned as a fictitious joint law. -/
theorem carriedResolveControl_no_posterior :
    (privateIterationState (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      2 () zeroControlHistory).belief = none := by
  rw [privateIterationState_no_posterior]
  intro possible
  apply publicSplice_unvisited_public
  rw [FinDist.support_map]
  obtain ⟨history, same, supported⟩ := possible
  exact ⟨history, supported, same⟩

/-- Earlier draws remain stored; the latest true policy differs from the
initial false policy. This is an arbitrary legal carried-memory control. -/
def carriedResolveControlState :
    PrivateIterationState (model fullPrior) (CarriedResolveMemory (model fullPrior) Unit) where
  iteration := ((), [carriedBitProfile true])
  history := decode (.second false false false false)
  belief := none

/-- A positive-fuel interval between two zero-fuel intervals preserves the
newest private policy against every opponent, not the initial false policy. -/
theorem carriedResolveControl_newest_law
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    executeCarriedResolves (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      unknown who 0
      (cfrDInformationResolveStages (reducedModel fullPrior)
        (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
        2 (1 / 4) 0 [0, 1, 0]) carriedResolveControlState =
      (model fullPrior).runBehavioralFrom
        (Profile.update unknown who (carriedBitProfile true who)) 1
        (decode (.second false false false false)) :=
  cfrDInformationResolveStages_run_none (reducedModel fullPrior)
    (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
    2 (1 / 4) 0 [0, 1, 0] unknown who carriedResolveControlState rfl

/-- Preserving the newest draw has an explicit nonconstant canonical payoff. -/
theorem carriedResolveControl_newest_value :
    (executeCarriedResolves (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      (carriedBitProfile false) 0 0
      (cfrDInformationResolveStages (reducedModel fullPrior)
        (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
        2 (1 / 4) 0 [0, 1, 0]) carriedResolveControlState).expect (cfrPayoff 0) = 2 := by
  rw [carriedResolveControl_newest_law]
  have own : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0 (carriedBitProfile true 0))
      false false false false 0 = FinDist.pure true := by
    unfold liveSecondLaw
    rw [Profile.update_same]
    exact carriedBit_second_law true false false false false 0
  have opponent : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0 (carriedBitProfile true 0))
      false false false false 1 = FinDist.pure false := by
    unfold liveSecondLaw
    rw [Profile.update_of_ne _ _ (by decide : (1 : Player) ≠ 0)]
    exact carriedBit_second_law false false false false false 1
  rw [liveSecond_value, own, opponent]
  norm_num [FinDist.expect_pure, signed, winValue]

/-- Resetting to the initial policy would change the actual payoff by two.
This guards the fallback's memory semantics, not a claim of per-draw safety. -/
theorem carriedResolveControl_reset_loses_two :
    (executeCarriedResolves (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      (carriedBitProfile false) 0 0
      (cfrDInformationResolveStages (reducedModel fullPrior)
        (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
        2 (1 / 4) 0 [0, 1, 0]) carriedResolveControlState).expect (cfrPayoff 0) -
      ((model fullPrior).runBehavioralFrom (carriedBitProfile false) 1
        (decode (.second false false false false))).expect (cfrPayoff 0) = 2 := by
  rw [carriedResolveControl_newest_value, wrongResolver_after]
  norm_num

/-- No extra loss is assumed: it follows from the entire recursive law. -/
theorem carriedResolveControl_missing_loss
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (schedule : List Nat) (finalFuel : Nat) :
    cfrDInformationResolveLoss (reducedModel fullPrior)
      (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
      2 (1 / 4) finalFuel schedule unknown who (cfrPayoff who)
      carriedResolveControlState = 0 :=
  cfrDInformationResolveLoss_none (reducedModel fullPrior)
    (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
    2 (1 / 4) finalFuel schedule unknown who (cfrPayoff who) carriedResolveControlState rfl

/-- Positive model-root child regret is supplied by the learner, not a
caller-provided Nash certificate or an optimality claim for each iterate. -/
theorem carriedResolveControl_child_gain (who : Player)
    (target : (model fullPrior).BehavioralPolicy who) :
    let average := pbsInformationConditionalProfile (reducedModel fullPrior)
      finiteBudgetControlBelief pbsRootControlFallback 1 (fun h player => cfrPayoff player h)
      2 (1 / 4)
    (finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
      (Profile.update average who target) 1)).expect (cfrPayoff who) -
      ((cfrDInformationResolveDraw (reducedModel fullPrior) finiteBudgetControlBelief
        pbsRootControlFallback cfrPayoff 1 2 (1 / 4)).bind
        (fun chosen => finiteBudgetControlBelief.law.bind
          ((model fullPrior).runBehavioralFrom (Profile.update average who (chosen who)) 1))).expect
          (cfrPayoff who) ≤ finiteBudgetControlBelief.law.positiveMassFloor * (1 / 4) :=
  cfrDInformationResolveDraw_gain_le (reducedModel fullPrior) finiteBudgetControlBelief
    pbsRootControlFallback cfrPayoff 1 2 (1 / 4) (cumulative_zeroSum fullPrior)
    (by norm_num) (by norm_num) (fun h player => cfrPayoff_abs_le_two player h) who target

end GameTheory.ReBeL.Examples.HiddenTypes
