/-
# An actually reached missing-model PBS

Player one's incumbent stays fixed while a seed-blind player-zero opponent
uses the canonical uniform legal policy. The opponent can reach an entire
public observation absent from the incumbent model. The carried state really
has no model posterior, and every later information-solving stage retains
the incumbent without additional replacement loss at that reached state.
-/

import GameTheory.Analysis.ReBeL.Examples.CFRDInformationResolve

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Every legal hidden-type history remains in the test domain. -/
local instance missingModelHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The fixed opponent has a finite legal menu at every full observation. -/
local instance missingModelChoiceFintype (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- One complete, seed-blind opposing strategy, fixed outside every private draw. -/
def missingModelOpponent : Profile (model fullPrior).behavioralSignature :=
  Profile.update (carriedBitProfile false) 0
    (uniformLegalPolicy (model fullPrior) 0 (cfrFallback 0))

/-- The factual-zero reference witness is an actual unknown-opponent history
when the deploying player is player one, not the deviating player zero. -/
theorem missingModel_actual_history :
    zeroControlHistory ∈ ((model fullPrior).runBehavioral
      (Profile.update missingModelOpponent 1 (carriedBitProfile false 1)) 2).support := by
  have unchanged : carriedBitProfile false 1 = missingModelOpponent 1 := by
    symm
    exact Profile.update_of_ne _ _ (by decide : (1 : Player) ≠ 0)
  rw [unchanged, Profile.update_eq_self]
  exact zeroControl_reference_supported

/-- The carried model law is computed from the incumbent, not the opponent. -/
def missingModelState : PrivateIterationState (model fullPrior) Unit :=
  privateIterationState (model fullPrior) (fun _ : Unit => carriedBitProfile false)
    2 () zeroControlHistory

/-- A real prefix execution reaches this retained-seed state. No support
certificate for an unrelated or user-supplied state law is assumed. -/
theorem missingModel_state_reached :
    missingModelState ∈ (privateCarriedPrefix (model fullPrior) (FinDist.pure ())
      (fun _ : Unit => carriedBitProfile false) missingModelOpponent 1 2).support := by
  simp only [privateCarriedPrefix, FinDist.pure_bind]
  rw [FinDist.support_map]
  exact ⟨zeroControlHistory, missingModel_actual_history, rfl⟩

/-- The reached state has no model posterior although its actual mass is positive. -/
theorem missingModel_state_none : missingModelState.belief = none :=
  carriedResolveControl_no_posterior

/-- This is a live continuation, not a vacuous exhausted or terminal case. -/
theorem missingModel_state_live : cfrDCutLive 1 missingModelState.history = true := by
  simp only [cfrDCutLive, decide_eq_true_eq]
  exact ⟨by decide, fun impossible => impossible⟩

/-- Every finite later schedule preserves the actual incumbent continuation
at the reached off-model state. It never reconstructs a guessed posterior. -/
theorem missingModel_recursive_law (schedule : List Nat) (finalFuel : Nat) :
    executeCarriedResolves (model fullPrior) (fun _ : Unit => carriedBitProfile false)
      missingModelOpponent 1 finalFuel
      (cfrDInformationResolveStages (reducedModel fullPrior)
        (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
        2 (1 / 4) finalFuel schedule) (enterCarriedMemory (model fullPrior) missingModelState) =
      (model fullPrior).runBehavioralFrom
        (Profile.update missingModelOpponent 1 (carriedBitProfile false 1))
        (schedule.sum + finalFuel) zeroControlHistory :=
  cfrDInformationResolveStages_run_none (reducedModel fullPrior)
    (fun _ : Unit => carriedBitProfile false) pbsRootControlFallback cfrPayoff
    2 (1 / 4) finalFuel schedule missingModelOpponent 1
    (enterCarriedMemory (model fullPrior) missingModelState) missingModel_state_none

end GameTheory.ReBeL.Examples.HiddenTypes
