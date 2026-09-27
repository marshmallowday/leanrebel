/-
# Native carried value controls

A noisy two-stage solver schedule consumes the signed bound, while stopped
stages retain positive late fuel. A selected child stores its own certified
posterior, not a pooled model or a reset from the initial history.
-/

import GameTheory.Analysis.ReBeL.PBSCarriedValue
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Enumerate all legal canonical histories, including off-model histories. -/
local instance carriedValueHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Two actually computed noisy child families are executed with their own
private memories. Their signed total loss uses the native full-state charge. -/
theorem carriedValue_noisy_two_stage
    (unknown : Profile (model fullPrior).behavioralSignature) :
    let M := model fullPrior
    let initial := fun _ : Unit => carriedBitProfile false
    let state := enterCarriedMemory M depthControlState
    (carriedSelectedTail M initial unknown 0 2 state).expect (cfrPayoff 0) -
      (executeCarriedResolves M initial unknown 0 0 depthControlStages state).expect
        (cfrPayoff 0) ≤
      2 * carriedSequenceExecutionCharge M initial unknown 0 0
        depthControlStages (FinDist.pure state) := by
  intro M initial state
  have totalFuel : carriedResolveFuel M 0 depthControlStages = 2 := rfl
  simpa only [FinDist.expect_pure, FinDist.pure_bind, totalFuel] using
    executeCarriedResolves_loss_le_executionCharge M initial unknown 0 0
      (cfrPayoff 0) 2 (by norm_num) (cfrPayoff_abs_le_two 0)
      depthControlStages (FinDist.pure state)

/-- Zero stage fuel suppresses replacement even when a positive late
continuation remains. Charging an unconditional new profile here is incorrect. -/
theorem carriedValue_stopped_positive_tail
    (unknown : Profile (model fullPrior).behavioralSignature) :
    let M := model fullPrior
    let initial := fun _ : Unit => carriedBitProfile false
    let stage := pbsCarriedDepthStage (reducedModel fullPrior) pbsRootControlFallback
      cfrPayoff 1 1 0 2 (1 / 4) depthControlNoise 2 initial
    carriedReplacementExecutionCharge M initial unknown 0 stage 2
      (enterCarriedMemory M depthControlState) = 0 := by
  simp only [carriedReplacementExecutionCharge, pbsCarriedDepthStage,
    cfrDCutLive_zero, Bool.false_eq_true, if_false]

/-- Every model-supported resulting history stores the posterior of that
particular actual computed iterate, propagated from the incoming joint PBS. -/
theorem carriedValue_selected_posterior (n : Fin 2) (history : (protocol fullPrior).History)
    (reached : history ∈ (PublicBelief.continuationLaw (model fullPrior)
      (pbsInformationDepthCFRIterate (reducedModel fullPrior) depthControlBelief
        pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
        (depthControlNoise depthControlBelief.law) n.val) 1 depthControlBelief).support) :
    let M := model fullPrior
    let chosen := pbsInformationDepthCFRIterate (reducedModel fullPrior) depthControlBelief
      pbsRootControlFallback cfrPayoff 1 1 2 (1 / 4)
      (depthControlNoise depthControlBelief.law) n.val
    ∃ posterior,
      (resolvedNextState M depthControlState chosen 1 history).belief = some posterior ∧
      posterior.law = (PublicBelief.continuationLaw M chosen 1 depthControlBelief).condOnFibre
        (fun h => publicTrace M.toInfoSignals h.trace)
        (publicTrace M.toInfoSignals history.trace) := by
  intro M chosen
  have positive : publicTrace M.toInfoSignals history.trace ∈
      (PublicBelief.publicLaw (S := M.toInfoSignals)
        (PublicBelief.continuationLaw M chosen 1 depthControlBelief)).support :=
    (PublicBelief.possible_iff_mem_publicLaw _ _).mp ⟨history, rfl, reached⟩
  refine ⟨PublicBelief.atObservation
    (PublicBelief.continuationLaw M chosen 1 depthControlBelief) _ positive, ?_, ?_⟩
  · exact resolvedNextState_belief_eq_atObservation M depthControlState depthControlBelief
      rfl chosen 1 history positive
  · exact PublicBelief.atObservation_law _ _ positive

end GameTheory.ReBeL.Examples.HiddenTypes
