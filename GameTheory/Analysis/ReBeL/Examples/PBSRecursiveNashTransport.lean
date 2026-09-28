/-
# Actual recursive solver consumers of Nash transport

The model-opponent example has a small solver-derived bound. The native chain
keeps all root/opponent/support costs and checks the full late horizon.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveNashBudget
import GameTheory.Analysis.ReBeL.Examples.PBSRecursiveDepth
import GameTheory.Analysis.ReBeL.Examples.PBSRecursiveRecomputedValue

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Include all legal histories of the hidden-type game. -/
local instance nashTransportHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Actual noisy recursive solving controls every old own policy on its
modeled root law, with the computed opposing policy held fixed. -/
theorem recursiveInitial_model_replacement
    (old : Profile (model fullPrior).behavioralSignature) (who : Player) :
    recursivePolicyValueChange (reducedModel fullPrior) old (recursiveInitialProfile (1 / 8))
      (recursiveInitialProfile (1 / 8)) who 3 recursiveInitialBelief.law (cfrPayoff who) ≤
      1 / 8 := by
  exact pbsRecursiveDepth_model_replacement_le (reducedModel fullPrior)
    pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded [1, 1, 1]
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 2 (by norm_num)
    cfrPayoff_abs_le_two recursiveInitialBelief (1 / 8) (by norm_num) old who

/-- Both recursive solves cover stage plus all remaining native and late fuel. -/
def nashTransportConfigs : List PBSRecursiveResolveConfig.{0} :=
  [⟨pbsRecursiveAllocatedNoise, [1, 1, 1], 1 / 4, 1⟩,
   ⟨pbsRecursiveAllocatedNoise, [1, 1], 1 / 8, 1⟩]

/-- The actual noise contract and positive tolerances discharge schedule validity. -/
theorem nashTransportConfigs_aligned : PBSRecursiveNashAligned 1 nashTransportConfigs :=
  ⟨pbsRecursiveAllocatedNoise_bounded, by norm_num, rfl,
    pbsRecursiveAllocatedNoise_bounded, by norm_num, rfl, True.intro⟩

/-- A previously valid exact signed accounting example has an insufficient
second training horizon for this stronger Nash consumer. It remains a valid
computed-cost example; no finite-horizon guarantee is extended silently. -/
theorem recomputedConfigs_not_nashAligned : ¬ PBSRecursiveNashAligned 1 recomputedConfigs := by
  intro aligned
  norm_num [PBSRecursiveNashAligned, recomputedConfigs, pbsRecursiveConfigFuel] at aligned

/-- The real noisy native two-stage chain consumes the solver-derived envelope.
The unknown opponent is arbitrary, so the displayed discrepancy costs remain. -/
theorem nashTransport_noisy_chain
    (unknown : Profile (model fullPrior).behavioralSignature) :
    let initial := fun _ : Unit => carriedBitProfile false
    let state := enterCarriedMemory (model fullPrior) depthControlState
    let stages := nashTransportConfigs.map
      (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 initial)
    (carriedSelectedTail (model fullPrior) initial unknown 0 3 state).expect (cfrPayoff 0) -
      (executeCarriedResolves (model fullPrior) initial unknown 0 1 stages state).expect
        (cfrPayoff 0) ≤
    pbsRecursiveNashBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      initial unknown 0 1 nashTransportConfigs (FinDist.pure state) := by
  intro initial state stages
  have totalFuel : carriedResolveFuel (model fullPrior) 1 stages = 3 := rfl
  have identity := executeCarriedResolves_loss_eq_signed (model fullPrior)
    initial unknown 0 1 (cfrPayoff 0) stages (FinDist.pure state)
  have estimate := carriedSignedSequenceLoss_le_nashBudget (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior) 2 (by norm_num)
    cfrPayoff_abs_le_two initial unknown 0 1 nashTransportConfigs nashTransportConfigs_aligned
    (FinDist.pure state)
  rw [← identity] at estimate
  simpa only [FinDist.expect_pure, FinDist.pure_bind, totalFuel] using estimate

end GameTheory.ReBeL.Examples.HiddenTypes
