/-
# Actual noisy consumers of recomputed recursive values

These consumers exercise native forward memory, positive late fuel and the
changed-budget term even when public termination removes posterior filtering.
-/

import GameTheory.Analysis.ReBeL.PBSRecursiveRecomputedValue
import GameTheory.Analysis.ReBeL.Examples.CFRDStoredChildDefect
import GameTheory.Analysis.ReBeL.Examples.PBSCarriedValue

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate the entire protocol, including off-model histories. -/
local instance recomputedHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The actual noisy parent has the existing finite legal menus. -/
local instance recomputedChoice (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The parent's CFR information-state comparison is classical. -/
local instance recomputedInfo (who : Player) : DecidableEq ((model fullPrior).InfoState who) :=
  Classical.decEq _

/-- Distinct actual recursive schedules and tolerances at the two stages. -/
def recomputedConfigs : List PBSRecursiveResolveConfig.{0} :=
  [⟨pbsRecursiveAllocatedNoise, [1, 1, 1], 1 / 4, 1⟩,
   ⟨pbsRecursiveAllocatedNoise, [1], 1 / 8, 1⟩]

/-- The real hidden-type native chain consumes the new budget. One extra
late step remains after both stages, so it cannot be omitted in either cost. -/
theorem recomputed_noisy_chain
    (unknown : Profile (model fullPrior).behavioralSignature) :
    let initial := fun _ : Unit => carriedBitProfile false
    let state := enterCarriedMemory (model fullPrior) depthControlState
    let stages := recomputedConfigs.map
      (pbsRecursiveConfigStage (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 initial)
    (carriedSelectedTail (model fullPrior) initial unknown 0 3 state).expect (cfrPayoff 0) -
      (executeCarriedResolves (model fullPrior) initial unknown 0 1 stages state).expect
        (cfrPayoff 0) ≤
    pbsRecursiveRecomputedBudget (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      initial unknown 0 1 (cfrPayoff 0) 2 recomputedConfigs (FinDist.pure state) := by
  intro initial state stages
  have totalFuel : carriedResolveFuel (model fullPrior) 1 stages = 3 := rfl
  have identity := executeCarriedResolves_loss_eq_signed (model fullPrior)
    initial unknown 0 1 (cfrPayoff 0) stages (FinDist.pure state)
  have estimate := carriedSignedSequenceLoss_le_recomputedBudget (reducedModel fullPrior)
    pbsRootControlFallback cfrPayoff 2 initial unknown 0 1 (cfrPayoff 0) 2
    (cfrPayoff_abs_le_two 0) recomputedConfigs (FinDist.pure state)
  rw [← identity] at estimate
  simpa only [FinDist.expect_pure, FinDist.pure_bind, totalFuel] using estimate

/-- Zero fuel does not run a fresh solver, despite positive late continuation. -/
theorem recomputed_zero_stage
    (unknown : Profile (model fullPrior).behavioralSignature) :
    pbsRecursiveRecomputedOutcome (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
      (fun _ : Unit => carriedBitProfile false) unknown 0
      ⟨pbsRecursiveAllocatedNoise, [1], 1 / 8, 0⟩ 2
      (enterCarriedMemory (model fullPrior) depthControlState) =
    carriedSelectedTail (model fullPrior) (fun _ : Unit => carriedBitProfile false) unknown 0 2
      (enterCarriedMemory (model fullPrior) depthControlState) := by
  simp only [pbsRecursiveRecomputedOutcome, cfrDCutLive_zero, Bool.false_eq_true, if_false]

/-- In the real noisy parent, public visibility removes the posterior term.
The separate recomputation term is retained: different solver budgets are not
identified merely because the two input PBS laws agree. -/
theorem recomputed_noisy_parent_residual (publicTolerance loss : ℝ) (round : Nat)
    (history : (protocol fullPrior).History)
    (possible : CFRDFactualChildPossible (reducedModel fullPrior)
      (cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) storedChildNoise round)
      2 1 (publicTrace (model fullPrior).toInfoSignals history.trace))
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (fuel : Nat) :
    let solve : PBSChildSolve (reducedModel fullPrior) :=
      pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
        (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    let trunk : Profile (model fullPrior).behavioralSignature :=
      cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        2 1 loss solve storedChildNoise round
    let obs := publicTrace (model fullPrior).toInfoSignals history.trace
    let saved := PublicBelief.condition (S := (model fullPrior).toInfoSignals)
      ((model fullPrior).runBehavioral trunk 2) obs
      (cfrDFactualChildPossible_public (reducedModel fullPrior) trunk 2 1 obs possible)
    let child := cfrDFactualChildBelief (reducedModel fullPrior) trunk 2 1 obs possible
    |((pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [1] (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 2 saved publicTolerance).expect (fun chosen =>
          (saved.law.bind ((model fullPrior).runBehavioralFrom
            (Profile.update unknown who (chosen who)) fuel)).expect (cfrPayoff who)) -
      (pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [1] (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 2 child (child.law.positiveMassFloor * loss)).expect
          (fun chosen => (child.law.bind ((model fullPrior).runBehavioralFrom
            (Profile.update unknown who (chosen who)) fuel)).expect (cfrPayoff who))) -
      recursivePolicyValueChange (reducedModel fullPrior) (solve saved publicTolerance)
        (solve child (child.law.positiveMassFloor * loss)) unknown who fuel child.law
        (cfrPayoff who)| ≤ 0 := by
  intro solve trunk obs saved child
  have estimate := pbsRecursiveDepthDraw_public_child_residual (reducedModel fullPrior)
    pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 publicTolerance loss
    trunk unknown 2 1 obs possible who fuel (cfrPayoff who) 2 (cfrPayoff_abs_le_two who)
  dsimp only at estimate
  have stopped := cfrDFactualChild_stoppedMass_eq_zero (reducedModel fullPrior)
    (hiddenTypes_publicTermination fullPrior) trunk 2 1 obs possible
  rw [stopped, zero_div, mul_zero] at estimate
  exact estimate

end GameTheory.ReBeL.Examples.HiddenTypes
