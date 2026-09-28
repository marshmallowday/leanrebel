/-
# Stored factual child in the canonical hidden-type game

The existing public phase distinguishes live and terminal states. The actual
noisy composed parent stores the same correlated child used in that round.
No actual hidden type or unknown-opponent policy is passed to the solver.
-/

import GameTheory.Analysis.ReBeL.PBSStoredChildReplay
import GameTheory.Analysis.ReBeL.Examples.PBSRecursiveDepth

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Canonical finite history enumeration, including off-path histories. -/
local instance storedHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The parent's information-local legal menus remain finite. -/
local instance storedChoice (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Classical equality is used only in the real-valued reference computation. -/
local instance storedInfo (who : Player) : DecidableEq ((model fullPrior).InfoState who) :=
  Classical.decEq _

/-- Public histories are newest first; their head is the current public phase. -/
theorem storedPublic_head (prior : FinDist Types) (history : (protocol prior).History) :
    (publicTrace (signals prior) history.trace).head? = some (phase history.state) := by
  rcases history with ⟨state, trace⟩
  cases trace <;> rfl

/-- Termination visibility is derived from the original game's phase signal. -/
theorem hiddenTypes_publicTermination (prior : FinDist Types) :
    PubliclyObservableTermination (reducedModel prior) := by
  intro first second same
  have heads := congrArg List.head? same
  rw [storedPublic_head, storedPublic_head] at heads
  have phases := Option.some.inj heads
  cases hfirst : first.state <;> cases hsecond : second.state <;>
    simp_all [phase, protocol, terminal]

/-- The actual model PBS before the original chance step. -/
def storedChildInitial : PrivateIterationState (model fullPrior) Unit where
  iteration := ()
  history := (protocol fullPrior).initHistory
  belief := some recursiveInitialBelief

/-- A nonzero query perturbation in the actual coupled parent recurrence. -/
def storedChildNoise : CFRDPredictionNoise (reducedModel fullPrior) :=
  fun _ _ _ _ => 1 / 8

/-- A factual child of the played round is also the native saved model PBS.
The actual child is the one-level recursive solver, not an external certificate. -/
theorem hiddenStoredChild (loss : ℝ) (round : Nat)
    (history : (protocol fullPrior).History)
    (possible : CFRDFactualChildPossible (reducedModel fullPrior)
      (cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) storedChildNoise round)
      2 1 (publicTrace (signals fullPrior) history.trace)) :
    let solve := pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
      (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    let trunk := cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      2 1 loss solve storedChildNoise round
    (cfrDComposedNextState (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
      solve storedChildNoise round storedChildInitial history).belief =
    some (cfrDFactualChildBelief (reducedModel fullPrior) trunk 2 1
      (publicTrace (signals fullPrior) history.trace) possible) := by
  exact cfrDComposedRound_storedChild (reducedModel fullPrior)
    (hiddenTypes_publicTermination fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss _
    storedChildNoise round storedChildInitial recursiveInitialBelief rfl rfl history possible

/-- The existing resolver consumes the derived child PBS at the exact parent
request. Different later budgets or root encodings are not identified by this. -/
theorem hiddenStoredChild_resolver (loss : ℝ) (round : Nat)
    (history : (protocol fullPrior).History)
    (possible : CFRDFactualChildPossible (reducedModel fullPrior)
      (cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) storedChildNoise round)
      2 1 (publicTrace (signals fullPrior) history.trace))
    (plays : (Unit × Profile (model fullPrior).behavioralSignature) →
      Profile (model fullPrior).behavioralSignature) :
    let solve := pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
      (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    let trunk := cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      2 1 loss solve storedChildNoise round
    let child := cfrDFactualChildBelief (reducedModel fullPrior) trunk 2 1
      (publicTrace (signals fullPrior) history.trace) possible
    let next := cfrDComposedNextState (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
      2 1 loss solve storedChildNoise round storedChildInitial history
    next.belief = some child ∧
      pbsRecursiveDepthResolver pbsRecursiveAllocatedNoise [1] (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 2 (child.law.positiveMassFloor * loss) plays
        next.iteration (publicTrace (signals fullPrior) history.trace) next.belief =
      pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [1] (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 2 child (child.law.positiveMassFloor * loss) :=
  pbsRecursiveResolver_composed_input (reducedModel fullPrior) pbsRecursiveAllocatedNoise
    [1] pbsRootControlFallback cfrPayoff 2 (hiddenTypes_publicTermination fullPrior) 2 1 loss
    storedChildNoise round storedChildInitial recursiveInitialBelief rfl rfl history possible plays

end GameTheory.ReBeL.Examples.HiddenTypes
