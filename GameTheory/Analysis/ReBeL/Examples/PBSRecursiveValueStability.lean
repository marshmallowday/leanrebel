/-
# Different recursive computations at actual public queries

The old and new solves share only the original protocol, payoff and horizon.
Their cut partitions and tolerances may differ. Scalar agreement does not
identify policies or the internally rooted solver representation.
-/

import GameTheory.Analysis.ReBeL.CFRDStoredSolveValue
import GameTheory.Analysis.ReBeL.Examples.CFRDStoredChildDefect

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Histories include legal off-path histories. -/
local instance crossQueryHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Full AOH menus remain the actual game's menus. -/
local instance crossQueryChoice (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- Classical equality is internal to the real-valued reference construction. -/
local instance crossQueryInfo (who : Player) : DecidableEq ((model fullPrior).InfoState who) :=
  Classical.decEq _

/-- Distinct [1,1,1] and [3] computations have comparable scalar values at
the same initial PBS. Neither profile identity nor equal iteration budgets
is used; their two requested errors remain visible. -/
theorem crossQuery_partition_value (who : Player) :
    let second := pbsRecursiveDepth pbsRecursiveAllocatedNoise [3] (protocol fullPrior)
      (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief (1 / 4)
    |(recursiveInitialBelief.law.bind
        ((model fullPrior).runBehavioralFrom (recursiveInitialProfile (1 / 8)) 3)).expect
        (cfrPayoff who) -
      (recursiveInitialBelief.law.bind
        ((model fullPrior).runBehavioralFrom second 3)).expect (cfrPayoff who)| ≤
      1 / 8 + 1 / 4 := by
  intro second
  have estimate := pbsRecursiveDepth_crossQuery_value_variation (reducedModel fullPrior)
    pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    pbsRecursiveAllocatedNoise_bounded [1, 1, 1] [3] rfl
    pbsRootControlFallback pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    2 (by norm_num) cfrPayoff_abs_le_two recursiveInitialBelief recursiveInitialBelief
    (1 / 8) (1 / 4) (by norm_num) (by norm_num) who
  simpa only [FinDist.atomVariation_self, mul_zero, add_zero] using estimate

/-- The actual [3] private draw secures the earlier [1,1,1] computed model
value against any fixed unknown opponent. The second tolerance is charged
twice by this comparison, separately from the first tolerance. -/
theorem crossQuery_partition_private
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    (recursiveInitialBelief.law.bind
      ((model fullPrior).runBehavioralFrom (recursiveInitialProfile (1 / 8)) 3)).expect
        (cfrPayoff who) - (1 / 8 + 2 * (1 / 4)) ≤
    (pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [3] (reducedModel fullPrior)
      pbsRootControlFallback cfrPayoff 2 recursiveInitialBelief (1 / 4)).expect
      (fun chosen => (recursiveInitialBelief.law.bind
        ((model fullPrior).runBehavioralFrom (Profile.update unknown who (chosen who)) 3)).expect
          (cfrPayoff who)) := by
  have estimate := pbsRecursiveDepth_crossQuery_private_security (reducedModel fullPrior)
    pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    pbsRecursiveAllocatedNoise_bounded [1, 1, 1] [3] rfl
    pbsRootControlFallback pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    2 (by norm_num) cfrPayoff_abs_le_two recursiveInitialBelief recursiveInitialBelief
    (1 / 8) (1 / 4) (by norm_num) (by norm_num) who unknown
  simpa only [FinDist.atomVariation_self, mul_zero, add_zero] using estimate

/-- The real noisy parent stores its public posterior. Two independently
recomputed one-step searches on that posterior and its live child have a
tolerance-only scalar gap because public termination is proved for this game. -/
theorem crossQuery_stored_noisy (loss : ℝ) (round : Nat)
    (history : (protocol fullPrior).History)
    (possible : CFRDFactualChildPossible (reducedModel fullPrior)
      (cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
        (pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
          (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2) storedChildNoise round)
      2 1 (publicTrace (model fullPrior).toInfoSignals history.trace)) (who : Player) :
    let solve : PBSChildSolve (reducedModel fullPrior) :=
      pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
        (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2
    let trunk : Profile (model fullPrior).behavioralSignature :=
      cfrDComposedTrunk (reducedModel fullPrior) pbsRootControlFallback cfrPayoff
        2 1 loss solve storedChildNoise round
    let obs := publicTrace (model fullPrior).toInfoSignals history.trace
    let posterior := PublicBelief.condition (S := (model fullPrior).toInfoSignals)
      ((model fullPrior).runBehavioral trunk 2) obs
      (cfrDFactualChildPossible_public (reducedModel fullPrior) trunk 2 1 obs possible)
    let child := cfrDFactualChildBelief (reducedModel fullPrior) trunk 2 1 obs possible
    let first := pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
      (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 posterior (1 / 8)
    let second := pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
      (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 child (1 / 4)
    (cfrDComposedNextState (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 1 loss
      solve storedChildNoise round storedChildInitial history).belief = some posterior ∧
    |(posterior.law.bind ((model fullPrior).runBehavioralFrom first 1)).expect (cfrPayoff who) -
      (child.law.bind ((model fullPrior).runBehavioralFrom second 1)).expect (cfrPayoff who)| ≤
      1 / 8 + 1 / 4 := by
  intro solve trunk obs posterior child first second
  refine ⟨hiddenStoredPublic loss round history possible, ?_⟩
  have estimate := cfrDStoredChild_recursive_value_error (reducedModel fullPrior) trunk 2 1
    obs possible pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise
    pbsRecursiveAllocatedNoise_bounded pbsRecursiveAllocatedNoise_bounded [1] [1] rfl rfl
    pbsRootControlFallback pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    2 (by norm_num) cfrPayoff_abs_le_two (1 / 8) (1 / 4) (by norm_num) (by norm_num) who
  dsimp only at estimate
  have stopped := cfrDFactualChild_stoppedMass_eq_zero (reducedModel fullPrior)
    (hiddenTypes_publicTermination fullPrior) trunk 2 1 obs possible
  rw [stopped, zero_div, mul_zero, add_zero] at estimate
  exact estimate

end GameTheory.ReBeL.Examples.HiddenTypes
