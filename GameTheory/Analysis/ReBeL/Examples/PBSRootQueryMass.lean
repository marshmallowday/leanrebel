/-
# Query-mass controls for the actual noisy rooted hidden-type parent

The comparison uses the actual mass-scaled internal request. Its mean retains
stopped mass and any actual/model history discrepancy. It is not a claim that
an unknown opponent produces the MODEL root or that a whole native chain is safe.
-/

import GameTheory.Analysis.ReBeL.PBSRootQueryMass
import GameTheory.Analysis.ReBeL.Examples.PBSRootStoredValue

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate every original legal history. -/
local instance queryMassHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Use the same rooted enumeration as the internal recursive solver. -/
local instance queryMassRootHistory :
    Fintype (pbsRootProtocol recursiveInitialBelief.law).History :=
  pbsRootHistoryFintype recursiveInitialBelief.law

/-- Both comparisons use actual parent loss1/4 and fresh tolerance1/4.
The parent trunk retains numerical bias1/8 and cut2/remaining1. -/
def rootedQueryComparison (round : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (tag : List (Option (List (reducedModel fullPrior).PublicSignal))) : ℝ × ℝ :=
  pbsRootQueryComparison (reducedModel fullPrior) recursiveInitialBelief (rootedChildTrunk round)
    2 1 pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise [1] [1]
    pbsRootControlFallback pbsRootControlFallback cfrPayoff 2 (1 / 4) (1 / 4) unknown who tag

/-- Under the model prefix's own public weights there is no inverse-reach
penalty and no actual/model variation. Stopped mass is still explicit. -/
theorem rootedQuery_model_mean (round : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    let law := (fullInformation rootedChildModel).runBehavioral (rootedChildTrunk round) 2
    (law.map (fun h => publicTrace (fullInformation rootedChildModel).toInfoSignals h.trace)).expect
      (fun tag => (rootedQueryComparison round unknown who tag).1) ≤
        1 / 4 + 1 / 4 + 2 * 2 * law.probOf {h | cfrDCutLive 1 h ≠ true} ∧
    (law.map (fun h => publicTrace (fullInformation rootedChildModel).toInfoSignals h.trace)).expect
      (fun tag => (rootedQueryComparison round unknown who tag).2) ≤
        1 / 4 + 2 * (1 / 4) + 2 * 2 * law.probOf {h | cfrDCutLive 1 h ≠ true} := by
  intro law
  have estimate := pbsRootQueryComparison_mean (reducedModel fullPrior) recursiveInitialBelief
    (rootedChildTrunk round) 2 1 pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise [1] [1]
    pbsRootControlFallback pbsRootControlFallback cfrPayoff 2 (1 / 4) (1 / 4) unknown who
    pbsRecursiveAllocatedNoise_bounded pbsRecursiveAllocatedNoise_bounded rfl rfl
    (cumulative_zeroSum fullPrior) (by norm_num) cfrPayoff_abs_le_two
    (by norm_num) (by norm_num) law
  dsimp only [law] at estimate
  simp only [FinDist.atomVariation_self, add_zero] at estimate
  exact estimate

/-- A correlated native checkpoint supplies its own query frequencies.
No saved posterior, incumbent or private-memory independence is assumed. -/
theorem rootedQuery_native_mean {K : Type*} (round : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (states : FinDist (PrivateIterationState (fullInformation rootedChildModel) K)) :
    states.expect (fun state => (rootedQueryComparison round unknown who
      (publicTrace (fullInformation rootedChildModel).toInfoSignals state.history.trace)).2) ≤
      1 / 4 + 2 * (1 / 4) + 2 * 2 *
        (((fullInformation rootedChildModel).runBehavioral (rootedChildTrunk round) 2).probOf
          {h | cfrDCutLive 1 h ≠ true} +
          FinDist.atomVariation (states.map (fun state => state.history))
            ((fullInformation rootedChildModel).runBehavioral (rootedChildTrunk round) 2)) := by
  exact pbsRootQueryComparison_native_mean (reducedModel fullPrior) recursiveInitialBelief
    (rootedChildTrunk round) 2 1 pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise [1] [1]
    pbsRootControlFallback pbsRootControlFallback cfrPayoff 2 (1 / 4) (1 / 4) unknown who
    pbsRecursiveAllocatedNoise_bounded pbsRecursiveAllocatedNoise_bounded rfl rfl
    (cumulative_zeroSum fullPrior) (by norm_num) cfrPayoff_abs_le_two
    (by norm_num) (by norm_num) states

/-- Initial public observations are outside this noninitial-query diagnostic.
This zero does not assert a zero native execution cost. -/
theorem rootedQuery_initial_excluded (round : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    rootedQueryComparison round unknown who [] = (0, 0) := rfl

end GameTheory.ReBeL.Examples.HiddenTypes
