/-
# Actual noisy rooted parent, unfiltered saved PBS and fresh original solve

The parent has cut 2 (one administrative and one original transition), remaining
fuel 1, numerical bias 1/8 and child loss 1/4. Public-only and live inputs stay
distinct, and the stopped fraction remains explicit.
-/

import GameTheory.Analysis.ReBeL.PBSRootStoredState
import GameTheory.Analysis.ReBeL.Examples.PBSRootChildRecursive

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Enumerate every original legal history. -/
local instance rootedStoredHistory : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Include all histories of the existing outer rooted protocol. -/
local instance rootedStoredRootHistory :
    Fintype (pbsRootProtocol recursiveInitialBelief.law).History :=
  pbsRootHistoryFintype recursiveInitialBelief.law

/-- Equality is used in the reference parent's full information recurrence. -/
local instance rootedStoredInfo (who : Player) :
    DecidableEq ((fullInformation rootedChildModel).InfoState who) := Classical.decEq _

/-- Finite menus retain the original action options. -/
local instance rootedStoredChoice (who : Player)
    (info : (fullInformation rootedChildModel).InfoState who) :
    Fintype ((fullInformation rootedChildModel).Choice who info) := by
  classical
  infer_instance


/-- The actual parent's saved public-only posterior before live filtering. -/
def rootedStoredPosterior (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past)) :
    PublicBelief (fullInformation rootedChildModel).toInfoSignals
      (some observations :: past) :=
  pbsRootPublicPosterior (reducedModel fullPrior) recursiveInitialBelief.law
    (rootedChildTrunk round) 2 1 observations past possible

/-- Decode what the actual native parent stores. The private state and
history are retained; the conclusion only projects its saved MODEL law. -/
theorem rootedStored_native_law {K : Type*} (round : Nat)
    (state : PrivateIterationState (fullInformation rootedChildModel) K)
    (prior : PublicBelief (fullInformation rootedChildModel).toInfoSignals
      (publicTrace (fullInformation rootedChildModel).toInfoSignals state.history.trace))
    (stored : state.belief = some prior)
    (initial : prior.law = FinDist.pure (pbsRootProtocol recursiveInitialBelief.law).initHistory)
    (history : (pbsRootProtocol recursiveInitialBelief.law).History)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (observed : publicTrace (fullInformation rootedChildModel).toInfoSignals history.trace =
      some observations :: past)
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past)) :
    pbsRootSavedLaw (reducedModel fullPrior) recursiveInitialBelief.law
      (cfrDComposedNextState rootedChildModel
        (pbsRootDepthFallback (reducedModel fullPrior) recursiveInitialBelief.law
          pbsRootControlFallback)
        (pbsRootPayoff recursiveInitialBelief.law cfrPayoff) 2 1 (1 / 4)
        rootedChildSolve (fun _ _ _ _ => 1 / 8) round state history).belief =
      some (pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law
        (rootedStoredPosterior round observations past possible)).law := by
  exact pbsRootComposed_stored_query_law (reducedModel fullPrior) recursiveInitialBelief.law
    (pbsRootDepthFallback (reducedModel fullPrior) recursiveInitialBelief.law
      pbsRootControlFallback)
    (pbsRootPayoff recursiveInitialBelief.law cfrPayoff) 2 1 (1 / 4)
    rootedChildSolve (fun _ _ _ _ => 1 / 8) round state prior stored initial history
    observations past observed possible

/-- The fresh original solver uses the unfiltered public input while the
internal child retains the parent's actual mass-scaled tolerance. -/
theorem rootedStored_value (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past)) (who : Player) :
    let child := rootedChildPosterior round observations past possible
    let posterior := rootedStoredPosterior round observations past possible
    let decodedChild := pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law child
    let decodedPublic := pbsRootChildBelief (reducedModel fullPrior)
      recursiveInitialBelief.law posterior
    let internal := pbsRootChildRecursiveProfile (reducedModel fullPrior) recursiveInitialBelief
      pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
        (child.law.positiveMassFloor * (1 / 4))
    let fresh := pbsRecursiveDepth pbsRecursiveAllocatedNoise [1] (protocol fullPrior)
      (reducedModel fullPrior) pbsRootControlFallback cfrPayoff 2 decodedPublic (1 / 4)
    |(decodedChild.law.bind ((model fullPrior).runBehavioralFrom internal 1)).expect
        (cfrPayoff who) -
      (decodedPublic.law.bind ((model fullPrior).runBehavioralFrom fresh 1)).expect
        (cfrPayoff who)| ≤ child.law.positiveMassFloor * (1 / 4) + 1 / 4 +
      2 * 2 * pbsRootStoppedFraction (reducedModel fullPrior) recursiveInitialBelief.law
        (rootedChildTrunk round) 2 1 observations past := by
  intro child posterior decodedChild decodedPublic internal fresh
  exact pbsRootStored_fresh_value (reducedModel fullPrior) recursiveInitialBelief
    (rootedChildTrunk round) 2 1 observations past possible
    pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    pbsRecursiveAllocatedNoise_bounded [1] [1] rfl rfl
    pbsRootControlFallback pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    2 (by norm_num) cfrPayoff_abs_le_two
    (child.law.positiveMassFloor * (1 / 4)) (1 / 4)
    (mul_pos (FinDist.positiveMassFloor_pos child.law) (by norm_num)) (by norm_num) who

/-- One fresh private draw secures the internal model value against an
arbitrary fixed opponent, with public/live mass and the extra fresh error. -/
theorem rootedStored_private_security (round : Nat)
    (observations : List (reducedModel fullPrior).PublicSignal)
    (past : List (Option (List (reducedModel fullPrior).PublicSignal)))
    (possible : CFRDFactualChildPossible rootedChildModel (rootedChildTrunk round)
      2 1 (some observations :: past))
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) :
    let child := rootedChildPosterior round observations past possible
    let posterior := rootedStoredPosterior round observations past possible
    let decodedChild := pbsRootChildBelief (reducedModel fullPrior) recursiveInitialBelief.law child
    let decodedPublic := pbsRootChildBelief (reducedModel fullPrior)
      recursiveInitialBelief.law posterior
    let internal := pbsRootChildRecursiveProfile (reducedModel fullPrior) recursiveInitialBelief
      pbsRecursiveAllocatedNoise [1] pbsRootControlFallback cfrPayoff 2 child
        (child.law.positiveMassFloor * (1 / 4))
    (decodedChild.law.bind ((model fullPrior).runBehavioralFrom internal 1)).expect
        (cfrPayoff who) -
      (child.law.positiveMassFloor * (1 / 4) + 2 * (1 / 4) +
        2 * 2 * pbsRootStoppedFraction (reducedModel fullPrior) recursiveInitialBelief.law
          (rootedChildTrunk round) 2 1 observations past) ≤
      (pbsRecursiveDepthDraw pbsRecursiveAllocatedNoise [1] (reducedModel fullPrior)
        pbsRootControlFallback cfrPayoff 2 decodedPublic (1 / 4)).expect
        (fun chosen => (decodedPublic.law.bind ((model fullPrior).runBehavioralFrom
          (Profile.update unknown who (chosen who)) 1)).expect (cfrPayoff who)) := by
  intro child posterior decodedChild decodedPublic internal
  exact pbsRootStored_fresh_security (reducedModel fullPrior) recursiveInitialBelief
    (rootedChildTrunk round) 2 1 observations past possible
    pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise pbsRecursiveAllocatedNoise_bounded
    pbsRecursiveAllocatedNoise_bounded [1] [1] rfl rfl
    pbsRootControlFallback pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    2 (by norm_num) cfrPayoff_abs_le_two
    (child.law.positiveMassFloor * (1 / 4)) (1 / 4)
    (mul_pos (FinDist.positiveMassFloor_pos child.law) (by norm_num)) (by norm_num) unknown who

/-- An absent saved public query stays absent under the analyst's readout. -/
theorem rootedStored_missing
    (obs : List (Option (List (reducedModel fullPrior).PublicSignal))) :
    pbsRootSavedLaw (reducedModel fullPrior) recursiveInitialBelief.law
      (none : Option (PublicBelief (fullInformation rootedChildModel).toInfoSignals obs)) =
      none := rfl

end GameTheory.ReBeL.Examples.HiddenTypes
