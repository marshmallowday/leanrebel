/-
# Live-cut and off-path controls for the constructed exact driver

The first strategic round is learned by CFR-D; the second is a genuinely
live exact child solve. The tests call derived contracts, never assume them.
The negative control rejects whole-profile equality under trunk restoration.
-/

import GameTheory.Analysis.ReBeL.CFRDExactSafety
import GameTheory.Analysis.ReBeL.Examples.CFRDFactualChild

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Finite canonical histories for the constructed-driver controls. -/
local instance exactDriverHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior
/-- Proof-level information equality does not reveal hidden game state. -/
local instance exactDriverInfoDecidable (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _
/-- Actual finite legal menus, including inactive decisions. -/
local instance exactDriverChoiceFintype (who : Player) (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- A live depth-two driver: the remaining second round is not searched by its trunk. -/
def exactDriverControlOracle : CFRDValueOracle (model fullPrior) :=
  cfrDConstructedExactOracle (reducedModel fullPrior) cfrFallback cfrPayoff 2 1

/-- Exact values are derived at every actual round, not supplied in the example. -/
theorem exactDriverControl_accurate :
    CFRDDepthAccurate (model fullPrior) (fullObservationClock (reducedModel fullPrior))
      cfrFallback cfrPayoff 2 1 exactDriverControlOracle 0 :=
  cfrDConstructedExactOracle_accurate (reducedModel fullPrior) cfrFallback cfrPayoff 2 1

/-- Every round's completed live continuation controls all behavioral deviations. -/
theorem exactDriverControl_leafOptimal :
    CFRDDepthLeafOptimal (model fullPrior) (fullObservationClock (reducedModel fullPrior))
      cfrFallback cfrPayoff 2 1 exactDriverControlOracle 0 :=
  cfrDConstructedExactOracle_leafOptimal (reducedModel fullPrior) cfrFallback cfrPayoff 2 1

/-- This non-full-search example has a derived finite-iteration full-game Nash bound. -/
theorem exactDriverControl_isNash (t : Nat) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrDDepthMeanBudget (model fullPrior) (fullObservationClock (reducedModel fullPrior))
            cfrFallback 2 1 2 0 0 0 t +
          cfrDDepthMeanBudget (model fullPrior) (fullObservationClock (reducedModel fullPrior))
            cfrFallback 2 1 2 0 0 1 t)
        (fun history who => cfrPayoff who history))
      (cfrDDepthAveragedProfile (model fullPrior) (fullObservationClock (reducedModel fullPrior))
        cfrFallback cfrPayoff 2 1 exactDriverControlOracle t) :=
  cfrDConstructedExactOracle_isNash (reducedModel fullPrior) cfrFallback cfrPayoff
    (cumulative_zeroSum fullPrior) 2 1 2 (by norm_num) cfrPayoff_abs_le_two t

/-- The actual completed oracle continuation, including factual-zero branches. -/
def exactDriverControlContinuation : Profile (model fullPrior).behavioralSignature :=
  cfrDExactContinuation (reducedModel fullPrior) (carriedBitProfile false)
    cfrFallback 2 1 (fun history who => cfrPayoff who history)

/-- Restoring the prefix preserves every deviation at a legal zero-own-reach root. -/
theorem exactDriverControl_offPath_deviation (who : Player)
    (target : (model fullPrior).BehavioralPolicy who) :
    (model fullPrior).runBehavioralFrom
        (Profile.update (cfrDDepthProfile (model fullPrior)
          (fullObservationClock (reducedModel fullPrior)) 2 (carriedBitProfile false)
          exactDriverControlContinuation) who target) 1 zeroControlHistory =
      (model fullPrior).runBehavioralFrom
        (Profile.update exactDriverControlContinuation who target) 1 zeroControlHistory :=
  cfrDDepthProfile_deviation_atCut (model fullPrior)
    (fullObservationClock (reducedModel fullPrior)) (carriedBitProfile false)
    exactDriverControlContinuation 2 1 zeroControlHistory rfl who target

/-- No live-child assumption is required at the zero-remaining-fuel boundary. -/
theorem exactDriverControl_zero_remaining :
    CFRDDepthLeafOptimal (model fullPrior) (fullObservationClock (reducedModel fullPrior))
      cfrFallback cfrPayoff 3 0
      (cfrDConstructedExactOracle (reducedModel fullPrior) cfrFallback cfrPayoff 3 0) 0 :=
  cfrDConstructedExactOracle_leafOptimal (reducedModel fullPrior) cfrFallback cfrPayoff 3 0

/-- Whole-profile equality is false: restoring the searched first-round policy
changes a real legal action. Only the proved conditional-at-cut equality is used. -/
theorem exactDriverControl_clamp_not_profile_eq :
    cfrDDepthProfile (model fullPrior) (fullObservationClock (reducedModel fullPrior))
        2 (carriedBitProfile false) (carriedBitProfile true) ≠ carriedBitProfile true := by
  intro same
  have before : (fullObservationClock (reducedModel fullPrior)).depth 0
      ((model fullPrior).infoOf 0 (decode (.drawn false false)).trace) < 2 := by
    rw [(fullObservationClock (reducedModel fullPrior)).correct]
    decide
  have evaluated := congrArg (fun strategy : Profile (model fullPrior).behavioralSignature =>
    (strategy 0 ((model fullPrior).infoOf 0 (decode (.drawn false false)).trace)).prob
      (rowChoiceEquiv 0 (.drawn false false) false)) same
  simp only [cfrDDepthProfile, cfrDDepthTrunk, decide_eq_true_eq, if_pos before] at evaluated
  rw [zeroControl_draw_prob, zeroControl_draw_prob] at evaluated
  norm_num at evaluated

end GameTheory.ReBeL.Examples.HiddenTypes
