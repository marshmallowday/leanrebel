/-
# A nontrivial zero-own-reach completion and its boundary

The complete original-game law is unchanged against every fixed opponent,
but play and payoff at a legal zero-own-reach continuation do change. A second
history is unreachable only because of the opponent: it must NOT trigger the
completion. All controls use the canonical two-stage hidden-type protocol.
-/

import GameTheory.Analysis.ReBeL.CFRDZeroReachCompletion
import GameTheory.Analysis.ReBeL.Examples.CFRDChildControl

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Constant-bit play has the exact canonical first-action probability. -/
theorem zeroControl_draw_prob (bit : Bool) (who : Player) (x y action : Bool) :
    (carriedBitProfile bit who
        ((model fullPrior).infoOf who (decode (.drawn x y)).trace)).prob
        (rowChoiceEquiv who (.drawn x y) action) = if action = bit then 1 else 0 := by
  classical
  have law : carriedBitProfile bit who
      ((model fullPrior).infoOf who (decode (.drawn x y)).trace) =
      FinDist.pure (rowChoiceEquiv who (.drawn x y) bit) := rfl
  rw [law, FinDist.prob_pure_eq_ite]
  by_cases same : action = bit
  · subst action
    simp
  · rw [if_neg (fun equal => same ((rowChoiceEquiv who (.drawn x y)).injective equal)),
      if_neg same]

/-- Own reach, rather than joint reach, decides whether completion is allowed. -/
theorem zeroControl_own_reach (bit : Bool) (who : Player) (x y a b : Bool) :
    (model fullPrior).playerReachProbability (carriedBitProfile bit) who
      (decode (.second x y a b)).trace =
        if GameTheory.ReBeL.Rational.HiddenTypes.own who a b = bit then 1 else 0 := by
  rw [playerReach_second, zeroControl_draw_prob]

/-- Legal zero-own-reach continuation: the focal first action was true. -/
def zeroControlHistory : (protocol fullPrior).History :=
  decode (.second false false true false)

/-- The baseline assigns zero OWN reach to this legal history. -/
theorem zeroControl_information_zero :
    informationOwnReach (model fullPrior) (carriedBitProfile false) 0
      ((model fullPrior).infoOf 0 zeroControlHistory.trace) = 0 := by
  rw [informationOwnReach_eq_player (model fullPrior) (perfectRecall fullPrior),
    zeroControlHistory, zeroControl_own_reach]
  norm_num [GameTheory.ReBeL.Rational.HiddenTypes.own]

/-- A genuine completion uses the opposite action only where own reach vanishes. -/
def zeroControlCompleted : Profile (model fullPrior).behavioralSignature :=
  cfrDCompleteZeroReach (model fullPrior) (carriedBitProfile false) (carriedBitProfile true)

/-- At the zero-own-reach history the completed focal action really is changed. -/
theorem zeroControl_completed_second :
    liveSecondLaw zeroControlCompleted false false true false 0 = FinDist.pure true := by
  unfold liveSecondLaw zeroControlCompleted
  have zero := zeroControl_information_zero
  dsimp only [zeroControlHistory] at zero
  rw [cfrDCompleteZeroReach_of_zero (model fullPrior) _ _ 0 _ zero]
  exact carriedBit_second_law true false false true false 0

/-- Every seed-blind opposing policy sees the unchanged complete original-game law. -/
theorem zeroControl_all_opponents
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player) (horizon : Nat) :
    (model fullPrior).runBehavioral (Profile.update unknown who (zeroControlCompleted who))
        horizon =
      (model fullPrior).runBehavioral
        (Profile.update unknown who (carriedBitProfile false who)) horizon :=
  cfrDCompleteZeroReach_unilateral_run (model fullPrior) (perfectRecall fullPrior)
    (carriedBitProfile false) (carriedBitProfile true) unknown who horizon

/-- The original continuation loses both rounds at this legal off-path history. -/
theorem zeroControl_before_value :
    ((model fullPrior).runBehavioralFrom (carriedBitProfile false) 1
      zeroControlHistory).expect (cfrPayoff 0) = -2 := by
  rw [zeroControlHistory, liveSecond_value, carriedBit_second_law, carriedBit_second_law]
  norm_num [FinDist.expect_pure, signed, winValue]

/-- The completed focal action improves this off-path continuation by two,
without changing any original-game law asserted by zeroControl_all_opponents. -/
theorem zeroControl_after_value :
    ((model fullPrior).runBehavioralFrom
      (Profile.update (carriedBitProfile false) 0 (zeroControlCompleted 0)) 1
      zeroControlHistory).expect (cfrPayoff 0) = 0 := by
  have focal : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0 (zeroControlCompleted 0))
        false false true false 0 = FinDist.pure true := by
    unfold liveSecondLaw
    rw [Profile.update_same]
    exact zeroControl_completed_second
  have other : liveSecondLaw
      (Profile.update (carriedBitProfile false) 0 (zeroControlCompleted 0))
        false false true false 1 = FinDist.pure false := by
    unfold liveSecondLaw
    rw [Profile.update_of_ne _ _ (by decide : (1 : Player) ≠ 0)]
    exact carriedBit_second_law false false false true false 1
  rw [zeroControlHistory, liveSecond_value, focal, other]
  norm_num [FinDist.expect_pure, signed, winValue]

/-- A different legal history is excluded only by the opponent's first action. -/
def zeroControlOpponentHistory : (protocol fullPrior).History :=
  decode (.second false false false true)

/-- Zero joint probability can coexist with positive focal own reach. -/
theorem zeroControl_joint_zero :
    ((model fullPrior).runBehavioral (carriedBitProfile false) 2).prob
      zeroControlOpponentHistory = 0 := by
  rw [run_probability_factorization (model fullPrior), Fin.prod_univ_two,
    zeroControlOpponentHistory, zeroControl_own_reach, zeroControl_own_reach]
  norm_num [GameTheory.ReBeL.Rational.HiddenTypes.own]

/-- This opponent-excluded history has focal own reach one, not zero. -/
theorem zeroControl_opponent_information_one :
    informationOwnReach (model fullPrior) (carriedBitProfile false) 0
      ((model fullPrior).infoOf 0 zeroControlOpponentHistory.trace) = 1 := by
  rw [informationOwnReach_eq_player (model fullPrior) (perfectRecall fullPrior),
    zeroControlOpponentHistory, zeroControl_own_reach]
  norm_num [GameTheory.ReBeL.Rational.HiddenTypes.own]

/-- The completion correctly leaves play unchanged at zero-joint-only histories. -/
theorem zeroControl_opponent_exclusion_not_completed :
    zeroControlCompleted 0
        ((model fullPrior).infoOf 0 zeroControlOpponentHistory.trace) =
      carriedBitProfile false 0
        ((model fullPrior).infoOf 0 zeroControlOpponentHistory.trace) := by
  apply cfrDCompleteZeroReach_of_ne
  rw [zeroControl_opponent_information_one]
  exact one_ne_zero

end GameTheory.ReBeL.Examples.HiddenTypes
