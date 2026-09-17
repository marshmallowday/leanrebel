/-
# A nonuniform public observation and an exact two-to-one posterior

Three actual dice histories have masses 1/2, 1/4, 1/4. The first two share the
public observation and the third is excluded. Conditioning gives 2/3, 1/3,
not the prior and not a uniform law on the remaining histories.
-/

import GameTheory.ReBeL.Examples.ObservedDice
import GameTheory.ReBeL.Belief

noncomputable section

namespace GameTheory.ReBeL.Examples.ObservedDice

open GameTheory.Protocol ExecutionProtocol GameTheory.Math.Probability

/-- The first hidden roll compatible with the public dice (4,6). -/
def bayesFirst : protocol.History := draw ((0, 3), (4, 5))
/-- A second hidden roll with exactly the same public dice. -/
def bayesSecond : protocol.History := draw ((1, 3), (4, 5))
/-- A third legal roll with different public dice. -/
def bayesOther : protocol.History := draw ((0, 0), (0, 0))

/-- The incoming law is supported on legal histories, but not one public fiber. -/
def bayesIncoming : FinDist protocol.History :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure bayesFirst)
    (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure bayesSecond) (FinDist.pure bayesOther))

/-- The three histories are physically distinct, not different proof witnesses. -/
theorem bayes_distinct :
    bayesFirst ≠ bayesSecond ∧ bayesFirst ≠ bayesOther ∧ bayesSecond ≠ bayesOther := by
  refine ⟨?_, ?_, ?_⟩
  · intro equal
    have impossible : (0 : Face) = 1 :=
      congrArg (fun h : protocol.History => (hiddenParts h.state).1) equal
    norm_num at impossible
  · intro equal
    have impossible : (4 : Face) = 0 :=
      congrArg (fun h : protocol.History => (hiddenParts h.state).2) equal
    norm_num at impossible
  · intro equal
    have impossible : (1 : Face) = 0 :=
      congrArg (fun h : protocol.History => (hiddenParts h.state).1) equal
    norm_num at impossible

/-- Exactly one quarter of the incoming mass is excluded by the observation. -/
theorem bayes_public_mass :
    bayesIncoming.probOf {h | publicTrace signals h.trace = publicObservations} = 3 / 4 := by
  classical
  rw [← FinDist.expect_indicator_eq_probOf]
  norm_num [bayesIncoming, FinDist.expect_mix, FinDist.expect_pure,
    bayesFirst, bayesSecond, bayesOther, draw, publicTrace, signals,
    publicObservation, publicObservations, History.extend]

/-- The conditional API receives a real positive-support witness. -/
theorem bayes_possible :
    PublicBelief.Possible (S := signals) bayesIncoming publicObservations := by
  refine ⟨bayesFirst, rfl, ?_⟩
  exact FinDist.mem_support_mix_left _ _ _ (by norm_num) (FinDist.mem_support_pure.mpr rfl)

/-- The complete normalized joint posterior, including the still-hidden die. -/
def bayesPosterior : PublicBelief signals publicObservations :=
  PublicBelief.condition bayesIncoming publicObservations bayes_possible

/-- Conditioning changes the masses to 2/3 and 1/3 and gives the excluded history zero. -/
theorem bayes_posterior_probabilities :
    bayesPosterior.law.prob bayesFirst = 2 / 3 ∧
      bayesPosterior.law.prob bayesSecond = 1 / 3 ∧
      bayesPosterior.law.prob bayesOther = 0 := by
  classical
  have firstObserved : publicTrace signals bayesFirst.trace = publicObservations := rfl
  have secondObserved : publicTrace signals bayesSecond.trace = publicObservations := rfl
  have otherExcluded : publicTrace signals bayesOther.trace ≠ publicObservations := by decide
  have distinct := bayes_distinct
  simp only [bayesPosterior, PublicBelief.prob_condition, firstObserved, secondObserved,
    otherExcluded, if_true, if_false, bayes_public_mass]
  norm_num [bayesIncoming, FinDist.prob_mix, FinDist.prob_pure_eq_ite,
    distinct.1, distinct.2.1, distinct.2.2,
    Ne.symm distinct.1, Ne.symm distinct.2.1, Ne.symm distinct.2.2]

/-- On actual post-draw histories the two public dice are a lossless compact public key.
This does not authorize dropping arbitrary history in a non-tree-shaped game. -/
theorem postdraw_public_key (first second : Dice) :
    publicTrace signals (draw first).trace = publicTrace signals (draw second).trace ↔
      (first.1.2, first.2.2) = (second.1.2, second.2.2) := by
  show [some (first.1.2, first.2.2), none] = [some (second.1.2, second.2.2), none] ↔ _
  simp

end GameTheory.ReBeL.Examples.ObservedDice
