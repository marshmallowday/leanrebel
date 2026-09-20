/-
# Finite-iteration and posterior-budget controls

The learner changes an actual action after its first payoff update. A live
canonical hidden-type PBS is solved by the finite recurrence, not by an exact
Nash selection. The mass-floor counterexample excludes a single positive
floor for all learned beliefs.
-/

import GameTheory.Analysis.ReBeL.PBSFinitePlanSolver
import GameTheory.Analysis.ReBeL.Examples.CFRDFactualChild

noncomputable section

namespace GameTheory.ReBeL.Examples.FinitePlan

open GameTheory.Math.Probability GameTheory.MatrixGame

/-- A profitable row action with a passive zero-sum opponent. -/
def gainMatrix (row : Bool) (_column : Unit) : ℝ := if row then 1 else 0

/-- The existing canonical finite matrix game, not a new execution model. -/
abbrev gainGame := utilityGame gainMatrix

/-- Explicit finite carriers for both dependent strategy coordinates. -/
local instance gainStrategyFintype (who : Fin 2) :
    Fintype (gainGame.form.sig.Strategy who) :=
  Fin.cases (inferInstanceAs (Fintype Bool))
    (fun tail : Fin 1 => Fin.cases (inferInstanceAs (Fintype Unit))
      (fun empty : Fin 0 => empty.elim0) tail) who

/-- Initial fallback declines the profitable action. -/
def gainInitial : Profile gainGame.form.sig := pureProfile false ()

/-- The first computed regret table records zero and one, not an assumed bound. -/
theorem first_regret_table (action : Bool) :
    (finiteGameRegretState gainGame gainInitial 1 0).ofLp action =
      if action then 1 else 0 := by
  have table := finiteGameRegretState_coordinate_sum gainGame gainInitial 0 action 1
  simp only [Nat.cast_one, one_mul, Finset.sum_range_one, finiteGameRegretPlay_zero] at table
  have initial : gainGame.form.purify gainInitial =
      mixedProfile (FinDist.pure false) (FinDist.pure ()) := (mixedProfile_pure false ()).symm
  rw [initial, finiteGameActionValue, mixedProfile_update_zero,
    expectedUtility_zero_mixedProfile, expectedUtility_zero_mixedProfile,
    expectedPayoff_pure_row, expectedPayoff_pure_row, FinDist.expect_pure,
    FinDist.expect_pure] at table
  simpa [gainMatrix] using table

/-- Real feedback makes the next row law choose the profitable action. -/
theorem second_play_changes_action :
    finiteGameRegretPlay gainGame gainInitial 1 0 = FinDist.pure true := by
  classical
  have total : (∑ action : Bool,
      max ((finiteGameRegretState gainGame gainInitial 1 0).ofLp action) 0) = 1 := by
    simp_rw [first_regret_table]
    norm_num [Fintype.sum_bool]
  apply FinDist.ext_of_prob
  intro action
  unfold finiteGameRegretPlay finiteGameRegretProfile
  rw [regretMatchWith, dif_pos (by rw [total]; norm_num), FinDist.prob_ofWeights,
    total, first_regret_table, FinDist.prob_pure_eq_ite]
  cases action <;> norm_num

/-- The generated trace is not a constant fallback or an unrelated Nash witness. -/
theorem generated_trace_nonconstant :
    finiteGameRegretPlay gainGame gainInitial 0 0 ≠
      finiteGameRegretPlay gainGame gainInitial 1 0 := by
  rw [finiteGameRegretPlay_zero, second_play_changes_action]
  intro equal
  have masses := congrArg (fun law : FinDist Bool => law.prob false) equal
  norm_num [gainInitial, GameForm.purify, pureProfile] at masses

/-- A concrete finite budget is certified for all mixed plan deviations. -/
theorem gain_budget_solve (error : ℝ) (positive : 0 < error) :
    IsNash gainGame.form.mixed (euPreferenceWithin error gainGame.utility)
      (finiteGameBudgetSolution gainGame.form gainGame.utility gainInitial 1 error) := by
  apply finiteGameBudgetSolution_isNash gainGame.form gainGame.utility
    (utility_isZeroSum gainMatrix) gainInitial 1 (by norm_num) _ error positive
  intro outcome who
  fin_cases who <;> cases outcome.1 <;> norm_num [utilityGame, utility, gainMatrix]

/-- Every proposed global positive floor is refuted by a genuine finite law.
The constructor instead computes a different positive floor for each PBS. -/
theorem no_uniform_positive_floor (claimed : ℝ) (positive : 0 < claimed) :
    ∃ law : FinDist Bool, law.positiveMassFloor < claimed := by
  let p := min (claimed / 2) (1 / 2)
  have hp : 0 < p := lt_min (half_pos positive) (by norm_num)
  have hp1 : p ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let law := FinDist.mix p hp.le hp1 (FinDist.pure false) (FinDist.pure true)
  have probability : law.prob false = p := by
    simp [law, FinDist.prob_mix]
  have member : false ∈ law.support := FinDist.prob_pos_iff.mp (by rw [probability]; exact hp)
  refine ⟨law, ?_⟩
  have floor := law.positiveMassFloor_le false member
  rw [probability] at floor
  exact floor.trans_lt ((min_le_left _ _).trans_lt (half_lt_self positive))

end GameTheory.ReBeL.Examples.FinitePlan

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- Explicit finite canonical histories for the actual live PBS solve. -/
local instance finiteBudgetHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The actual factual live posterior supplied by canonical stopped play. -/
def finiteBudgetControlBelief :=
  cfrDFactualChildBelief (reducedModel fullPrior) (carriedBitProfile false) 2 1
    (publicTrace (model fullPrior).toInfoSignals factualChildHistory.trace) factualChild_possible

/-- The finite solve is used at a child where another strategic round remains.
Its approximate Nash property is derived from the recurrence and a payoff bound. -/
theorem finiteBudget_live_child (error : ℝ) (positive : 0 < error) :
    IsNash (behavioralBeliefForm (model fullPrior) finiteBudgetControlBelief 1)
      (euPreferenceWithin error (fun h who => cfrPayoff who h))
      (pbsFiniteBudgetProfile (model fullPrior) decisionClock cfrFallback
        finiteBudgetControlBelief 1 (fun h who => cfrPayoff who h) 2 error) :=
  pbsFiniteBudgetProfile_isNash (model fullPrior) (perfectRecall fullPrior) decisionClock
    cfrFallback finiteBudgetControlBelief 1 (fun h who => cfrPayoff who h)
    (cumulative_zeroSum fullPrior) 2 (by norm_num)
    (fun history who => cfrPayoff_abs_le_two who history) error positive

end GameTheory.ReBeL.Examples.HiddenTypes
