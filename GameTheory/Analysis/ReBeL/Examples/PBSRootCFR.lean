/-
# PBS-rooted information-set CFR controls

The positive solve uses an actual live factual posterior from the two-stage
hidden-type game. Further controls retain hidden-information indistinguishability,
nontrivial root correlations, terminal roots and the extra administrative fuel.
-/

import GameTheory.Analysis.ReBeL.PBSRootCFR
import GameTheory.Analysis.ReBeL.PBSRootExecution
import GameTheory.Analysis.ReBeL.PBSRootBehavioral
import GameTheory.Analysis.ReBeL.Examples.PBSFinitePlanSolver

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Use the concrete game's existing exhaustive legal-history enumeration. -/
local instance rootControlHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- An original local fallback, before either full-AOH adapter is applied. -/
def pbsRootControlFallback (who : Player) : (reducedModel fullPrior).Policy who :=
  planPolicy fullPrior who (baselinePlans who)

/-- A genuinely live factual PBS is solved by fixed-T information-set CFR.
The positive finite iteration count is arbitrary, not selected by a Nash witness. -/
theorem pbsRoot_live_cfr (t : Nat) [NeZero t] :
    IsNash ((pbsRootFullInformation (reducedModel fullPrior)
        finiteBudgetControlBelief.law).toBehavioralGameForm 2)
      (euPreferenceWithin
        (pbsRootCFRBound (reducedModel fullPrior) finiteBudgetControlBelief.law (fun _ => 2) 1 t)
        (fun history who => pbsRootPayoff finiteBudgetControlBelief.law cfrPayoff who history))
      (pbsRootCFR (reducedModel fullPrior) finiteBudgetControlBelief.law
        pbsRootControlFallback cfrPayoff 1 t) :=
  pbsRootCFR_isNash (reducedModel fullPrior) finiteBudgetControlBelief.law
    pbsRootControlFallback cfrPayoff (cumulative_zeroSum fullPrior)
    (fun _ => 2) (fun _ => by norm_num) cfrPayoff_abs_le_two 1 t

/-- A genuinely randomized original deviation at a live factual child has
exactly the same law under the rooted full-AOH behavioral runner. -/
theorem pbsRoot_live_randomized_deviation :
    ((pbsRootFullInformation (reducedModel fullPrior) finiteBudgetControlBelief.law).runBehavioral
      (Profile.update
        (pbsRootBehavioralFullProfile (reducedModel fullPrior) finiteBudgetControlBelief.law
          carriedBitOpponent) 0
        (pbsRootBehavioralFullPolicy (reducedModel fullPrior) finiteBudgetControlBelief.law
          0 freshBitPolicy)) 2).map History.state =
      (finiteBudgetControlBelief.law.bind ((model fullPrior).runBehavioralFrom
        (Profile.update carriedBitOpponent 0 freshBitPolicy) 1)).map some :=
  pbsRoot_behavioralFull_unilateral_law (reducedModel fullPrior) finiteBudgetControlBelief.law
    carriedBitOpponent 0 freshBitPolicy 1

/-- Two supported hidden roots differ only in player one's private bit. -/
def pbsRootHiddenRoots : FinDist (protocol fullPrior).History :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (fullDraw (false, false))) (FinDist.pure (fullDraw (false, true)))

/-- Actual chance-root history for the first hidden outcome. -/
def pbsRootHiddenFirst : (pbsRootProtocol pbsRootHiddenRoots).History :=
  pbsRootDrawHistory pbsRootHiddenRoots (fullDraw (false, false))
    (FinDist.mem_support_mix_left (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (FinDist.mem_support_pure.mpr rfl))

/-- Actual chance-root history for the second hidden outcome. -/
def pbsRootHiddenSecond : (pbsRootProtocol pbsRootHiddenRoots).History :=
  pbsRootDrawHistory pbsRootHiddenRoots (fullDraw (false, true))
    (FinDist.mem_support_mix_right (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (FinDist.mem_support_pure.mpr rfl))

/-- Even the complete rooted local AOH does not reveal the opponent's hidden bit. -/
theorem pbsRoot_full_no_hidden_leak :
    (pbsRootFullInformation (reducedModel fullPrior) pbsRootHiddenRoots).infoOf
        0 pbsRootHiddenFirst.trace =
      (pbsRootFullInformation (reducedModel fullPrior) pbsRootHiddenRoots).infoOf
        0 pbsRootHiddenSecond.trace := rfl

/-- Every legal behavioral policy, not just a convenient plan family, must agree. -/
theorem pbsRoot_policy_no_hidden_leak
    (policy : (pbsRootFullInformation (reducedModel fullPrior)
      pbsRootHiddenRoots).BehavioralPolicy 0) :
    policy ((pbsRootFullInformation (reducedModel fullPrior) pbsRootHiddenRoots).infoOf
        0 pbsRootHiddenFirst.trace) =
      policy ((pbsRootFullInformation (reducedModel fullPrior) pbsRootHiddenRoots).infoOf
        0 pbsRootHiddenSecond.trace) := rfl

/-- A correlated joint root law, not the product of its two fair marginals. -/
def pbsRootDiagonal : FinDist (protocol fullPrior).History :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure (fullDraw (false, false))) (FinDist.pure (fullDraw (true, true)))

/-- A bounded test observable of the retained original joint type. -/
def pbsRootSameType : Option (protocol fullPrior).History → ℝ
  | none => 0
  | some history => match history.state with
    | .first types => if types.1 = types.2 then 1 else 0
    | _ => 0

/-- The actual randomized runner preserves the perfect correlation of the root law. -/
theorem pbsRoot_correlation_preserved (chooser : (protocol fullPrior).RandomizedChooser) :
    (((pbsRootProtocol pbsRootDiagonal).runRandomizedFor
      (pbsRootChooser pbsRootDiagonal chooser) 1
      (pbsRootProtocol pbsRootDiagonal).initHistory).map History.state).expect
        pbsRootSameType = 1 := by
  rw [pbsRoot_run_one, FinDist.expect_map]
  norm_num [pbsRootDiagonal, FinDist.expect_mix, FinDist.expect_pure, pbsRootSameType,
    fullDraw, drawHistory, History.extend]

/-- An already terminal sampled root never asks the original chooser for another action. -/
theorem pbsRoot_terminal_stops (chooser : (protocol fullPrior).RandomizedChooser) (fuel : Nat) :
    ((pbsRootProtocol (FinDist.pure (offPathFinish false))).runRandomizedFor
      (pbsRootChooser (FinDist.pure (offPathFinish false)) chooser) (fuel + 1)
      (pbsRootProtocol (FinDist.pure (offPathFinish false))).initHistory).map History.state =
      FinDist.pure (some (offPathFinish false)) := by
  rw [pbsRoot_run_initial, FinDist.pure_bind,
    runRandomizedFor_of_terminal chooser fuel (by trivial), FinDist.map_pure]

/-- Zero administrative fuel must not be confused with zero continuation fuel. -/
theorem pbsRoot_zero_does_not_draw (chooser : (protocol fullPrior).RandomizedChooser) :
    ((pbsRootProtocol pbsRootDiagonal).runRandomizedFor (pbsRootChooser pbsRootDiagonal chooser)
      0 (pbsRootProtocol pbsRootDiagonal).initHistory).map History.state ≠
      pbsRootDiagonal.map some := by
  rw [runRandomizedFor_zero, FinDist.map_pure]
  intro equal
  have member : (none : Option (protocol fullPrior).History) ∈
      (pbsRootDiagonal.map some).support := by
    rw [← equal]
    exact FinDist.mem_support_pure.mpr rfl
  rw [FinDist.support_map] at member
  obtain ⟨history, _, impossible⟩ := member
  cases impossible

end GameTheory.ReBeL.Examples.HiddenTypes
