/-
# Actual CFR guarantees in the two-stage hidden-type game

The instance has chance, simultaneous moves, private information, physical
state merges and off-path decisions. Every premise is supplied by this game;
no convenient Plan subfamily restricts the final behavioral deviations.
-/

import GameTheory.Analysis.ReBeL.CFRNash
import GameTheory.ReBeL.Examples.Schedule

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Math.Probability

/-- Every legal history, not just the current policy support, is enumerated. -/
local instance cfrHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- This proof-level equality test does not enlarge a player's observations. -/
local instance cfrInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Menus are subtypes of the finite optional Boolean action carrier. -/
local instance cfrChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) :
    Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- A specified total legal fallback on full action-observation histories. -/
def cfrFallback (who : Player) : (model fullPrior).Policy who :=
  fullPlanPolicy fullPrior who (baselinePlans who)

/-- The solver evaluates the actual accumulated stage rewards. -/
def cfrPayoff (who : Player) (history : (protocol fullPrior).History) : ℝ :=
  cumulativeUtility (reward fullPrior) history who

/-- Two unit-magnitude stage rewards bound all histories, even partial ones. -/
theorem cfrPayoff_abs_le_two (who : Player) (history : (protocol fullPrior).History) :
    |cfrPayoff who history| ≤ 2 := by
  unfold cfrPayoff
  rw [cumulative_eq]
  cases history.state with
  | initial => norm_num [potential]
  | first types => norm_num [potential]
  | second types won =>
      fin_cases who <;> cases won <;> norm_num [potential, signed, winValue]
  | finished firstWon finalWon =>
      fin_cases who <;> cases firstWon <;> cases finalWon <;>
        norm_num [potential, signed, winValue]

/-- The concrete two-stage game satisfies the complete generated-solver
Nash guarantee for every positive iteration count and every behavioral deviation. -/
theorem fullGame_cfr_average_isNash (t : ℕ) [NeZero t] :
    IsNash ((model fullPrior).toBehavioralGameForm 3)
      (euPreferenceWithin
        (cfrCumulativeBound (model fullPrior) decisionClock 3 0 2 t / t +
          cfrCumulativeBound (model fullPrior) decisionClock 3 1 2 t / t)
        (fun history who => cfrPayoff who history))
      (cfrAveragedProfile (model fullPrior) decisionClock cfrFallback cfrPayoff 3 t) :=
  cfrAveragedProfile_isNash (model fullPrior) decisionClock (perfectRecall fullPrior)
    cfrFallback cfrPayoff (cumulative_zeroSum fullPrior)
    (fun _ => 2) (fun _ => by norm_num) cfrPayoff_abs_le_two 3 t

/-- Iteration zero has not consumed a payoff observation or performed an update. -/
theorem fullGame_cfr_zero :
    cfrPlay (model fullPrior) decisionClock cfrFallback cfrPayoff 3 0 =
      fun who => (cfrFallback who).toBehavioral :=
  cfrPlay_zero (model fullPrior) decisionClock cfrFallback cfrPayoff 3

end GameTheory.ReBeL.Examples.HiddenTypes
