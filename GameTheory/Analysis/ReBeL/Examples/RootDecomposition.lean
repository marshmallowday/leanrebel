/-
# Whole-policy root decomposition in the genuine hidden-type game

All behavioral deviations are quantified. The concrete game includes a chance
transition, simultaneous decisions, merging states, private information and
zero-reach decisions. No convenient finite Plan family restricts deviations.
-/

import GameTheory.Analysis.ReBeL.RootDecomposition
import GameTheory.ReBeL.Examples.Schedule

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Math.Probability

/-- The complete legal history carrier supplies every information fiber. -/
local instance rootHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Deciding equality never gives a policy access to another player's type. -/
local instance rootInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- The full two-stage game satisfies the constructed decomposition for
arbitrary payoff observables, opponents and complete behavioral deviations. -/
theorem fullGame_root_decomposition
    (strategy : Profile (model fullPrior).behavioralSignature)
    (who : Player) (target : (model fullPrior).BehavioralPolicy who)
    (payoff : (protocol fullPrior).History → ℝ) :
    ((model fullPrior).runBehavioral (Profile.update strategy who target) 3).expect payoff -
        ((model fullPrior).runBehavioral strategy 3).expect payoff =
      ((scheduledSites (model fullPrior) decisionClock 3 who).map
        (targetRegretTerm (model fullPrior) decisionClock strategy who target payoff 3)).sum :=
  scheduled_root_gain (model fullPrior) decisionClock (perfectRecall fullPrior)
    strategy who target payoff 3

/-- The same theorem has an empty sum at zero fuel; no fictitious initial
iteration or decision contributes to the root difference. -/
theorem fullGame_zero_cut_root_gain
    (strategy : Profile (model fullPrior).behavioralSignature)
    (who : Player) (target : (model fullPrior).BehavioralPolicy who)
    (payoff : (protocol fullPrior).History → ℝ) :
    ((model fullPrior).runBehavioral (Profile.update strategy who target) 0).expect payoff -
        ((model fullPrior).runBehavioral strategy 0).expect payoff = 0 := by
  rw [scheduled_root_gain (model fullPrior) decisionClock (perfectRecall fullPrior)]
  simp

end GameTheory.ReBeL.Examples.HiddenTypes
