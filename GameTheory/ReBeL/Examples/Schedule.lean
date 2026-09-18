/-
# Exhaustive scheduling on the genuine two-stage hidden-type game

The tests retain zero-reach decisions and distinct equal-depth information
sites. Both players' information contains their own previous actions. Neither
a smaller convenient Plan family nor a reference strategy selects the sites.
-/

import GameTheory.ReBeL.Schedule
import GameTheory.ReBeL.Examples.HiddenTypesHistories

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Math.Probability

/-- Enumerate every legal history, not only positive-probability histories. -/
local instance scheduleHistoryFintype : Fintype (protocol fullPrior).History := historyFintype fullPrior

/-- The two-stage game uses the length of the player's own full AOH. -/
def decisionClock : ObservationClock (model fullPrior) :=
  fullObservationClock (reducedModel fullPrior)

/-- Every actual nonterminal decision in the entire game is scheduled. -/
theorem all_decisions_scheduled (who : Player) (history : (protocol fullPrior).History)
    (hterm : ¬ (protocol fullPrior).terminal history.state)
    (hactive : (protocol fullPrior).active history.state who) :
    ∃ site ∈ scheduledSites (model fullPrior) decisionClock 3 who,
      site.1 = (model fullPrior).infoOf who history.trace := by
  apply scheduledSites_covers (model fullPrior) decisionClock 3 who history _ hterm hactive
  by_contra h
  exact hterm (bounded fullPrior history.state history.trace (by omega))

/-- A zero-reach second-stage history still contributes an information site
for each player to the production schedule. -/
theorem zeroReach_decisions_scheduled :
    ((model fullPrior).run (fun i => fullPlanPolicy fullPrior i (baselinePlans i)) 2).prob
      offPathHistory = 0 ∧
    ∀ who, ∃ site ∈ scheduledSites (model fullPrior) decisionClock 3 who,
      site.1 = (model fullPrior).infoOf who offPathHistory.trace := by
  refine ⟨offPath_zero_reach, fun who => ?_⟩
  exact all_decisions_scheduled who offPathHistory offPath_nonterminal (by trivial)

/-- The canonical decision information site after a supported nature draw. -/
def drawSite (types : Types) (who : Player) : (model fullPrior).InformationSite who :=
  (model fullPrior).informationSite who (fullDraw types) false
    (by intro impossible; exact impossible)
    (by apply ((model fullPrior).menu_adequate who (fullDraw types).trace _).mpr; trivial)

/-- First-stage decisions occur after the chance transition, at depth one. -/
@[simp]
theorem drawSite_depth (types : Types) (who : Player) :
    decisionClock.depth who (drawSite types who).1 = 1 :=
  decisionClock.correct who (fullDraw types)

/-- The stable chronological order keeps distinct sites at the same depth.
The example uses private information legitimately available to player one. -/
theorem equal_depth_sites_retained :
    drawSite (false, false) 1 ∈ scheduledSites (model fullPrior) decisionClock 3 1 ∧
    drawSite (false, true) 1 ∈ scheduledSites (model fullPrior) decisionClock 3 1 ∧
    drawSite (false, false) 1 ≠ drawSite (false, true) 1 ∧
    decisionClock.depth 1 (drawSite (false, false) 1).1 =
      decisionClock.depth 1 (drawSite (false, true) 1).1 := by
  refine ⟨?_, ?_, ?_, by simp⟩
  · apply (mem_scheduledSites (model fullPrior) decisionClock 3 1 _).mpr
    simp
  · apply (mem_scheduledSites (model fullPrior) decisionClock 3 1 _).mpr
    simp
  · intro equal
    exact hidden_draw_distinguishable (congrArg Subtype.val equal)

/-- A zero-step game cut schedules no fictitious local decision. -/
theorem zero_cut_has_no_decisions (who : Player) :
    scheduledSites (model fullPrior) decisionClock 0 who = [] :=
  scheduledSites_zero (model fullPrior) decisionClock who

end GameTheory.ReBeL.Examples.HiddenTypes
