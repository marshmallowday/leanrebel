/-
# Equal-depth locality in the full hidden-type game

The two sites belong to distinct observations of the same player. Changing one
must not leak into the other, even though both occur at the same trace depth.
The profile, replacement law, payoff, continuation horizon and tested action
are arbitrary; this is not an on-path or fixed-plan calculation.
-/

import GameTheory.Analysis.ReBeL.ChronologicalLocality
import GameTheory.ReBeL.Examples.Schedule

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Math.Probability

/-- All legal histories are retained, including off-path information fibers. -/
local instance localityHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Local updates use equality only on a player's own full AOH. -/
local instance localityInfoDecidableEq (who : Player) :
    DecidableEq ((model fullPrior).InfoState who) := Classical.decEq _

/-- Updating a distinct private-information site at the same depth leaves
all canonical local regrets at the other site unchanged. -/
theorem equal_depth_update_preserves_regret
    (strategy : Profile (model fullPrior).behavioralSignature)
    (law : FinDist ((model fullPrior).Choice 1 (drawSite (false, true) 1).1))
    (payoff : (protocol fullPrior).History → ℝ) (fuel : ℕ)
    (choice : (model fullPrior).Choice 1 (drawSite (false, false) 1).1) :
    (model fullPrior).counterfactualActionRegret
        (Profile.update strategy 1 ((strategy 1).withLaw (drawSite (false, true) 1).1 law))
        1 (drawSite (false, false) 1) payoff fuel choice =
      (model fullPrior).counterfactualActionRegret strategy 1
        (drawSite (false, false) 1) payoff fuel choice := by
  apply actionRegret_withLaw_at_earlier_or_other (model fullPrior) decisionClock
    strategy 1 (drawSite (false, true) 1) (drawSite (false, false) 1)
  · simp
  · exact hidden_draw_distinguishable

end GameTheory.ReBeL.Examples.HiddenTypes
