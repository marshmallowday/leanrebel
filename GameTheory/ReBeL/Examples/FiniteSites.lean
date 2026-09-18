/-
# Finite all-history plans on the two-stage hidden-type game

These tests use both simultaneous decision stages and arbitrary behavioral
opponents, not the smaller convenient Plan family. Zero-probability branches
remain in the cover, while finite plan lookup cannot reveal another player's
private type. This file tests the M04 finite-plan slice, not the CFR solver.
-/

import GameTheory.ReBeL.FiniteSites
import GameTheory.ReBeL.Examples.HiddenTypesHistories

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Math.Probability

local instance : Fintype (protocol fullPrior).History := historyFintype fullPrior

/-- Every arbitrary fixed behavioral opponent has an attaining pure best
response for the complete two-stage payoff in the canonical game. -/
theorem fullGame_bestResponse_attained
    (behavioral : Profile (model fullPrior).behavioralSignature) (who : Player) :
    ∃ policy : (model fullPrior).Policy who,
      IsBestResponse ((model fullPrior).toBehavioralGameForm 3)
        (euPreference (cumulativeUtility (reward fullPrior))) who behavioral policy.toBehavioral :=
  exists_pure_bestResponse (model fullPrior) (perfectRecall fullPrior) (reward fullPrior) 3
    behavioral (fun i => (behavioral i).supportFallback) who

/-- A real legal branch of zero baseline probability is not deleted from
any player's policy-independent information cover. -/
theorem zeroReach_kept_in_cover :
    ((model fullPrior).run (fun i => fullPlanPolicy fullPrior i (baselinePlans i)) 2).prob
        offPathHistory = 0 ∧
      ∀ i, (model fullPrior).infoOf i offPathHistory.trace ∈ finiteSites (model fullPrior) i := by
  refine ⟨offPath_zero_reach, fun i => ?_⟩
  exact (mem_finiteSites (model fullPrior) i _).mpr ⟨offPathHistory, rfl⟩

/-- Predrawing a finite plan does not admit the forbidden omniscient type guess. -/
theorem no_omniscient_finitePlan (fallback : (model fullPrior).Policy 0) :
    ¬ ∃ plan : FinitePlan (model fullPrior) 0,
      (FinitePlan.toPolicy (model fullPrior) fallback plan).act
          ((model fullPrior).infoOf 0 (fullDraw (false, false)).trace) = some false ∧
      (FinitePlan.toPolicy (model fullPrior) fallback plan).act
          ((model fullPrior).infoOf 0 (fullDraw (false, true)).trace) = some true := by
  rintro ⟨plan, first, second⟩
  exact no_omniscient_guess ⟨FinitePlan.toPolicy (model fullPrior) fallback plan, first, second⟩

end GameTheory.ReBeL.Examples.HiddenTypes
