/-
# Local CFR realization in the full two-stage hidden-type game

The profile and each replacement local law are arbitrary. The tests use the
actual full-AOH game and canonical continuation values rather than a smaller
normal-form example, a convenient Plan family, or an assumed realization law.
-/

import GameTheory.Analysis.ReBeL.LocalRegret
import GameTheory.ReBeL.Examples.Schedule

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Math.Probability

/-- Enumerate the complete legal history carrier for all information fibers. -/
local instance localRegretHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Equality is used only to install a law at a specified full-AOH site. -/
local instance (who : Player) : DecidableEq ((model fullPrior).InfoState who) :=
  Classical.decEq _

/-- Every actual information site admits the proven local regret realization,
for arbitrary behavioral opponents, local laws, payoffs, and continuation cuts. -/
theorem fullGame_local_regret_realization
    (strategy : Profile (model fullPrior).behavioralSignature)
    (who : Player) (site : (model fullPrior).InformationSite who)
    (law : FinDist ((model fullPrior).Choice who site.1))
    (payoff : (protocol fullPrior).History → ℝ) (fuel : ℕ) :
    (model fullPrior).localCounterfactualRegretVector
      ((model fullPrior).strategyWithLocalLaw strategy who site law) who site payoff fuel =
    GameTheory.Analysis.Approachability.regretPayoff
      (fun choice (_environment : Unit) =>
        (model fullPrior).counterfactualActionUtility strategy who site payoff fuel choice)
      law () := by
  classical
  exact localVector_withLaw_eq_regretPayoff (model fullPrior)
    ((model fullPrior).actsOnceWhereItMatters_of_perfectRecall (perfectRecall fullPrior))
    strategy who site law payoff fuel

/-- A cut with no continuation cannot create a fictitious local gain. -/
theorem fullGame_zero_fuel_regret
    (strategy : Profile (model fullPrior).behavioralSignature)
    (who : Player) (site : (model fullPrior).InformationSite who)
    (payoff : (protocol fullPrior).History → ℝ)
    (choice : (model fullPrior).Choice who site.1) :
    (model fullPrior).counterfactualActionRegret strategy who site payoff 0 choice = 0 := by
  classical
  simp [InformationModel.counterfactualActionRegret,
    InformationModel.counterfactualRegret, InformationModel.counterfactualContinuationValue,
    InformationModel.behavioralContinuationValue, InformationModel.runBehavioralFrom]

/-- Absorbed terminal continuations are constant for every local-law update. -/
theorem fullGame_terminal_continuation
    (strategy : Profile (model fullPrior).behavioralSignature) (who : Player)
    (replacement : (model fullPrior).BehavioralPolicy who)
    (guess : Bool) (payoff : (protocol fullPrior).History → ℝ) (fuel : ℕ) :
    (model fullPrior).behavioralContinuationValue strategy who replacement payoff fuel
      (offPathFinish guess) = payoff (offPathFinish guess) := by
  unfold InformationModel.behavioralContinuationValue
  rw [InformationModel.runBehavioralFrom_of_terminal]
  · exact FinDist.expect_pure _ _
  · trivial

end GameTheory.ReBeL.Examples.HiddenTypes
