/-
# Opponent/model transport controls

The live consumer uses a computed information-set CFR child and the actual
history's point mass. Finite-law controls separately expose lost model support
and the wrong-prefix-law error; they are not purported CFR regret tables.
-/

import GameTheory.Analysis.ReBeL.PBSOpponentModelTransport
import GameTheory.Analysis.ReBeL.Examples.PBSConditionedNativeGap

noncomputable section

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Include the entire legal history carrier, not only currently reached histories. -/
local instance opponentModelHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- The actual budget-1/8 child is executed for one live step from an actual
history, not a replacement draw from its model PBS. Its model-support failure
has the derived source charge against arbitrary fixed legal opponents. -/
theorem pbsOpponentModelTransport_live
    (unknown : Profile (fullInformation (reducedModel fullPrior)).behavioralSignature)
    (history : (protocol fullPrior).History) :
    let M := fullInformation (reducedModel fullPrior)
    let chosen := pbsInformationBudgetProfile (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 (1 / 8)
    (M.runBehavioralFrom (Profile.update unknown 0 (chosen 0)) 1 history).probOf
      {h | ¬ ∃ next, carriedBeliefUpdate M (some finiteBudgetControlBelief) chosen 1
        (publicTrace M.toInfoSignals h.trace) = some next ∧ h ∈ next.law.support} ≤
      carriedOpponentModelCharge M finiteBudgetControlBelief (FinDist.pure history)
        chosen unknown 0 1 := by
  intro M chosen
  simpa only [FinDist.pure_bind] using
    carriedBeliefUpdate_failure_probability_le M finiteBudgetControlBelief
      (FinDist.pure history) chosen unknown 0 1

/-- At the identical stored model and incoming law, the same real child has
zero discrepancy. This does not assert equality for an unknown opponent. -/
theorem pbsOpponentModelTransport_matched :
    let M := fullInformation (reducedModel fullPrior)
    let chosen := pbsInformationBudgetProfile (reducedModel fullPrior) finiteBudgetControlBelief
      pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 (1 / 8)
    carriedOpponentModelCharge M finiteBudgetControlBelief finiteBudgetControlBelief.law
      chosen chosen 0 1 = 0 := by
  intro M chosen
  exact carriedOpponentModelCharge_self M finiteBudgetControlBelief chosen 0 1

end GameTheory.ReBeL.Examples.HiddenTypes

namespace GameTheory.ReBeL.Examples.OpponentModelTransport

open GameTheory.Math.Probability

/-- The actual prefix has a rare atom that the model prefix omits. -/
def actualPrefix : FinDist (Fin 2) :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num) (FinDist.pure 0) (FinDist.pure 1)

/-- The model observes only the other atom. This is a law, not a posterior claim. -/
def modelPrefix : FinDist (Fin 2) := FinDist.pure 1

/-- A canonical finite-law kernel retains its input. -/
def retain (x : Fin 2) : FinDist (Fin 2) := FinDist.pure x

/-- The changed kernel erases the rare atom, so its output support shrinks. -/
def collapse (_ : Fin 2) : FinDist (Fin 2) := FinDist.pure 1

/-- The distinct input laws have discrepancy one half, not zero. -/
theorem incoming_variation : FinDist.atomVariation actualPrefix modelPrefix = 1 / 2 := by
  norm_num [FinDist.atomVariation, Fin.sum_univ_two, actualPrefix, modelPrefix,
    FinDist.prob_mix, FinDist.prob_pure_eq_ite]

/-- The actual-prefix weighted kernel charge exactly captures the output gap. -/
theorem actual_kernel_charge :
    actualPrefix.expect (fun x => FinDist.atomVariation (retain x) (collapse x)) = 1 / 2 ∧
      FinDist.atomVariation (actualPrefix.bind retain) (actualPrefix.bind collapse) = 1 / 2 := by
  constructor
  · norm_num [actualPrefix, FinDist.expect_mix, FinDist.expect_pure,
      FinDist.atomVariation, Fin.sum_univ_two, retain, collapse, FinDist.prob_pure_eq_ite]
  · norm_num [FinDist.atomVariation, Fin.sum_univ_two, FinDist.prob_bind,
      actualPrefix, FinDist.expect_mix, FinDist.expect_pure, retain, collapse,
      FinDist.prob_pure_eq_ite]

/-- Charging the same discrepancy under an unrelated model prefix gives zero.
It is strictly too small: the FIRST-law weighting in the kernel bound matters. -/
theorem model_prefix_undercharges :
    ¬ FinDist.atomVariation (actualPrefix.bind retain) (actualPrefix.bind collapse) ≤
      modelPrefix.expect (fun x => FinDist.atomVariation (retain x) (collapse x)) := by
  rw [actual_kernel_charge.2]
  norm_num [modelPrefix, FinDist.expect_pure, retain, collapse, FinDist.atomVariation_self]

/-- The omitted model atom still has positive actual probability. An assumed
model-support inclusion would suppress this genuine quarter-mass failure. -/
theorem disappearing_model_support :
    actualPrefix.probOf ({0} : Set (Fin 2)) = 1 / 4 ∧ (0 : Fin 2) ∉ modelPrefix.support := by
  constructor
  · rw [FinDist.probOf_singleton]
    norm_num [actualPrefix, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  · simp [modelPrefix, FinDist.mem_support_pure]

/-- The actual lost-support event is controlled without constructing an
impossible conditional distribution or supplying a density certificate. -/
theorem disappearing_model_support_bound :
    actualPrefix.probOf ({0} : Set (Fin 2)) ≤
      FinDist.atomVariation actualPrefix modelPrefix := by
  apply FinDist.probOf_le_atomVariation_of_model_impossible
  intro x selected
  have same : x = 0 := selected
  subst x
  exact disappearing_model_support.2

end GameTheory.ReBeL.Examples.OpponentModelTransport
