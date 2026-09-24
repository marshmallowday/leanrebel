/-
# Native variation controls

A nonzero rational law attains the quantitative bound. The canonical hidden-type
live-cut solver has zero variation against every unknown opponent when its
continuation law really agrees. Exact equilibria alone need not give zero
variation: the existing exploitation counterexample forces a positive charge.
-/

import GameTheory.Analysis.ReBeL.CFRDNativeVariation
import GameTheory.Analysis.ReBeL.Examples.CFRDResolveControl
import GameTheory.Analysis.ReBeL.Examples.CFRDEquilibriumReplacement

noncomputable section

namespace GameTheory.ReBeL.Examples.NativeVariation

open GameTheory.Protocol InformationModel
open GameTheory.Math.Probability

/-- A balanced two-point law. -/
def balanced : FinDist (Fin 2) := FinDist.uniformFin 2

/-- A genuinely different law with full support and rational masses. -/
def biased : FinDist (Fin 2) :=
  FinDist.ofWeights (fun x => if x = 0 then (3 / 4 : ℝ) else 1 / 4)
    (by intro x; fin_cases x <;> norm_num)
    (by rw [Fin.sum_univ_two]; norm_num)

/-- Full support does not mean the two laws agree. -/
theorem quarter_variation : FinDist.totalVariation balanced biased = 1 / 4 := by
  rw [FinDist.totalVariation_eq_sum, Fin.sum_univ_two]
  norm_num [balanced, biased]

/-- A bounded observable attaining the factor two in the variation bound. -/
def signedOutcome (x : Fin 2) : ℝ := if x = 0 then 1 else -1

/-- The rational control is sharp, not merely the vacuous range bound. -/
theorem sharp_value_change :
    |balanced.expect signedOutcome - biased.expect signedOutcome| =
      2 * FinDist.totalVariation balanced biased := by
  rw [quarter_variation, FinDist.expect_eq_sum, FinDist.expect_eq_sum]
  norm_num [balanced, biased, signedOutcome, Fin.sum_univ_two]

/-- Unsupported mass receives a sharp one-sided probability bound. -/
theorem half_support_defect :
    balanced.probOf {x | x ∉ (FinDist.pure (0 : Fin 2)).support} = 1 / 2 ∧
      FinDist.totalVariation balanced (FinDist.pure (0 : Fin 2)) = 1 / 2 := by
  constructor
  · rw [← FinDist.expect_indicator_eq_probOf, FinDist.expect_eq_sum, Fin.sum_univ_two]
    norm_num [balanced, FinDist.mem_support_pure]
  · rw [FinDist.totalVariation_eq_sum, Fin.sum_univ_two]
    norm_num [balanced, FinDist.prob_pure_eq_ite]

open GameTheory.ReBeL.Examples.HiddenTypes
open GameTheory.ReBeL.Rational.HiddenTypes.Canonical

/-- A genuine public live-cut solve, installed in the canonical memory runner. -/
def liveVariationStage : CarriedResolveStage (model fullPrior) Nat where
  fuel := 1
  resolver := livePublicResolver (CarriedResolveMemory (model fullPrior) Nat)

/-- The newly derived coefficient detects an actual law equality at every
hidden-type second-stage history, uniformly over all unknown behavioral opponents. -/
theorem live_solver_zero_variation (n : Nat)
    (unknown : Profile (model fullPrior).behavioralSignature) (who : Player)
    (x y a b : Bool) :
    carriedStepVariation (model fullPrior) (liveResolvePlays (fun k : Nat => k)) unknown who
      liveVariationStage 0
      (enterCarriedMemory (model fullPrior)
        (privateIterationState (model fullPrior) (liveResolvePlays (fun k : Nat => k))
          2 n (decode (.second x y a b)))) = 0 := by
  unfold carriedStepVariation
  split_ifs
  · simp only [liveVariationStage, livePublicResolver, FinDist.pure_bind, Nat.add_zero]
    change FinDist.totalVariation
      ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who
          (cfrDDepthPlay (model fullPrior) decisionClock cfrFallback cfrPayoff
            2 1 liveControlOracle n who)) 1 (decode (.second x y a b)))
      ((model fullPrior).runBehavioralFrom
        (Profile.update unknown who (liveFairContinuation who))
        1 (decode (.second x y a b))) = 0
    rw [liveResolve_second_run n unknown who x y a b, FinDist.totalVariation_self]
  · rfl

open GameTheory.ReBeL.Examples.EquilibriumValue
open GameTheory.ReBeL.Examples.EquilibriumReplacement

/-- Zero Nash error does not imply a vanishing probability-change coefficient.
This refutes only that inference, not the source's complete test-time theorem. -/
theorem exact_equilibria_can_have_positive_variation :
    IsNash form (euPreference replacementUtility) (strategy 1) ∧
      IsNash form (euPreference replacementUtility) (strategy 0) ∧
      (1 / 2 : ℝ) ≤ FinDist.totalVariation
        (form.play (Profile.update (strategy 1) 1 (1 : Fin 3)))
        (form.play (Profile.update (strategy 0) 1 (1 : Fin 3))) := by
  refine ⟨replacement_isNash 1 (Or.inr rfl), replacement_isNash 0 (Or.inl rfl), ?_⟩
  have bounded (outcome : Fin 3 × Fin 3) : |replacementUtility outcome 0| ≤ 1 := by
    simp only [replacementUtility, if_pos rfl]
    unfold replacementPayoff
    split_ifs <;> norm_num
  have estimate := FinDist.abs_expect_sub_le_totalVariation
    (form.play (Profile.update (strategy 1) 1 (1 : Fin 3)))
    (form.play (Profile.update (strategy 0) 1 (1 : Fin 3)))
    (fun outcome => replacementUtility outcome 0) 1 bounded
  change |expectedUtility replacementUtility 0
      (form.play (Profile.update (strategy 1) 1 (1 : Fin 3))) -
    expectedUtility replacementUtility 0
      (form.play (Profile.update (strategy 0) 1 (1 : Fin 3)))| ≤ _ at estimate
  rw [replacement_loses_one, abs_one] at estimate
  linarith

end GameTheory.ReBeL.Examples.NativeVariation
