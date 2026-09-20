/-
# Approximate child-loss controls

A genuine finite canonical zero-sum type game has root gap p and conditional
gap one. It detects both rare-type amplification and the absent-type failure
of ordinary Nash. A live HiddenTypes child exercises the new completed
reference-table theorem using its constructed exact Nash as the zero-error case.
-/

import GameTheory.Analysis.ReBeL.CFRDApproximateLeaf
import GameTheory.Analysis.ReBeL.TypeValue
import GameTheory.Analysis.ReBeL.Examples.CFRDFactualChild

noncomputable section

namespace GameTheory.ReBeL.Examples.ApproximateLeaf

open GameTheory.Math.Probability GameTheory.MatrixGame

/-- Only type zero has a profitable action; the opponent has one action. -/
def rarePayoff (type : Fin 2) (action : Bool) (_opponent : Unit) : ℝ :=
  if type = 0 then if action then 1 else 0 else 0

/-- Type zero has probability p and type one has the complementary mass. -/
def rareWeight (p : ℝ) (type : Fin 2) : ℝ := if type = 0 then p else 1 - p

/-- The weights really form a probability simplex, including p=0 and p=1. -/
theorem rareWeight_simplex (p : ℝ) (nonneg : 0 ≤ p) (atMostOne : p ≤ 1) :
    rareWeight p ∈ stdSimplex ℝ (Fin 2) := by
  constructor
  · intro type
    fin_cases type <;> simp [rareWeight, nonneg, sub_nonneg.mpr atMostOne]
  · simp [rareWeight, Fin.sum_univ_two]

/-- Reuse the existing finite type-plan compiler, not an independent Nash notion. -/
def rareMatrix (p : ℝ) : (Fin 2 → Bool) → Unit → ℝ :=
  TypeGame.matrix rarePayoff (rareWeight p)

/-- The complete type-local plan affects exactly the probability-p payoff. -/
theorem rareMatrix_eq (p : ℝ) (plan : Fin 2 → Bool) (opponent : Unit) :
    rareMatrix p plan opponent = if plan 0 then p else 0 := by
  cases action : plan 0 <;>
    simp [rareMatrix, TypeGame.matrix, rareWeight, rarePayoff, Fin.sum_univ_two, action]

/-- The baseline declines the profitable action at every type. -/
theorem rare_baseline_payoff (p : ℝ) (opponent : FinDist Unit) :
    expectedPayoff (rareMatrix p) (FinDist.pure (fun _ => false)) opponent = 0 := by
  rw [expectedPayoff_pure_row]
  simp [rareMatrix_eq]

/-- Every mixed complete-plan deviation gains at most p at the root. -/
theorem rare_payoff_le (p : ℝ) (nonneg : 0 ≤ p)
    (row : FinDist (Fin 2 → Bool)) (opponent : FinDist Unit) :
    expectedPayoff (rareMatrix p) row opponent ≤ p := by
  rw [expectedPayoff_eq_expect_rows]
  apply FinDist.expect_le_of_forall
  intro plan _
  rw [expectedPayoff_pure_row]
  apply FinDist.expect_le_of_forall
  intro col _
  rw [rareMatrix_eq]
  cases plan 0 <;> simp [nonneg]

/-- Actual approximate Nash quantifies over ALL mixed deviations, not just
selected pure plans. At p=0 this is ordinary zero-error Nash as well. -/
theorem rare_approxNash (p : ℝ) (nonneg : 0 ≤ p) :
    IsNash (form (Fin 2 → Bool) Unit).mixed (euPreferenceWithin p (utility (rareMatrix p)))
      (mixedProfile (FinDist.pure (fun _ => false)) (FinDist.pure ())) := by
  rw [isNash_iff]
  intro who replacement
  fin_cases who
  · simp only [euPreferenceWithin_apply, mixedProfile_update_zero,
      expectedUtility_zero_mixedProfile, rare_baseline_payoff, zero_add]
    exact rare_payoff_le p nonneg replacement (FinDist.pure ())
  · simp only [euPreferenceWithin_apply, mixedProfile_update_one,
      expectedUtility_one_mixedProfile, rare_baseline_payoff, neg_zero, zero_add]
    exact nonneg

/-- Root error can be arbitrarily small while the supported type's gain is one. -/
theorem rare_supported_amplification (p : ℝ) (positive : 0 < p) (small : p < 1) :
    IsNash (form (Fin 2 → Bool) Unit).mixed (euPreferenceWithin p (utility (rareMatrix p)))
      (mixedProfile (FinDist.pure (fun _ => false)) (FinDist.pure ())) ∧
    0 < rareWeight p 0 ∧ rareWeight p 0 *
      (rarePayoff 0 true () - rarePayoff 0 false ()) = p ∧
    p < rarePayoff 0 true () - rarePayoff 0 false () := by
  refine ⟨rare_approxNash p positive.le, ?_, ?_, ?_⟩ <;>
    simp [rareWeight, rarePayoff, positive, small]

/-- Even exact root Nash cannot constrain the omitted type's positive gain. -/
theorem rare_absent_counterexample :
    IsNash (form (Fin 2 → Bool) Unit).mixed (euPreference (utility (rareMatrix 0)))
      (mixedProfile (FinDist.pure (fun _ => false)) (FinDist.pure ())) ∧
    rareWeight 0 0 = 0 ∧ rarePayoff 0 true () - rarePayoff 0 false () = 1 := by
  refine ⟨?_, rfl, by norm_num [rarePayoff]⟩
  simpa only [euPreferenceWithin, euPreference, add_zero] using rare_approxNash 0 (le_refl 0)

end GameTheory.ReBeL.Examples.ApproximateLeaf

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol GameTheory.Protocol.InformationModel
open GameTheory.Math.Probability

/-- Finite canonical histories for the live approximate-contract control. -/
local instance approximateChildHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Finite legal choices for each information-local reference query. -/
local instance approximateChildChoiceFintype (who : Player)
    (info : (model fullPrior).InfoState who) : Fintype ((model fullPrior).Choice who info) := by
  classical
  infer_instance

/-- The approximate theorem works on the actual live child and all reference
queries, including off-path ones. Exact child Nash supplies a zero root budget;
the caller does not assume the desired conditional leaf inequality. -/
theorem factualChild_approximate_contract (who : Player) (loss : ℝ) (nonneg : 0 ≤ loss) :
    CFRDLeafOptimal (model fullPrior)
      (cfrDCompleteZeroReach (model fullPrior) factualChildProfile
        (cfrDPublicResponseCompletion (reducedModel fullPrior) 2
          (cfrDReferenceTable (reducedModel fullPrior) factualChildProfile cfrFallback 2 1)
          cfrFallback 1 (fun h player => cfrPayoff player h) factualChildProfile))
      cfrFallback who (cfrPayoff who) 2 1 loss := by
  apply cfrDReferenceTable_approx_leafOptimal (reducedModel fullPrior)
    factualChildProfile cfrFallback 2 1 (fun h player => cfrPayoff player h) who loss nonneg
  intro observations root type sampled
  obtain ⟨own, equilibrium, supported⟩ := cfrDFactualChildProfile_referenceNash
    (reducedModel fullPrior) (carriedBitProfile false) cfrFallback 2 1
    (fun h player => cfrPayoff player h) who observations root type sampled
  refine ⟨own, 0, ?_, supported, ?_⟩
  · simpa only [euPreferenceWithin, euPreference, add_zero] using equilibrium
  · exact mul_nonneg (FinDist.prob_nonneg own type) nonneg

end GameTheory.ReBeL.Examples.HiddenTypes
