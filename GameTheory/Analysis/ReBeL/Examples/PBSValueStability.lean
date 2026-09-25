/-
# Same-PBS finite-solve value control and a sharp coupling boundary

The positive control runs the existing hidden-type child solver twice at
strictly positive, different finite budgets. The negative canonical zero-sum
game has exact equilibria with equal scalar values, yet EVERY coupling of
their outcome laws costs one half. This does not refute ReBeL or establish
stability of conditional value vectors under changed carried beliefs.
-/

import GameTheory.Analysis.ReBeL.PBSValueStability
import GameTheory.Math.Probability.FinDistValueCoupling
import GameTheory.Analysis.ReBeL.Examples.PBSRootDecode

noncomputable section

namespace GameTheory.ReBeL.Examples.ValueStability

open GameTheory.Math.Probability

/-- The incumbent outcome is the zero-payoff atom. -/
def oldLaw : FinDist (Fin 3) := FinDist.pure 0

/-- A mean-preserving spread puts equal mass on the negative and positive atoms. -/
def freshLaw : FinDist (Fin 3) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure 1) (FinDist.pure 2)

/-- The outcome payoff has three genuinely distinct values. -/
def value (outcome : Fin 3) : ℝ :=
  if outcome = 0 then 0 else if outcome = 1 then -1 else 1

/-- Both actual means are zero; no transport conclusion is inferred from this. -/
theorem equal_means : oldLaw.expect value = 0 ∧ freshLaw.expect value = 0 := by
  norm_num [oldLaw, freshLaw, value, FinDist.expect_mix, FinDist.expect_pure]

/-- Reuse the canonical strategy and game-form interfaces. -/
abbrev signature : GameSignature (Fin 2) where
  Strategy _ := Bool
  Outcome := Fin 3

/-- The row selects the deterministic zero payoff or the fair payoff spread.
The column is strategically irrelevant but retains its full legal menu. -/
abbrev form : GameForm (Fin 2) where
  sig := signature
  play profile := if profile 0 then freshLaw else oldLaw

/-- Opposing utilities are exact negatives at every outcome. -/
def utility (outcome : Fin 3) (who : Fin 2) : ℝ :=
  if who = 0 then value outcome else -value outcome

/-- The chance game is zero sum, not a coordination-game counterexample. -/
theorem zeroSum : IsZeroSum utility := by
  intro outcome
  simp [Fin.sum_univ_two, utility]

/-- Every profile has the same zero expected payoff for either player. -/
theorem profile_value_zero (profile : Profile form.sig) (who : Fin 2) :
    expectedUtility utility who (form.play profile) = 0 := by
  fin_cases who <;> cases choice : profile 0 <;>
    norm_num [form, choice, expectedUtility, utility, value, oldLaw, freshLaw,
      FinDist.expect_mix, FinDist.expect_pure]

/-- All legal pure deviations, not only a selected response, preserve value. -/
theorem profile_isNash (profile : Profile form.sig) :
    IsNash form (euPreference utility) profile := by
  rw [isNash_iff]
  intro who alternative
  simp only [euPreference_apply, profile_value_zero, le_refl]

/-- The same control exercises the new zero-error approximate-value theorem. -/
theorem value_comparison (first second : Profile form.sig) :
    |expectedUtility utility 0 (form.play first) -
      expectedUtility utility 0 (form.play second)| ≤ 0 := by
  have approximate (profile : Profile form.sig) :
      IsNash form (euPreferenceWithin 0 utility) profile := by
    rw [isNash_iff]
    intro who alternative
    simp only [euPreferenceWithin_apply, profile_value_zero, add_zero, le_refl]
  simpa only [add_zero] using approxNash_value_abs_sub_le form utility zeroSum
    first second 0 0 (approximate first) (approximate second)

/-- The exact two laws do have a valid coupling, so the negative test is
not a vacuous consequence of impossible marginal equations. -/
theorem valid_coupling_exists :
    ∃ joint : FinDist (Fin 3 × Fin 3),
      joint.map Prod.fst = oldLaw ∧ joint.map Prod.snd = freshLaw :=
  ⟨oldLaw.product freshLaw, FinDist.map_fst_product _ _, FinDist.map_snd_product _ _⟩

/-- Every coupling pays one half, not merely the particular product coupling.
The old marginal forces zero old payoff on each supported pair. -/
theorem every_coupling_cost_half (joint : FinDist (Fin 3 × Fin 3))
    (oldMarginal : joint.map Prod.fst = oldLaw)
    (newMarginal : joint.map Prod.snd = freshLaw) :
    FinDist.directedValueCost joint value value = 1 / 2 := by
  have oldSupport (pair : Fin 3 × Fin 3) (reached : pair ∈ joint.support) : pair.1 = 0 := by
    have projected : pair.1 ∈ (joint.map Prod.fst).support := by
      rw [FinDist.support_map]
      exact ⟨pair, reached, rfl⟩
    rw [oldMarginal] at projected
    exact FinDist.mem_support_pure.mp projected
  calc
    FinDist.directedValueCost joint value value =
        joint.expect (fun pair => max 0 (value pair.2)) := by
      apply FinDist.expect_congr
      intro pair reached
      rw [oldSupport pair reached]
      norm_num [value]
    _ = (joint.map Prod.snd).expect (fun outcome => max 0 (value outcome)) :=
      (FinDist.expect_map _ _ _).symm
    _ = 1 / 2 := by
      rw [newMarginal]
      norm_num [freshLaw, value, FinDist.expect_mix, FinDist.expect_pure]

/-- Equal means, even at exact Nash, do not permit arbitrarily small directed
coupling costs. This guards the boundary of the SAME-PBS scalar theorem. -/
theorem no_small_coupling (error : ℝ) (small : error < 1 / 2) :
    ¬ ∃ joint : FinDist (Fin 3 × Fin 3), joint.map Prod.fst = oldLaw ∧
      joint.map Prod.snd = freshLaw ∧ FinDist.directedValueCost joint value value ≤ error := by
  rintro ⟨joint, oldMarginal, newMarginal, cost⟩
  rw [every_coupling_cost_half joint oldMarginal newMarginal] at cost
  linarith only [small, cost]

end GameTheory.ReBeL.Examples.ValueStability

namespace GameTheory.ReBeL.Examples.HiddenTypes

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

/-- Keep every legal history, including factually absent histories. -/
local instance valueStabilityHistoryFintype : Fintype (protocol fullPrior).History :=
  historyFintype fullPrior

/-- Two actual finite information-set child solves at budgets one quarter and
one eighth differ in root value by at most three eighths. No equilibrium or
coupling witness is supplied. This is not a per-infostate conclusion. -/
theorem pbsValueStability_two_budget_solves :
    |(PublicBelief.continuationLaw (model fullPrior)
        (pbsInformationBudgetProfile (reducedModel fullPrior) finiteBudgetControlBelief
          pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 (1 / 4))
        1 finiteBudgetControlBelief).expect (cfrPayoff 0) -
      (PublicBelief.continuationLaw (model fullPrior)
        (pbsInformationBudgetProfile (reducedModel fullPrior) finiteBudgetControlBelief
          pbsRootControlFallback 1 (fun h who => cfrPayoff who h) 2 (1 / 8))
        1 finiteBudgetControlBelief).expect (cfrPayoff 0)| ≤ 3 / 8 := by
  have bound := pbsInformationBudgetProfile_value_abs_sub_le (reducedModel fullPrior)
    finiteBudgetControlBelief pbsRootControlFallback pbsRootControlFallback 1
    (fun h who => cfrPayoff who h) (cumulative_zeroSum fullPrior) 2 (by norm_num)
    (fun h who => cfrPayoff_abs_le_two who h) (1 / 4) (1 / 8) (by norm_num) (by norm_num)
  norm_num at bound ⊢
  exact bound

end GameTheory.ReBeL.Examples.HiddenTypes
