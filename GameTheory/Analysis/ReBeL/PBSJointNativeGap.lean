/-
# Joint seed/type control for actual native CFR gaps

The queried type may depend on the retained private iteration. The reference
law is the product used by the native mean theorem; the actual law need not
be a product and need not have its marginals. A bounded JOINT density is an
explicit source-law hypothesis, not a consequence of marginal domination.
The fixed conditional kernels and fixed average opponents do not change.
-/

import GameTheory.Analysis.ReBeL.PBSNativeConditionalGap

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

universe us ua up uq uk ut
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]
variable {observations : List M.PublicSignal} {who : Fin 2} {T : Type ut}

/-- A bounded JOINT density transfers the actual finite-iteration mean bound.
The ratio may depend on both the retained seed and the type. It is not an
information-local policy or a disclosure of the private seed to an opponent. -/
theorem pbsInformationCFR_joint_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel t : Nat) [NeZero t]
    (actual : FinDist (Fin t × T)) (ratio : Fin t × T → ℝ)
    (factor : ℝ) (factorNonneg : 0 ≤ factor)
    (density : ∀ pair, actual.prob pair =
      (cfrIterationLaw t).prob pair.1 * own.prob pair.2 * ratio pair)
    (ratioBound : ∀ pair ∈ ((cfrIterationLaw t).product own).support,
      ratio pair ≤ factor) :
    actual.expect (fun pair =>
      |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t pair.2 pair.1|) ≤
        factor * pbsRootCFRBound M (slice.mixture own).law bound fuel t := by
  classical
  let model := (cfrIterationLaw t).product own
  let gap := fun pair : Fin t × T =>
    |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t pair.2 pair.1|
  have jointDensity : ∀ pair, actual.prob pair = model.prob pair * ratio pair := by
    intro pair
    rw [density, FinDist.prob_product]
  calc
    actual.expect gap = model.expect (fun pair => ratio pair * gap pair) :=
      informationReweight_expect model actual (fun pair => pair) ratio jointDensity gap
    _ ≤ model.expect (fun pair => factor * gap pair) :=
      FinDist.expect_mono (fun pair reached =>
        mul_le_mul_of_nonneg_right (ratioBound pair reached) (abs_nonneg _))
    _ = factor * own.expect (fun type => (cfrIterationLaw t).expect (fun n =>
        |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t type n|)) := by
      rw [FinDist.expect_smul, FinDist.expect_product, FinDist.expect_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pbsInformationCFR_native_mean_abs_le M slice own fallback payoff zeroSum
        bound nonneg bounded fuel t) factorNonneg

/-- A type query made AFTER retaining the native iteration has a tagged joint
law. Each seed may have its own query kernel and density. The joint density
identity is derived from that actual bind/map law, not assumed as a product.
The cap is needed only on model-supported types. -/
theorem pbsInformationCFR_seed_query_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (payoff : Fin 2 → E.History → ℝ)
    (zeroSum : IsZeroSum (fun h player => payoff player h))
    (bound : Fin 2 → ℝ) (nonneg : ∀ player, 0 ≤ bound player)
    (bounded : ∀ player h, |payoff player h| ≤ bound player)
    (fuel t : Nat) [NeZero t]
    (query : Fin t → FinDist T) (ratio : Fin t → T → ℝ)
    (factor : ℝ) (factorNonneg : 0 ≤ factor)
    (density : ∀ n type, (query n).prob type = own.prob type * ratio n type)
    (ratioBound : ∀ n type, type ∈ own.support → ratio n type ≤ factor) :
    ((cfrIterationLaw t).bind (fun n => (query n).map (fun type => (n, type)))).expect
      (fun pair =>
        |pbsInformationCFRConditionalDrawGap M slice own fallback payoff fuel t pair.2 pair.1|) ≤
      factor * pbsRootCFRBound M (slice.mixture own).law bound fuel t := by
  classical
  apply pbsInformationCFR_joint_native_mean_abs_le M slice own fallback payoff zeroSum
    bound nonneg bounded fuel t _ (fun pair => ratio pair.1 pair.2) factor factorNonneg
  · rintro ⟨n, type⟩
    rw [FinDist.prob_bind_map_prod, density]
    ring
  · intro pair reached
    apply ratioBound pair.1 pair.2
    by_contra absent
    have zero : ((cfrIterationLaw t).product own).prob pair = 0 := by
      rw [FinDist.prob_product, FinDist.prob_eq_zero_iff.mpr absent, mul_zero]
    exact (FinDist.prob_eq_zero_iff.mp zero) reached

/-- The computed positive CFR budget also controls a correlated joint query.
Only the source-law factor multiplies the requested error; the actual finite
iteration count and its residual are retained. No learner convergence, input
Nash witness, or minimum type probability is used. -/
theorem pbsInformationBudget_joint_native_mean_abs_le
    (slice : TypeBeliefSlice (fullInformation M) observations who T) (own : FinDist T)
    (fallback : Profile M.strategicSignature) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h player, |utility h player| ≤ bound)
    (error : ℝ) (positive : 0 < error)
    (actual : FinDist
      (Fin (pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error) × T))
    (ratio : Fin
      (pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error) × T → ℝ)
    (factor : ℝ) (factorNonneg : 0 ≤ factor)
    (density : ∀ pair, actual.prob pair =
      (cfrIterationLaw
        (pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error)).prob
          pair.1 * own.prob pair.2 * ratio pair)
    (ratioBound : ∀ pair ∈ ((cfrIterationLaw
        (pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error)).product
          own).support, ratio pair ≤ factor) :
    let t := pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error
    actual.expect (fun pair =>
      |pbsInformationCFRConditionalDrawGap M slice own fallback (fun player h => utility h player)
        fuel t pair.2 pair.1|) ≤ factor * error := by
  exact (pbsInformationCFR_joint_native_mean_abs_le M slice own fallback
    (fun player h => utility h player) zeroSum (fun _ => bound) (fun _ => nonneg)
    (fun player h => bounded h player) fuel
    (pbsInformationBudgetRounds M (slice.mixture own).law (fun _ => bound) fuel error)
    actual ratio factor factorNonneg density ratioBound).trans
      (mul_le_mul_of_nonneg_left
        (pbsInformationBudgetRounds_error M (slice.mixture own).law (fun _ => bound)
          fuel error positive) factorNonneg)

end GameTheory.ReBeL
