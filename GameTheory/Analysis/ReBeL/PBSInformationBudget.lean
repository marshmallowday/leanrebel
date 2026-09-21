/-
# Finite information-set CFR budgets at an actual joint public belief

The iteration count is computed from the existing information-set CFR bound,
not from complete-plan normal-form learning or a supplied equilibrium witness.
The joint law's derived positive mass floor budgets all supported local types.
Zero-mass counterfactual types still require the separate response completion.
-/

import GameTheory.Analysis.ReBeL.PBSInformationCFR
import GameTheory.Math.Probability.FinDistMassFloor
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace GameTheory.ReBeL

open GameTheory.Protocol ExecutionProtocol InformationModel
open GameTheory.Math.Probability

private theorem pbsBudget_sum_mul {A : Type*} (xs : List A) (f : A → ℝ) (k : ℝ) :
    (xs.map (fun x => f x * k)).sum = (xs.map f).sum * k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

universe us ua up uq uk
variable {E : ExecutionProtocol.{0, us, ua} (Fin 2)}
variable (M : InformationModel.{0, us, ua, up, uq, uk} E)
variable [Fintype E.History] [∀ who, Fintype (E.Action who)]

/-- The finite schedule coefficient is independent of the iteration count. -/
theorem pbsInformationCFRBound_factor (roots : FinDist E.History)
    (bound : Fin 2 → ℝ) (fuel t : Nat) :
    pbsRootCFRBound M roots bound fuel t =
      pbsRootCFRBound M roots bound fuel 1 * Real.sqrt t / t := by
  unfold pbsRootCFRBound cfrCumulativeBound
  simp only [Nat.cast_one, Real.sqrt_one, mul_one, div_one]
  rw [pbsBudget_sum_mul, pbsBudget_sum_mul]
  ring

/-- Choose a positive finite count before running the information-set recurrence.
The absolute coefficient makes this total even outside the payoff hypotheses. -/
def pbsInformationBudgetRounds (roots : FinDist E.History)
    (bound : Fin 2 → ℝ) (fuel : Nat) (error : ℝ) : Nat :=
  ⌊(|pbsRootCFRBound M roots bound fuel 1| / error) ^ 2⌋₊ + 1

/-- The computed learner never averages an empty set of iterations. -/
instance pbsInformationBudgetRounds_neZero (roots : FinDist E.History)
    (bound : Fin 2 → ℝ) (fuel : Nat) (error : ℝ) :
    NeZero (pbsInformationBudgetRounds M roots bound fuel error) := ⟨Nat.succ_ne_zero _⟩

/-- The actual information-set bound meets every prescribed positive budget. -/
theorem pbsInformationBudgetRounds_error (roots : FinDist E.History)
    (bound : Fin 2 → ℝ) (fuel : Nat) (error : ℝ) (positive : 0 < error) :
    pbsRootCFRBound M roots bound fuel
      (pbsInformationBudgetRounds M roots bound fuel error) ≤ error := by
  let c := |pbsRootCFRBound M roots bound fuel 1|
  let n := pbsInformationBudgetRounds M roots bound fuel error
  have hc : 0 ≤ c := abs_nonneg _
  have hn : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have floor : (c / error) ^ 2 < (⌊(c / error) ^ 2⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have budget : (c / error) ^ 2 ≤ (n : ℝ) := by
    simpa only [n, pbsInformationBudgetRounds, c, Nat.cast_add, Nat.cast_one] using floor.le
  rw [div_pow] at budget
  have square : c ^ 2 ≤ (n : ℝ) * error ^ 2 :=
    (div_le_iff₀ (pow_pos positive 2)).mp budget
  have multiplied : (c * Real.sqrt n) ^ 2 ≤ (error * n) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn.le]
    nlinarith [mul_le_mul_of_nonneg_right square hn.le]
  have linear : c * Real.sqrt n ≤ error * n := by
    nlinarith [mul_nonneg hc (Real.sqrt_nonneg (n : ℝ)), mul_pos positive hn]
  rw [pbsInformationCFRBound_factor]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg (n : ℝ))) hn.le).trans
      ((div_le_iff₀ hn).mpr linear)

variable {observations : List M.PublicSignal}

/-- A finite solve in the ORIGINAL continuation game with its requested budget. -/
def pbsInformationBudgetProfile
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound error : ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  pbsInformationCFR M belief fallback (fun who history => utility history who) fuel
    (pbsInformationBudgetRounds M belief.law (fun _ => bound) fuel error)

/-- No Nash or regret certificate is supplied: both are derived for this solver. -/
theorem pbsInformationBudgetProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound : ℝ) (nonneg : 0 ≤ bound) (bounded : ∀ h who, |utility h who| ≤ bound)
    (error : ℝ) (positive : 0 < error) :
    IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreferenceWithin error utility)
      (pbsInformationBudgetProfile M belief fallback fuel utility bound error) := by
  have equilibrium := pbsInformationCFR_isNash M belief fallback
    (fun who history => utility history who) zeroSum (fun _ => bound) (fun _ => nonneg)
    (fun who history => bounded history who) fuel
    (pbsInformationBudgetRounds M belief.law (fun _ => bound) fuel error)
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  have gain := equilibrium who replacement
  rw [euPreferenceWithin_apply] at gain ⊢
  exact gain.trans (add_le_add_left
    (pbsInformationBudgetRounds_error M belief.law (fun _ => bound) fuel error positive) _)

/-- One joint-posterior budget controls every supported private-type probability. -/
def pbsInformationConditionalProfile
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (bound loss : ℝ) :
    Profile (fullInformation M).behavioralSignature :=
  pbsInformationBudgetProfile M belief fallback fuel utility bound
    (belief.law.positiveMassFloor * loss)

/-- The mass floor comes from the actual finite joint law, not an input assumption. -/
theorem pbsInformationConditionalProfile_isNash
    (belief : PublicBelief (fullInformation M).toInfoSignals observations)
    (fallback : (who : Fin 2) → M.Policy who) (fuel : Nat)
    (utility : E.History → Fin 2 → ℝ) (zeroSum : IsZeroSum utility)
    (bound loss : ℝ) (nonneg : 0 ≤ bound) (positive : 0 < loss)
    (bounded : ∀ h who, |utility h who| ≤ bound) :
    IsNash (behavioralBeliefForm (fullInformation M) belief fuel)
      (euPreferenceWithin (belief.law.positiveMassFloor * loss) utility)
      (pbsInformationConditionalProfile M belief fallback fuel utility bound loss) :=
  pbsInformationBudgetProfile_isNash M belief fallback fuel utility zeroSum bound nonneg bounded
    _ (mul_pos (FinDist.positiveMassFloor_pos belief.law) positive)

end GameTheory.ReBeL
