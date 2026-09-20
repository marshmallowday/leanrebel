/-
# A finite iteration count meeting a prescribed positive Nash budget

The count is computed from the proved game-dependent regret coefficient,
not selected by assuming an equilibrium or a convergence certificate. The
algorithm remains a real-arithmetic normal-form reference variant.
-/

import GameTheory.Analysis.ReBeL.FinitePlanNash
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace GameTheory.ReBeL

universe us uo
variable (F : GameForm.{0, us, uo} (Fin 2))
variable [∀ who, Fintype (F.sig.Strategy who)]

/-- A strictly positive finite number of rounds for every positive budget. -/
def finiteGameBudgetRounds (bound error : ℝ) : ℕ :=
  ⌊(finiteGameSolutionCoefficient F bound / error) ^ 2⌋₊ + 1

/-- The average never receives an empty round set, even outside the guarantee. -/
instance finiteGameBudgetRounds_neZero (bound error : ℝ) :
    NeZero (finiteGameBudgetRounds F bound error) := ⟨Nat.succ_ne_zero _⟩

/-- The explicitly chosen round count meets the requested positive error. -/
theorem finiteGameBudgetRounds_error (bound : ℝ) (nonneg : 0 ≤ bound)
    (error : ℝ) (positive : 0 < error) :
    finiteGameSolutionError F bound (finiteGameBudgetRounds F bound error) ≤ error := by
  let c := finiteGameSolutionCoefficient F bound
  let n := finiteGameBudgetRounds F bound error
  have hc : 0 ≤ c := by dsimp [c, finiteGameSolutionCoefficient]; positivity
  have hn : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have floor : (c / error) ^ 2 < (⌊(c / error) ^ 2⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have budget : (c / error) ^ 2 ≤ (n : ℝ) := by
    simpa only [n, finiteGameBudgetRounds, c, Nat.cast_add, Nat.cast_one] using floor.le
  rw [div_pow] at budget
  have square : c ^ 2 ≤ (n : ℝ) * error ^ 2 :=
    (div_le_iff₀ (pow_pos positive 2)).mp budget
  have multiplied : (c * Real.sqrt n) ^ 2 ≤ (error * n) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hn.le]
    nlinarith [mul_le_mul_of_nonneg_right square hn.le]
  have linear : c * Real.sqrt n ≤ error * n := by
    nlinarith [mul_nonneg hc (Real.sqrt_nonneg (n : ℝ)), mul_pos positive hn]
  exact (div_le_iff₀ hn).mpr linear

/-- A finite solve whose horizon is chosen before executing the recurrence. -/
def finiteGameBudgetSolution (utility : F.sig.Outcome → Fin 2 → ℝ)
    (fallback : Profile F.sig) (bound error : ℝ) : Profile F.sig.mixed :=
  finiteGameMixedSolution F utility fallback (finiteGameBudgetRounds F bound error)

/-- The computed finite solve meets its input budget against every mixed
replacement. Neither a Nash witness nor a regret inequality is an input. -/
theorem finiteGameBudgetSolution_isNash (utility : F.sig.Outcome → Fin 2 → ℝ)
    (zeroSum : IsZeroSum utility) (fallback : Profile F.sig)
    (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ outcome who, |utility outcome who| ≤ bound)
    (error : ℝ) (positive : 0 < error) :
    IsNash F.mixed (euPreferenceWithin error utility)
      (finiteGameBudgetSolution F utility fallback bound error) := by
  have equilibrium := finiteGameMixedSolution_isNash F utility zeroSum fallback bound nonneg
    bounded (finiteGameBudgetRounds F bound error)
  rw [isNash_iff] at equilibrium ⊢
  intro who replacement
  have gain := equilibrium who replacement
  rw [euPreferenceWithin_apply] at gain ⊢
  exact gain.trans (add_le_add (le_refl _)
    (finiteGameBudgetRounds_error F bound nonneg error positive))

end GameTheory.ReBeL
