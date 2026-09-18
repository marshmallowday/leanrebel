/-
# Nonsmooth and nonunique equilibrium controls

The row observes one of two types and has one legal action. The column guesses
a type and pays one on a correct guess, zero otherwise. The actual canonical
finite-game value is `min p (1-p)`. At the midpoint both pure columns are
optimal, their centered value vectors differ, and the value has no derivative.
-/

import GameTheory.Analysis.ReBeL.Examples.ValueRadial
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic.FinCases

noncomputable section

namespace GameTheory.ReBeL.Examples.ValueKink

open GameTheory.Math.Probability GameTheory.MatrixGame
open ValueRadial (weights weights_zero weights_one)

/-- The opponent minimizes the payoff by choosing the less likely type. -/
def payoff (t : Fin 2) (_action : Unit) (opponent : Fin 2) : ℝ :=
  if t = opponent then 1 else 0

theorem matrix_eq (weight : Fin 2 → ℝ) (plan : Fin 2 → Unit) (opponent : Fin 2) :
    TypeGame.matrix payoff weight plan opponent = weight opponent := by
  fin_cases opponent <;> simp [TypeGame.matrix, payoff]

theorem expectedPayoff_eq (weight : Fin 2 → ℝ)
    (row : FinDist (Fin 2 → Unit)) (opponent : FinDist (Fin 2)) :
    expectedPayoff (TypeGame.matrix payoff weight) row opponent = opponent.expect weight := by
  rw [expectedPayoff_eq_expect_rows]
  simp only [expectedPayoff_pure_row, matrix_eq, FinDist.expect_const]

/-- A closed form for the canonical minimax value, derived using the selected
saddle strategies rather than defining the game value by this formula. -/
theorem value_eq (weight : Fin 2 → ℝ) :
    TypeGame.value payoff weight = min (weight 0) (weight 1) := by
  have upper (opponent : Fin 2) : TypeGame.value payoff weight ≤ weight opponent := by
    have bound := valueRow_guarantees (TypeGame.matrix payoff weight) (FinDist.pure opponent)
    simpa only [TypeGame.value, expectedPayoff_eq, FinDist.expect_pure] using bound
  have lower : min (weight 0) (weight 1) ≤ TypeGame.value payoff weight := by
    have bound := valueColumn_caps (TypeGame.matrix payoff weight)
      (FinDist.pure (fun _ : Fin 2 => ()))
    rw [expectedPayoff_eq] at bound
    apply le_trans _ bound
    calc
      min (weight 0) (weight 1) =
          (valueColumn (TypeGame.matrix payoff weight)).expect
            (fun _ => min (weight 0) (weight 1)) := (FinDist.expect_const _ _).symm
      _ ≤ (valueColumn (TypeGame.matrix payoff weight)).expect weight := by
        apply FinDist.expect_mono
        intro opponent _
        fin_cases opponent
        · exact min_le_left _ _
        · exact min_le_right _ _
  exact le_antisymm (le_min (upper 0) (upper 1)) lower

theorem branch_eq (weight : Fin 2 → ℝ) (opponent : FinDist (Fin 2)) :
    TypeGame.branch payoff weight opponent = opponent.expect weight := by
  rw [← TypeGame.simultaneous_response, expectedPayoff_eq]

theorem infoValue_pure (opponent t : Fin 2) :
    TypeGame.infoValue payoff (FinDist.pure opponent) t = if t = opponent then 1 else 0 := by
  simp [TypeGame.infoValue, payoff]

/-- The kink is in the value of the game, not just in a hand-written proxy. -/
theorem value_not_differentiable : ¬ DifferentiableAt ℝ
    (fun p : ℝ => TypeGame.value payoff (weights (p, 1 - p))) (1 / 2) := by
  intro differentiable
  have shift : DifferentiableAt ℝ (fun z : ℝ => 1 / 2 + z) 0 :=
    (differentiableAt_const (1 / 2 : ℝ)).add differentiableAt_id
  have atShift : DifferentiableAt ℝ
      (fun p : ℝ => TypeGame.value payoff (weights (p, 1 - p))) ((1 / 2 : ℝ) + 0) := by
    simpa only [add_zero] using differentiable
  have shifted : DifferentiableAt ℝ
      (fun z : ℝ => TypeGame.value payoff (weights (1 / 2 + z, 1 - (1 / 2 + z)))) 0 :=
    atShift.comp 0 shift
  have identity : (fun z : ℝ => (1 / 2 : ℝ) -
      TypeGame.value payoff (weights (1 / 2 + z, 1 - (1 / 2 + z)))) = abs := by
    funext z
    rw [value_eq, weights_zero, weights_one]
    by_cases nonnegative : 0 ≤ z
    · rw [min_eq_right (by linarith), abs_of_nonneg nonnegative]
      ring
    · rw [min_eq_left (by linarith), abs_of_neg (lt_of_not_ge nonnegative)]
      ring
  have impossible : DifferentiableAt ℝ (fun z : ℝ => (1 / 2 : ℝ) -
      TypeGame.value payoff (weights (1 / 2 + z, 1 - (1 / 2 + z)))) 0 :=
    (differentiableAt_const (1 / 2 : ℝ)).sub shifted
  rw [identity] at impossible
  exact not_differentiableAt_abs_zero impossible

/-- Every pure guess is an equilibrium opponent at the midpoint. -/
theorem both_equilibrium_opponents (opponent : Fin 2) :
    ∃ row : FinDist (Fin 2 → Unit),
      IsNash (form (Fin 2 → Unit) (Fin 2)).mixed
        (euPreference (utility (TypeGame.matrix payoff
          (weights ((1 / 2 : ℝ), (1 / 2 : ℝ))))))
        (mixedProfile row (FinDist.pure opponent)) := by
  apply (TypeGame.branch_eq_value_iff_equilibriumOpponent payoff _
    (fun t => by simp [weights]) (FinDist.pure opponent)).mp
  rw [branch_eq, FinDist.expect_pure, value_eq]
  simp [weights]

/-- The two equilibrium opponent strategies are distinct laws. -/
theorem distinct_equilibrium_opponents :
    (FinDist.pure (0 : Fin 2)) ≠ FinDist.pure (1 : Fin 2) := by
  intro equality
  have impossible := congrArg (fun law : FinDist (Fin 2) => law.prob 0) equality
  norm_num [FinDist.prob_pure_eq_ite] at impossible

/-- Distinct supporting vectors coexist where the game value has no gradient. -/
theorem distinct_centered_vectors :
    TypeGame.centeredVector payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ)))
      (FinDist.pure 0) 0 = 1 / 2 ∧
    TypeGame.centeredVector payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ)))
      (FinDist.pure 1) 0 = -(1 / 2) := by
  norm_num [TypeGame.centeredVector, infoValue_pure, value_eq, weights]

/-- Either optimal opponent still supplies global support to the repaired
extension; no nonexistent derivative of the value is used. -/
theorem nonsmooth_support (opponent : Fin 2) (point : Fin 2 → ℝ) :
    TypeGame.allSpaceExtension payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ))) point ≤
      TypeGame.allSpaceExtension payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (weights ((1 / 2 : ℝ), (1 / 2 : ℝ))) +
      ∑ t, TypeGame.centeredVector payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (FinDist.pure opponent) t * (point t - weights ((1 / 2 : ℝ), (1 / 2 : ℝ)) t) := by
  apply TypeGame.allSpaceExtension_support
  · constructor
    · intro t
      simp [weights]
    · norm_num [weights, Fin.sum_univ_two]
  · rw [branch_eq, FinDist.expect_pure, value_eq]
    simp [weights]

/-- Doubling a valid supporting vector need not preserve support. This
separates arbitrary linear combinations from Footnote 8's valid convex ones. -/
theorem arbitrary_linear_combination_not_supporting : ¬ (∀ point : Fin 2 → ℝ,
    point ∈ stdSimplex ℝ (Fin 2) →
    TypeGame.value payoff point ≤ (1 / 2 : ℝ) +
      ∑ t, (2 * TypeGame.centeredVector payoff
        (weights ((1 / 2 : ℝ), (1 / 2 : ℝ))) (FinDist.pure 0) t) *
        (point t - weights ((1 / 2 : ℝ), (1 / 2 : ℝ)) t)) := by
  intro supporting
  have boundary : weights ((0 : ℝ), (1 : ℝ)) ∈ stdSimplex ℝ (Fin 2) := by
    constructor
    · intro t
      fin_cases t <;> norm_num [weights]
    · norm_num [weights, Fin.sum_univ_two]
  have impossible := supporting (weights ((0 : ℝ), (1 : ℝ))) boundary
  norm_num [value_eq, TypeGame.centeredVector, infoValue_pure, weights,
    Fin.sum_univ_two] at impossible

end GameTheory.ReBeL.Examples.ValueKink
