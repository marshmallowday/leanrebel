/-
# A game-value counterexample to radial normalization

This is a finite two-player zero-sum type game with one legal continuation
per type and one opponent continuation. Payoff is one in the first type and
zero in the second. The scalar is the canonical minimax value, not a supplied
rational function. Its normalized extension is differentiable at an interior
belief but the resulting gradient does not give global concave support.
-/

import GameTheory.Analysis.ReBeL.ValueEnvelopeBridge
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section

namespace GameTheory.ReBeL.Examples.ValueRadial

open GameTheory.Math.Probability GameTheory.MatrixGame

/-- Two explicit coordinates, shared by the boundary and kink controls. -/
def weights (point : ℝ × ℝ) (t : Fin 2) : ℝ := if t = 0 then point.1 else point.2

@[simp] theorem weights_zero (point : ℝ × ℝ) : weights point 0 = point.1 := rfl
@[simp] theorem weights_one (point : ℝ × ℝ) : weights point 1 = point.2 := rfl

/-- No strategic action can change the payoff conditional on the type. -/
def payoff (t : Fin 2) (_action : Unit) (_opponent : Unit) : ℝ :=
  if t = 0 then 1 else 0

/-- Computing an actual canonical finite minimax value. The identity holds
even for signed weights since every matrix entry is the same scalar. -/
theorem value_eq (weight : Fin 2 → ℝ) : TypeGame.value payoff weight = weight 0 := by
  have matrix_eq : TypeGame.matrix payoff weight =
      fun (_plan : Fin 2 → Unit) (_opponent : Unit) => weight 0 := by
    funext plan opponent
    simp [TypeGame.matrix, payoff]
  rw [TypeGame.value, matrix_eq, ← expectedPayoff_valueProfile,
    expectedPayoff_eq_expect_rows]
  simp only [expectedPayoff_pure_row, FinDist.expect_const]

/-- Eq. (1) retains the off-path conditional payoff rather than assigning
zero to every zero-probability type. -/
theorem infoValue_eq (opponent : FinDist Unit) (t : Fin 2) :
    TypeGame.infoValue payoff opponent t = if t = 0 then 1 else 0 :=
  FinDist.expect_const _ _

theorem branch_eq (weight : Fin 2 → ℝ) (opponent : FinDist Unit) :
    TypeGame.branch payoff weight opponent = weight 0 := by
  simp [TypeGame.branch, infoValue_eq]

/-- Appendix F's degree-zero normalization, evaluated at the actual game
value. Counterexamples below use strictly positive coordinates only. -/
def radialValue (point : ℝ × ℝ) : ℝ :=
  TypeGame.value payoff (weights
    (point.1 / (point.1 + point.2), point.2 / (point.1 + point.2)))

theorem radialValue_eq (point : ℝ × ℝ) : radialValue point =
    point.1 / (point.1 + point.2) := by
  rw [radialValue, value_eq, weights_zero]

/-- The genuine Fréchet derivative at the interior belief `(1/2, 1/2)`. -/
def radialGradient : (ℝ × ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem radialValue_hasFDerivAt :
    HasFDerivAt radialValue radialGradient ((1 / 2 : ℝ), (1 / 2 : ℝ)) := by
  have first := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
    (x := ((1 / 2 : ℝ), (1 / 2 : ℝ)))
  have second := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    (x := ((1 / 2 : ℝ), (1 / 2 : ℝ)))
  have inverse := (hasFDerivAt_inv (by norm_num : (1 / 2 : ℝ) + 1 / 2 ≠ 0)).comp
    ((1 / 2 : ℝ), (1 / 2 : ℝ)) (first.add second)
  have derivative : HasFDerivAt (fun point : ℝ × ℝ => point.1 * (point.1 + point.2)⁻¹)
      ((1 / 2 : ℝ) • (ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) +
          ContinuousLinearMap.fst ℝ ℝ ℝ) ((1 / 2 : ℝ), (1 / 2 : ℝ)) := by
    have calculation := first.mul inverse
    norm_num at calculation
    simpa using calculation
  have linear : ((1 / 2 : ℝ) • (ContinuousLinearMap.toSpanSingleton ℝ (-1 : ℝ)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) +
        ContinuousLinearMap.fst ℝ ℝ ℝ) = radialGradient := by
    apply ContinuousLinearMap.ext
    intro point
    norm_num [radialGradient]
    ring
  rw [linear] at derivative
  have equality : radialValue = fun point : ℝ × ℝ =>
      point.1 * (point.1 + point.2)⁻¹ := by
    funext point
    rw [radialValue_eq, div_eq_mul_inv]
  rw [equality]
  exact derivative

/-- The derivative is precisely the centered Eq. (1) value vector. -/
theorem gradient_eq_centered (direction : ℝ × ℝ) :
    radialGradient direction = ∑ t,
      TypeGame.centeredVector payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (FinDist.pure ()) t * weights direction t := by
  simp [radialGradient, TypeGame.centeredVector, infoValue_eq, value_eq,
    weights, Fin.sum_univ_two]
  ring

/-- Restricting to positive mass and positive types does not repair global
support of the radial extension. At `(1/2, 3/2)` it gives `1/4 ≤ 0`. -/
theorem radial_gradient_not_supporting : ¬ (∀ point : ℝ × ℝ,
    0 < point.1 → 0 < point.2 →
    radialValue point ≤ radialValue ((1 / 2 : ℝ), (1 / 2 : ℝ)) +
      radialGradient (point - ((1 / 2 : ℝ), (1 / 2 : ℝ)))) := by
  intro supporting
  have impossible := supporting ((1 / 2 : ℝ), (3 / 2 : ℝ)) (by norm_num) (by norm_num)
  norm_num [radialValue_eq, radialGradient] at impossible

/-- Two interior points refute concavity of the normalized game value by
Jensen's inequality: `3/8 ≤ 1/3` would be required. -/
theorem radialValue_not_concave :
    ¬ ConcaveOn ℝ {point : ℝ × ℝ | 0 < point.1 ∧ 0 < point.2} radialValue := by
  intro concave
  have impossible := concave.2
    (by norm_num : ((1 : ℝ), (1 : ℝ)) ∈ {point : ℝ × ℝ | 0 < point.1 ∧ 0 < point.2})
    (by norm_num : ((1 : ℝ), (3 : ℝ)) ∈ {point : ℝ × ℝ | 0 < point.1 ∧ 0 < point.2})
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  norm_num [radialValue_eq] at impossible

/-- A boundary belief with a nonzero value at its unrepresented own type. -/
theorem zero_mass_type_control :
    weights ((0 : ℝ), (1 : ℝ)) 0 = 0 ∧
    TypeGame.value payoff (weights ((0 : ℝ), (1 : ℝ))) = 0 ∧
    TypeGame.infoValue payoff (FinDist.pure ()) 0 = 1 := by
  simp [value_eq, infoValue_eq]

/-- The repaired extension supplies support where the radial one fails. -/
theorem corrected_support (point : Fin 2 → ℝ) :
    TypeGame.allSpaceExtension payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ))) point ≤
      TypeGame.allSpaceExtension payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (weights ((1 / 2 : ℝ), (1 / 2 : ℝ))) +
      ∑ t, TypeGame.centeredVector payoff (weights ((1 / 2 : ℝ), (1 / 2 : ℝ)))
        (FinDist.pure ()) t * (point t - weights ((1 / 2 : ℝ), (1 / 2 : ℝ)) t) := by
  apply TypeGame.allSpaceExtension_support
  · constructor
    · intro t
      simp [weights]
    · norm_num [weights, Fin.sum_univ_two]
  · rw [branch_eq, value_eq]

end GameTheory.ReBeL.Examples.ValueRadial
