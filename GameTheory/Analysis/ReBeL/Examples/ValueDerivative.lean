/-
# A genuine derivative of the normalized finite-game value

The counterexample's centered value vector is a Fréchet derivative, not just
an algebraically assigned candidate. Together with `ValueRadial` this separates
a valid local derivative calculation from invalid global concave support.
-/

import GameTheory.Analysis.ReBeL.Examples.ValueRadial
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

namespace GameTheory.ReBeL.Examples.ValueRadial

/-- The actual normalized game value has this derivative at an interior belief. -/
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
    rw [hasFDerivAt_iff_isLittleOTVS] at calculation ⊢
    simpa only [Function.comp_def, Pi.mul_apply, Pi.add_apply] using calculation
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

end GameTheory.ReBeL.Examples.ValueRadial
