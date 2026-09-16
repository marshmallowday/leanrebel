/-
# Source diagnostics for ReBeL

This module checks the rational diagnostic in docs/rebel/ROADMAP.md, risk R3.
It does not formalize a PBS, embed the example in a game, or refute every
interpretation of the paper's Theorem 1. In particular, support on the simplex
and support on the whole positive cone are different claims.
-/

import Mathlib.Data.Rat.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace GameTheory.ReBeL.SourceDiagnostics

/-- The degree-zero normalization used in the R3 diagnostic. -/
def normalizedCoordinate (x y : ℚ) : ℚ := x / (x + y)

/-- The affine plane at `(1/2, 1/2)` with centered vector `(1/2, -1/2)`. -/
def centeredPlane (x y : ℚ) : ℚ :=
  1 / 2 + (1 / 2) * (x - 1 / 2) - (1 / 2) * (y - 1 / 2)

/-- The plane agrees with the normalized function on the affine simplex.
Nonnegativity is not needed for this algebraic identity. -/
theorem simplex_plane_agrees (x y : ℚ) (h : x + y = 1) :
    normalizedCoordinate x y = centeredPlane x y := by
  simp only [normalizedCoordinate, h, div_one]
  unfold centeredPlane
  linarith

/-- Value at the interior anchor of the simplex. -/
theorem anchor_value : normalizedCoordinate (1 / 2) (1 / 2) = 1 / 2 := by
  norm_num [normalizedCoordinate]

/-- The off-simplex witness is in the strictly positive cone. -/
theorem witness_positive : (0 : ℚ) < 1 / 2 ∧ (0 : ℚ) < 3 / 2 := by
  norm_num

/-- Its actual normalized value is positive. -/
theorem witness_value : normalizedCoordinate (1 / 2) (3 / 2) = 1 / 4 := by
  norm_num [normalizedCoordinate]

/-- The proposed supporting plane is zero at the same point. -/
theorem witness_plane : centeredPlane (1 / 2) (3 / 2) = 0 := by
  norm_num [centeredPlane]

/-- A concrete failure of the global supporting inequality. -/
theorem supporting_inequality_fails :
    ¬ normalizedCoordinate (1 / 2) (3 / 2) ≤ centeredPlane (1 / 2) (3 / 2) := by
  norm_num [normalizedCoordinate, centeredPlane]

/-- Simplex support must not be interpreted as support on the positive cone. -/
theorem not_global_support :
    ¬ ∀ x y : ℚ, 0 < x → 0 < y → normalizedCoordinate x y ≤ centeredPlane x y := by
  intro h
  exact supporting_inequality_fails
    (h (1 / 2) (3 / 2) witness_positive.1 witness_positive.2)

/-- A strict midpoint Jensen violation for two points in the positive cone.
The midpoint of `(1/2, 1/2)` and `(1/2, 3/2)` is `(1/2, 1)`.
Thus normalization need not preserve concavity away from the simplex. -/
theorem midpoint_jensen_fails :
    normalizedCoordinate (1 / 2) 1 <
      (normalizedCoordinate (1 / 2) (1 / 2) +
        normalizedCoordinate (1 / 2) (3 / 2)) / 2 := by
  norm_num [normalizedCoordinate]

end GameTheory.ReBeL.SourceDiagnostics
