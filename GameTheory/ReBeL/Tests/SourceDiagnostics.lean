/-
Positive, boundary, and negative checks for the M01 compiler probe.
These are arithmetic diagnostics, not game-level ReBeL theorems.
-/
import GameTheory.ReBeL.SourceDiagnostics

namespace GameTheory.ReBeL.SourceDiagnostics.Tests

/-- A noncentral point of the simplex is a positive control. -/
theorem simplex_positive_control :
    normalizedCoordinate (3 / 4) (1 / 4) = centeredPlane (3 / 4) (1 / 4) := by
  apply simplex_plane_agrees
  norm_num

/-- The supported simplex identity includes its boundary, with nonzero mass. -/
theorem simplex_boundary_control :
    normalizedCoordinate 1 0 = centeredPlane 1 0 := by
  apply simplex_plane_agrees
  norm_num

/-- The counterexample is genuinely outside the affine simplex. -/
theorem witness_not_on_simplex : (1 / 2 : ℚ) + 3 / 2 ≠ 1 := by
  norm_num

/-- The undefined probabilistic normalization at the origin is not an
admissible positive-cone input; Lean's total division must not hide this. -/
theorem origin_excluded : ¬ ((0 : ℚ) < 0 ∧ (0 : ℚ) < 0) := by
  norm_num

end GameTheory.ReBeL.SourceDiagnostics.Tests
