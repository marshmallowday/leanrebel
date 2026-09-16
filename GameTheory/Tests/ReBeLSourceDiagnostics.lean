/-
# ReBeL source diagnostics (M01-A)

This is a compiler probe and a rational diagnostic for ROADMAP.md risk R3,
not a game model, PBS API, or a proof/refutation of every interpretation of
ReBeL Theorem 1. Keep it in the existing architecture-owned test surface;
the production ReBeL root will accompany the first game-semantic slice.

The whole-library build, Phase 2/3 source audits, dedicated Batteries lint,
and scripts/rebel/audit_axioms.py all include this file.
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

/-- On the affine simplex the proposed plane agrees with the function.
Nonnegativity is not needed for this algebraic identity. -/
theorem simplex_plane_agrees (x y : ℚ) (h : x + y = 1) :
    normalizedCoordinate x y = centeredPlane x y := by
  simp only [normalizedCoordinate, h, div_one]
  unfold centeredPlane
  linarith

/-- Value at the interior anchor of the simplex. -/
theorem anchor_value : normalizedCoordinate (1 / 2) (1 / 2) = 1 / 2 := by
  norm_num [normalizedCoordinate]

/-- The off-simplex witness lies strictly inside the positive cone. -/
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

/-- A strict midpoint Jensen violation in the positive cone.
The midpoint of `(1/2, 1/2)` and `(1/2, 3/2)` is `(1/2, 1)`.
Normalization need not preserve concavity away from the simplex. -/
theorem midpoint_jensen_fails :
    normalizedCoordinate (1 / 2) 1 <
      (normalizedCoordinate (1 / 2) (1 / 2) +
        normalizedCoordinate (1 / 2) (3 / 2)) / 2 := by
  norm_num [normalizedCoordinate]

/-- A noncentral simplex point is a positive control. -/
theorem simplex_positive_control :
    normalizedCoordinate (3 / 4) (1 / 4) = centeredPlane (3 / 4) (1 / 4) := by
  apply simplex_plane_agrees
  norm_num

/-- The simplex identity includes its boundary, with nonzero total mass. -/
theorem simplex_boundary_control :
    normalizedCoordinate 1 0 = centeredPlane 1 0 := by
  apply simplex_plane_agrees
  norm_num

/-- The counterexample genuinely lies outside the affine simplex. -/
theorem witness_not_on_simplex : (1 / 2 : ℚ) + 3 / 2 ≠ 1 := by
  norm_num

/-- Lean's total division at the origin is not a probabilistic normalization;
the origin is excluded from the positive-cone domain. -/
theorem origin_excluded : ¬ ((0 : ℚ) < 0 ∧ (0 : ℚ) < 0) := by
  norm_num

end GameTheory.ReBeL.SourceDiagnostics
