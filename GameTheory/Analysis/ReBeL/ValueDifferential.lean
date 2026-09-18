/-
# Normalization derivatives, separated from concave support

Appendix F equations (5)-(12) concern differentiation of a fixed affine
opponent branch after radial normalization. The Jacobian exists away from
zero mass; on mass one it produces the centered conditional-value vector.
None of these differential identities asserts that the normalized envelope
is concave or that its derivative is a global supporting supergradient.
-/

import GameTheory.Analysis.ReBeL.ValueEnvelope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring

noncomputable section

namespace GameTheory.ReBeL.ValueDifferential

open scoped BigOperators

variable {T : Type*} [Fintype T]

/-- Total signed mass as a continuous linear map. -/
def massMap : (T → ℝ) →L[ℝ] ℝ := ∑ type, ContinuousLinearMap.proj type

@[simp] theorem massMap_apply (point : T → ℝ) : massMap point = ∑ type, point type := by
  simp [massMap]

/-- A fixed conditional-value branch is a genuine continuous linear functional. -/
def branchMap (values : T → ℝ) : (T → ℝ) →L[ℝ] ℝ :=
  ∑ type, values type • ContinuousLinearMap.proj type

@[simp] theorem branchMap_apply (values point : T → ℝ) :
    branchMap values point = ∑ type, values type * point type := by
  simp [branchMap]

/-- Radial normalization. Differential statements require nonzero mass. -/
def normalize (point : T → ℝ) (type : T) : ℝ := point type / massMap point

/-- The full Jacobian obtained from the product and inverse derivative rules. -/
def normalizationJacobian (base : T → ℝ) : (T → ℝ) →L[ℝ] (T → ℝ) :=
  ContinuousLinearMap.pi fun type =>
    base type • (ContinuousLinearMap.toSpanSingleton ℝ (-(massMap base ^ 2)⁻¹)).comp massMap +
      (massMap base)⁻¹ • ContinuousLinearMap.proj type

/-- Equations (7)-(8): the actual Fréchet derivative, with its nonzero-mass
premise visible. This is valid on the signed ambient space near the point. -/
theorem normalize_hasFDerivAt (base : T → ℝ) (nonzero : massMap base ≠ 0) :
    HasFDerivAt normalize (normalizationJacobian base) base := by
  unfold normalize normalizationJacobian
  apply hasFDerivAt_pi.mpr
  intro type
  have inverse := (hasFDerivAt_inv nonzero).comp base massMap.hasFDerivAt
  convert! (hasFDerivAt_apply type base).mul inverse using 1

/-- Coordinate formula for the Jacobian acting on an arbitrary direction. -/
theorem normalizationJacobian_apply (base direction : T → ℝ) (type : T) :
    normalizationJacobian base direction type =
      direction type / massMap base - base type * massMap direction / massMap base ^ 2 := by
  simp [normalizationJacobian, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

/-- Equation (9): at mass one the derivative removes the radial component. -/
theorem normalizationJacobian_mass_one (base : T → ℝ) (unitMass : massMap base = 1)
    (direction : T → ℝ) :
    normalizationJacobian base direction = direction - massMap direction • base := by
  funext type
  rw [normalizationJacobian_apply, unitMass]
  simp only [one_pow, div_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Each matrix entry has the expected Kronecker-delta form. -/
theorem normalizationJacobian_coordinate [DecidableEq T]
    (base : T → ℝ) (unitMass : massMap base = 1) (row column : T) :
    normalizationJacobian base (Pi.single column 1) row =
      (if row = column then 1 else 0) - base row := by
  rw [normalizationJacobian_mass_one base unitMass]
  simp [Pi.single_apply, eq_comm]

/-- The branch after normalization, distinct from the lower envelope. -/
def normalizedBranch (values point : T → ℝ) : ℝ := branchMap values (normalize point)

/-- Chain rule for every fixed opponent branch, not just one diagnostic game. -/
theorem normalizedBranch_hasFDerivAt (values base : T → ℝ)
    (nonzero : massMap base ≠ 0) :
    HasFDerivAt (normalizedBranch values)
      ((branchMap values).comp (normalizationJacobian base)) base :=
  (branchMap values).hasFDerivAt.comp base (normalize_hasFDerivAt base nonzero)

/-- The centered covector in equations (10)-(12). -/
def centeredMap (values base : T → ℝ) : (T → ℝ) →L[ℝ] ℝ :=
  branchMap values - branchMap values base • massMap

/-- The Jacobian contraction is exactly centering by the scalar branch value. -/
theorem contraction_eq_centered (values base : T → ℝ) (unitMass : massMap base = 1) :
    (branchMap values).comp (normalizationJacobian base) = centeredMap values base := by
  apply ContinuousLinearMap.ext
  intro direction
  rw [ContinuousLinearMap.comp_apply, normalizationJacobian_mass_one base unitMass]
  simp [centeredMap, map_sub, map_smul, mul_comm]

/-- Smooth normalized branch derivative at every simplex point, including
boundary points; the ambient derivative is defined because mass is one. -/
theorem normalizedBranch_centered_derivative (values base : T → ℝ)
    (unitMass : massMap base = 1) :
    HasFDerivAt (normalizedBranch values) (centeredMap values base) base := by
  have derivative := normalizedBranch_hasFDerivAt values base (by rw [unitMass]; norm_num)
  rw [contraction_eq_centered values base unitMass] at derivative
  exact derivative

/-- Equation (12) on coordinate directions: conditional value minus scalar value. -/
theorem centeredMap_coordinate [DecidableEq T] (values base : T → ℝ) (type : T) :
    centeredMap values base (Pi.single type 1) = values type - branchMap values base := by
  simp [centeredMap, branchMap, massMap, Pi.single_apply]

omit [Fintype T] in
/-- Fixed conditional values do not depend on own weights (equation (6)). -/
theorem conditional_coordinate_derivative_zero (values : T → ℝ) (type : T) (base : T → ℝ) :
    HasFDerivAt (fun _ : T → ℝ => values type) (0 : (T → ℝ) →L[ℝ] ℝ) base :=
  hasFDerivAt_const (values type) base

end GameTheory.ReBeL.ValueDifferential
