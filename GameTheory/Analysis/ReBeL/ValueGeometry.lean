/-
# Simplex support and a corrected concave extension

The value is an attained minimum of affine fixed-opponent branches. This
module proves the simplex supporting inequality first, and then extends it
by an affine mass correction. It does not identify that extension with the
radially normalized expression in Appendix F: the latter need not be concave.
-/

import GameTheory.Analysis.ReBeL.TypeValue
import GameTheory.Math.Probability.Simplex
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Convert

noncomputable section

namespace GameTheory.ReBeL.TypeGame

open GameTheory.Math.Probability GameTheory.MatrixGame

universe u

variable {T B : Type u} [Fintype T] [DecidableEq T] [Fintype B] [Nonempty B]
variable {Action : T → Type u}
variable [∀ t, Fintype (Action t)] [∀ t, Nonempty (Action t)]
variable (payoff : (t : T) → Action t → B → ℝ)

/-- Lemma 2's concavity on the full nonnegative cone of own weights. It is
proved using an attaining opponent at the combined point, not assumed. -/
theorem value_concaveOn :
    ConcaveOn ℝ {weight : T → ℝ | ∀ t, 0 ≤ weight t} (value payoff) := by
  constructor
  · intro first hfirst second hsecond a b ha hb _ t
    exact add_nonneg (mul_nonneg ha (hfirst t)) (mul_nonneg hb (hsecond t))
  · intro first hfirst second hsecond a b ha hb _
    let combined : T → ℝ := fun t => a * first t + b * second t
    have hcombined : ∀ t, 0 ≤ combined t := fun t =>
      add_nonneg (mul_nonneg ha (hfirst t)) (mul_nonneg hb (hsecond t))
    let opponent := valueColumn (matrix payoff combined)
    have hfirst' := value_le_branch payoff first hfirst opponent
    have hsecond' := value_le_branch payoff second hsecond opponent
    have attained := branch_valueColumn payoff combined hcombined
    have linear := branch_linear payoff first second a b opponent
    have bound := add_le_add (mul_le_mul_of_nonneg_left hfirst' ha)
      (mul_le_mul_of_nonneg_left hsecond' hb)
    have result : a * value payoff first + b * value payoff second ≤
        value payoff combined := bound.trans_eq (linear.symm.trans attained)
    convert! result using 1

/-- Restricting the own weights to the existing probability simplex preserves
concavity, including its boundary. -/
theorem value_concaveOn_simplex : ConcaveOn ℝ (stdSimplex ℝ T) (value payoff) :=
  (value_concaveOn payoff).subset (fun _ h => h.1) (convex_stdSimplex ℝ T)

/-- The centered value vector appearing in Eq. (2). -/
def centeredVector (base : T → ℝ) (opponent : FinDist B) (t : T) : ℝ :=
  infoValue payoff opponent t - value payoff base

/-- A purely algebraic identity separating the simplex normal direction from
its tangent directions. It makes no positivity or differentiability claim. -/
theorem centered_dot_eq (base point : T → ℝ) (opponent : FinDist B) :
    (∑ t, centeredVector payoff base opponent t * (point t - base t)) =
      branch payoff point opponent - branch payoff base opponent -
        ((∑ t, point t) - ∑ t, base t) * value payoff base := by
  calc
    (∑ t, centeredVector payoff base opponent t * (point t - base t)) =
        ∑ t, ((point t * infoValue payoff opponent t -
          base t * infoValue payoff opponent t) -
            (point t - base t) * value payoff base) := by
      apply Finset.sum_congr rfl
      intro t _
      unfold centeredVector
      ring
    _ = branch payoff point opponent - branch payoff base opponent -
        ((∑ t, point t) - ∑ t, base t) * value payoff base := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        Finset.sum_sub_distrib]
      rfl

/-- Theorem 1 on the simplex: any minimizing opponent supplies a supporting
centered value vector, even where the value is nondifferentiable. -/
theorem simplex_support {base point : T → ℝ}
    (hbase : base ∈ stdSimplex ℝ T) (hpoint : point ∈ stdSimplex ℝ T)
    (opponent : FinDist B)
    (optimal : branch payoff base opponent = value payoff base) :
    value payoff point ≤ value payoff base +
      ∑ t, centeredVector payoff base opponent t * (point t - base t) := by
  have bound := value_le_branch payoff point hpoint.1 opponent
  rw [centered_dot_eq, optimal, hbase.2, hpoint.2]
  linarith

/-- This concave extension agrees with the value on mass-one weights. Its
normal derivative is fixed by the value at the chosen base point. It is not
Appendix F's radial normalization. -/
def centeredExtension (base point : T → ℝ) : ℝ :=
  value payoff point + (1 - ∑ t, point t) * value payoff base

/-- The repaired extension really extends the same simplex value. -/
theorem centeredExtension_eq_on_simplex (base : T → ℝ) :
    Set.EqOn (centeredExtension payoff base) (value payoff) (stdSimplex ℝ T) := by
  intro point hpoint
  simp only [centeredExtension, hpoint.2, sub_self, zero_mul, add_zero]

/-- Adding the affine mass correction preserves concavity on the whole
nonnegative cone, unlike radial normalization. -/
theorem centeredExtension_concaveOn (base : T → ℝ) :
    ConcaveOn ℝ {weight : T → ℝ | ∀ t, 0 ≤ weight t}
      (centeredExtension payoff base) := by
  refine ⟨(value_concaveOn payoff).1, ?_⟩
  intro first hfirst second hsecond a b ha hb hab
  have bound := (value_concaveOn payoff).2 hfirst hsecond ha hb hab
  have mass : (∑ t, (a • first + b • second) t) =
      a * (∑ t, first t) + b * ∑ t, second t := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
  have affine : a * ((1 - ∑ t, first t) * value payoff base) +
      b * ((1 - ∑ t, second t) * value payoff base) =
        (1 - ∑ t, (a • first + b • second) t) * value payoff base := by
    rw [mass]
    calc
      _ = ((a + b) - (a * (∑ t, first t) + b * ∑ t, second t)) *
          value payoff base := by ring
      _ = _ := by rw [hab]
  simp only [smul_eq_mul] at bound ⊢
  unfold centeredExtension
  nlinarith only [bound, affine]

/-- Global support on the repaired extension. Both the base and candidate
may lie on the boundary; no division by a type probability occurs. -/
theorem centeredExtension_support {base : T → ℝ}
    (hbase : base ∈ stdSimplex ℝ T) (point : T → ℝ) (hpoint : ∀ t, 0 ≤ point t)
    (opponent : FinDist B)
    (optimal : branch payoff base opponent = value payoff base) :
    centeredExtension payoff base point ≤ centeredExtension payoff base base +
      ∑ t, centeredVector payoff base opponent t * (point t - base t) := by
  have bound := value_le_branch payoff point hpoint opponent
  rw [centered_dot_eq, optimal, hbase.2]
  simp only [centeredExtension, hbase.2, sub_self, zero_mul, add_zero]
  nlinarith

/-- Eq. (2)'s coordinate identity for the vector certified above. -/
theorem infoValue_eq_value_add_centered (base : T → ℝ) (opponent : FinDist B) (t : T) :
    infoValue payoff opponent t = value payoff base + centeredVector payoff base opponent t := by
  unfold centeredVector
  ring

/-- The source's existential extension and Eq. (2), under the explicit finite
normal-form interpretation. This theorem chooses the corrected extension,
not the nonconcave normalized formula printed in Appendix F. -/
theorem theorem1_correctedExtension {base : T → ℝ} (hbase : base ∈ stdSimplex ℝ T)
    (opponent : FinDist B)
    (optimal : branch payoff base opponent = value payoff base) :
    ∃ extension : (T → ℝ) → ℝ,
      Set.EqOn extension (value payoff) (stdSimplex ℝ T) ∧
      ConcaveOn ℝ {weight : T → ℝ | ∀ t, 0 ≤ weight t} extension ∧
      (∀ point : T → ℝ, (∀ t, 0 ≤ point t) →
        extension point ≤ extension base +
          ∑ t, centeredVector payoff base opponent t * (point t - base t)) ∧
      (∀ t, infoValue payoff opponent t =
        value payoff base + centeredVector payoff base opponent t) := by
  exact ⟨centeredExtension payoff base, centeredExtension_eq_on_simplex payoff base,
    centeredExtension_concaveOn payoff base,
    fun point hpoint => centeredExtension_support payoff hbase point hpoint opponent optimal,
    infoValue_eq_value_add_centered payoff base opponent⟩

/-- Footnote 8: finite convex combinations of optimal value vectors retain
simplex support. A `FinDist` enforces nonnegative weights summing to one. -/
theorem averaged_simplex_support {base point : T → ℝ}
    (hbase : base ∈ stdSimplex ℝ T) (hpoint : point ∈ stdSimplex ℝ T)
    (opponents : FinDist (FinDist B))
    (optimal : ∀ opponent ∈ opponents.support,
      branch payoff base opponent = value payoff base) :
    value payoff point ≤ value payoff base +
      ∑ t, opponents.expect (fun opponent => centeredVector payoff base opponent t) *
        (point t - base t) := by
  calc
    value payoff point = opponents.expect (fun _ => value payoff point) :=
      (FinDist.expect_const _ _).symm
    _ ≤ opponents.expect (fun opponent => value payoff base +
        ∑ t, centeredVector payoff base opponent t * (point t - base t)) :=
      FinDist.expect_mono fun opponent supported =>
        simplex_support payoff hbase hpoint opponent (optimal opponent supported)
    _ = _ := by
      rw [FinDist.expect_add, FinDist.expect_const, ← FinDist.expect_sum_comm]
      simp only [FinDist.expect_mul_const]

end GameTheory.ReBeL.TypeGame
