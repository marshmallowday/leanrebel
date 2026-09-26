/-
# Finite-kernel perturbation in source-atom variation

These estimates use the existing FinDist atomVariation, not a new metric or
probability representation. The kernel discrepancy is averaged under the
FIRST input law. Disappearing support is charged rather than normalized.
-/

import GameTheory.Math.Probability.FinDistTransportRate

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {A : Type u} {B : Type v} [Fintype A]

/-- Source-atom variation obeys the triangle inequality. -/
theorem atomVariation_triangle (first middle last : FinDist A) :
    atomVariation first last ≤ atomVariation first middle + atomVariation middle last := by
  unfold atomVariation
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun x _ => abs_sub_le (first.prob x) (middle.prob x) (last.prob x))

/-- An event impossible under the model is charged under the ACTUAL law.
No support inclusion or positive lower bound on a model atom is needed. -/
theorem probOf_le_atomVariation_of_model_impossible (actual model : FinDist A)
    (event : Set A) (impossible : ∀ x ∈ event, x ∉ model.support) :
    actual.probOf event ≤ atomVariation actual model := by
  classical
  rw [← expect_indicator_eq_probOf, expect_eq_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases selected : x ∈ event
  · rw [if_pos selected, mul_one, prob_eq_zero_iff.mpr (impossible x selected), sub_zero,
      abs_of_nonneg (prob_nonneg actual x)]
  · rw [if_neg selected, mul_zero]
    exact abs_nonneg _

variable [Fintype B]

/-- Applying the same stochastic kernel cannot increase source-law variation. -/
theorem atomVariation_bind_same_kernel (first second : FinDist A) (kernel : A → FinDist B) :
    atomVariation (first.bind kernel) (second.bind kernel) ≤ atomVariation first second := by
  calc
    _ ≤ ∑ y, ∑ x, |first.prob x - second.prob x| * (kernel x).prob y := by
      apply Finset.sum_le_sum
      intro y _
      rw [prob_bind, prob_bind, expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ x, |first.prob x * (kernel x).prob y -
            second.prob x * (kernel x).prob y| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← sub_mul, abs_mul, abs_of_nonneg (prob_nonneg _ _)]
    _ = atomVariation first second := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, sum_prob, mul_one, atomVariation]

/-- Kernel changes are averaged under their actual input, not the model input. -/
theorem atomVariation_bind_same_input (law : FinDist A) (first second : A → FinDist B) :
    atomVariation (law.bind first) (law.bind second) ≤
      law.expect (fun x => atomVariation (first x) (second x)) := by
  calc
    _ ≤ ∑ y, ∑ x, law.prob x * |(first x).prob y - (second x).prob y| := by
      apply Finset.sum_le_sum
      intro y _
      rw [prob_bind, prob_bind, expect_eq_sum, expect_eq_sum, ← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ x, |law.prob x * (first x).prob y -
            law.prob x * (second x).prob y| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← mul_sub, abs_mul, abs_of_nonneg (prob_nonneg _ _)]
    _ = _ := by
      rw [Finset.sum_comm, expect_eq_sum]
      simp only [atomVariation, Finset.mul_sum]

/-- Both source and kernel may change. Only the first source samples the
kernel error; the second kernel contracts the remaining input-law mismatch. -/
theorem atomVariation_bind_le (actual model : FinDist A) (first second : A → FinDist B) :
    atomVariation (actual.bind first) (model.bind second) ≤
      atomVariation actual model + actual.expect (fun x => atomVariation (first x) (second x)) := by
  calc
    _ ≤ atomVariation (actual.bind first) (actual.bind second) +
        atomVariation (actual.bind second) (model.bind second) := atomVariation_triangle _ _ _
    _ ≤ actual.expect (fun x => atomVariation (first x) (second x)) +
        atomVariation actual model :=
      add_le_add (atomVariation_bind_same_input actual first second)
        (atomVariation_bind_same_kernel actual model second)
    _ = _ := add_comm _ _

end GameTheory.Math.Probability.FinDist
