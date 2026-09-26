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


omit [Fintype A] in
/-- Changing positive weights inside model support does not create missing mass. -/
theorem probOf_unsupported_eq_zero_of_support_subset (actual model : FinDist A)
    (included : actual.support ⊆ model.support) :
    actual.probOf {x | x ∉ model.support} = 0 := by
  classical
  rw [← expect_indicator_eq_probOf]
  calc
    _ = actual.expect (fun _ => (0 : ℝ)) := by
      apply expect_congr
      intro x reached
      simp only [Set.mem_ofPred_eq, included reached, not_true_eq_false, if_false]
    _ = 0 := expect_const _ _

omit [Fintype A] in
/-- Every model-impossible event is included in the actual unsupported mass. -/
theorem probOf_le_probOf_unsupported (actual model : FinDist A) (event : Set A)
    (impossible : ∀ x ∈ event, x ∉ model.support) :
    actual.probOf event ≤ actual.probOf {x | x ∉ model.support} := by
  classical
  rw [← expect_indicator_eq_probOf, ← expect_indicator_eq_probOf]
  apply expect_mono
  intro x _
  by_cases selected : x ∈ event
  · simp only [Set.mem_ofPred_eq, selected, impossible x selected, if_true, le_refl]
  · simp only [selected, if_false]
    split <;> norm_num

omit [Fintype A] in
/-- Missing output support is charged by incoming missing mass and one-step
kernel leakage under the ACTUAL input. Unequal supported weights cost nothing. -/
theorem probOf_bind_unsupported_le (actual model : FinDist A)
    (first second : A → FinDist B) :
    (actual.bind first).probOf {y | y ∉ (model.bind second).support} ≤
      actual.probOf {x | x ∉ model.support} +
        actual.expect (fun x => (first x).probOf {y | y ∉ (second x).support}) := by
  classical
  calc
    _ = actual.expect (fun x => (first x).expect
        (fun y => if y ∉ (model.bind second).support then (1 : ℝ) else 0)) := by
      rw [← expect_indicator_eq_probOf, expect_bind]
    _ ≤ actual.expect (fun x => (if x ∉ model.support then (1 : ℝ) else 0) +
        (first x).probOf {y | y ∉ (second x).support}) := by
      apply expect_mono
      intro x _
      have pointwise (y : B) :
          (if y ∉ (model.bind second).support then (1 : ℝ) else 0) ≤
            (if x ∉ model.support then 1 else 0) +
              (if y ∉ (second x).support then 1 else 0) := by
        by_cases source : x ∈ model.support
        · by_cases target : y ∈ (second x).support
          · have reached : y ∈ (model.bind second).support := by
              rw [support_bind]
              exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨source, target⟩⟩
            simp only [source, target, reached, not_true_eq_false, if_false, add_zero, le_refl]
          · simp only [source, target, not_true_eq_false, not_false_eq_true, if_false, if_true,
              zero_add]
            split <;> norm_num
        · simp only [source, not_false_eq_true, if_true]
          split_ifs <;> norm_num
      have averaged := expect_mono (μ := first x) (fun y _ => pointwise y)
      simpa only [expect_add, expect_const, expect_indicator_eq_probOf] using averaged
    _ = _ := by rw [expect_add, expect_indicator_eq_probOf]

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
