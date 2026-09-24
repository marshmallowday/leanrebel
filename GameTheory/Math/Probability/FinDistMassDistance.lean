/-
# Finite mass distance and bounded observable stability

The distance is the sum of absolute probability differences, without the
one-half normalization. It uses only the finite supports and the public law
API. No common support, probability floor or finiteness of the carrier is
required. An independent product is stable under replacing one marginal.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {A : Type u}

/-- Unnormalized total variation, summed on the union of the finite supports. -/
def massDistance (first second : FinDist A) : ℝ := by
  classical
  exact ∑ a ∈ first.supportFinset ∪ second.supportFinset,
    |first.prob a - second.prob a|

/-- The finite mass distance is nonnegative. -/
theorem massDistance_nonneg (first second : FinDist A) : 0 ≤ massDistance first second := by
  classical
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Identical laws have zero mass distance. -/
theorem massDistance_self (law : FinDist A) : massDistance law law = 0 := by
  classical
  simp only [massDistance, sub_self, abs_zero, Finset.sum_const_zero]

/-- The order of the laws does not matter. -/
theorem massDistance_comm (first second : FinDist A) :
    massDistance first second = massDistance second first := by
  classical
  simp only [massDistance, Finset.union_comm, abs_sub_comm]

/-- On an explicitly finite carrier the support sum is the usual full sum. -/
theorem massDistance_eq_sum [Fintype A] (first second : FinDist A) :
    massDistance first second = ∑ a, |first.prob a - second.prob a| := by
  classical
  unfold massDistance
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ outside
  have notFirst : a ∉ first.support := by
    intro inside
    exact outside (Finset.mem_union_left _ (mem_supportFinset.mpr inside))
  have notSecond : a ∉ second.support := by
    intro inside
    exact outside (Finset.mem_union_right _ (mem_supportFinset.mpr inside))
  rw [prob_eq_zero_iff.mpr notFirst, prob_eq_zero_iff.mpr notSecond, sub_self, abs_zero]

/-- Every bounded observable is Lipschitz for the finite mass distance.
The bound includes new support instead of silently dropping newly possible outcomes. -/
theorem abs_expect_sub_le_massDistance (first second : FinDist A)
    (value : A → ℝ) (bound : ℝ) (bounded : ∀ a, |value a| ≤ bound) :
    |first.expect value - second.expect value| ≤ bound * massDistance first second := by
  classical
  let carrier := first.supportFinset ∪ second.supportFinset
  have containsFirst : first.support ⊆ ↑carrier := fun a inside =>
    Finset.mem_union_left _ (mem_supportFinset.mpr inside)
  have containsSecond : second.support ⊆ ↑carrier := fun a inside =>
    Finset.mem_union_right _ (mem_supportFinset.mpr inside)
  rw [expect_eq_sum_of_subset first value carrier containsFirst,
    expect_eq_sum_of_subset second value carrier containsSecond, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ carrier, |first.prob a * value a - second.prob a * value a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ carrier, |first.prob a - second.prob a| * bound := by
      apply Finset.sum_le_sum
      intro a _
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (bounded a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]; rfl

/-- The normalization is explicit: disjoint laws can have distance two. -/
theorem massDistance_le_two (first second : FinDist A) : massDistance first second ≤ 2 := by
  classical
  let carrier := first.supportFinset ∪ second.supportFinset
  have sumFirst : (∑ a ∈ carrier, first.prob a) = 1 := by
    have total := expect_eq_sum_of_subset first (fun _ => (1 : ℝ)) carrier
      (fun a inside => Finset.mem_union_left _ (mem_supportFinset.mpr inside))
    simpa only [expect_const, mul_one] using total.symm
  have sumSecond : (∑ a ∈ carrier, second.prob a) = 1 := by
    have total := expect_eq_sum_of_subset second (fun _ => (1 : ℝ)) carrier
      (fun a inside => Finset.mem_union_right _ (mem_supportFinset.mpr inside))
    simpa only [expect_const, mul_one] using total.symm
  calc
    _ ≤ ∑ a ∈ carrier, (first.prob a + second.prob a) := by
      apply Finset.sum_le_sum
      intro a _
      exact (abs_sub (first.prob a) (second.prob a)).trans_eq
        (by rw [abs_of_nonneg (prob_nonneg first a), abs_of_nonneg (prob_nonneg second a)])
    _ = 2 := by rw [Finset.sum_add_distrib, sumFirst, sumSecond]; norm_num

/-- Replacing one independent marginal costs only that marginal's distance.
The remaining coordinates may be arbitrary, including a fixed unknown opponent. -/
theorem abs_expect_pi_sub_le_massDistance {I : Type v} [Fintype I] [DecidableEq I]
    {Choice : I → Type*} (first second : ∀ i, FinDist (Choice i)) (who : I)
    (same : ∀ other, other ≠ who → first other = second other)
    (value : ((i : I) → Choice i) → ℝ) (bound : ℝ)
    (bounded : ∀ choice, |value choice| ≤ bound) :
    |(FinDist.pi first).expect value - (FinDist.pi second).expect value| ≤
      bound * massDistance (first who) (second who) := by
  rw [pi_eq_map_product who first, pi_eq_map_product who second]
  have rest : (fun other : {other : I // other ≠ who} => first other.1) =
      (fun other : {other : I // other ≠ who} => second other.1) :=
    funext fun other => same other.1 other.2
  rw [rest]
  simp only [expect_map, product, expect_bind]
  exact abs_expect_sub_le_massDistance _ _ _ bound fun choice =>
    abs_expect_le_of_abs_bound _ _ (fun other _ => bounded _)

end GameTheory.Math.Probability.FinDist
