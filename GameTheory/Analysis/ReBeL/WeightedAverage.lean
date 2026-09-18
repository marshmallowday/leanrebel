/-
# Law averages with nonnegative reach weights

A zero denominator selects an explicit fallback law. It is not interpreted as
a posterior. The mass-times-probability identity holds without a positivity
premise and therefore preserves genuinely unreachable branches.
-/

import GameTheory.ReBeL.ReachWeights

noncomputable section

namespace GameTheory.ReBeL.ReachWeights

open GameTheory.Math.Probability

variable {K A : Type*} [Fintype K]

/-- Average local laws by their unnormalized reach weights. At zero total
reach the prescribed fallback is a legal law, not a fabricated conditional law. -/
def average (weights : ReachWeights K) (laws : K → FinDist A)
    (fallback : FinDist A) : FinDist A := by
  classical
  exact if positive : 0 < weights.mass then
    (weights.normalize positive).bind laws else fallback

/-- A zero-reach information state uses exactly the stated fallback law. -/
theorem average_of_mass_zero (weights : ReachWeights K) (laws : K → FinDist A)
    (fallback : FinDist A) (hzero : weights.mass = 0) :
    weights.average laws fallback = fallback := by
  simp [average, hzero]

/-- Multiplication by total reach cancels normalization, including the
zero-reach case. No reachable branch is removed from either side of the sum. -/
theorem mass_mul_prob_average (weights : ReachWeights K) (laws : K → FinDist A)
    (fallback : FinDist A) (action : A) :
    weights.mass * (weights.average laws fallback).prob action =
      ∑ k, weights.weight k * (laws k).prob action := by
  classical
  by_cases positive : 0 < weights.mass
  · simp only [average, dif_pos positive, FinDist.prob_bind,
      FinDist.expect_eq_sum, prob_normalize]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    field_simp
  · have hzero : weights.mass = 0 :=
      le_antisymm (le_of_not_gt positive) weights.mass_nonneg
    rw [hzero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hk : weights.weight k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => weights.nonneg j).mp
        hzero k (Finset.mem_univ k)
    rw [hk, zero_mul]

/-- Positive rescaling does not change either the selected law or the
zero-reach fallback. This covers sums versus uniform iteration averages. -/
theorem average_scale (weights : ReachWeights K) (laws : K → FinDist A)
    (fallback : FinDist A) (scale : ℝ) (hscale : 0 < scale) :
    (weights.scale scale hscale.le).average laws fallback =
      weights.average laws fallback := by
  classical
  by_cases positive : 0 < weights.mass
  · have hscaled : 0 < (weights.scale scale hscale.le).mass := by
      rw [mass_scale]
      exact mul_pos hscale positive
    simp only [average, dif_pos positive, dif_pos hscaled]
    rw [normalize_scale weights scale hscale positive]
  · have hzero : weights.mass = 0 :=
      le_antisymm (le_of_not_gt positive) weights.mass_nonneg
    have hscaled : (weights.scale scale hscale.le).mass = 0 := by
      rw [mass_scale, hzero, mul_zero]
    rw [average_of_mass_zero _ _ _ hscaled, average_of_mass_zero _ _ _ hzero]

end GameTheory.ReBeL.ReachWeights
