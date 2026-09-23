/-
# Finite-law errors confined to an explicit event

Only the probability of the exceptional event is charged. The observable
and kernels may be unrelated on that event. No support domination or
identification of two conditional distributions is an input.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v

/-- Equality away from an event confines the mean error to that event's mass.
Bounds and equality are required only at points the actual law can reach. -/
theorem expect_sub_le_of_eq_off_event {A : Type u} (law : FinDist A)
    (event : Set A) (first second : A → ℝ) (bound : ℝ)
    (firstBound : ∀ x ∈ law.support, |first x| ≤ bound)
    (secondBound : ∀ x ∈ law.support, |second x| ≤ bound)
    (equal : ∀ x ∈ law.support, x ∉ event → first x = second x) :
    law.expect first - law.expect second ≤ 2 * bound * law.probOf event := by
  classical
  calc
    _ = law.expect (fun x => first x - second x) := (FinDist.expect_sub _ _ _).symm
    _ ≤ law.expect (fun x => 2 * bound * (if x ∈ event then 1 else 0)) := by
      apply FinDist.expect_mono
      intro x reached
      by_cases exceptional : x ∈ event
      · rw [if_pos exceptional, mul_one]
        have upper := (abs_le.mp (firstBound x reached)).2
        have lower := (abs_le.mp (secondBound x reached)).1
        linarith
      · rw [if_neg exceptional, mul_zero, equal x reached exceptional, sub_self]
    _ = _ := by rw [FinDist.expect_smul, FinDist.expect_indicator_eq_probOf]

/-- The event bound controls both signs, not just a favorable payoff direction. -/
theorem abs_expect_sub_le_of_eq_off_event {A : Type u} (law : FinDist A)
    (event : Set A) (first second : A → ℝ) (bound : ℝ)
    (firstBound : ∀ x ∈ law.support, |first x| ≤ bound)
    (secondBound : ∀ x ∈ law.support, |second x| ≤ bound)
    (equal : ∀ x ∈ law.support, x ∉ event → first x = second x) :
    |law.expect first - law.expect second| ≤ 2 * bound * law.probOf event := by
  have upper := expect_sub_le_of_eq_off_event law event first second bound
    firstBound secondBound equal
  have lower := expect_sub_le_of_eq_off_event law event second first bound
    secondBound firstBound (fun x reached outside => (equal x reached outside).symm)
  exact abs_le.mpr ⟨by linarith, upper⟩

/-- Two finite kernels need agree only outside an explicit exceptional event.
Their arbitrary behavior on that event costs at most twice the payoff bound. -/
theorem abs_expect_bind_sub_le_of_eq_off_event {A : Type u} {B : Type v}
    (law : FinDist A) (event : Set A) (first second : A → FinDist B)
    (payoff : B → ℝ) (bound : ℝ) (bounded : ∀ x, |payoff x| ≤ bound)
    (equal : ∀ x ∈ law.support, x ∉ event → first x = second x) :
    |(law.bind first).expect payoff - (law.bind second).expect payoff| ≤
      2 * bound * law.probOf event := by
  have boundedMean (distribution : FinDist B) : |distribution.expect payoff| ≤ bound := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have lower : distribution.expect (fun _ => -bound) ≤ distribution.expect payoff :=
        FinDist.expect_mono (fun x _ => (abs_le.mp (bounded x)).1)
      simpa only [FinDist.expect_const] using lower
    · exact FinDist.expect_le_of_forall distribution payoff bound
        (fun x _ => (abs_le.mp (bounded x)).2)
  rw [FinDist.expect_bind, FinDist.expect_bind]
  exact abs_expect_sub_le_of_eq_off_event law event _ _ bound
    (fun x _ => boundedMean (first x)) (fun x _ => boundedMean (second x))
    (fun x reached outside => congrArg (fun distribution => distribution.expect payoff)
      (equal x reached outside))

end GameTheory.Math.Probability.FinDist
