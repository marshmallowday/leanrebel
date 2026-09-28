/-
# Payoff intervals for errors confined to an event

The interval width is independent of a common payoff translation. No symmetry
about zero or identification of either conditional law is required.
-/

import GameTheory.Math.Probability.FinDistEventError

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v

/-- An old upper endpoint and a new lower endpoint suffice for a signed
event error. Equality is required only off the event on actual support. -/
theorem expect_sub_le_of_eq_off_event_range {A : Type u} (law : FinDist A)
    (event : Set A) (first second : A → ℝ) (lower upper : ℝ)
    (firstUpper : ∀ x ∈ law.support, first x ≤ upper)
    (secondLower : ∀ x ∈ law.support, lower ≤ second x)
    (equal : ∀ x ∈ law.support, x ∉ event → first x = second x) :
    law.expect first - law.expect second ≤ (upper - lower) * law.probOf event := by
  classical
  calc
    _ = law.expect (fun x => first x - second x) := (FinDist.expect_sub _ _ _).symm
    _ ≤ law.expect (fun x => (upper - lower) * (if x ∈ event then 1 else 0)) := by
      apply FinDist.expect_mono
      intro x reached
      by_cases exceptional : x ∈ event
      · rw [if_pos exceptional, mul_one]
        exact sub_le_sub (firstUpper x reached) (secondLower x reached)
      · rw [if_neg exceptional, mul_zero, equal x reached exceptional, sub_self]
    _ = _ := by rw [FinDist.expect_smul, FinDist.expect_indicator_eq_probOf]

/-- Kernel payoff errors on an event cost its actual mass times the payoff
diameter. The two laws need only agree in value outside the event. -/
theorem expect_bind_sub_le_of_eq_off_event_range {A : Type u} {B : Type v}
    (law : FinDist A) (event : Set A) (first second : A → FinDist B)
    (value : B → ℝ) (lower upper : ℝ)
    (lowerBound : ∀ x, lower ≤ value x) (upperBound : ∀ x, value x ≤ upper)
    (equal : ∀ x ∈ law.support, x ∉ event →
      (first x).expect value = (second x).expect value) :
    (law.bind first).expect value - (law.bind second).expect value ≤
      (upper - lower) * law.probOf event := by
  rw [FinDist.expect_bind, FinDist.expect_bind]
  apply expect_sub_le_of_eq_off_event_range law event
    (fun x => (first x).expect value) (fun x => (second x).expect value) lower upper
  · intro x _
    exact FinDist.expect_le_of_forall (first x) value upper (fun y _ => upperBound y)
  · intro x _
    calc
      lower = (second x).expect (fun _ => lower) := (FinDist.expect_const _ _).symm
      _ ≤ _ := FinDist.expect_mono (fun y _ => lowerBound y)
  · exact equal

end GameTheory.Math.Probability.FinDist
