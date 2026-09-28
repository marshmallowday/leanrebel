/-
# Error from discarding part of a conditional law

Conditioning on a nested positive event changes a bounded expectation by at
most twice its bound times the discarded conditional mass. No positive lower
bound on individual atoms, finite carrier, or independence is required.
-/

import GameTheory.Math.Probability.FinDistEventError

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u
variable {α : Type u}

/-- Replacing values off a positive event by its conditional mean leaves that
mean as the unconditional expectation. This is an analysis identity only. -/
theorem expect_paste_conditional_mean (law : FinDist α) (event : Set α)
    [DecidablePred (· ∈ event)]
    (possible : ∃ x ∈ event, x ∈ law.support) (value : α → ℝ) :
    law.expect (fun x => if x ∈ event then value x
      else (law.condOn event possible).expect value) =
      (law.condOn event possible).expect value := by
  classical
  let mean := (law.condOn event possible).expect value
  let residual := fun x => if x ∈ event then value x - mean else 0
  have inside : (law.condOn event possible).expect residual = 0 := by
    calc
      _ = (law.condOn event possible).expect (fun x => value x - mean) := by
        apply expect_congr
        intro x reached
        exact if_pos ((support_condOn law event possible reached).1)
      _ = 0 := by rw [expect_sub, expect_const]; exact sub_self mean
  have ratio := expect_condOn_eq_div_of_eq_zero_off law event possible residual
    (fun x _ outside => if_neg outside)
  have zero : law.expect residual = 0 := by
    rw [inside] at ratio
    have product := (div_eq_iff (ne_of_gt (probOf_pos possible))).mp ratio.symm
    simpa only [zero_mul] using product
  calc
    _ = law.expect (fun x => residual x + mean) := by
      apply expect_congr
      intro x _
      dsimp only [residual]
      by_cases member : x ∈ event
      · rw [if_pos member, if_pos member]; ring
      · rw [if_neg member, if_neg member, zero_add]
    _ = mean := by rw [expect_add, expect_const, zero, zero_add]

/-- The discarded conditional mass, rather than a uniform lower bound on
reach, controls both signs of the change of a bounded expectation. -/
theorem abs_expect_sub_condOn_le_compl (law : FinDist α) (event : Set α)
    (possible : ∃ x ∈ event, x ∈ law.support) (value : α → ℝ) (bound : ℝ)
    (bounded : ∀ x ∈ law.support, |value x| ≤ bound) :
    |law.expect value - (law.condOn event possible).expect value| ≤
      2 * bound * law.probOf eventᶜ := by
  classical
  have meanBound : |(law.condOn event possible).expect value| ≤ bound :=
    abs_expect_le_of_abs_bound _ value
      (fun x reached => bounded x (support_condOn law event possible reached).2)
  have estimate := abs_expect_sub_le_of_eq_off_event law eventᶜ value
    (fun x => if x ∈ event then value x else (law.condOn event possible).expect value)
    bound bounded (by
      intro x reached
      by_cases member : x ∈ event
      · rw [if_pos member]; exact bounded x reached
      · rw [if_neg member]; exact meanBound) (by
      intro x _ outside
      have member : x ∈ event := by simpa only [Set.mem_compl_iff, not_not] using outside
      exact (if_pos member).symm)
  rw [expect_paste_conditional_mean] at estimate
  exact estimate

/-- Nested conditioning has an explicit discarded-mass numerator and public
reach denominator. The smaller event must have positive mass. -/
theorem abs_condOn_expect_sub_le_discarded (law : FinDist α) (outer inner : Set α)
    (outerPossible : ∃ x ∈ outer, x ∈ law.support)
    (innerPossible : ∃ x ∈ inner, x ∈ law.support)
    (contained : inner ∩ law.support ⊆ outer)
    (value : α → ℝ) (bound : ℝ) (bounded : ∀ x ∈ law.support, |value x| ≤ bound) :
    |(law.condOn outer outerPossible).expect value -
      (law.condOn inner innerPossible).expect value| ≤
      2 * bound * (law.probOf (outer ∩ innerᶜ) / law.probOf outer) := by
  have innerConditional : ∃ x ∈ inner, x ∈ (law.condOn outer outerPossible).support := by
    obtain ⟨x, member, reached⟩ := innerPossible
    exact ⟨x, member, mem_support_condOn law outer outerPossible
      (contained ⟨member, reached⟩) reached⟩
  have estimate := abs_expect_sub_condOn_le_compl (law.condOn outer outerPossible)
    inner innerConditional value bound
    (fun x reached => bounded x (support_condOn law outer outerPossible reached).2)
  rw [condOn_condOn law outerPossible innerPossible contained innerConditional,
    probOf_condOn_eq_inter outerPossible] at estimate
  exact estimate

end GameTheory.Math.Probability.FinDist
