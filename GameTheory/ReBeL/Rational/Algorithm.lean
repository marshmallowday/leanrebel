/-
# Executable rational CFR arithmetic

This frontend uses exact rationals, supplied finite enumerations and decidable
equality only. Its pure fallback is an explicit legal action. The real-valued
interpretation and its connection to canonical regret matching live in Analysis.
-/

import GameTheory.Core.Signature
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

namespace GameTheory.ReBeL.Rational

variable {A : Type*} [Fintype A]

/-- Sum of the positive coordinates of an exact rational regret table. -/
def positiveMass (score : A → ℚ) : ℚ := ∑ a, max (score a) 0

/-- Positive mass is nonnegative even when all regrets are negative. -/
theorem positiveMass_nonneg (score : A → ℚ) : 0 ≤ positiveMass score :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

variable [DecidableEq A]

/-- An exact rational point mass, with no arbitrary choice of fallback. -/
def pointMass (fallback : A) (a : A) : ℚ := if a = fallback then 1 else 0

/-- Vanilla regret matching, not CFR+ clipping of accumulated regrets. -/
def matchProb (fallback : A) (score : A → ℚ) (a : A) : ℚ :=
  if 0 < positiveMass score then max (score a) 0 / positiveMass score
  else pointMass fallback a

/-- The numerical matcher never produces a negative action weight. -/
theorem matchProb_nonneg (fallback : A) (score : A → ℚ) (a : A) :
    0 ≤ matchProb fallback score a := by
  unfold matchProb
  split
  · exact div_nonneg (le_max_right _ _) (positiveMass_nonneg score)
  · simp only [pointMass]
    split <;> decide

/-- Both the positive-mass branch and the specified fallback are normalized. -/
theorem sum_matchProb (fallback : A) (score : A → ℚ) :
    ∑ a, matchProb fallback score a = 1 := by
  by_cases h : 0 < positiveMass score
  · simp only [matchProb, if_pos h]
    rw [← Finset.sum_div]
    exact div_self h.ne'
  · simp [matchProb, h, pointMass]

/-- Zero-regret initialization yields exactly the selected fallback. -/
theorem matchProb_zero (fallback : A) : matchProb fallback (fun _ => 0) = pointMass fallback := by
  funext a
  simp [matchProb, positiveMass]

/-- A scalar update in the average-regret coordinates used by the real solver. -/
def averageRegretUpdate (round : ℕ) (previous instantaneous : ℚ) : ℚ :=
  ((round : ℚ) / ((round : ℚ) + 1)) * previous +
    (1 / ((round : ℚ) + 1)) * instantaneous

/-- An unnormalized weighted average with an explicit zero-denominator branch.
The callers supply nonnegative reaches and normalized action vectors. -/
def weightedPolicy {K : Type*} [Fintype K] (fallback : A)
    (weights : K → ℚ) (policies : K → A → ℚ) (a : A) : ℚ :=
  if 0 < ∑ k, weights k then (∑ k, weights k * policies k a) / ∑ k, weights k
  else pointMass fallback a

/-- No fictitious posterior or uniform distribution is introduced at zero reach. -/
theorem weightedPolicy_zero {K : Type*} [Fintype K] (fallback : A)
    (policies : K → A → ℚ) :
    weightedPolicy fallback (fun _ => (0 : ℚ)) policies = pointMass fallback := by
  funext a
  simp [weightedPolicy]

end GameTheory.ReBeL.Rational
