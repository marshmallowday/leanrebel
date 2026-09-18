/-
# Exact rational arithmetic refines canonical real regret matching

This is a kernel-checked cast bridge, not a numerical tolerance test. The
positive-mass and zero-mass branches agree, including their explicit fallback.
It is one component of the full-game evaluator refinement, not that entire proof.
-/

import GameTheory.ReBeL.Rational.Algorithm
import GameTheory.Analysis.ReBeL.RegretMatching

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Math.Probability

variable {A : Type*} [Fintype A]

/-- Embed a rational score vector in the existing Euclidean regret carrier. -/
def realScore (score : A → ℚ) : EuclideanSpace ℝ A :=
  WithLp.toLp 2 fun a => (score a : ℝ)

/-- Positive-part summation commutes with the exact rational embedding. -/
theorem cast_positiveMass (score : A → ℚ) :
    (positiveMass score : ℝ) = ∑ a, max ((realScore score).ofLp a) 0 := by
  simp only [positiveMass, realScore, WithLp.ofLp_toLp]
  push_cast

variable [DecidableEq A]

omit [Fintype A] in
/-- The rational fallback is the probability vector of the canonical point mass. -/
theorem cast_pointMass (fallback a : A) :
    (pointMass fallback a : ℝ) = (FinDist.pure fallback).prob a := by
  by_cases h : a = fallback <;> simp [pointMass, FinDist.prob_pure_eq_ite, h]

/-- Every action weight of the executable matcher equals the real specification. -/
theorem cast_matchProb (fallback : A) (score : A → ℚ) (a : A) :
    (matchProb fallback score a : ℝ) =
      (regretMatchWith fallback (realScore score)).prob a := by
  have hpos : (0 : ℝ) < ∑ b, max ((realScore score).ofLp b) 0 ↔
      0 < positiveMass score := by
    rw [← cast_positiveMass]
    exact Rat.cast_pos
  by_cases h : 0 < positiveMass score
  · rw [matchProb, if_pos h, regretMatchWith, dif_pos (hpos.mpr h),
      FinDist.prob_ofWeights]
    push_cast
    rw [cast_positiveMass]
  · rw [matchProb, if_neg h, regretMatchWith, dif_neg (fun hp => h (hpos.mp hp))]
    exact cast_pointMass fallback a

/-- Package an executable matcher result using the one canonical probability law. -/
def matchLaw (fallback : A) (score : A → ℚ) : FinDist A :=
  FinDist.ofWeights (fun a => (matchProb fallback score a : ℝ))
    (fun a => by exact_mod_cast matchProb_nonneg fallback score a)
    (by exact_mod_cast sum_matchProb fallback score)

/-- Exact distribution equality, including the fallback branch. -/
theorem matchLaw_eq (fallback : A) (score : A → ℚ) :
    matchLaw fallback score = regretMatchWith fallback (realScore score) := by
  apply FinDist.ext_of_prob
  intro a
  rw [matchLaw, FinDist.prob_ofWeights]
  exact cast_matchProb fallback score a

omit [Fintype A] [DecidableEq A] in
/-- Every numerical average-regret update is exact over the real specification. -/
theorem cast_averageRegretUpdate (round : ℕ) (previous instantaneous : ℚ) :
    (averageRegretUpdate round previous instantaneous : ℝ) =
      ((round : ℝ) / ((round : ℝ) + 1)) * (previous : ℝ) +
        (1 / ((round : ℝ) + 1)) * (instantaneous : ℝ) := by
  simp [averageRegretUpdate]

end GameTheory.ReBeL.Rational
