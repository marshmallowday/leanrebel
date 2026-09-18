/-
# Regret matching commutes with exact legal-menu equivalence

The executable and semantic menus need not be the same carrier. Every action,
its regret coordinate and the explicit fallback are transported by a bijection.
This theorem accounts for positive-part normalization and the all-nonpositive
branch; it does not replace regret matching by an assumed policy oracle.
-/

import GameTheory.Analysis.ReBeL.RationalArithmetic

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Math.Probability

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

/-- Reindexing every local regret coordinate preserves every matcher probability. -/
theorem cast_matchProb_equiv (e : A ≃ B) (fallback : A) (score : A → ℚ)
    (semantic : EuclideanSpace ℝ B)
    (hscore : ∀ a, (score a : ℝ) = semantic.ofLp (e a)) (a : A) :
    (matchProb fallback score a : ℝ) =
      (regretMatchWith (e fallback) semantic).prob (e a) := by
  classical
  have hmass : (positiveMass score : ℝ) = ∑ b, max (semantic.ofLp b) 0 := by
    rw [cast_positiveMass, ← e.sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    exact congrArg (fun value : ℝ => max value 0) (hscore b)
  have hpos : (0 : ℝ) < ∑ b, max (semantic.ofLp b) 0 ↔ 0 < positiveMass score := by
    rw [← hmass]
    exact Rat.cast_pos
  by_cases hp : 0 < positiveMass score
  · rw [matchProb, if_pos hp, regretMatchWith, dif_pos (hpos.mpr hp),
      FinDist.prob_ofWeights, Rat.cast_div, hmass]
    congr 1
    rw [← hscore a]
    push_cast
    rfl
  · rw [matchProb, if_neg hp, regretMatchWith, dif_neg (fun h => hp (hpos.mp h)),
      cast_pointMass, FinDist.prob_pure_eq_ite, FinDist.prob_pure_eq_ite]
    simp only [e.injective.eq_iff]

/-- Equality after exact averaging is independent of the menu's runtime wrapper. -/
theorem matcher_law_map_equiv (e : A ≃ B) (fallback : A) (score : A → ℚ)
    (semantic : EuclideanSpace ℝ B)
    (hscore : ∀ a, (score a : ℝ) = semantic.ofLp (e a)) :
    (matchLaw fallback score).map e = regretMatchWith (e fallback) semantic := by
  classical
  apply FinDist.ext_of_prob
  intro b
  obtain ⟨a, rfl⟩ := e.surjective b
  rw [FinDist.prob_map_of_injective e e.injective, matchLaw, FinDist.prob_ofWeights]
  exact cast_matchProb_equiv e fallback score semantic hscore a

end GameTheory.ReBeL.Rational
