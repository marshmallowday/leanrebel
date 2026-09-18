/-
# Exact weighted policy averaging across a legal-menu bijection

The correspondence preserves all local action probabilities, including the
zero-total fallback branch. It uses the canonical weighted FinDist average
rather than introducing a second behavioral probability semantics.
-/

import GameTheory.Analysis.ReBeL.RationalAverage

noncomputable section

namespace GameTheory.ReBeL.Rational

open GameTheory.Math.Probability

variable {K A B : Type*} [Fintype K] [DecidableEq A]

/-- Reindexing legal actions commutes with exact own-reach weighted averaging. -/
theorem cast_weightedPolicy_equiv (e : A ≃ B) (fallback : A)
    (weights : K → ℚ) (laws : K → A → ℚ)
    (semanticWeights : ReachWeights K) (semanticLaws : K → FinDist B)
    (hweights : ∀ k, (weights k : ℝ) = semanticWeights.weight k)
    (hlaws : ∀ k a, (laws k a : ℝ) = (semanticLaws k).prob (e a)) (a : A) :
    (weightedPolicy fallback weights laws a : ℝ) =
      (semanticWeights.average semanticLaws (FinDist.pure (e fallback))).prob (e a) := by
  classical
  have hmass : ((∑ k, weights k : ℚ) : ℝ) = semanticWeights.mass := by
    unfold ReachWeights.mass
    push_cast
    exact Finset.sum_congr rfl fun k _ => hweights k
  have hpos : 0 < semanticWeights.mass ↔ 0 < ∑ k, weights k := by
    rw [← hmass]
    exact Rat.cast_pos
  by_cases positive : 0 < ∑ k, weights k
  · rw [weightedPolicy, if_pos positive, ReachWeights.average,
      dif_pos (hpos.mpr positive), FinDist.prob_bind, FinDist.expect_eq_sum]
    simp only [ReachWeights.prob_normalize]
    have hnum : ((∑ k, weights k * laws k a : ℚ) : ℝ) =
        ∑ k, semanticWeights.weight k * (semanticLaws k).prob (e a) := by
      push_cast
      apply Finset.sum_congr rfl
      intro k _
      rw [hweights, hlaws]
    rw [Rat.cast_div, hnum, hmass, div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  · rw [weightedPolicy, if_neg positive, ReachWeights.average,
      dif_neg (fun hp => positive (hpos.mp hp)), cast_pointMass,
      FinDist.prob_pure_eq_ite, FinDist.prob_pure_eq_ite]
    simp only [e.injective.eq_iff]

end GameTheory.ReBeL.Rational
