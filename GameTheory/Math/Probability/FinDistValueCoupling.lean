/-
# One-sided payoff comparison through finite couplings

A coupling keeps both actual marginals. Its directed cost charges only an
increase of the selected payoff, not a change of outcome labels. No symmetry,
independence, optimal transport construction or probability floor is assumed.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Math.Probability.FinDist

universe u v
variable {α : Type u} {β : Type v}

/-- Expected positive new-minus-old payoff under one explicit joint law. -/
def directedValueCost (joint : FinDist (α × β)) (oldValue : α → ℝ)
    (newValue : β → ℝ) : ℝ :=
  joint.expect fun pair => max 0 (newValue pair.2 - oldValue pair.1)

/-- Directed payoff cost is nonnegative without any marginal assumptions. -/
theorem directedValueCost_nonneg (joint : FinDist (α × β)) (oldValue : α → ℝ)
    (newValue : β → ℝ) : 0 ≤ directedValueCost joint oldValue newValue := by
  have lower := expect_mono (μ := joint) (u := fun _ => (0 : ℝ))
    (fun pair _ => le_max_left 0 (newValue pair.2 - oldValue pair.1))
  simpa only [expect_const] using lower

/-- The exact marginal identities, not independent resampling, justify the
one-sided expectation comparison. Decreases in payoff need no allowance. -/
theorem expect_sub_le_directedValueCost (old : FinDist α) (fresh : FinDist β)
    (joint : FinDist (α × β)) (oldValue : α → ℝ) (newValue : β → ℝ)
    (oldMarginal : joint.map Prod.fst = old) (newMarginal : joint.map Prod.snd = fresh) :
    fresh.expect newValue - old.expect oldValue ≤ directedValueCost joint oldValue newValue := by
  rw [← oldMarginal, ← newMarginal, expect_map, expect_map, ← expect_sub]
  exact expect_mono (fun pair _ => le_max_right 0 (newValue pair.2 - oldValue pair.1))

/-- A supported pairwise payoff bound supplies a quantitative cost. No
condition is imposed on pairs outside the support of the proposed coupling. -/
theorem directedValueCost_le_of_support (joint : FinDist (α × β))
    (oldValue : α → ℝ) (newValue : β → ℝ) (error : ℝ) (nonneg : 0 ≤ error)
    (bounded : ∀ pair ∈ joint.support, newValue pair.2 - oldValue pair.1 ≤ error) :
    directedValueCost joint oldValue newValue ≤ error := by
  apply expect_le_of_forall
  intro pair reached
  exact max_le nonneg (bounded pair reached)

/-- A coupling supported on non-increasing payoff pairs has exactly zero
cost, even when its two outcome laws have disjoint supports. -/
theorem directedValueCost_eq_zero_of_support (joint : FinDist (α × β))
    (oldValue : α → ℝ) (newValue : β → ℝ)
    (decreasing : ∀ pair ∈ joint.support, newValue pair.2 ≤ oldValue pair.1) :
    directedValueCost joint oldValue newValue = 0 := by
  apply le_antisymm
  · exact directedValueCost_le_of_support joint oldValue newValue 0 (le_refl _)
      (fun pair reached => sub_nonpos.mpr (decreasing pair reached))
  · exact directedValueCost_nonneg joint oldValue newValue

end GameTheory.Math.Probability.FinDist
